//! The QEMU virt default image of krepi.
//!
//! Feature: krepi.platform.qemu-virt-boot
//! Feature: krepi.platform.device-tree
//! Feature: krepi.kernel.kernel-memory
//!
//! The cold entry `_start` of `krepi-arch` calls `kernel_main` at EL1 on
//! CPU 0, with every exception masked, the exception vectors installed, the
//! MMU and the caches off, BSS and the stack cleared and FP/SIMD
//! instructions trapping. The image checks that state and writes its boot
//! record to the PL011 console. It then reads the device tree that QEMU's
//! loader placed at the start of RAM, builds the boot memory map, the page
//! ownership table and the kernel tables and turns the MMU on with the
//! caches off, writes its ready record and echoes every byte that it
//! receives. Its exception dispatch reports every exception that the vectors
//! take and halts. It holds no diagnostic operation, fault probe or command
//! that a received byte triggers.
//!
//! The image runs only on the bare-metal target. On the host, where the
//! repository checks build and lint the crate, the binary is an empty
//! program.

#![cfg_attr(all(target_arch = "aarch64", target_os = "none"), no_std, no_main)]

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod image {
    use core::panic::PanicInfo;
    use core::{ptr, slice};

    use krepi_arch::cpu;
    use krepi_arch::exception::Frame;
    use krepi_kernel::fdt::MAX_BLOB_SIZE;
    use krepi_qemu_virt::boot_memory::{TREE_BASE, Wired, wire};
    use krepi_qemu_virt::console::PanicLocation;
    use krepi_qemu_virt::{CPU_MODEL, MIDR_CORTEX_A76, MIDR_PART_MASK, uart};

    /// The size of the header of a device tree, which holds its
    /// `totalsize` at offset 4.
    const HEADER_SIZE: usize = 40;

    /// The value of [`DATA_PROBE`] in the image.
    const DATA_PATTERN: u64 = 0x4341_5358_4900_0001;

    /// The bits of `SCTLR_EL1` that must be clear at entry: the MMU (M, bit
    /// 0), the data cache (C, bit 2) and the instruction cache (I, bit 12).
    const MMU_AND_CACHES: u64 = (1 << 0) | (1 << 2) | (1 << 12);

    /// The bit of `SCTLR_EL1` that makes EL1 data accesses big-endian (EE,
    /// bit 25), which must be clear at entry.
    const BIG_ENDIAN: u64 = 1 << 25;

    /// The `FPEN` field of `CPACR_EL1`, which must be 0 so that FP/SIMD
    /// instructions trap.
    const FP_ENABLE: u64 = 3 << 20;

    /// A word in BSS, which the cold entry clears.
    static mut BSS_PROBE: u64 = 0;
    /// A word in the data section, which QEMU loads with the image.
    static mut DATA_PROBE: u64 = DATA_PATTERN;

    /// The Rust entry of the image, which `_start` calls once on CPU 0.
    #[unsafe(no_mangle)]
    extern "C" fn kernel_main() -> ! {
        initialize();
        uart::print(format_args!(
            "CASXI_BOOT kernel=krepi board=qemu-virt el={}\n",
            cpu::exception_level()
        ));
        let _memory = boot_memory(device_tree());
        uart::print(format_args!("CASXI_READY\n"));
        loop {
            match uart::get() {
                Some(byte) => uart::write_echo(byte),
                None => core::hint::spin_loop(),
            }
        }
    }

    /// Sets the console up and checks the state that the cold entry left;
    /// a check that fails panics. Its temporaries leave the stack before the
    /// echo loop runs.
    #[inline(never)]
    fn initialize() {
        uart::init();
        // SAFETY: the cold entry cleared BSS before it called Rust, and only
        // CPU 0 runs. The volatile read of the raw pointer keeps the probe in
        // the linked BSS and reads the word as memory holds it.
        let bss = unsafe { ptr::read_volatile(&raw const BSS_PROBE) };
        // SAFETY: `DATA_PROBE` lies in the image's data section, which QEMU
        // loaded, and nothing writes it. The volatile read of the raw pointer
        // reads the word as memory holds it.
        let data = unsafe { ptr::read_volatile(&raw const DATA_PROBE) };
        assert!(bss == 0, "BSS not initialized");
        assert!(data == DATA_PATTERN, "data not initialized");
        assert!(cpu::exception_level() == 1, "kernel requires EL1");
        let control = cpu::system_control();
        assert!(control & MMU_AND_CACHES == 0, "MMU/cache must be off");
        verify_cpu();
        assert!(control & BIG_ENDIAN == 0, "EL1 data must be little-endian");
        assert!(cpu::cpacr() & FP_ENABLE == 0, "FP/SIMD must trap");
    }

    /// Checks the CPU identity independently of the QEMU command line and
    /// the device tree, and writes the CPU identity record: the CPU must be
    /// a Cortex-A76 of any variant and revision.
    ///
    /// # Panics
    ///
    /// Panics with `QEMU Cortex-A76 required` on any other CPU.
    fn verify_cpu() {
        let midr = cpu::main_id();
        assert!(
            midr & MIDR_PART_MASK == MIDR_CORTEX_A76,
            "QEMU Cortex-A76 required"
        );
        uart::print(format_args!(
            "CASXI_CPU model={CPU_MODEL} midr={midr:#018x}\n"
        ));
    }

    /// The device tree that QEMU's loader placed at the start of RAM: the
    /// slice of its 40-byte header, then of its `totalsize` bytes once that
    /// is at least 40 and at most `MAX_BLOB_SIZE`, 2 MiB, so that the tree
    /// ends at or below the start of the image, which the link script puts
    /// 2 MiB above the start of RAM.
    ///
    /// # Panics
    ///
    /// Panics with `device tree size out of bounds` on another `totalsize`.
    fn device_tree() -> &'static [u8] {
        // SAFETY: the 40 bytes at `TREE_BASE` are RAM below the image, where
        // QEMU's loader places the tree, which the CPU reads with the MMU off
        // and which nothing writes while the kernel runs; a byte slice needs
        // no alignment.
        let header = unsafe { slice::from_raw_parts(TREE_BASE as *const u8, HEADER_SIZE) };
        let size = u32::from_be_bytes([header[4], header[5], header[6], header[7]]);
        let size = u64::from(size);
        assert!(
            (HEADER_SIZE as u64..=MAX_BLOB_SIZE).contains(&size),
            "device tree size out of bounds"
        );
        // SAFETY: the `size` bytes from `TREE_BASE` are RAM below the start
        // of the image, which the bound above keeps them in, and hold the
        // tree, which nothing writes while the kernel runs.
        unsafe { slice::from_raw_parts(TREE_BASE as *const u8, size as usize) }
    }

    /// Builds the boot memory, the kernel tables and the page ownership
    /// table from the device tree `tree` and turns the MMU on, through the
    /// boot wiring of the board.
    fn boot_memory(tree: &'static [u8]) -> Wired {
        // SAFETY: `kernel_main` calls this function once, on CPU 0 at EL1,
        // with every exception masked and the MMU off, which `initialize`
        // checked, and `tree` is the tree at the start of RAM that
        // `device_tree` formed, which nothing writes.
        unsafe { wire(tree) }
    }

    /// The exception dispatch of the image, which the vectors of
    /// `krepi-arch` call with every exception masked: it writes the
    /// exception record of `frame` and `CASXI_HALTED` and halts. The image
    /// never unmasks an exception, so only a synchronous exception of its
    /// own code reaches it.
    #[unsafe(no_mangle)]
    extern "C" fn exception_dispatch(frame: &mut Frame) {
        uart::report_fatal(frame)
    }

    /// Writes the panic record and halts. Only a static message is written:
    /// the formatting of a dynamic message could run arbitrary code on a
    /// fatal path.
    #[panic_handler]
    fn panic(info: &PanicInfo<'_>) -> ! {
        let location = info.location().map(|location| PanicLocation {
            file: location.file(),
            line: location.line(),
            column: location.column(),
        });
        uart::report_panic(info.message().as_str(), location);
        cpu::halt()
    }
}

#[cfg(not(all(target_arch = "aarch64", target_os = "none")))]
fn main() {}
