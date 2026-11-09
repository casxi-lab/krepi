//! The QEMU virt default image of krepi.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! The cold entry `_start` of `krepi-arch` calls `kernel_main` at EL1 on
//! CPU 0, with every exception masked, the MMU and the caches off, BSS and
//! the stack cleared and FP/SIMD instructions trapping. The image checks that
//! state, writes its boot records to the PL011 console and then echoes every
//! byte that it receives. It holds no diagnostic operation, fault probe or
//! command that a received byte triggers.
//!
//! The image runs only on the bare-metal target. On the host, where the
//! repository checks build and lint the crate, the binary is an empty
//! program.

#![cfg_attr(all(target_arch = "aarch64", target_os = "none"), no_std, no_main)]

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod image {
    use core::panic::PanicInfo;
    use core::ptr;

    use krepi_arch::cpu;
    use krepi_qemu_virt::console::PanicLocation;
    use krepi_qemu_virt::{uart, verify_cpu};

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
