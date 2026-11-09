//! The test image of an interrupt other than the timer interrupt on QEMU
//! virt: the physical timer of the CPU interrupts as the private peripheral
//! interrupt 30, and the board's `irq::handle` disables it and ends it.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! The image sets the interrupts up with the board's `irq::init` and stops
//! the virtual timer, so that interrupt 27 does not come. It enables
//! interrupt 30 in the GICv2, arms the physical timer to fire at once and
//! waits in `krepi_test_wait`, which unmasks IRQs, until an interrupt has
//! come or [`WAIT_MS`] have passed. The dispatch writes the exception
//! record and calls `irq::handle`, which must take interrupt 30 as
//! unexpected, disable it and end it; the physical timer keeps its level up,
//! so an interrupt left enabled would come again at once. The image then
//! stops the physical timer, checks that one interrupt came, that it was
//! interrupt 30 and that it is disabled, and writes `CASXI_RESUMED`. On the
//! host it is an empty program.

#![cfg_attr(all(target_arch = "aarch64", target_os = "none"), no_std, no_main)]

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod common;

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod image {
    use core::arch::{asm, global_asm};
    use core::ptr;

    use crate::common;
    use krepi_arch::exception::{Frame, IRQ};
    use krepi_arch::gic::{self, Gic};
    use krepi_arch::{cpu, timer};
    use krepi_qemu_virt::console::window_ticks;
    use krepi_qemu_virt::irq::{self, Interrupt};
    use krepi_qemu_virt::{GIC_CPU, GIC_DISTRIBUTOR, TIMER_PRIORITY, uart};

    /// The interrupt ID of the physical timer of the CPU on QEMU virt, the
    /// private peripheral interrupt 30.
    const PHYSICAL_TIMER: u32 = 30;
    /// The offset of `GICD_ISENABLER0`, whose bit `n` is set while the
    /// interrupt `n` is enabled.
    const GICD_ISENABLER0: usize = 0x100;
    /// The longest wait for the interrupt, in milliseconds on the counter: a
    /// platform parameter of the test images on QEMU virt, where it comes at
    /// once.
    const WAIT_MS: u64 = 1000;

    /// The entries of the dispatch.
    static mut ENTRIES: u64 = 0;
    /// What `irq::handle` returned at the first entry.
    static mut TAKEN: Option<Interrupt> = None;

    unsafe extern "C" {
        /// Unmasks IRQs, waits until the word at `count` is at least
        /// `target` or the virtual count reaches `deadline`, and masks IRQs
        /// again; an IRQ is taken within
        /// `[krepi_test_wait, krepi_test_wait_end)`.
        fn krepi_test_wait(count: *const u64, target: u64, deadline: u64);
    }

    // The entry of the image, the cold entry, and the wait with IRQs
    // unmasked.
    global_asm!(
        r#"
        .section .text.krepi_test, "ax"
        .global krepi_test_entry
        .type krepi_test_entry, %function
    krepi_test_entry:
        b _start
        .size krepi_test_entry, . - krepi_test_entry

        .global krepi_test_wait
        .type krepi_test_wait, %function
    krepi_test_wait:
        msr daifclr, #2
    1:
        ldr x3, [x0]
        cmp x3, x1
        b.hs 2f
        isb
        mrs x3, cntvct_el0
        cmp x3, x2
        b.lo 1b
    2:
        msr daifset, #2
        ret
        .global krepi_test_wait_end
    krepi_test_wait_end:
        .size krepi_test_wait, . - krepi_test_wait
        "#
    );

    /// Reads a static of the image.
    fn load<T: Copy>(source: *const T) -> T {
        // SAFETY: `source` is an aligned, initialized static of this image;
        // only CPU 0 runs, and the dispatch, which writes it, runs with every
        // exception masked between two instructions of the code it
        // interrupts, so the read races with no write.
        unsafe { ptr::read_volatile(source) }
    }

    /// Writes a static of the image.
    fn store<T>(destination: *mut T, value: T) {
        // SAFETY: as in `load`: an aligned static of this image, written only
        // by the dispatch.
        unsafe { ptr::write_volatile(destination, value) }
    }

    /// Arms the physical timer with a deadline of 0, which the count has
    /// passed, so that it asserts its interrupt at once.
    fn arm_physical_now() {
        // SAFETY: EL1 owns the physical timer of the executing CPU on QEMU
        // virt without EL2; the writes and the `ISB` touch no memory, the
        // stack or the flags.
        unsafe {
            asm!(
                "msr cntp_cval_el0, xzr",
                "msr cntp_ctl_el0, {enable}",
                "isb",
                enable = in(reg) 1u64,
                options(nostack, preserves_flags)
            )
        };
    }

    /// Stops the physical timer, so that it asserts no interrupt.
    fn stop_physical() {
        // SAFETY: as in `arm_physical_now`.
        unsafe {
            asm!(
                "msr cntp_ctl_el0, xzr",
                "isb",
                options(nostack, preserves_flags)
            )
        };
    }

    /// The Rust entry of the image, which `_start` calls once on CPU 0.
    #[unsafe(no_mangle)]
    extern "C" fn kernel_main() -> ! {
        common::start("unexpected-irq");
        irq::init();
        timer::stop_virtual();
        // SAFETY: these are the distributor and the CPU interface of the
        // GICv2 of QEMU virt, which the MMU, off, reaches as Device memory;
        // only CPU 0 uses the controller, here with IRQs masked and in the
        // dispatch with every exception masked.
        let gic = unsafe { Gic::new(GIC_DISTRIBUTOR, GIC_CPU) };
        gic.enable_ppi(PHYSICAL_TIMER, TIMER_PRIORITY);
        arm_physical_now();
        gic::barrier();
        let deadline =
            cpu::virtual_counter().wrapping_add(window_ticks(cpu::counter_frequency(), WAIT_MS));
        // SAFETY: `krepi_test_wait` reads the counter of the entries and the
        // virtual count, uses only `x3` besides its arguments, and leaves
        // IRQs masked as it found them.
        unsafe { krepi_test_wait(&raw const ENTRIES, 1, deadline) };
        stop_physical();
        // SAFETY: `GICD_ISENABLER0` is an aligned register of the
        // distributor above, read with IRQs masked.
        let enabled =
            unsafe { ptr::read_volatile((GIC_DISTRIBUTOR + GICD_ISENABLER0) as *const u32) };
        common::check(
            "unexpected-irq-disabled",
            &[
                load(&raw const ENTRIES) == 1,
                load(&raw const TAKEN) == Some(Interrupt::Unexpected(PHYSICAL_TIMER)),
                enabled & (1 << PHYSICAL_TIMER) == 0,
            ],
        );
        common::finish()
    }

    /// The exception dispatch of the image: an IRQ is reported and handled
    /// by `irq::handle`, the first one recorded, and the dispatch returns;
    /// any other exception is fatal.
    #[unsafe(no_mangle)]
    extern "C" fn exception_dispatch(frame: &mut Frame) {
        if frame.vector != IRQ {
            uart::report_fatal(frame);
        }
        let entries = load(&raw const ENTRIES) + 1;
        store(&raw mut ENTRIES, entries);
        uart::report_exception(frame);
        let taken = irq::handle();
        if entries == 1 {
            store(&raw mut TAKEN, Some(taken));
        }
    }
}

#[cfg(not(all(target_arch = "aarch64", target_os = "none")))]
fn main() {}
