//! The test image of the timer interrupt on QEMU virt: the virtual timer
//! interrupts through the GICv2 as interrupt 27, the IRQ vector of EL1
//! takes it, and the dispatch reports it, ends it and returns.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! The image sets the interrupts up with the board's `irq::init` and waits
//! in `krepi_test_wait`, which unmasks IRQs, until two timer interrupts have
//! come or [`WAIT_MS`] have passed. The dispatch reads `DAIF`, writes the
//! exception record, acknowledges and ends the interrupt with the board's
//! `irq::handle` and returns; after the second timer interrupt it stops the
//! timer, so that exactly two arrive. The image then checks the interrupts,
//! among them that the second came at least one period after the first had
//! entered the dispatch, which only the re-arm in `irq::handle` makes so,
//! and the masking of the dispatch, and writes `CASXI_RESUMED`. On the host
//! it is an empty program.

#![cfg_attr(all(target_arch = "aarch64", target_os = "none"), no_std, no_main)]

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod common;

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod image {
    use core::arch::{asm, global_asm};
    use core::ptr;

    use crate::common;
    use krepi_arch::exception::{Frame, IRQ};
    use krepi_arch::{cpu, timer};
    use krepi_qemu_virt::console::window_ticks;
    use krepi_qemu_virt::irq::{self, Interrupt};
    use krepi_qemu_virt::{TIMER_RATE, uart};

    /// The timer interrupts that the image waits for.
    const TICKS: u64 = 2;
    /// The longest wait for them, in milliseconds on the counter: a platform
    /// parameter of the test images on QEMU virt, where they take 20 ms.
    const WAIT_MS: u64 = 1000;
    /// `DAIF` with D, A, I and F set.
    const ALL_MASKED: u64 = 0x3c0;

    /// The timer interrupts that the dispatch took.
    static mut TIMER: u64 = 0;
    /// The interrupts that were not the timer interrupt.
    static mut OTHER: u64 = 0;
    /// The entries of the dispatch at which `DAIF` was not [`ALL_MASKED`].
    static mut UNMASKED: u64 = 0;
    /// The virtual count at the entry of the dispatch of the first timer
    /// interrupt.
    static mut FIRST: u64 = 0;
    /// The virtual count at the entry of the dispatch of the second.
    static mut SECOND: u64 = 0;

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
    fn load(source: *const u64) -> u64 {
        // SAFETY: `source` is an aligned, initialized static of this image;
        // only CPU 0 runs, and the dispatch, which writes it, runs with every
        // exception masked between two instructions of the code it
        // interrupts, so the read races with no write.
        unsafe { ptr::read_volatile(source) }
    }

    /// Writes a static of the image.
    fn store(destination: *mut u64, value: u64) {
        // SAFETY: as in `load`: an aligned static of this image, written only
        // by the dispatch.
        unsafe { ptr::write_volatile(destination, value) }
    }

    /// The Rust entry of the image, which `_start` calls once on CPU 0.
    #[unsafe(no_mangle)]
    extern "C" fn kernel_main() -> ! {
        common::start("timer-irq");
        irq::init();
        let deadline =
            cpu::virtual_counter().wrapping_add(window_ticks(cpu::counter_frequency(), WAIT_MS));
        // SAFETY: `krepi_test_wait` reads the counter of the timer interrupts
        // and the virtual count, uses only `x3` besides its arguments, and
        // leaves IRQs masked as it found them.
        unsafe { krepi_test_wait(&raw const TIMER, TICKS, deadline) };
        let ticks = load(&raw const TIMER);
        // The period of `irq`: the counter frequency divided by the rate,
        // rounded up, and at least 1.
        let period = cpu::counter_frequency().div_ceil(TIMER_RATE).max(1);
        let gap = load(&raw const SECOND).wrapping_sub(load(&raw const FIRST));
        common::check(
            "timer-irq",
            &[ticks == TICKS, load(&raw const OTHER) == 0, gap >= period],
        );
        common::check(
            "dispatch-masks-daif",
            &[ticks > 0, load(&raw const UNMASKED) == 0],
        );
        common::finish()
    }

    /// `DAIF` of the executing CPU.
    fn daif() -> u64 {
        let value: u64;
        // SAFETY: `DAIF` is readable at EL1; the read has no side effect and
        // touches no memory, the stack or the flags.
        unsafe { asm!("mrs {}, daif", out(reg) value, options(nomem, nostack, preserves_flags)) };
        value
    }

    /// The exception dispatch of the image: an IRQ is reported, acknowledged
    /// and ended, and the dispatch returns; any other exception is fatal.
    /// The virtual count at the entry of the first two timer interrupts is
    /// kept.
    #[unsafe(no_mangle)]
    extern "C" fn exception_dispatch(frame: &mut Frame) {
        let entered = cpu::virtual_counter();
        if daif() != ALL_MASKED {
            store(&raw mut UNMASKED, load(&raw const UNMASKED) + 1);
        }
        if frame.vector != IRQ {
            uart::report_fatal(frame);
        }
        uart::report_exception(frame);
        if irq::handle() == Interrupt::Timer {
            let ticks = load(&raw const TIMER) + 1;
            store(&raw mut TIMER, ticks);
            match ticks {
                1 => store(&raw mut FIRST, entered),
                TICKS => {
                    store(&raw mut SECOND, entered);
                    timer::stop_virtual();
                }
                _ => {}
            }
        } else {
            store(&raw mut OTHER, load(&raw const OTHER) + 1);
        }
    }
}

#[cfg(not(all(target_arch = "aarch64", target_os = "none")))]
fn main() {}
