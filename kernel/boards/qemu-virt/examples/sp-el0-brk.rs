//! The test image of an exception at EL1 with `SP_EL0` selected on QEMU
//! virt: `BRK #0x5e` at the symbol `krepi_test_sp0_site`, with `SPSel` 0,
//! enters vector 0, whose return path halts once the dispatch returns.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! Before the breakpoint the code records `SP_EL1`, puts a value of its own
//! into `SP_EL0` and selects it. The dispatch writes the exception record,
//! checks that the frame records the stack pointer above it on `SP_EL1`
//! rather than `SP_EL0`, moves `ELR` in the frame past the breakpoint and
//! returns. The vectors must then halt: if they returned, the code after
//! the breakpoint would select `SP_EL1` again and the image would write
//! `CASXI_RESUMED`. On the host the image is an empty program.

#![cfg_attr(all(target_arch = "aarch64", target_os = "none"), no_std, no_main)]

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod common;

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod image {
    use core::arch::global_asm;
    use core::ptr;

    use crate::common;
    use krepi_arch::exception::{FRAME_BYTES, Frame};
    use krepi_qemu_virt::uart;

    /// The vector of a synchronous exception at the current exception level
    /// with `SP_EL0`.
    const SYNC_SP_EL0: u64 = 0;
    /// The mode field of `SPSR_EL1`, bits 0 to 3.
    const MODE: u64 = 0xf;
    /// The mode EL1 with `SP_EL0`, EL1t.
    const EL1T: u64 = 0x4;
    /// The value that the code puts into `SP_EL0`, which no stack pointer of
    /// the image has.
    const SP_EL0_VALUE: u64 = 0x5a5a_5a50;

    /// `SP_EL1` just before the breakpoint.
    static mut SP_EL1: u64 = 0;
    /// The entries of the dispatch.
    static mut ENTRIES: u64 = 0;

    unsafe extern "C" {
        /// Records `SP_EL1` at `sp_el1`, selects `SP_EL0` with
        /// [`SP_EL0_VALUE`] in it, executes the breakpoint and, if execution
        /// continues after it, selects `SP_EL1` again and returns.
        fn krepi_test_sp0(sp_el1: *mut u64);
    }

    // The entry of the image, the cold entry, and the breakpoint with SP_EL0
    // selected. Between the selection and the breakpoint the code does not
    // use the stack.
    global_asm!(
        r#"
        .section .text.krepi_test, "ax"
        .global krepi_test_entry
        .type krepi_test_entry, %function
    krepi_test_entry:
        b _start
        .size krepi_test_entry, . - krepi_test_entry

        .global krepi_test_sp0
        .type krepi_test_sp0, %function
    krepi_test_sp0:
        mov x1, sp
        str x1, [x0]
        movz x1, #0x5a50
        movk x1, #0x5a5a, lsl #16
        msr sp_el0, x1
        msr spsel, #0
        .global krepi_test_sp0_site
    krepi_test_sp0_site:
        brk #0x5e
        msr spsel, #1
        ret
        .size krepi_test_sp0, . - krepi_test_sp0
        "#
    );

    /// Reads a static of the image.
    fn load(source: *const u64) -> u64 {
        // SAFETY: `source` is an aligned, initialized static of this image;
        // only CPU 0 runs, and no other code accesses it during the read.
        unsafe { ptr::read_volatile(source) }
    }

    /// Writes a static of the image.
    fn store(destination: *mut u64, value: u64) {
        // SAFETY: as in `load`: an aligned static of this image that no other
        // code accesses during the write.
        unsafe { ptr::write_volatile(destination, value) }
    }

    /// The Rust entry of the image, which `_start` calls once on CPU 0.
    #[unsafe(no_mangle)]
    extern "C" fn kernel_main() -> ! {
        common::start("sp-el0-brk");
        // SAFETY: `krepi_test_sp0` writes only the static at its argument,
        // `x1`, `SP_EL0` and `SPSel`, which it selects as `SP_EL1` again
        // before it returns; it uses no stack while `SP_EL0` is selected.
        unsafe { krepi_test_sp0(&raw mut SP_EL1) };
        common::finish()
    }

    /// The exception dispatch of the image: the first breakpoint is
    /// reported and checked, and the dispatch returns past it, so that only
    /// the halt of the vectors keeps the code from resuming; any other
    /// exception, or a second one, is fatal.
    #[unsafe(no_mangle)]
    extern "C" fn exception_dispatch(frame: &mut Frame) {
        let entries = load(&raw const ENTRIES) + 1;
        store(&raw mut ENTRIES, entries);
        if entries != 1 || frame.vector != SYNC_SP_EL0 {
            uart::report_fatal(frame);
        }
        uart::report_exception(frame);
        let top = (ptr::from_mut(frame) as u64).wrapping_add(FRAME_BYTES as u64);
        common::check(
            "sp-el0-frame-records-sp-el1",
            &[
                frame.sp == top,
                frame.sp == load(&raw const SP_EL1),
                frame.sp != SP_EL0_VALUE,
                frame.spsr & MODE == EL1T,
            ],
        );
        frame.elr += 4;
    }
}

#[cfg(not(all(target_arch = "aarch64", target_os = "none")))]
fn main() {}
