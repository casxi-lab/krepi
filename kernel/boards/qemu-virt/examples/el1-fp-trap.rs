//! The test image of an FP/SIMD access at EL1 on QEMU virt: with
//! `CPACR_EL1.FPEN` 0, as the cold entry leaves it, the instruction at the
//! symbol `krepi_test_fp_site` traps, and the dispatch reports the trap and
//! halts.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! The instruction is `FMOV D0, XZR`, written as its encoding because the
//! kernel target has no FP/SIMD registers. On the host the image is an empty
//! program.

#![cfg_attr(all(target_arch = "aarch64", target_os = "none"), no_std, no_main)]

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod common;

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod image {
    use core::arch::global_asm;

    use crate::common;
    use krepi_arch::exception::Frame;
    use krepi_qemu_virt::uart;

    unsafe extern "C" {
        /// Executes `FMOV D0, XZR` at `krepi_test_fp_site` and returns if it
        /// does not trap.
        fn krepi_test_fp();
    }

    // The entry of the image, the cold entry, and the FP/SIMD instruction.
    global_asm!(
        r#"
        .section .text.krepi_test, "ax"
        .global krepi_test_entry
        .type krepi_test_entry, %function
    krepi_test_entry:
        b _start
        .size krepi_test_entry, . - krepi_test_entry

        .global krepi_test_fp
        .type krepi_test_fp, %function
    krepi_test_fp:
        .global krepi_test_fp_site
    krepi_test_fp_site:
        .inst 0x9e6703e0
        ret
        .size krepi_test_fp, . - krepi_test_fp
        "#
    );

    /// The Rust entry of the image, which `_start` calls once on CPU 0.
    #[unsafe(no_mangle)]
    extern "C" fn kernel_main() -> ! {
        common::start("el1-fp-trap");
        // SAFETY: when it does not trap, `krepi_test_fp` writes only `d0`,
        // which no code of the image uses, and returns.
        unsafe { krepi_test_fp() };
        common::check("el1-fp-trap", &[false]);
        common::finish()
    }

    /// The exception dispatch of the image: every exception is reported and
    /// halts, as in the default image.
    #[unsafe(no_mangle)]
    extern "C" fn exception_dispatch(frame: &mut Frame) {
        uart::report_fatal(frame)
    }
}

#[cfg(not(all(target_arch = "aarch64", target_os = "none")))]
fn main() {}
