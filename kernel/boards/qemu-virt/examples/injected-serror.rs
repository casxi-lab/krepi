//! The test image of an SError at EL1 on QEMU virt with EL2: its own entry
//! at EL2 makes a virtual SError pending through `HCR_EL2.VSE` and drops to
//! the cold entry at EL1, where the image unmasks SErrors and the dispatch
//! reports the SError and halts.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! The entry `krepi_test_entry` runs at EL2 without a stack. It sets
//! `HCR_EL2` to RW, so that EL1 is AArch64, AMO, which routes SErrors to
//! EL2 and lets the virtual SError reach EL1, and VSE, which makes the
//! virtual SError pending. It gives EL1 the physical counter and timer
//! (`CNTHCTL_EL2` 3), a virtual offset of 0, the syndrome 0 for the virtual
//! SError (`VSESR_EL2`) and the affinity of the CPU in `VMPIDR_EL2`, which
//! EL1 reads as `MPIDR_EL1`. It then returns to `_start` at EL1 with
//! `SP_EL1` and every exception masked. The image runs only on the machine
//! with EL2. On the host it is an empty program.

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
        /// Unmasks SErrors and synchronizes the context, so that a pending
        /// SError is taken within `[krepi_test_serror, krepi_test_serror_end)`;
        /// masks them again and returns when none was.
        fn krepi_test_serror();
    }

    // The entry of the image at EL2, as the module documentation describes,
    // and the code that unmasks SErrors at EL1.
    global_asm!(
        r#"
        .section .text.krepi_test, "ax"
        .global krepi_test_entry
        .type krepi_test_entry, %function
    krepi_test_entry:
        mov x0, #(1 << 31)
        orr x0, x0, #(1 << 8)
        orr x0, x0, #(1 << 5)
        msr hcr_el2, x0
        mov x0, #3
        msr cnthctl_el2, x0
        msr cntvoff_el2, xzr
        msr S3_4_C5_C2_3, xzr
        mrs x0, mpidr_el1
        msr vmpidr_el2, x0
        mov x0, #0x3c5
        msr spsr_el2, x0
        adrp x0, _start
        add x0, x0, :lo12:_start
        msr elr_el2, x0
        isb
        eret
        .size krepi_test_entry, . - krepi_test_entry

        .global krepi_test_serror
        .type krepi_test_serror, %function
    krepi_test_serror:
        msr daifclr, #4
        isb
        msr daifset, #4
        ret
        .global krepi_test_serror_end
    krepi_test_serror_end:
        .size krepi_test_serror, . - krepi_test_serror
        "#
    );

    /// The Rust entry of the image, which `_start` calls once on CPU 0 at
    /// EL1.
    #[unsafe(no_mangle)]
    extern "C" fn kernel_main() -> ! {
        common::start("injected-serror");
        // SAFETY: `krepi_test_serror` changes only `PSTATE.A`, which it masks
        // again before it returns, and touches no memory or register of the
        // calling convention.
        unsafe { krepi_test_serror() };
        common::check("injected-serror", &[false]);
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
