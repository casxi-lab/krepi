//! The ARM generic timer of the executing CPU: its virtual timer, which
//! fires when the virtual count reaches a deadline.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! The functions write the timer registers of the CPU that executes them at
//! EL1, where EL2 is absent or lets EL1 use them. They touch no memory, but
//! their asm is not `nomem`, so that the compiler keeps the memory accesses
//! around them, such as those of the interrupt controller, on their side.
//! They are compiled only for the bare-metal target.

use core::arch::asm;

/// Stops the virtual timer: `CNTV_CTL_EL0` becomes 0, so that the timer
/// asserts no interrupt.
pub fn stop_virtual() {
    // SAFETY: EL1 owns the virtual timer of the executing CPU; the write and
    // the `ISB` that makes it take effect touch no memory, the stack or the
    // flags.
    unsafe {
        asm!(
            "msr cntv_ctl_el0, xzr",
            "isb",
            options(nostack, preserves_flags)
        )
    };
}

/// Arms the virtual timer to fire once the virtual count reaches
/// `deadline`: `CNTV_CVAL_EL0` becomes `deadline` and `CNTV_CTL_EL0` enables
/// the timer with its interrupt unmasked. The interrupt stays asserted
/// until the timer is armed again or stopped.
pub fn arm_virtual(deadline: u64) {
    // SAFETY: EL1 owns the virtual timer of the executing CPU; the writes and
    // the `ISB` touch no memory, the stack or the flags.
    unsafe {
        asm!(
            "msr cntv_cval_el0, {deadline}",
            "msr cntv_ctl_el0, {enable}",
            "isb",
            deadline = in(reg) deadline,
            enable = in(reg) 1u64,
            options(nostack, preserves_flags)
        )
    };
}
