//! The processor registers that EL1 code reads, and the halt of the
//! executing CPU.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! Each function acts on the CPU that executes it, and only on its system
//! registers: none reads or writes memory, so none needs a lock or a barrier
//! against another CPU. They are written for the state that the cold entry
//! `_start` establishes, AArch64 at EL1h, and are compiled only for the
//! bare-metal target.

use core::arch::asm;

/// The exception level that the CPU executes at, from `CurrentEL`: 1 for the
/// kernel.
pub fn exception_level() -> u64 {
    let value: u64;
    // SAFETY: `CurrentEL` is readable at every exception level above EL0,
    // and the cold entry enters Rust only at EL1. The read has no side effect
    // and touches no memory, the stack or the condition flags.
    unsafe { asm!("mrs {}, CurrentEL", out(reg) value, options(nomem, nostack, preserves_flags)) };
    value >> 2
}

/// The main ID register `MIDR_EL1`: the implementer, variant, architecture,
/// part number and revision of the CPU.
pub fn main_id() -> u64 {
    let value: u64;
    // SAFETY: `MIDR_EL1` is readable at EL1, where the cold entry enters
    // Rust. The read has no side effect and touches no memory, the stack or
    // the condition flags.
    unsafe { asm!("mrs {}, midr_el1", out(reg) value, options(nomem, nostack, preserves_flags)) };
    value
}

/// The system control register `SCTLR_EL1`, which holds, among others, the
/// MMU enable (bit 0), the data cache enable (bit 2), the instruction cache
/// enable (bit 12) and the endianness of EL1 data accesses (bit 25).
pub fn system_control() -> u64 {
    let value: u64;
    // SAFETY: `SCTLR_EL1` is readable at EL1, where the cold entry enters
    // Rust. The read has no side effect and touches no memory, the stack or
    // the condition flags.
    unsafe { asm!("mrs {}, sctlr_el1", out(reg) value, options(nomem, nostack, preserves_flags)) };
    value
}

/// The frequency of the system counter in ticks per second, from
/// `CNTFRQ_EL0`, as the firmware or the machine set it.
pub fn counter_frequency() -> u64 {
    let value: u64;
    // SAFETY: `CNTFRQ_EL0` is readable at EL1 on every machine that krepi
    // runs on. The read has no side effect and touches no memory, the stack
    // or the condition flags.
    unsafe { asm!("mrs {}, cntfrq_el0", out(reg) value, options(nomem, nostack, preserves_flags)) };
    value
}

/// The virtual count `CNTVCT_EL0`, read after the instructions before it.
pub fn virtual_counter() -> u64 {
    let value: u64;
    // SAFETY: EL1 may read `CNTVCT_EL0` when EL2 is absent or disabled, as on
    // QEMU virt without virtualization. The `ISB` keeps the read after the
    // instructions before it; it is not a barrier for data accesses. The asm
    // is not marked pure or `nomem`, so that the compiler neither merges two
    // reads nor moves one across a memory access; `CNTVCTSS_EL0`, which needs
    // no `ISB`, is not used, as the Cortex-A76 does not implement it.
    unsafe { asm!("isb", "mrs {}, cntvct_el0", out(reg) value, options(nostack, preserves_flags)) };
    value
}

/// The architectural feature access control register `CPACR_EL1`, whose
/// `FPEN` field (bits 20 and 21) is 0 while FP/SIMD instructions trap at EL0
/// and EL1.
pub fn cpacr() -> u64 {
    let value: u64;
    // SAFETY: `CPACR_EL1` is readable at EL1, where the cold entry enters
    // Rust. The read has no side effect and touches no memory, the stack or
    // the condition flags.
    unsafe { asm!("mrs {}, cpacr_el1", out(reg) value, options(nomem, nostack, preserves_flags)) };
    value
}

/// Masks every exception of the executing CPU and waits forever: the end of
/// a fatal path. Other CPUs are not stopped.
pub fn halt() -> ! {
    // SAFETY: EL1 owns `DAIF` of the executing CPU. Masking debug, SError,
    // IRQ and FIQ exceptions keeps any handler from running while the CPU is
    // halted; the write touches no memory, the stack or the condition flags.
    unsafe {
        asm!(
            "msr daifset, #0xf",
            options(nomem, nostack, preserves_flags)
        )
    };
    loop {
        // SAFETY: `WFE` only waits for an event; it touches no memory or the
        // stack, and with every exception masked no handler runs after it.
        unsafe { asm!("wfe", options(nomem, nostack)) };
    }
}
