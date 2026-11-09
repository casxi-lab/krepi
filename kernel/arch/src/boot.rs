//! The cold entry of a krepi image: the assembly of `_start`, the ELF entry
//! point, in the section `.text.boot`, which the link script of the image
//! places first.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! `_start` runs before any Rust code. It masks every exception with
//! `DAIF`, parks every CPU whose `MPIDR_EL1` affinity 0 to 2 is not 0 and a
//! CPU that is not at EL1, makes FP/SIMD instructions trap at EL0 and EL1
//! through `CPACR_EL1.FPEN`, clears `TPIDR_EL1`, selects `SP_EL1`, sets the
//! stack pointer to `__stack_top`, clears `[__bss_start, __bss_end)` and the
//! stack from `__stack_bottom` up to the stack pointer, clears the frame
//! pointer and the link register and calls `kernel_main`, which never
//! returns. The link script provides the four symbols, all 8-byte aligned,
//! and the image provides `kernel_main` as an `extern "C" fn() -> !`.

core::arch::global_asm!(include_str!("boot.S"));
