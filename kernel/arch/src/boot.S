//! Feature: krepi.platform.qemu-virt-boot
//
// The cold entry of a krepi image. Contract: one Cortex-A76 enters it at
// EL1h with the MMU and the caches off. The link script provides
// __stack_top, __stack_bottom, __bss_start and __bss_end, each 8-byte
// aligned, exception.S provides __exception_vectors and the image provides
// kernel_main, which never returns. A CPU other than CPU 0, or one that is
// not at EL1, parks here and never enters Rust.
.section .text.boot, "ax"
.global _start
.type _start, %function
_start:
    msr daifset, #0xf
    mrs x1, mpidr_el1
    and x1, x1, #0xffffff
    cbnz x1, .Lpark
    mrs x1, CurrentEL
    cmp x1, #4
    b.ne .Lpark
    // Make FP/SIMD instructions trap by default (CPACR_EL1.FPEN = 0).
    mrs x1, cpacr_el1
    bic x1, x1, #(3 << 20)
    msr cpacr_el1, x1
    msr tpidr_el1, xzr
    isb
    msr spsel, #1
    adrp x1, __stack_top
    add x1, x1, :lo12:__stack_top
    mov sp, x1

    // Clear only BSS. The stack occupies a separate NOLOAD section.
    adrp x1, __bss_start
    add x1, x1, :lo12:__bss_start
    adrp x2, __bss_end
    add x2, x2, :lo12:__bss_end
.Lbss:
    cmp x1, x2
    b.hs .Lbss_done
    str xzr, [x1], #8
    b .Lbss
.Lbss_done:
    // Install the exception vectors of exception.S.
    adrp x1, __exception_vectors
    add x1, x1, :lo12:__exception_vectors
    msr vbar_el1, x1
    isb
    // Clear the whole stack before the first Rust frame is created, so that
    // a bounded read of frame records never finds stale bytes.
    adrp x1, __stack_bottom
    add x1, x1, :lo12:__stack_bottom
    mov x2, sp
.Lstack_clear:
    cmp x1, x2
    b.hs .Lstack_ready
    str xzr, [x1], #8
    b .Lstack_clear
.Lstack_ready:
    mov x29, xzr
    mov x30, xzr
    bl kernel_main
.Lpark:
    wfe
    b .Lpark
.size _start, . - _start
