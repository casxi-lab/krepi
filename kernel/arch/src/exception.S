//! Feature: krepi.platform.qemu-virt-boot
//
// The exception vectors of EL1. The layout of the 304-byte frame is that of
// Frame in exception.rs. Every entry needs a valid SP_EL1 with a frame of
// room below it. Each image defines exception_dispatch(&mut Frame). Only
// the entries of the current EL with SP_EL1, vectors 4 to 7, return; the
// others halt if their dispatch returns.
.section .text.vectors, "ax"
.balign 2048
.global __exception_vectors
.type __exception_vectors, %function
__exception_vectors:
.macro VECTOR number
    .balign 128
    sub sp, sp, #304
    stp x0, x1, [sp, #0]
    mov x0, #\number
    b .Lexception
.endm
    VECTOR 0
    VECTOR 1
    VECTOR 2
    VECTOR 3
    VECTOR 4
    VECTOR 5
    VECTOR 6
    VECTOR 7
    VECTOR 8
    VECTOR 9
    VECTOR 10
    VECTOR 11
    VECTOR 12
    VECTOR 13
    VECTOR 14
    VECTOR 15
.balign 128
.Lexception:
    stp x2, x3, [sp, #16]
    stp x4, x5, [sp, #32]
    stp x6, x7, [sp, #48]
    stp x8, x9, [sp, #64]
    stp x10, x11, [sp, #80]
    stp x12, x13, [sp, #96]
    stp x14, x15, [sp, #112]
    stp x16, x17, [sp, #128]
    stp x18, x19, [sp, #144]
    stp x20, x21, [sp, #160]
    stp x22, x23, [sp, #176]
    stp x24, x25, [sp, #192]
    stp x26, x27, [sp, #208]
    stp x28, x29, [sp, #224]
    str x30, [sp, #240]
    str x0, [sp, #288]
    // Keep the vector number in x19, which the dispatch preserves, so that
    // the choice between return and halt never reads the frame.
    mov x19, x0
    add x1, sp, #304
    str x1, [sp, #248]
    mrs x1, elr_el1
    mrs x2, spsr_el1
    stp x1, x2, [sp, #256]
    mrs x1, esr_el1
    mrs x2, far_el1
    stp x1, x2, [sp, #272]
    str xzr, [sp, #296]
    // Taking an exception to EL1 has set D, A, I and F already; the write
    // keeps them set during the dispatch whatever state the entry left.
    msr daifset, #0xf
    mov x0, sp
    bl exception_dispatch
    // The dispatch may have unmasked exceptions; mask them again, so that
    // none is taken between the writes of ELR_EL1 and SPSR_EL1 and the ERET.
    msr daifset, #0xf
    sub x0, x19, #4
    cmp x0, #3
    b.hi .Lhalt
    ldp x1, x2, [sp, #256]
    msr elr_el1, x1
    msr spsr_el1, x2
    // Clear every general register, then load each from the frame. The
    // loads alone return the saved values; the clear makes a register that
    // a load missed read 0 rather than a value of the dispatch.
    mov x0, xzr
    mov x1, xzr
    mov x2, xzr
    mov x3, xzr
    mov x4, xzr
    mov x5, xzr
    mov x6, xzr
    mov x7, xzr
    mov x8, xzr
    mov x9, xzr
    mov x10, xzr
    mov x11, xzr
    mov x12, xzr
    mov x13, xzr
    mov x14, xzr
    mov x15, xzr
    mov x16, xzr
    mov x17, xzr
    mov x18, xzr
    mov x19, xzr
    mov x20, xzr
    mov x21, xzr
    mov x22, xzr
    mov x23, xzr
    mov x24, xzr
    mov x25, xzr
    mov x26, xzr
    mov x27, xzr
    mov x28, xzr
    mov x29, xzr
    mov x30, xzr
    ldp x0, x1, [sp, #0]
    ldp x2, x3, [sp, #16]
    ldp x4, x5, [sp, #32]
    ldp x6, x7, [sp, #48]
    ldp x8, x9, [sp, #64]
    ldp x10, x11, [sp, #80]
    ldp x12, x13, [sp, #96]
    ldp x14, x15, [sp, #112]
    ldp x16, x17, [sp, #128]
    ldp x18, x19, [sp, #144]
    ldp x20, x21, [sp, #160]
    ldp x22, x23, [sp, #176]
    ldp x24, x25, [sp, #192]
    ldp x26, x27, [sp, #208]
    ldp x28, x29, [sp, #224]
    ldr x30, [sp, #240]
    add sp, sp, #304
    eret
.Lhalt:
    msr daifset, #0xf
    wfe
    b .Lhalt
.size __exception_vectors, . - __exception_vectors
