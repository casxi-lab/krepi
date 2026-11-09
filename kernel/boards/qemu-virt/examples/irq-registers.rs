//! The test image of the registers across an IRQ on QEMU virt: the timer
//! interrupt is taken at one known instruction, `krepi_test_irq_resume`,
//! and the interrupted code finds every register as it left it.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! The image sets the interrupts up with the board's `irq::init` and calls
//! `krepi_test_irq_registers` with IRQs masked. That code records the stack
//! pointer, waits until `ISR_EL1` shows the timer IRQ pending, sets NZCV
//! and a different known value in each of `x0` to `x30`, and unmasks IRQs
//! with `MSR DAIFClr`; QEMU takes the pending IRQ before the next
//! instruction, `krepi_test_irq_resume`, which masks IRQs again. The
//! dispatch copies the frame, writes the exception record, ends the
//! interrupt with the board's `irq::handle`, stops the timer and returns.
//! The resumed code then records `x0` to `x30`, the stack pointer, NZCV,
//! `ELR_EL1` and `SPSR_EL1`, and the image checks them against the values
//! from before and against the frame. On the host it is an empty program.

#![cfg_attr(all(target_arch = "aarch64", target_os = "none"), no_std, no_main)]

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod common;

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod image {
    use core::arch::global_asm;
    use core::ptr;

    use crate::common;
    use krepi_arch::exception::{Frame, IRQ};
    use krepi_arch::{cpu, timer};
    use krepi_qemu_virt::console::window_ticks;
    use krepi_qemu_virt::irq;
    use krepi_qemu_virt::uart;

    /// The longest wait for the pending timer interrupt, in milliseconds on
    /// the counter: a platform parameter of the test images on QEMU virt,
    /// where it takes 10 ms.
    const WAIT_MS: u64 = 1000;
    /// NZCV before the IRQ: N and V set.
    const NZCV_BEFORE: u64 = 0x9000_0000;
    /// The bits of `SPSR_EL1` that the interrupted code sets: NZCV, DAIF and
    /// the mode.
    const SPSR_SET: u64 = 0xf000_03cf;
    /// The `SPSR_EL1` of the IRQ in those bits: NZCV as set, D, A and F
    /// masked, I unmasked, and EL1 with `SP_EL1`.
    const SPSR_AT_IRQ: u64 = NZCV_BEFORE | 0x340 | 0x5;

    /// What the code around the IRQ records: the stack pointer before it,
    /// whether the IRQ never became pending, and after the return `x0` to
    /// `x30`, the stack pointer, NZCV, `ELR_EL1` and `SPSR_EL1`.
    #[repr(C)]
    #[derive(Clone, Copy)]
    struct Probe {
        sp_before: u64,
        timed_out: u64,
        after: [u64; 31],
        sp_after: u64,
        nzcv: u64,
        elr: u64,
        spsr: u64,
    }

    /// The record of the code around the IRQ.
    static mut PROBE: Probe = Probe {
        sp_before: 0,
        timed_out: 0,
        after: [0; 31],
        sp_after: 0,
        nzcv: 0,
        elr: 0,
        spsr: 0,
    };
    /// The frame as the dispatch received it.
    static mut SAVED: Frame = Frame::ZERO;
    /// The entries of the dispatch.
    static mut ENTRIES: u64 = 0;

    unsafe extern "C" {
        /// Runs the sequence of the module documentation with the probe at
        /// `probe`, waiting for the pending IRQ until the virtual count
        /// reaches `deadline`.
        fn krepi_test_irq_registers(probe: *mut Probe, deadline: u64);
        /// The instruction after the unmask, where the IRQ is taken.
        static krepi_test_irq_resume: u8;
    }

    // The entry of the image, the cold entry, and the code around the IRQ.
    // TPIDR_EL1, which the cold entry cleared and nothing else uses, holds the
    // probe while x0 to x30 hold their known values, and TPIDRRO_EL0 holds x0
    // while its value is stored.
    global_asm!(
        r#"
        .section .text.krepi_test, "ax"
        .global krepi_test_entry
        .type krepi_test_entry, %function
    krepi_test_entry:
        b _start
        .size krepi_test_entry, . - krepi_test_entry

        .global krepi_test_irq_registers
        .type krepi_test_irq_registers, %function
    krepi_test_irq_registers:
        stp x29, x30, [sp, #-96]!
        stp x19, x20, [sp, #16]
        stp x21, x22, [sp, #32]
        stp x23, x24, [sp, #48]
        stp x25, x26, [sp, #64]
        stp x27, x28, [sp, #80]
        msr tpidr_el1, x0
        mov x2, sp
        str x2, [x0]
    1:
        mrs x2, isr_el1
        tbnz x2, #7, 2f
        isb
        mrs x2, cntvct_el0
        cmp x2, x1
        b.lo 1b
        mov x2, #1
        str x2, [x0, #8]
        b 3f
    2:
        mov x1, #0x90000000
        msr nzcv, x1
        .irp n, 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30
        movz x\n, #(0x5a00 + \n), lsl #48
        movk x\n, #(0xa500 + \n)
        .endr
        msr daifclr, #2
        .global krepi_test_irq_resume
    krepi_test_irq_resume:
        msr daifset, #2
        msr tpidrro_el0, x0
        mrs x0, tpidr_el1
        stp x1, x2, [x0, #24]
        stp x3, x4, [x0, #40]
        stp x5, x6, [x0, #56]
        stp x7, x8, [x0, #72]
        stp x9, x10, [x0, #88]
        stp x11, x12, [x0, #104]
        stp x13, x14, [x0, #120]
        stp x15, x16, [x0, #136]
        stp x17, x18, [x0, #152]
        stp x19, x20, [x0, #168]
        stp x21, x22, [x0, #184]
        stp x23, x24, [x0, #200]
        stp x25, x26, [x0, #216]
        stp x27, x28, [x0, #232]
        stp x29, x30, [x0, #248]
        mrs x1, nzcv
        str x1, [x0, #272]
        mrs x1, tpidrro_el0
        str x1, [x0, #16]
        mov x1, sp
        str x1, [x0, #264]
        mrs x1, elr_el1
        str x1, [x0, #280]
        mrs x1, spsr_el1
        str x1, [x0, #288]
    3:
        ldr x1, [x0]
        mov sp, x1
        msr tpidr_el1, xzr
        msr tpidrro_el0, xzr
        ldp x19, x20, [sp, #16]
        ldp x21, x22, [sp, #32]
        ldp x23, x24, [sp, #48]
        ldp x25, x26, [sp, #64]
        ldp x27, x28, [sp, #80]
        ldp x29, x30, [sp], #96
        ret
        .size krepi_test_irq_registers, . - krepi_test_irq_registers
        "#
    );

    /// The known value of `x<n>` at the IRQ.
    fn sentinel(n: u64) -> u64 {
        ((0x5a00 + n) << 48) | (0xa500 + n)
    }

    /// Reads a static of the image.
    fn load<T: Copy>(source: *const T) -> T {
        // SAFETY: `source` is a static of this image, aligned and
        // initialized; only CPU 0 runs, and the dispatch, the only other code
        // that accesses it, does not run during the read.
        unsafe { ptr::read_volatile(source) }
    }

    /// Writes a static of the image.
    fn store<T>(destination: *mut T, value: T) {
        // SAFETY: as in `load`: an aligned static of this image that no other
        // code accesses during the write.
        unsafe { ptr::write_volatile(destination, value) }
    }

    /// The Rust entry of the image, which `_start` calls once on CPU 0.
    #[unsafe(no_mangle)]
    extern "C" fn kernel_main() -> ! {
        common::start("irq-registers");
        irq::init();
        let deadline =
            cpu::virtual_counter().wrapping_add(window_ticks(cpu::counter_frequency(), WAIT_MS));
        // SAFETY: `krepi_test_irq_registers` keeps the registers that the
        // calling convention preserves, the stack pointer and DAIF, uses only
        // the probe, its own stack, `TPIDR_EL1` and `TPIDRRO_EL0`, which it
        // clears again, and returns.
        unsafe { krepi_test_irq_registers(&raw mut PROBE, deadline) };
        let probe = load(&raw const PROBE);
        let saved = load(&raw const SAVED);
        let resume = (&raw const krepi_test_irq_resume) as u64;
        let mut checks = [false; 39];
        checks[..8].copy_from_slice(&[
            probe.timed_out == 0,
            load(&raw const ENTRIES) == 1,
            saved.elr == resume,
            saved.spsr & SPSR_SET == SPSR_AT_IRQ,
            probe.elr == saved.elr,
            probe.spsr == saved.spsr,
            probe.sp_after == probe.sp_before,
            probe.nzcv == NZCV_BEFORE,
        ]);
        for (n, held) in checks[8..].iter_mut().enumerate() {
            *held = probe.after[n] == sentinel(n as u64);
        }
        common::check("irq-preserves-registers", &checks);
        common::finish()
    }

    /// The exception dispatch of the image: the first IRQ is recorded,
    /// reported and ended, the timer stopped, and the dispatch returns; any
    /// other exception, or a second one, is fatal.
    #[unsafe(no_mangle)]
    extern "C" fn exception_dispatch(frame: &mut Frame) {
        let entries = load(&raw const ENTRIES) + 1;
        store(&raw mut ENTRIES, entries);
        if entries != 1 || frame.vector != IRQ {
            uart::report_fatal(frame);
        }
        store(&raw mut SAVED, *frame);
        uart::report_exception(frame);
        irq::handle();
        timer::stop_virtual();
    }
}

#[cfg(not(all(target_arch = "aarch64", target_os = "none")))]
fn main() {}
