//! The test image of a breakpoint at EL1 on QEMU virt: `BRK #0xc5` at the
//! symbol `krepi_test_brk_site`, whose exception the dispatch reports and
//! returns from, past the breakpoint.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! Before the breakpoint the code records the stack pointer, sets NZCV and
//! DAIF to known values and puts a different known value into each of `x0`
//! to `x30`. The dispatch copies the frame and the exception registers,
//! writes the exception record, moves `ELR` in the frame past the
//! breakpoint and changes NZCV in the frame's `SPSR`. After the return the
//! code records the stack pointer and `PSTATE`, and the image checks the
//! rules of the frame and of the return: one `CASXI_CHECK` record for each,
//! then `CASXI_RESUMED`. On the host the image is an empty program.

#![cfg_attr(all(target_arch = "aarch64", target_os = "none"), no_std, no_main)]

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod common;

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod image {
    use core::arch::{asm, global_asm};
    use core::ptr;

    use crate::common;
    use krepi_arch::exception::{Class, FRAME_BYTES, Frame};
    use krepi_qemu_virt::uart;

    /// NZCV before the breakpoint: N and C set.
    const NZCV_BEFORE: u64 = 0xa000_0000;
    /// NZCV that the dispatch writes into the frame's `SPSR`: Z and V set.
    const NZCV_RETURN: u64 = 0x5000_0000;
    /// The NZCV bits of `SPSR_EL1` and of the `NZCV` register.
    const NZCV: u64 = 0xf000_0000;
    /// DAIF before the breakpoint: debug exceptions and IRQs masked, SError
    /// and FIQ not, so that it differs from the DAIF of the dispatch.
    const DAIF_BEFORE: u64 = 0x280;
    /// The bits of `SPSR_EL1` that the code before the breakpoint sets: NZCV,
    /// DAIF and the mode.
    const SPSR_SET: u64 = NZCV | 0x3c0 | 0xf;
    /// The `SPSR_EL1` of the breakpoint in those bits: NZCV and DAIF as set,
    /// and EL1 with `SP_EL1`.
    const SPSR_BEFORE: u64 = NZCV_BEFORE | DAIF_BEFORE | 0x5;
    /// The syndrome of `BRK #0xc5`: EC `0x3c`, IL 1, the immediate.
    const BRK_ESR: u64 = 0xf200_00c5;

    /// What the code around the breakpoint records: the stack pointer before
    /// it, and after the return the stack pointer, NZCV, DAIF, `CurrentEL`
    /// and `SPSel`.
    #[repr(C)]
    #[derive(Clone, Copy)]
    struct Probe {
        sp_before: u64,
        sp_after: u64,
        nzcv: u64,
        daif: u64,
        current_el: u64,
        spsel: u64,
    }

    /// The record of the code around the breakpoint.
    static mut PROBE: Probe = Probe {
        sp_before: 0,
        sp_after: 0,
        nzcv: 0,
        daif: 0,
        current_el: 0,
        spsel: 0,
    };
    /// The frame as the dispatch received it.
    static mut SAVED: Frame = Frame::ZERO;
    /// The address of the frame that the dispatch received.
    static mut FRAME_ADDRESS: u64 = 0;
    /// `ELR_EL1`, `SPSR_EL1`, `ESR_EL1` and `FAR_EL1` as the dispatch read
    /// them.
    static mut REGISTERS: [u64; 4] = [0; 4];
    /// The entries of the dispatch.
    static mut ENTRIES: u64 = 0;

    unsafe extern "C" {
        /// Runs the breakpoint with the probe at `probe`, as the module
        /// documentation describes.
        fn krepi_test_brk(probe: *mut Probe);
        /// The breakpoint instruction.
        static krepi_test_brk_site: u8;
    }

    // The entry of the image, the cold entry; the code around the breakpoint.
    // TPIDR_EL1, which the cold entry cleared and nothing else uses, holds the
    // probe while x0 to x30 hold their known values.
    global_asm!(
        r#"
        .section .text.krepi_test, "ax"
        .global krepi_test_entry
        .type krepi_test_entry, %function
    krepi_test_entry:
        b _start
        .size krepi_test_entry, . - krepi_test_entry

        .global krepi_test_brk
        .type krepi_test_brk, %function
    krepi_test_brk:
        stp x29, x30, [sp, #-96]!
        stp x19, x20, [sp, #16]
        stp x21, x22, [sp, #32]
        stp x23, x24, [sp, #48]
        stp x25, x26, [sp, #64]
        stp x27, x28, [sp, #80]
        msr tpidr_el1, x0
        mov x1, sp
        str x1, [x0]
        mov x1, #0xa0000000
        msr nzcv, x1
        msr daifclr, #5
        .irp n, 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30
        movz x\n, #(0x5a00 + \n), lsl #48
        movk x\n, #(0xa500 + \n)
        .endr
        .global krepi_test_brk_site
    krepi_test_brk_site:
        brk #0xc5
        mrs x0, tpidr_el1
        mov x1, sp
        str x1, [x0, #8]
        mrs x1, nzcv
        str x1, [x0, #16]
        mrs x1, daif
        str x1, [x0, #24]
        mrs x1, CurrentEL
        str x1, [x0, #32]
        mrs x1, SPSel
        str x1, [x0, #40]
        msr daifset, #0xf
        ldr x1, [x0]
        mov sp, x1
        msr tpidr_el1, xzr
        ldp x19, x20, [sp, #16]
        ldp x21, x22, [sp, #32]
        ldp x23, x24, [sp, #48]
        ldp x25, x26, [sp, #64]
        ldp x27, x28, [sp, #80]
        ldp x29, x30, [sp], #96
        ret
        .size krepi_test_brk, . - krepi_test_brk
        "#
    );

    /// The known value of `x<n>` at the breakpoint.
    fn sentinel(n: u64) -> u64 {
        ((0x5a00 + n) << 48) | (0xa500 + n)
    }

    /// Reads a static of the image.
    fn load<T: Copy>(source: *const T) -> T {
        // SAFETY: `source` is a static of this image, aligned and
        // initialized; only CPU 0 runs, and the dispatch, the only other
        // code that accesses it, does not run during the read.
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
        common::start("el1-brk");
        // SAFETY: `krepi_test_brk` keeps the registers that the calling
        // convention preserves, the stack pointer and DAIF, uses only the
        // probe and its own stack, and returns once the dispatch has
        // returned past the breakpoint.
        unsafe { krepi_test_brk(&raw mut PROBE) };
        let probe = load(&raw const PROBE);
        let saved = load(&raw const SAVED);
        let frame = load(&raw const FRAME_ADDRESS);
        let registers = load(&raw const REGISTERS);
        let site = (&raw const krepi_test_brk_site) as u64;
        common::check(
            "frame-records-interrupted-sp",
            &[
                saved.sp == probe.sp_before,
                frame == probe.sp_before.wrapping_sub(FRAME_BYTES as u64),
                frame.is_multiple_of(16),
            ],
        );
        let general: [bool; 31] = core::array::from_fn(|n| saved.x[n] == sentinel(n as u64));
        common::check("entry-saves-general-registers", &general);
        common::check(
            "frame-records-system-registers",
            &[
                saved.elr == registers[0],
                saved.spsr == registers[1],
                saved.esr == registers[2],
                saved.far == registers[3],
                saved.vector == krepi_arch::exception::SYNC,
                saved.reserved == 0,
                saved.elr == site,
                saved.esr == BRK_ESR,
                saved.spsr & SPSR_SET == SPSR_BEFORE,
            ],
        );
        common::check(
            "return-restores-elr-and-pstate",
            &[
                load(&raw const ENTRIES) == 1,
                probe.nzcv == NZCV_RETURN,
                probe.daif == DAIF_BEFORE,
                probe.current_el == 1 << 2,
                probe.spsel == 1,
            ],
        );
        common::check("return-restores-sp", &[probe.sp_after == probe.sp_before]);
        common::finish()
    }

    /// `ELR_EL1`, `SPSR_EL1`, `ESR_EL1` and `FAR_EL1`.
    fn exception_registers() -> [u64; 4] {
        let (elr, spsr, esr, far): (u64, u64, u64, u64);
        // SAFETY: the four registers are readable at EL1; the reads have no
        // side effect and touch no memory, the stack or the flags.
        unsafe {
            asm!(
                "mrs {}, elr_el1",
                "mrs {}, spsr_el1",
                "mrs {}, esr_el1",
                "mrs {}, far_el1",
                out(reg) elr,
                out(reg) spsr,
                out(reg) esr,
                out(reg) far,
                options(nomem, nostack, preserves_flags)
            )
        };
        [elr, spsr, esr, far]
    }

    /// The exception dispatch of the image: the first breakpoint is recorded,
    /// reported and returned from past the breakpoint with the NZCV of
    /// [`NZCV_RETURN`]; any other exception, or a second one, is fatal.
    #[unsafe(no_mangle)]
    extern "C" fn exception_dispatch(frame: &mut Frame) {
        let registers = exception_registers();
        let entries = load(&raw const ENTRIES) + 1;
        store(&raw mut ENTRIES, entries);
        if entries != 1 || Class::of(frame.vector, frame.esr) != Class::Brk {
            uart::report_fatal(frame);
        }
        store(&raw mut SAVED, *frame);
        store(&raw mut FRAME_ADDRESS, ptr::from_mut(frame) as u64);
        store(&raw mut REGISTERS, registers);
        uart::report_exception(frame);
        frame.elr += 4;
        frame.spsr = (frame.spsr & !NZCV) | NZCV_RETURN;
    }
}

#[cfg(not(all(target_arch = "aarch64", target_os = "none")))]
fn main() {}
