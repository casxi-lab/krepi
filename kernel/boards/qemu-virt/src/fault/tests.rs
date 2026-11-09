//! The tests of the exception record: the examples of the QEMU virt boot
//! feature document and the records of every kind of entry, with the bytes
//! written from the record table of the boot contract.
//!
//! Feature: krepi.platform.qemu-virt-boot

use super::*;

/// The bounds of the tests: those of QEMU virt.
const BOUNDS: Bounds = crate::CONSOLE_BOUNDS;

/// A counter frequency of 62.5 MHz.
const FREQUENCY: u64 = 62_500_000;

/// The syndrome of `BRK #0xc5` in AArch64 state.
const BRK_ESR: u64 = 0xf200_00c5;

/// A frame of the entry `vector` with the syndrome `esr` and the return
/// address `elr`, taken at EL1h with every exception masked.
fn frame(vector: u64, esr: u64, elr: u64) -> Frame {
    Frame {
        vector,
        esr,
        elr,
        spsr: 0x3c5,
        ..Frame::ZERO
    }
}

/// The bytes that `report` writes for `frame` to a device that takes every
/// byte.
fn record(frame: &Frame) -> Vec<u8> {
    let mut output = Vec::new();
    let written = report(
        frame,
        &BOUNDS,
        FREQUENCY,
        || 0,
        |byte| {
            output.push(byte);
            true
        },
    );
    assert_eq!(written, Ok(output.len()));
    output
}

mod examples {
    use super::*;

    /// A breakpoint at EL1 is reported with its vector, the four registers
    /// and the class `brk`, after a line break.
    #[test]
    fn ex4_a_breakpoint_is_reported_with_its_registers() {
        assert_eq!(
            record(&frame(4, BRK_ESR, 0x4020_1000)),
            b"\r\nCASXI_EXCEPTION vector=4 ESR=0x00000000f20000c5 ELR=0x0000000040201000 FAR=0x0000000000000000 SPSR=0x00000000000003c5 class=brk\r\n"
        );
    }

    /// A fatal exception, here an FP/SIMD access that traps, writes its
    /// record and then `CASXI_HALTED`.
    #[test]
    fn ex5_a_fatal_exception_ends_in_the_halt_record() {
        let mut output = Vec::new();
        let written = report_fatal(
            &frame(4, 0x1fe0_0000, 0x4020_2000),
            &BOUNDS,
            FREQUENCY,
            || 0,
            |byte| {
                output.push(byte);
                true
            },
        );
        assert_eq!(
            output,
            b"\r\nCASXI_EXCEPTION vector=4 ESR=0x000000001fe00000 ELR=0x0000000040202000 FAR=0x0000000000000000 SPSR=0x00000000000003c5 class=fp\r\nCASXI_HALTED\r\n"
        );
        assert_eq!(written, Ok(output.len()));
    }

    /// The syndrome of a breakpoint taken through an entry of the current
    /// exception level with `SP_EL0`, vector 0, is not a breakpoint of the
    /// kernel: the class is `sync`.
    #[test]
    fn ex6_a_breakpoint_through_another_entry_is_sync() {
        assert_eq!(
            record(&frame(0, BRK_ESR, 0x4020_1000)),
            b"\r\nCASXI_EXCEPTION vector=0 ESR=0x00000000f20000c5 ELR=0x0000000040201000 FAR=0x0000000000000000 SPSR=0x00000000000003c5 class=sync\r\n"
        );
    }
}

/// Every kind of entry names its class: an IRQ, an FIQ, an SError, another
/// synchronous exception of the current level and one of a lower level.
#[test]
fn each_kind_of_entry_names_its_class() {
    let cases: [(u64, u64, &[u8]); 5] = [
        (5, 0, b"vector=5 ESR=0x0000000000000000 ELR=0x0000000040201000 FAR=0x0000000000000000 SPSR=0x00000000000003c5 class=irq"),
        (6, 0, b"vector=6 ESR=0x0000000000000000 ELR=0x0000000040201000 FAR=0x0000000000000000 SPSR=0x00000000000003c5 class=fiq"),
        (7, 0xbe00_0000, b"vector=7 ESR=0x00000000be000000 ELR=0x0000000040201000 FAR=0x0000000000000000 SPSR=0x00000000000003c5 class=serror"),
        (4, 0x9600_0010, b"vector=4 ESR=0x0000000096000010 ELR=0x0000000040201000 FAR=0x0000000000000000 SPSR=0x00000000000003c5 class=sync"),
        (8, BRK_ESR, b"vector=8 ESR=0x00000000f20000c5 ELR=0x0000000040201000 FAR=0x0000000000000000 SPSR=0x00000000000003c5 class=sync"),
    ];
    for (vector, esr, fields) in cases {
        let expected = [b"\r\nCASXI_EXCEPTION ".as_slice(), fields, b"\r\n"].concat();
        assert_eq!(
            record(&frame(vector, esr, 0x4020_1000)),
            expected,
            "{vector}"
        );
    }
}

/// The widest record, with every register all ones, is 135 bytes, well
/// within a console record, and writes the fault address as it is.
#[test]
fn the_widest_record_fits_a_console_record() {
    let widest = Frame {
        vector: 15,
        esr: u64::MAX,
        elr: u64::MAX,
        far: u64::MAX,
        spsr: u64::MAX,
        ..Frame::ZERO
    };
    let output = record(&widest);
    assert_eq!(
        output,
        b"\r\nCASXI_EXCEPTION vector=15 ESR=0xffffffffffffffff ELR=0xffffffffffffffff FAR=0xffffffffffffffff SPSR=0xffffffffffffffff class=serror\r\n"
    );
    assert_eq!(output.len(), 135);
    assert!(output.len() <= crate::console::RECORD_BYTES);
}

/// A device that never takes a byte fails the exception record, and the
/// halt record is not written after it.
#[test]
fn a_failed_record_writes_no_halt_record() {
    let mut attempts = 0;
    let result = report_fatal(
        &frame(4, BRK_ESR, 0x4020_1000),
        &BOUNDS,
        FREQUENCY,
        || 0,
        |_| {
            attempts += 1;
            false
        },
    );
    assert_eq!(result, Err(PolledError::PollLimit));
    assert_eq!(attempts, 1_000_000);
}
