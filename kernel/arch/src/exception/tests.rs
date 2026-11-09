//! The tests of the classes of exceptions, with syndromes written from the
//! Arm Architecture Reference Manual.
//!
//! Feature: krepi.platform.qemu-virt-boot

use super::*;

/// The syndrome of `BRK #0xc5` in AArch64 state: EC `0x3c`, IL 1 and the
/// immediate as the ISS.
const BRK_ESR: u64 = 0xf200_00c5;
/// The syndrome of an FP/SIMD access from AArch64 state that
/// `CPACR_EL1.FPEN` traps: EC `0x07`, IL 1, and the CV bit 1 with the
/// condition `0b1110`, which the manual gives for a trap from AArch64 state.
const FP_ESR: u64 = 0x1fe0_0000;
/// The syndrome of a data abort at the current exception level: EC `0x25`.
const DATA_ABORT_ESR: u64 = 0x9600_0010;
/// The syndrome of a virtual SError without a syndrome of its own: EC
/// `0x2f` and IL 1.
const SERROR_ESR: u64 = 0xbe00_0000;

/// The exception class is bits 26 to 31 of the syndrome.
#[test]
fn the_exception_class_is_the_top_six_bits_of_the_syndrome() {
    assert_eq!(exception_class(BRK_ESR), EC_BRK);
    assert_eq!(exception_class(FP_ESR), EC_FP);
    assert_eq!(exception_class(SERROR_ESR), 0x2f);
    assert_eq!(exception_class(0xffff_ffff_0000_0000 | BRK_ESR), EC_BRK);
    assert_eq!(exception_class(0x03ff_ffff), 0);
}

/// The entries of the current exception level with `SP_EL1` give the class
/// of their kind, and a synchronous exception there is a breakpoint, an
/// FP/SIMD trap or another synchronous exception by its syndrome.
#[test]
fn the_entries_of_the_current_level_give_their_classes() {
    assert_eq!(Class::of(SYNC, BRK_ESR), Class::Brk);
    assert_eq!(Class::of(SYNC, FP_ESR), Class::Fp);
    assert_eq!(Class::of(SYNC, DATA_ABORT_ESR), Class::Sync);
    assert_eq!(Class::of(IRQ, 0), Class::Irq);
    assert_eq!(Class::of(6, BRK_ESR), Class::Fiq);
    assert_eq!(Class::of(7, SERROR_ESR), Class::Serror);
}

/// A synchronous exception of an entry other than vector 4 is `sync`,
/// whatever its syndrome; the other entries give the class of their kind.
#[test]
fn the_other_entries_give_sync_for_a_breakpoint() {
    for vector in [0, 8, 12] {
        assert_eq!(Class::of(vector, BRK_ESR), Class::Sync, "{vector}");
        assert_eq!(Class::of(vector, FP_ESR), Class::Sync, "{vector}");
    }
    let kinds = [Class::Sync, Class::Irq, Class::Fiq, Class::Serror];
    for vector in (0..16).filter(|vector| !(4..8).contains(vector)) {
        assert_eq!(Class::of(vector, 0), kinds[vector as usize % 4], "{vector}");
    }
}
