//! The rows of the kind table, the format of a page descriptor and the
//! direct address of a physical range.
//!
//! Feature: krepi.kernel.kernel-memory

use super::*;

/// The columns AP[2:1], PXN, UXN, AttrIndx, SH, nG and AF of a leaf.
fn columns(d: u64) -> [u64; 7] {
    [
        (d >> 6) & 3,
        (d >> 53) & 1,
        (d >> 54) & 1,
        (d >> 2) & 7,
        (d >> 8) & 3,
        (d >> 11) & 1,
        (d >> 10) & 1,
    ]
}

#[test]
fn each_kind_has_the_bits_of_its_row() {
    for (kind, row) in [
        (Kind::ReadExecute, [0b10, 0, 1, 1, 0b11, 0, 1]),
        (Kind::ReadOnly, [0b10, 1, 1, 1, 0b11, 0, 1]),
        (Kind::ReadWrite, [0b00, 1, 1, 1, 0b11, 0, 1]),
        (Kind::KernelPrivateReadWrite, [0b00, 1, 1, 1, 0b11, 1, 1]),
        (Kind::Device, [0b00, 1, 1, 0, 0b00, 0, 1]),
        (Kind::UserReadExecute, [0b11, 1, 0, 1, 0b11, 1, 1]),
        (Kind::UserReadOnly, [0b11, 1, 1, 1, 0b11, 1, 1]),
        (Kind::UserReadWrite, [0b01, 1, 1, 1, 0b11, 1, 1]),
        (Kind::UserDevice, [0b01, 1, 1, 0, 0b00, 1, 1]),
    ] {
        let d = descriptor(kind, 0);
        assert_eq!(columns(d), row, "{kind:?}");
        // Every other bit is 0, and bits 1 and 0 are those of a page.
        assert_eq!(d & !0x0060_0000_0000_0fdf, 0, "{kind:?}");
        assert_eq!(d & 3, 3);
        // No kind is writable and executable.
        let writable = d & (1 << 7) == 0;
        assert!(!writable || d & (3 << 53) == 3 << 53, "{kind:?}");
    }
}

#[test]
fn a_descriptor_takes_bits_12_to_47_of_its_address() {
    let d = descriptor(Kind::ReadWrite, 0xffff_ffff_ffff_ffff);
    assert_eq!(d, 0x0060_ffff_ffff_f707);
    assert_eq!(
        descriptor(Kind::Device, 0x1234_5678_9abc),
        0x0060_1234_5678_9403
    );
}

#[test]
fn direct_addresses_keep_the_start_and_end_at_the_window() {
    let range = |start, len| PhysRange::new(start, len).unwrap();
    // The cases of `as-32` of the address-space contract.
    assert_eq!(
        direct_address(range(0, 0x1000)),
        Some(0xffff_ff80_0000_0000)
    );
    assert_eq!(
        direct_address(range(0x1_0000_0000, 0x2000)),
        Some(0xffff_ff81_0000_0000)
    );
    assert_eq!(
        direct_address(range(0x7f_ffff_f000, 0x1000)),
        Some(0xffff_ffff_ffff_f000)
    );
    assert_eq!(direct_address(range(0x7f_ffff_f000, 0x2000)), None);
    assert_eq!(direct_address(range(0x80_0000_0000, 0x1000)), None);
    // A range that ends at the top of the address space has none.
    assert_eq!(direct_address(range(0xffff_ffff_ffff_f000, 0xfff)), None);
}
