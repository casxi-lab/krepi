//! The vectors of `src/memory/tests.rs` of the contract: physical ranges
//! and the page ownership table.
//!
//! Feature: krepi.kernel.kernel-memory

use super::*;

/// `own-02`.
#[test]
fn ranges_preserve_high_addresses_and_reject_invalid_bounds() {
    let range = PhysRange::new(0x10_0000_0000, 0x2000).unwrap();
    assert_eq!(range.end(), 0x10_0000_2000);
    assert!(range.contains(PhysRange::new(0x10_0000_1000, 8).unwrap()));
    assert!(!range.overlaps(PhysRange::new(0x10_0000_2000, 1).unwrap()));
    assert_eq!(PhysRange::new(1, 0), Err(OwnershipError::InvalidRange));
    assert_eq!(
        PhysRange::new(0xffff_ffff_ffff_fffd, 3),
        Err(OwnershipError::AddressOverflow)
    );
    let top = PhysRange::new(0xffff_ffff_ffff_fffd, 2).unwrap();
    assert_eq!(top.end(), 0xffff_ffff_ffff_ffff);
}
