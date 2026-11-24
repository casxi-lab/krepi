//! The selection of available spans: boot storage, reservations and holes
//! between banks, invalid bounds, alignments and overflow, and reusable
//! reservations at full capacity.
//!
//! Feature: krepi.platform.device-tree

use super::*;

#[test]
fn selection_skips_boot_storage_reservations_and_bank_holes() {
    let mut b = root();
    ram(&mut b, &[0, 0, 0, 0x400000, 1, 0, 0, 0x10000]);
    b.reservations.push(Span::new(0x4000, 0x1001).unwrap());
    b.reservations.push(Span::new(0, 0x4000).unwrap());
    b.reservations
        .push(Span::new(0x1_0000_0000, 0x3000).unwrap());
    let bytes = finish(b);
    let map = report(&bytes).unwrap();
    assert_eq!(
        map.find_available(0x2000, 0x1000, 0, 0x10000).unwrap(),
        Some(Span::new(0x6000, 0x2000).unwrap())
    );
    assert_eq!(
        map.find_available(0x2000, 0x1000, IMAGE.start, DTB)
            .unwrap()
            .unwrap()
            .start,
        IMAGE.end().unwrap()
    );
    let after_dtb = map
        .find_available(0x1000, 0x1000, DTB, 0x400000)
        .unwrap()
        .unwrap();
    assert!(after_dtb.start >= map.dtb().end().unwrap());
    assert!(map.is_available(after_dtb).unwrap());
    assert_eq!(
        map.find_available(0x2000, 0x1000, 0x3ff000, 0x1_0000_5000)
            .unwrap(),
        Some(Span::new(0x1_0000_3000, 0x2000).unwrap())
    );
    assert_eq!(
        map.find_available(0x2000, 0x1000, 0x3ff000, 0x1_0000_4000)
            .unwrap(),
        None
    );
}

#[test]
fn selection_rejects_invalid_bounds_alignment_and_overflow() {
    let mut b = root();
    ram(&mut b, &[0, 0, 2, 0]);
    let bytes = finish(b);
    let map = report(&bytes).unwrap();
    assert_eq!(
        map.find_available(0, 4096, 0, 10000),
        Err(Error::EmptyRegion)
    );
    assert_eq!(map.find_available(1, 4096, 10, 10), Err(Error::EmptyRegion));
    for alignment in [0, 3, 4095] {
        assert_eq!(
            map.find_available(1, alignment, 0, 10000),
            Err(Error::BadAlignment)
        );
    }
    assert_eq!(
        map.find_available(4096, 4096, u64::MAX - 1, u64::MAX),
        Err(Error::Overflow)
    );
    assert_eq!(
        map.find_available(u64::MAX, 4096, 4096, u64::MAX).unwrap(),
        None
    );
}

#[test]
fn selection_preserves_reusable_reservations_and_full_capacity() {
    let mut b = root();
    ram(&mut b, &[0, 0, 2, 0]);
    reservations(&mut b);
    for i in 0..MAX_RESERVED_REGIONS {
        b.begin("pool");
        b.cells("reg", &[0, 0x400000 + i as u32 * 4096, 0, 4096]);
        b.property("reusable", &[]);
        b.end();
    }
    b.end();
    let bytes = finish(b);
    let map = report(&bytes).unwrap();
    let selected = map
        .find_available(32768, 4096, 0x400000, 0x10000000)
        .unwrap()
        .unwrap();
    assert_eq!(selected.start, 0x400000 + MAX_RESERVED_REGIONS * 4096);
    assert!(map.is_available(selected).unwrap());
}
