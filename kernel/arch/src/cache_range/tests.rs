//! The tests of the cache-line walks: the tests taken from the prototype
//! tree, with their expected values, and the examples of the feature
//! document.
//!
//! Feature: krepi.platform.qemu-virt-boot

use super::*;

#[test]
fn firmware_image_walk_uses_the_complete_platform_window() {
    let pi5 = 0x80000..0x1000000;
    let bytes = 0x206000;
    let walk = handoff_lines(pi5.start, bytes, 4, pi5.clone()).unwrap();
    assert_eq!(walk.clone().count() as u64, bytes / 64);
    assert_eq!(walk.clone().next(), Some(pi5.start));
    assert_eq!(walk.last(), Some(pi5.start + bytes - 64));
    assert!(handoff_lines(pi5.start, pi5.end - pi5.start, 4, pi5.clone()).is_some());
    for (start, bytes, field) in [
        (pi5.start, pi5.end - pi5.start + 4096, 4),
        (pi5.start + 4096, 4096, 4),
        (pi5.start, 4095, 4),
        (pi5.start, 0, 4),
        (pi5.start, 4096, 11),
    ] {
        assert!(handoff_lines(start, bytes, field, pi5.clone()).is_none());
    }
    let virt = 0x40200000..0x48000000;
    assert!(handoff_lines(virt.start, 0x300000, 4, virt.clone()).is_some());
    assert!(handoff_lines(pi5.start, bytes, 4, virt).is_none());
    assert!(handoff_lines(u64::MAX - 4095, 4096, 4, (u64::MAX - 4095)..u64::MAX).is_none());
}

#[test]
fn partial_lines_and_exact_boundaries() {
    assert!(lines(0x103f, 2, 4, 4096).unwrap().eq([0x1000, 0x1040]));
    assert!(lines(0x1000, 64, 4, 4096).unwrap().eq([0x1000]));
    assert!(lines(0x1004, 4, 0, 4096).unwrap().eq([0x1004]));
}

#[test]
fn rejects_unbounded_or_wrapping_requests() {
    for (start, size, field) in [(0, 0, 4), (0, 4097, 4), (u64::MAX, 1, 4), (0, 8, 16)] {
        assert!(lines(start, size, field, 4096).is_none());
    }
    assert_eq!(lines(u64::MAX - 63, 63, 4, 4096).unwrap().count(), 1);
}

/// ex7: 200 bytes from `0x4020_1005` at 64-byte lines touch the four lines
/// from `0x4020_1000` to `0x4020_10c0`; the first starts before the range
/// and the last ends after it.
#[test]
fn ex7_a_range_with_unaligned_ends_covers_each_line_it_touches() {
    let walk = lines(0x4020_1005, 200, 4, MAX_RANGE_BYTES).unwrap();
    assert!(walk.eq([0x4020_1000, 0x4020_1040, 0x4020_1080, 0x4020_10c0]));
}

/// ex8: an empty range and a range one byte longer than
/// [`MAX_RANGE_BYTES`] are refused; a range of exactly that length is
/// walked, in 1,024 lines of 64 bytes from an aligned start and 1,025 from
/// an unaligned one.
#[test]
fn ex8_an_empty_or_oversized_range_is_refused() {
    assert!(lines(0x4020_1000, 0, 4, MAX_RANGE_BYTES).is_none());
    assert!(lines(0x4020_1000, MAX_RANGE_BYTES + 1, 4, MAX_RANGE_BYTES).is_none());
    let aligned = lines(0x4020_1000, MAX_RANGE_BYTES, 4, MAX_RANGE_BYTES).unwrap();
    assert_eq!(aligned.count(), 1024);
    let unaligned = lines(0x4020_1001, MAX_RANGE_BYTES, 4, MAX_RANGE_BYTES).unwrap();
    assert_eq!(unaligned.count(), 1025);
}
