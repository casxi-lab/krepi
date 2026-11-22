//! The vectors of `src/memory/extents.rs` and `src/memory/tests.rs` of the
//! contract: physical ranges and the page ownership table; and its owners.
//!
//! Feature: krepi.kernel.kernel-memory

use super::*;
use OwnershipError::*;

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

/// `own-01`.
#[test]
fn generation_exhaustion_never_wraps_to_an_old_receipt() {
    let mut t = table::<2>(1, &[(0, 0x1000)], &[]).unwrap();
    t.counter = Counter::Next(u64::MAX);
    let c = t.choose(1, 1, 1, LOW).unwrap();
    assert_eq!(c.range, range(0, 0x1000));
    let a = t.assign(c, true).unwrap();
    assert_eq!(a, receipt(1, 1, u64::MAX, 0, 0x1000));
    assert_eq!(t.release(1, a), Ok(()));
    assert_eq!(t.choose(1, 1, 1, LOW).unwrap_err(), GenerationExhausted);
}

/// `own-03`.
#[test]
fn initialization_rejects_unaligned_ram_and_missing_metadata() {
    assert_eq!(
        table::<8>(1, &[(1, 0x1000)], &[]).err(),
        Some(InvalidAlignment)
    );
    assert_eq!(
        table::<8>(1, &[(0, 0x1001)], &[]).err(),
        Some(InvalidAlignment)
    );
    assert_eq!(
        table::<0>(1, &[(0, 0x1000)], &[]).err(),
        Some(MetadataExhausted)
    );
    assert_eq!(table::<8>(0, &[(0, 0x1000)], &[]).err(), Some(InvalidArena));
}

/// `own-04`: the choices are the ranges that the caller zeroes.
#[test]
fn overlapping_and_unaligned_reservations_exclude_whole_pages() {
    let firmware = [(0x1001, 1), (0x1fff, 2), (0x2000, 0x1000), (0x9000, 1)];
    let mut t = table::<8>(1, &[(0, 0x8000)], &firmware).unwrap();
    assert_eq!(t.stats().managed, 0x6000);
    let c = t.choose(1, 1, 1, LOW).unwrap();
    assert_eq!(c.range, range(0, 0x1000));
    let a = t.assign(c, true).unwrap();
    assert_eq!(a, receipt(1, 1, 1, 0, 0x1000));
    let c = t.choose(1, 5, 1, LOW).unwrap();
    assert_eq!(c.range, range(0x3000, 0x5000));
    let b = t.assign(c, true).unwrap();
    assert_eq!(b, receipt(1, 1, 2, 0x3000, 0x5000));
    assert_eq!(t.release(1, a), Ok(()));
    assert_eq!(t.release(1, b), Ok(()));
    assert_eq!(t.stats().free_extents, 2);
}

/// `own-05`.
#[test]
fn reservations_can_cover_all_ram_or_exceed_metadata_capacity() {
    let t = table::<1>(1, &[(0x1000, 0x4000)], &[(0, 0x8000)]).unwrap();
    assert_eq!(t.stats().managed, 0);
    assert_eq!(t.choose(1, 1, 1, LOW).unwrap_err(), OutOfMemory);
    let split = table::<1>(2, &[(0x1000, 0x4000)], &[(0x2000, 0x1000)]);
    assert_eq!(split.err(), Some(MetadataExhausted));
}

/// `own-06`.
#[test]
fn page_alignment_and_zeroing_work_above_four_gib() {
    let mut t = table::<8>(1, &[(0x1_0000_1000, 0x8000)], &[]).unwrap();
    let c = t.choose(7, 2, 4, LOW).unwrap();
    assert_eq!(c.range, range(0x1_0000_4000, 0x2000));
    let a = t.assign(c, true).unwrap();
    assert_eq!(a, receipt(1, 7, 1, 0x1_0000_4000, 0x2000));
    assert_eq!(t.release(7, a), Ok(()));
    assert_eq!(t.stats().largest_free, 0x8000);
}

/// `own-07`: no refused request gives a range to zero.
#[test]
fn invalid_page_requests_never_call_zero_backend() {
    let t = table::<8>(1, &[(0, 0x8000)], &[]).unwrap();
    assert_eq!(t.choose(1, 0, 1, LOW).unwrap_err(), InvalidSize);
    assert_eq!(t.choose(1, 1, 3, LOW).unwrap_err(), InvalidAlignment);
    assert_eq!(t.choose(1, 1, 0, LOW).unwrap_err(), InvalidAlignment);
    assert_eq!(t.choose(1, u64::MAX, 1, LOW).unwrap_err(), AddressOverflow);
    assert_eq!(t.stats().allocated, 0);
}

/// `own-08`.
#[test]
fn metadata_exhaustion_is_distinct_from_ram_exhaustion() {
    let mut t = table::<1>(1, &[(0, 0x2000)], &[]).unwrap();
    assert_eq!(t.choose(1, 1, 1, LOW).unwrap_err(), MetadataExhausted);
    let all = allocate(&mut t, 1, 2, 1, LOW).unwrap();
    assert_eq!(all, receipt(1, 1, 1, 0, 0x2000));
    assert_eq!(t.choose(1, 1, 1, LOW).unwrap_err(), OutOfMemory);
    assert_eq!(t.release(1, all), Ok(()));
    assert_eq!((t.stats().free, t.stats().extents), (0x2000, 1));
}

/// `own-09`.
#[test]
fn foreign_owner_and_arena_cannot_release_allocation() {
    let mut t = table::<2>(1, &[(0, 0x1000)], &[]).unwrap();
    let mut u = table::<2>(2, &[(0x2000, 0x1000)], &[]).unwrap();
    let a = allocate(&mut t, 9, 1, 1, LOW).unwrap();
    assert_eq!(a, receipt(1, 9, 1, 0, 0x1000));
    let before = t.stats();
    assert_eq!(t.release(8, a), Err(WrongOwner));
    assert_eq!(u.release(9, a), Err(WrongArena));
    let expected = Stats {
        managed: 0x1000,
        free: 0,
        allocated: 0x1000,
        allocations: 1,
        free_extents: 0,
        largest_free: 0,
        extents: 1,
        capacity: 2,
    };
    assert_eq!((t.stats(), before), (expected, expected));
    assert_eq!(t.release(9, a), Ok(()));
}

/// `own-10`.
#[test]
fn double_and_stale_frees_cannot_free_a_reused_address() {
    let mut t = table::<2>(1, &[(0, 0x1000)], &[]).unwrap();
    let old = allocate(&mut t, 3, 1, 1, LOW).unwrap();
    assert_eq!(old, receipt(1, 3, 1, 0, 0x1000));
    assert_eq!(t.release(3, old), Ok(()));
    assert_eq!(t.release(3, old), Err(InvalidAllocation));
    let new = allocate(&mut t, 3, 1, 1, LOW).unwrap();
    assert_eq!(new, receipt(1, 3, 2, 0, 0x1000));
    assert_eq!(t.release(3, old), Err(InvalidAllocation));
    assert_eq!(t.stats().allocations, 1);
    assert_eq!(t.release(3, new), Ok(()));
}

/// `own-11`.
#[test]
fn partial_zero_failure_does_not_publish_or_consume_allocation() {
    let mut t = table::<2>(1, &[(0, 0x1000)], &[]).unwrap();
    let c = t.choose(1, 1, 1, LOW).unwrap();
    assert_eq!(c.range, range(0, 0x1000));
    assert_eq!(t.assign(c, false), Err(ZeroFailed));
    assert_eq!((t.stats().allocated, t.stats().free), (0, 0x1000));
    assert_eq!(
        allocate(&mut t, 2, 1, 1, LOW),
        Ok(receipt(1, 2, 1, 0, 0x1000))
    );
}

/// `own-16`.
#[test]
fn exact_later_extent_can_allocate_without_metadata_for_earlier_split() {
    let mut t = table::<2>(1, &[(0, 0x4000)], &[(0x2000, 0x1000)]).unwrap();
    let a = allocate(&mut t, 1, 1, 1, LOW).unwrap();
    assert_eq!(a, receipt(1, 1, 1, 0x3000, 0x1000));
    assert_eq!(t.stats().free, 0x2000);
    assert_eq!(t.release(1, a), Ok(()));
    assert_eq!(t.stats().free, 0x3000);
}

/// The owner of a page: the holding of its extent, the first owner of the
/// exclusions that touch it in the order firmware, image, boot storage, and
/// none outside the banks.
#[test]
fn owners_follow_the_extents_then_the_exclusions_by_kind() {
    let exclusion = |start, len, owner| Exclusion {
        range: range(start, len),
        owner,
    };
    let exclusions = [
        exclusion(0x1800, 0x10, Excluder::BootStorage),
        exclusion(0x1000, 0x1000, Excluder::Image),
        exclusion(0x2fff, 2, Excluder::Firmware),
        exclusion(0x3000, 0x800, Excluder::BootStorage),
    ];
    let mut t = Ownership::<8, 4>::new(5, &[range(0, 0x6000)], &exclusions).unwrap();
    let a = allocate(&mut t, 9, 1, 1, HIGH).unwrap();
    assert_eq!(a.range, range(0x5000, 0x1000));
    let excluded = |x| Some(Owner::Excluded(x));
    assert_eq!(t.owner(0x1fff), excluded(Excluder::Image));
    assert_eq!(t.owner(0x2000), excluded(Excluder::Firmware));
    assert_eq!(t.owner(0x3800), excluded(Excluder::Firmware));
    assert_eq!(t.owner(0x4abc), Some(Owner::Free));
    let held = Owner::Held(9, 1, HoldState::Published);
    assert_eq!(t.owner(0x5fff), Some(held));
    assert_eq!(t.owner(0x6000), None);
}
