//! The vectors of `src/memory/tests/reservations.rs` of the contract: staged
//! reservations, their zeroing outcome, publication and cancel.
//!
//! Feature: krepi.kernel.kernel-memory

use super::*;
use OwnershipError::*;

/// `own-23`: the reservation holds its pages before any zeroing.
#[test]
fn reservation_excludes_uninitialized_bytes_until_external_zeroing_completes() {
    let mut t = table::<8>(7, &[(0, 0x4000)], &[]).unwrap();
    let r = t.reserve(11, 2, 1, LOW).unwrap();
    assert_eq!(r.allocation, receipt(7, 11, 1, 0, 0x2000));
    assert_eq!((r.attempted, r.failures), (false, 0));
    assert_eq!((t.stats().allocated, t.stats().allocations), (0x2000, 1));
    let c = t.choose(22, 1, 1, LOW).unwrap();
    assert_eq!(c.range, range(0x2000, 0x1000));
    let other = t.assign(c, true).unwrap();
    assert_eq!(other, receipt(7, 22, 2, 0x2000, 0x1000));
    assert!(!other.range.overlaps(r.allocation.range));
    let x = r.initialized(true).unwrap();
    assert_eq!(
        (x.allocation, x.failures),
        (receipt(7, 11, 1, 0, 0x2000), 0)
    );
    assert_eq!(t.validate(11, x.allocation(), HoldState::Reserved), Ok(()));
    let a = t.publish(11, x).unwrap();
    assert_eq!(a, receipt(7, 11, 1, 0, 0x2000));
    assert_eq!(t.release(11, a), Ok(()));
    assert_eq!(t.release(22, other), Ok(()));
    assert_eq!(t.stats().free, 0x4000);
}

/// `own-24`.
#[test]
fn failed_initialization_retains_partial_bytes_and_cannot_cancel_as_unused() {
    let mut t = table::<4>(3, &[(0, 0x2000)], &[]).unwrap();
    let r = t.reserve(4, 2, 1, LOW).unwrap();
    assert_eq!(r.allocation, receipt(3, 4, 1, 0, 0x2000));
    let before = t.stats();
    let r = r.initialized(false).unwrap_err();
    assert_eq!(
        (r.allocation, r.attempted, r.failures),
        (receipt(3, 4, 1, 0, 0x2000), true, 1)
    );
    let expected = Stats {
        managed: 0x2000,
        free: 0,
        allocated: 0x2000,
        allocations: 1,
        free_extents: 0,
        largest_free: 0,
        extents: 1,
        capacity: 4,
    };
    assert_eq!((t.stats(), before), (expected, expected));
    let (error, r) = t.cancel(4, r).unwrap_err();
    assert_eq!(error, ZeroFailed);
    assert_eq!(t.reserve(9, 1, 1, LOW).unwrap_err(), OutOfMemory);
    let r = r.initialized(false).unwrap_err();
    assert_eq!((r.attempted, r.failures), (true, 2));
    let x = r.initialized(true).unwrap();
    assert_eq!(
        (x.allocation, x.failures()),
        (receipt(3, 4, 1, 0, 0x2000), 2)
    );
    let (error, x) = t.publish(9, x).unwrap_err();
    assert_eq!(error, WrongOwner);
    assert_eq!(t.publish(4, x).unwrap(), receipt(3, 4, 1, 0, 0x2000));
    assert_eq!(t.release(4, receipt(3, 4, 1, 0, 0x2000)), Ok(()));
    assert_eq!(t.stats().free, 0x2000);
}

/// `own-25`.
#[test]
fn arena_and_owner_mismatch_never_consume_the_retained_packet() {
    let mut t = table::<8>(1, &[(0, 0x2000)], &[]).unwrap();
    let mut u = table::<8>(2, &[(0x2000, 0x2000)], &[]).unwrap();
    let r = t.reserve(7, 1, 1, LOW).unwrap();
    assert_eq!(r.allocation(), receipt(1, 7, 1, 0, 0x1000));
    let before = t.stats();
    let (error, r) = u.cancel(7, r).unwrap_err();
    assert_eq!(error, WrongArena);
    let (error, r) = t.cancel(8, r).unwrap_err();
    assert_eq!(error, WrongOwner);
    let expected = Stats {
        managed: 0x2000,
        free: 0x1000,
        allocated: 0x1000,
        allocations: 1,
        free_extents: 1,
        largest_free: 0x1000,
        extents: 2,
        capacity: 8,
    };
    assert_eq!((t.stats(), before), (expected, expected));
    let x = r.initialized(true).unwrap();
    assert_eq!(
        u.validate(7, x.allocation(), HoldState::Reserved),
        Err(WrongArena)
    );
    let (error, x) = u.publish(7, x).unwrap_err();
    assert_eq!(error, WrongArena);
    assert_eq!(t.stats(), expected);
    let first = t.publish(7, x).unwrap();
    assert_eq!(first, receipt(1, 7, 1, 0, 0x1000));
    assert_eq!(t.release(7, first), Ok(()));
    let r = t.reserve(7, 1, 1, LOW).unwrap();
    assert_eq!(r.allocation, receipt(1, 7, 2, 0, 0x1000));
    let next = t.publish(7, r.initialized(true).unwrap()).unwrap();
    assert_eq!(next, receipt(1, 7, 2, 0, 0x1000));
    assert_eq!(t.release(7, first), Err(InvalidAllocation));
    assert_eq!(t.release(7, next), Ok(()));
}

/// `own-26`: a cancel zeroes nothing, and the next reservation takes a new
/// generation.
#[test]
fn unused_reservations_roll_back_without_touching_bytes_or_reusing_generations() {
    let mut t = table::<4>(5, &[(0, 0x3000)], &[]).unwrap();
    let first = t.reserve(1, 3, 1, LOW).unwrap();
    assert_eq!(first.allocation, receipt(5, 1, 1, 0, 0x3000));
    assert_eq!(t.reserve(1, 1, 1, LOW).unwrap_err(), OutOfMemory);
    assert!(t.cancel(1, first).is_ok());
    assert_eq!(t.stats().allocations, 0);
    let r = t.reserve(1, 3, 1, LOW).unwrap();
    assert_eq!(r.allocation, receipt(5, 1, 2, 0, 0x3000));
    let x = r.initialized(true).unwrap();
    let a = t.publish(1, x).unwrap();
    assert_eq!(a, receipt(5, 1, 2, 0, 0x3000));
    assert_eq!(t.release(1, a), Ok(()));
}

/// `own-27`.
#[test]
fn dropped_reservations_stay_excluded_instead_of_implicitly_releasing_backing() {
    let mut t = table::<6>(17, &[(0, 0x3000)], &[]).unwrap();
    // The holders drop a reservation and a packet at the end of the block.
    {
        let r = t.reserve(21, 1, 1, LOW).unwrap();
        assert_eq!(r.allocation, receipt(17, 21, 1, 0, 0x1000));
        let x = t.reserve(22, 1, 1, LOW).unwrap().initialized(true).unwrap();
        assert_eq!(x.allocation, receipt(17, 22, 2, 0x1000, 0x1000));
    }
    let other = t.reserve(23, 1, 1, LOW).unwrap();
    assert_eq!(other.allocation, receipt(17, 23, 3, 0x2000, 0x1000));
    assert_eq!(t.reserve(24, 1, 1, LOW).unwrap_err(), OutOfMemory);
    assert_eq!(t.stats().allocated, 0x3000);
    assert!(t.cancel(23, other).is_ok());
    assert_eq!(t.stats().allocated, 0x2000);
}

/// `own-28`.
#[test]
fn staged_placement_respects_windows_banks_exclusions_and_high_alignment() {
    let banks = [(0, 0x4000), (0x8000, 0x8000)];
    let mut t = table::<12>(29, &banks, &[(0xa000, 0x1000)]).unwrap();
    let before = t.stats();
    assert_eq!(before.free, 0xb000);
    let hole = within(Direction::Low, 0x4000, 0x4000);
    assert_eq!(t.reserve(3, 1, 1, hole).unwrap_err(), OutOfMemory);
    let excluded = within(Direction::Low, 0xa000, 0x1000);
    assert_eq!(t.reserve(3, 1, 1, excluded).unwrap_err(), OutOfMemory);
    assert_eq!(t.reserve(3, 0, 1, LOW).unwrap_err(), InvalidSize);
    assert_eq!(t.reserve(3, 1, 3, LOW).unwrap_err(), InvalidAlignment);
    assert_eq!(t.reserve(3, u64::MAX, 1, LOW).unwrap_err(), AddressOverflow);
    assert_eq!(t.stats().free, before.free);
    let a = t
        .reserve(3, 2, 2, within(Direction::High, 0x8000, 0x8000))
        .unwrap();
    assert_eq!(a.allocation, receipt(29, 3, 1, 0xe000, 0x2000));
    let b = t
        .reserve(4, 2, 1, within(Direction::High, 0x8000, 0x3000))
        .unwrap();
    assert_eq!(b.allocation, receipt(29, 4, 2, 0x8000, 0x2000));
    assert!(t.cancel(3, a).is_ok());
    assert!(t.cancel(4, b).is_ok());
    let after = t.stats();
    assert_eq!(
        (after.free, after.free_extents),
        (before.free, before.free_extents)
    );
    assert_eq!(after.free_extents, 3);
}
