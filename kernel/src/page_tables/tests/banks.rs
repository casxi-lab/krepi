//! The vectors of `src/memory/tests/banks.rs` of the contract: tables of
//! several banks.
//!
//! Feature: krepi.kernel.kernel-memory

use super::*;
use OwnershipError::*;

/// `own-17`.
#[test]
fn banks_reject_empty_overlap_unaligned_and_excess_metadata() {
    assert_eq!(table::<8>(1, &[], &[]).err(), Some(InvalidRange));
    let overlapping = [(0, 0x2000), (0x1000, 0x1000)];
    assert_eq!(table::<8>(1, &overlapping, &[]).err(), Some(InvalidRange));
    let twice = [(0, 0x1000), (0, 0x1000)];
    assert_eq!(table::<8>(1, &twice, &[]).err(), Some(InvalidRange));
    assert_eq!(
        table::<8>(1, &[(1, 0x1000)], &[]).err(),
        Some(InvalidAlignment)
    );
    let two = [(0, 0x1000), (0x2000, 0x1000)];
    assert_eq!(table::<1>(1, &two, &[]).err(), Some(MetadataExhausted));
}

/// `own-18`.
#[test]
fn adjacent_banks_never_merge_after_release_in_either_order() {
    for reverse in [false, true] {
        let mut t = table::<8>(1, &[(0x1000, 0x2000), (0x3000, 0x2000)], &[]).unwrap();
        let a = allocate(&mut t, 1, 2, 1, LOW).unwrap();
        assert_eq!(a, receipt(1, 1, 1, 0x1000, 0x2000));
        let b = allocate(&mut t, 1, 2, 1, LOW).unwrap();
        assert_eq!(b, receipt(1, 1, 2, 0x3000, 0x2000));
        for r in if reverse { [b, a] } else { [a, b] } {
            assert_eq!(t.release(1, r), Ok(()));
        }
        assert_eq!(
            (t.stats().free_extents, t.stats().largest_free),
            (2, 0x2000)
        );
        assert_eq!(t.choose(1, 3, 1, LOW).unwrap_err(), OutOfMemory);
        let d = allocate(&mut t, 2, 1, 1, HIGH);
        assert_eq!(d, Ok(receipt(1, 2, 3, 0x4000, 0x1000)));
    }
}

/// `own-19`.
#[test]
fn unsorted_banks_and_reservations_preserve_physical_order_and_holes() {
    let banks = [(0x1_0000_0000, 0x4000), (0, 0x4000)];
    let firmware = [(0x3001, 0xffff_d000), (0x1001, 1)];
    let mut t = table::<8>(1, &banks, &firmware).unwrap();
    assert_eq!(t.stats().managed, 0x5000);
    let a = allocate(&mut t, 1, 3, 1, HIGH).unwrap();
    assert_eq!(a, receipt(1, 1, 1, 0x1_0000_1000, 0x3000));
    let b = allocate(&mut t, 1, 1, 1, HIGH).unwrap();
    assert_eq!(b, receipt(1, 1, 2, 0x2000, 0x1000));
    assert_eq!(t.release(1, a), Ok(()));
    assert_eq!(t.release(1, b), Ok(()));
    assert_eq!(t.stats().free_extents, 3);
}

/// `own-20`: the choice is the range that the caller zeroes.
#[test]
fn high_placement_honors_alignment_window_and_backend_failure() {
    let mut t = table::<8>(1, &[(0x1_0000_0000, 0x1_0000)], &[]).unwrap();
    let window = within(Direction::High, 0x1_0000_1001, 0xc000);
    let c = t.choose(1, 2, 4, window).unwrap();
    assert_eq!(c.range, range(0x1_0000_8000, 0x2000));
    assert_eq!(t.assign(c, false), Err(ZeroFailed));
    assert_eq!(t.stats().free, 0x1_0000);
    let c = t.choose(2, 2, 4, window).unwrap();
    assert_eq!(c.range, range(0x1_0000_8000, 0x2000));
    let a = t.assign(c, true).unwrap();
    assert_eq!(a, receipt(1, 2, 1, 0x1_0000_8000, 0x2000));
    let outside = within(Direction::High, 0, 0x1000);
    assert_eq!(t.choose(2, 1, 1, outside).unwrap_err(), OutOfMemory);
    assert_eq!(t.release(2, a), Ok(()));
}

/// `own-21`.
#[test]
fn multi_gib_capacity_is_bookkeeping_without_host_ram_access() {
    let banks = [(0x4000_0000, 0xc000_0000), (0x1_0000_0000, 0x1_0000_0000)];
    let mut t = table::<2>(1, &banks, &[]).unwrap();
    let a = allocate(&mut t, 1, 0xc000_0000 / PAGE_SIZE, 1, LOW).unwrap();
    assert_eq!(a, receipt(1, 1, 1, 0x4000_0000, 0xc000_0000));
    let b = allocate(&mut t, 1, 0x1_0000_0000 / PAGE_SIZE, 1, HIGH).unwrap();
    assert_eq!(b, receipt(1, 1, 2, 0x1_0000_0000, 0x1_0000_0000));
    assert_eq!((t.stats().free, t.stats().managed), (0, 0x1_c000_0000));
    assert_eq!(t.release(1, a), Ok(()));
    assert_eq!(t.release(1, b), Ok(()));
    assert_eq!((t.stats().free_extents, t.stats().extents), (2, 2));
}

/// The pages of a bank of `own-22`.
const PAGES: usize = 24;

/// `own-22`: 800 steps of allocations, low and high, and releases against
/// a model that marks each page of each bank busy or free.
#[test]
fn mixed_placement_matches_an_independent_sparse_page_model() {
    let bytes = PAGES as u64 * PAGE_SIZE;
    let banks = [0x10_0000, 0x11_8000, 0x1_0000_1000];
    let firmware = [(0x10_2fff, 2), (0x11_7fff, 2), (0x1_0001_4000, 0x1000)];
    let mut t = table::<128>(1, &banks.map(|start| (start, bytes)), &firmware).unwrap();
    let mut busy = [[false; PAGES]; 3];
    for (start, row) in banks.iter().zip(busy.iter_mut()) {
        for (page, used) in row.iter_mut().enumerate() {
            let at = range(start + page as u64 * PAGE_SIZE, PAGE_SIZE);
            *used = firmware.iter().any(|&(s, l)| range(s, l).overlaps(at));
        }
    }
    let excluded = busy;
    let free = |busy: &[[bool; PAGES]; 3]| {
        busy.iter().flatten().filter(|&&used| !used).count() as u64 * PAGE_SIZE
    };
    let mut live: Vec<Allocation> = Vec::new();
    for step in 0..800usize {
        if step % 3 != 0 && !live.is_empty() {
            let old = live.remove(step * 7 % live.len());
            let bank = banks
                .iter()
                .position(|&s| s <= old.range.start && old.range.start < s + bytes);
            let bank = bank.unwrap();
            let first = ((old.range.start - banks[bank]) / PAGE_SIZE) as usize;
            busy[bank][first..first + (old.range.len / PAGE_SIZE) as usize].fill(false);
            assert_eq!(t.release(old.owner, old), Ok(()));
        } else {
            let length = step % 5 + 1;
            let alignment = 1u64 << (step % 4);
            let mut fits = Vec::new();
            for (bank, &start) in banks.iter().enumerate() {
                for first in 0..=PAGES - length {
                    let address = start + first as u64 * PAGE_SIZE;
                    if address % (alignment * PAGE_SIZE) == 0
                        && busy[bank][first..first + length].iter().all(|&used| !used)
                    {
                        fits.push((address, bank, first));
                    }
                }
            }
            let high = step % 2 == 0;
            let expected = if high { fits.last() } else { fits.first() };
            let placement = if high { HIGH } else { LOW };
            let result = allocate(&mut t, 7, length as u64, alignment, placement);
            match expected {
                Some(&(address, bank, first)) => {
                    let a = result.unwrap();
                    assert_eq!(a.range.start, address);
                    busy[bank][first..first + length].fill(true);
                    live.push(a);
                }
                None => assert_eq!(result, Err(OutOfMemory)),
            }
        }
        assert_eq!(t.stats().free, free(&busy));
        for (row, fixed) in busy.iter().zip(excluded) {
            assert!(row.iter().zip(fixed).all(|(&used, out)| !out || used));
        }
    }
    for a in live {
        assert_eq!(t.release(a.owner, a), Ok(()));
    }
    assert_eq!(t.stats().free, free(&excluded));
}
