//! The capacities of the contract: the 80 tables of the pool of the direct
//! map, the free tables of a pool whose record of tables in use is all its
//! tables but one, all of them or above them, and the 160 extents and 132
//! exclusion records of the page ownership table.
//!
//! Feature: krepi.kernel.kernel-memory

use super::*;
use OwnershipError::*;
use Step::{Fence, Store, Sync, Zero};
use TableError::OutOfTables;
use std::vec;

/// The boot memory map of one bank of 1 GiB from 0, whose boot storage is
/// the page at `0x3000`, with `count` firmware reservations of one page,
/// each at `0x1000` into a 2 MiB block of its own from block 0 on: its
/// direct map needs the root, one level 2 table and a level 3 table for each
/// reservation.
fn reserved_gib(count: u64) -> MemoryPlan {
    let firmware: Vec<ReservedRegion> = (0..count)
        .map(|block| ReservedRegion {
            span: span(block * BLOCK_SIZE + 0x1000, 0x1000),
            no_map: true,
            reusable: false,
        })
        .collect();
    let ram = [span(0, 0x4000_0000)];
    MemoryPlan::all_ram(&ram, &[span(0x3000, 0x1000)], &firmware).unwrap()
}

#[test]
fn direct_map_fills_exactly_the_pool() {
    let mut t = set::<DIRECT_MAP_TABLES, true>();
    let steps = direct(&mut t, &reserved_gib(78), BASE, BITS).unwrap();
    assert_eq!(t.used(), DIRECT_MAP_TABLES);
    assert_eq!(counts(&steps).1, 512 - 78);
}

#[test]
fn direct_map_one_table_over_the_pool_fails() {
    let mut t = set::<DIRECT_MAP_TABLES, true>();
    let map = direct(&mut t, &reserved_gib(79), BASE, BITS);
    assert_eq!(map, Err(TableError::OutOfTables));
    assert_eq!(t.used(), 1);
    assert!(t.pool.iter().all(|table| table.iter().all(|&d| d == 0)));
}

/// The page descriptor of `ReadWrite` at `pa`.
const fn page(pa: u64) -> u64 {
    0x60_0000_0000_0707 | pa
}

/// The table descriptor of table `t` of the pool at `BASE`.
const fn table_entry(t: u64) -> u64 {
    (BASE + 0x1000 * t) | 3
}

/// The boot memory map of RAM `[start, start + 0x2000)` whose boot storage
/// is the page at `held`: its usable page is the other one.
fn one_page(start: u64, held: u64) -> MemoryPlan {
    MemoryPlan::all_ram(&[span(start, 0x2000)], &[span(held, 0x1000)], &[]).unwrap()
}

/// A record of `usize::MAX` on a pool of one table leaves no table free: a
/// map of one page at 0, which needs a level 2 and a level 3 table, fails
/// with `OutOfTables` and changes nothing.
#[test]
fn a_record_above_the_pool_leaves_no_free_table() {
    let mut lower = set::<1, false>();
    lower.used = usize::MAX;
    let one = layout(&[(0, PAGE_SIZE, LayoutKind::ReadWrite)], &[]);
    assert_eq!(kernel(&mut lower, one, 0, BITS), Err(OutOfTables));
    assert_eq!(lower.used, usize::MAX);
    let mut upper = set::<1, true>();
    upper.used = usize::MAX;
    let map = direct(&mut upper, &one_page(0, PAGE_SIZE), 0, BITS);
    assert_eq!(map, Err(OutOfTables));
    assert_eq!(upper.used, usize::MAX);
    assert!(lower.pool[0].iter().chain(&upper.pool[0]).all(|&d| d == 0));
}

/// On a pool of 3 tables with a block at 0, which uses 2: a page that needs
/// a level 2 and a level 3 table is refused; a page at `0x20_0000` takes the
/// third table, under the level 2 table of the block; then a page beside it
/// needs no table and is mapped, and one at `0x40_0000`, which needs one, is
/// refused. A refusal changes nothing. With a record of `usize::MAX` no
/// table is free, but a page into the level 3 table, which needs none, is
/// still mapped, and the record stays.
#[test]
fn the_last_free_table_is_taken_and_one_more_is_refused() {
    let new = vec![
        Zero(2),
        Store(2, 0, page(0x20_0000)),
        Fence,
        Store(1, 1, table_entry(2)),
        Sync,
    ];
    let beside = vec![Store(2, 1, page(0x20_1000)), Sync];
    let mut t = set::<3, false>();
    block(&mut t, 0, 0, BASE, BITS).unwrap();
    let rw = LayoutKind::ReadWrite;
    for (start, steps, used) in [
        (0x4000_0000, Err(OutOfTables), 2),
        (0x20_0000, Ok(new.clone()), 3),
        (0x20_1000, Ok(beside.clone()), 3),
        (0x40_0000, Err(OutOfTables), 3),
    ] {
        let map = kernel(&mut t, layout(&[(start, PAGE_SIZE, rw)], &[]), BASE, BITS);
        assert_eq!((map, t.used()), (steps, used), "{start:#x}");
    }
    t.used = usize::MAX;
    let page_in_level_3 = layout(&[(0x20_2000, PAGE_SIZE, rw)], &[]);
    let map = kernel(&mut t, page_in_level_3, BASE, BITS);
    assert_eq!(map, Ok(vec![Store(2, 2, page(0x20_2000)), Sync]));
    assert_eq!(t.used, usize::MAX);
    let mut t = set::<3, true>();
    block(&mut t, DIRECT_BASE, 0, BASE, BITS).unwrap();
    for (memory, steps, used) in [
        (one_page(0x4000_0000, 0x4000_1000), Err(OutOfTables), 2),
        (one_page(0x20_0000, 0x20_1000), Ok(new), 3),
        (one_page(0x20_0000, 0x20_0000), Ok(beside), 3),
        (one_page(0x40_0000, 0x40_1000), Err(OutOfTables), 3),
    ] {
        assert_eq!(
            (direct(&mut t, &memory, BASE, BITS), t.used()),
            (steps, used)
        );
    }
    t.used = usize::MAX;
    let map = direct(&mut t, &one_page(0x20_2000, 0x20_3000), BASE, BITS);
    assert_eq!(map, Ok(vec![Store(2, 2, page(0x20_2000)), Sync]));
    assert_eq!(t.used, usize::MAX);
}

#[test]
fn extents_fill_to_capacity_and_refuse_one_more() {
    // Each page at an alignment of 2 pages from the lowest takes the next
    // even page of the bank: from the second on, it leaves the odd page
    // before it free and adds two extents.
    let mut t = table::<EXTENTS>(1, &[(0, 200 * PAGE_SIZE)], &[]).unwrap();
    let mut held = Vec::new();
    for page in 0..80 {
        let a = allocate(&mut t, 1, 1, 2, LOW).unwrap();
        assert_eq!(a.range, range(2 * page * PAGE_SIZE, PAGE_SIZE));
        held.push(a);
    }
    assert_eq!(t.stats().extents, EXTENTS);
    let before = t.stats();
    assert_eq!(t.choose(1, 1, 2, LOW).unwrap_err(), MetadataExhausted);
    assert_eq!(t.stats(), before);
    // A fit that needs no extent is still taken.
    let c = t.choose(1, 1, 1, LOW).unwrap();
    assert_eq!(c.range, range(PAGE_SIZE, PAGE_SIZE));
    // A release never needs an extent.
    for a in held {
        assert_eq!(t.release(1, a), Ok(()));
    }
    assert_eq!(t.stats().extents, 1);
}

/// One bank of 300 pages and `count` firmware reservations of one byte, one
/// on each odd page.
fn every_other_page(count: u64) -> Result<Ownership<EXTENTS, EXCLUSION_RECORDS>, OwnershipError> {
    let firmware: Vec<(u64, u64)> = (0..count).map(|i| ((2 * i + 1) * PAGE_SIZE, 1)).collect();
    table::<EXTENTS>(1, &[(0, 300 * PAGE_SIZE)], &firmware)
}

#[test]
fn exclusions_to_capacity_initialize() {
    let t = every_other_page(EXCLUSION_RECORDS as u64).unwrap();
    assert_eq!(t.exclusion_count, EXCLUSION_RECORDS);
    assert_eq!(t.stats().extents, EXCLUSION_RECORDS + 1);
    let firmware = Some(Owner::Excluded(Excluder::Firmware));
    assert_eq!(t.owner(263 * PAGE_SIZE + 0x800), firmware);
    assert_eq!(t.owner(264 * PAGE_SIZE), Some(Owner::Free));
}

#[test]
fn one_exclusion_over_capacity_fails() {
    let refused = every_other_page(EXCLUSION_RECORDS as u64 + 1);
    assert_eq!(refused.err(), Some(MetadataExhausted));
}
