//! The capacities of the contract: the 80 tables of the pool of the direct
//! map, and the 160 extents and 132 exclusion records of the page ownership
//! table.
//!
//! Feature: krepi.kernel.kernel-memory

use super::*;
use OwnershipError::*;

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
