//! The capacities of the contract: the 80 tables of the pool of the direct
//! map.
//!
//! Feature: krepi.kernel.kernel-memory

use super::*;

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
