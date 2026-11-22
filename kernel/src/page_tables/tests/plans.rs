//! The plans of the write entries in the order of the contract's write
//! plans: a new table is zeroed and written before the one store that makes
//! it reachable, after a `Fence`; a plan whose last store makes an entry
//! valid ends with `Sync`; an unmap is `Store(t, i, 0)` and `Invalidate`; a
//! reset zeroes the tables in use; a copy zeroes the target's tables in use,
//! stores every valid entry of the source in index order and ends with
//! `Sync`; and the maps take their leaves in address order, each 1 GiB slot
//! under a new level 2 table with its new level 3 tables first.
//!
//! Feature: krepi.kernel.kernel-memory
//!
//! The expected steps are written from the contract, with the descriptors of
//! its kind table and the new tables at the lowest free indices.

use super::*;
use Step::{Fence, Invalidate, Store, Sync, Zero};
use std::vec;

/// The table descriptor of table `t` of the pool at `base`.
fn table(base: u64, t: usize) -> u64 {
    (base + 0x1000 * t as u64) | 3
}

/// The page descriptor of `ReadWrite` at `pa`.
fn page(pa: u64) -> u64 {
    0x60_0000_0000_0707 | pa
}

/// The steps of a write plan.
fn steps(plan: WritePlan) -> Vec<Step> {
    let mut all: Vec<Step> = (0..plan.zero_tables).map(Zero).collect();
    all.extend_from_slice(&plan.steps[..plan.len]);
    all
}

#[test]
fn map_page_writes_new_tables_before_the_stores_that_reach_them() {
    let mut t = set::<4, false>();
    let rw = Kind::ReadWrite;
    let new = [
        Zero(2),
        Store(2, 1, page(0x4020_1000)),
        Zero(1),
        Store(1, 1, table(BASE, 2)),
        Fence,
        Store(0, 1, table(BASE, 1)),
        Sync,
    ];
    let plan = t
        .map_page(0x4020_1000, 0x4020_1000, rw, BASE, BITS)
        .unwrap();
    assert_eq!(steps(plan), new);
    apply(&mut t, plan);
    // Into the level 3 table of the set.
    let plan = t
        .map_page(0x4020_2000, 0x4020_2000, rw, BASE, BITS)
        .unwrap();
    assert_eq!(steps(plan), [Store(2, 2, page(0x4020_2000)), Sync]);
    // A new level 3 table under the level 2 table of the set.
    let held = [
        Zero(3),
        Store(3, 0, page(0x4040_0000)),
        Fence,
        Store(1, 2, table(BASE, 3)),
        Sync,
    ];
    let plan = t
        .map_page(0x4040_0000, 0x4040_0000, rw, BASE, BITS)
        .unwrap();
    assert_eq!(steps(plan), held);
}

#[test]
fn map_block_writes_a_new_level_2_table_before_the_root_entry() {
    let mut t = set::<3, true>();
    let block = |pa: u64| 0x60_0000_0000_0705 | pa;
    let new = [
        Zero(1),
        Store(1, 0, block(0x4000_0000)),
        Fence,
        Store(0, 1, table(BASE, 1)),
        Sync,
    ];
    let plan = t
        .map_block(DIRECT_BASE | 0x4000_0000, 0x4000_0000, BASE, BITS)
        .unwrap();
    assert_eq!(steps(plan), new);
    apply(&mut t, plan);
    let plan = t
        .map_block(DIRECT_BASE | 0x4020_0000, 0x4020_0000, BASE, BITS)
        .unwrap();
    assert_eq!(steps(plan), [Store(1, 1, block(0x4020_0000)), Sync]);
}

#[test]
fn unmap_stores_zero_then_invalidates_and_reset_zeroes_the_tables_in_use() {
    let mut t = set::<4, false>();
    map(&mut t, 0x4020_1000, 0x7000, Kind::ReadWrite, BASE, BITS).unwrap();
    let (plan, pa) = t.unmap_page(0x4020_1000, BASE, BITS).unwrap();
    assert_eq!(pa, 0x7000);
    assert_eq!(steps(plan), [Store(2, 1, 0), Invalidate(0x4020_1000)]);
    apply(&mut t, plan);
    assert_eq!(steps(t.reset()), [Zero(0), Zero(1), Zero(2)]);
    assert_eq!(t.used(), 1);
}

#[test]
fn copy_zeroes_the_target_then_stores_in_index_order_then_syncs() {
    let mut source = set::<6, false>();
    let mut target = set::<6, false>();
    map(
        &mut source,
        0x4020_1000,
        0x7000,
        Kind::ReadWrite,
        BASE,
        BITS,
    )
    .unwrap();
    map(&mut source, 0x5000, 0x8000, Kind::ReadExecute, BASE, BITS).unwrap();
    map(
        &mut target,
        0x1000,
        0x9000,
        Kind::ReadOnly,
        0x2_0000_0000,
        BITS,
    )
    .unwrap();
    let mut plan = target
        .clone_kernel_from(&source, BASE, 0x2_0000_0000, BITS)
        .unwrap();
    let all: Vec<Step> = std::iter::from_fn(|| plan.next()).collect();
    let base = 0x2_0000_0000;
    let expected = [
        Zero(0),
        Zero(1),
        Zero(2),
        Store(0, 0, table(base, 3)),
        Store(0, 1, table(base, 1)),
        Store(1, 1, table(base, 2)),
        Store(2, 1, page(0x7000)),
        Store(3, 0, table(base, 4)),
        Store(4, 5, 0x40_0000_0000_0787 | 0x8000),
        Sync,
    ];
    assert_eq!(all, expected);
}

#[test]
fn kernel_map_writes_each_level_3_table_then_the_level_2_table() {
    let mut t = set::<KERNEL_TABLES, false>();
    let text = (0x4020_0000, 0x2000, LayoutKind::ReadExecute);
    let data = (0x4040_0000, 0x1000, LayoutKind::ReadWrite);
    let rx = |pa: u64| 0x40_0000_0000_0787 | pa;
    let new = [
        Zero(2),
        Store(2, 0, rx(0x4020_0000)),
        Store(2, 1, rx(0x4020_1000)),
        Zero(3),
        Store(3, 0, page(0x4040_0000)),
        Zero(1),
        Store(1, 1, table(BASE, 2)),
        Store(1, 2, table(BASE, 3)),
        Fence,
        Store(0, 1, table(BASE, 1)),
        Sync,
    ];
    assert_eq!(
        kernel(&mut t, layout(&[data, text], &[]), BASE, BITS),
        Ok(new.to_vec())
    );
    // Under the level 2 table of the set: a page into a level 3 table of
    // the set, then a new level 3 table.
    let rodata = (0x4020_2000, 0x1000, LayoutKind::ReadOnly);
    let device = (0x4060_0000, 0x1000, LayoutKind::Device);
    let held = [
        Store(2, 2, 0x60_0000_0000_0787 | 0x4020_2000),
        Zero(4),
        Store(4, 0, 0x60_0000_0000_0403 | 0x4060_0000),
        Fence,
        Store(1, 3, table(BASE, 4)),
        Sync,
    ];
    let steps = kernel(&mut t, layout(&[device, rodata], &[]), BASE, BITS);
    assert_eq!(steps, Ok(held.to_vec()));
}

#[test]
fn direct_map_writes_blocks_and_pages_in_address_order() {
    let block = |pa: u64| 0x60_0000_0000_0705 | pa;
    // The last page of 4 MiB is boot storage: a block, then 511 pages.
    let memory = MemoryPlan::all_ram(&[span(0, 0x40_0000)], &[span(0x3f_f000, 0x1000)], &[]);
    let memory = memory.unwrap();
    let pages =
        |t3: usize| (0..511).map(move |i| Store(t3, i, page(0x20_0000 + 0x1000 * i as u64)));
    let mut new = vec![Zero(2)];
    new.extend(pages(2));
    new.extend([
        Zero(1),
        Store(1, 0, block(0)),
        Store(1, 1, table(BASE, 2)),
        Fence,
        Store(0, 0, table(BASE, 1)),
        Sync,
    ]);
    let mut t = set::<4, true>();
    assert_eq!(direct(&mut t, &memory, BASE, BITS), Ok(new));
    // Under the level 2 table of a set that holds the last block of the
    // 1 GiB slot: the block, then a new level 3 table with its pages.
    let mut t = set::<4, true>();
    super::block(&mut t, DIRECT_BASE | 0x3fe0_0000, 0x3fe0_0000, BASE, BITS).unwrap();
    let mut held = vec![Store(1, 0, block(0)), Zero(2)];
    held.extend(pages(2));
    held.extend([Fence, Store(1, 1, table(BASE, 2)), Sync]);
    assert_eq!(direct(&mut t, &memory, BASE, BITS), Ok(held));
}
