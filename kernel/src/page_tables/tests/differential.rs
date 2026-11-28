//! The differential tests of `kernel_map` and `direct_map`, whose checks
//! count the new tables from 0, against the verbatim copy of the entries
//! with their checks from before, which counted from the record of the
//! tables in use. Each input runs on two sets that one construction builds;
//! the two must give the same error or plans of the same steps, and leave
//! the same record and descriptors. The inputs reach every branch of both
//! checks that a caller can reach, with each loop run once and up to its
//! bound and the range loops also 0 times, and hold the frozen vectors
//! `dm-01` to `dm-04` with their pools; the pools give the largest inputs
//! of both entries exactly the free tables that they need and one fewer.
//! No record exceeds its pool, where the copy can overflow. No caller
//! reaches the `else` of `MapCheck::passed`, a page or leaf loop run 0
//! times, or, in `direct_map`, the `Alignment` branch of the range check and
//! its exit for a leaf that an earlier range holds: a range has at least a
//! page, and the usable ranges are whole pages, disjoint and in order.
//!
//! Feature: krepi.kernel.kernel-memory
//!
//! The comparison shows that the two codes agree on these inputs, not that
//! either is right: the expected values are those of the vectors and of the
//! other host tests, among them the capacities of the pools.

use super::old::{direct_map_old, kernel_map_old};
use super::*;
use LayoutKind::{Device as DV, ReadExecute as RX, ReadOnly as RO, ReadWrite as RW};
use std::vec;

/// What an entry gives and leaves: its error or the steps of its plan, the
/// record of the tables in use and the descriptors of the set.
type Outcome = (Result<Vec<Step>, TableError>, usize, Vec<u64>);

/// A construction of a set before the entry.
type Build<const N: usize, const UPPER: bool> = fn(&mut Tables<N, UPPER>);

/// The pools of the inputs: the two of the tests and of the vectors, one of
/// width 32, and a base off a page, a width of 31 and a pool that ends above
/// `2^40` once it holds two tables.
const POOLS: [(u64, u8); 6] = [
    (BASE, BITS),
    (0x8_0000, 40),
    (0x8_0000, 32),
    (BASE + 0x800, BITS),
    (BASE, 31),
    ((1 << 40) - 0x1000, 40),
];

/// The virtual address of `pa` in the region of the set.
fn va<const UPPER: bool>(pa: u64) -> u64 {
    if UPPER { DIRECT_BASE | pa } else { pa }
}

/// The kind of the page of a construction.
const PAGE: Kind = Kind::ReadWrite;

/// The constructions: the root alone; a record of 0, of all the tables but
/// one and of all of them; a block at 0 with its level 2 table; that block
/// and a page at `0x20_1000` with its level 3 table; a block in the second
/// 1 GiB slot; and a root entry, or a level 2 entry beside the block, that
/// points at the first table outside the pool. A map that does not fit the
/// pool leaves the set unchanged.
fn builds<const N: usize, const UPPER: bool>() -> [Build<N, UPPER>; 9] {
    [
        |_| {},
        |t| t.used = 0,
        |t| t.used = N - 1,
        |t| t.used = N,
        |t| _ = block(t, va::<UPPER>(0), 0, BASE, BITS),
        |t| {
            _ = block(t, va::<UPPER>(0), 0, BASE, BITS);
            _ = map(t, va::<UPPER>(0x20_1000), 0x20_1000, PAGE, BASE, BITS);
        },
        |t| _ = block(t, va::<UPPER>(1 << 30), 1 << 30, BASE, BITS),
        |t| t.pool[0][0] = (BASE + 0x1000 * N as u64) | 3,
        |t| {
            _ = block(t, va::<UPPER>(0), 0, BASE, BITS);
            if N > 1 {
                t.pool[1][2] = (BASE + 0x1000 * N as u64) | 3;
            }
        },
    ]
}

/// What `entry` gives on a set that `build` makes, with the record and the
/// descriptors that it leaves.
fn run<const N: usize, const UPPER: bool>(
    build: Build<N, UPPER>,
    entry: impl FnOnce(&mut Tables<N, UPPER>) -> Result<Vec<Step>, TableError>,
) -> Outcome {
    let mut t = set();
    build(&mut t);
    let steps = entry(&mut t);
    (steps, t.used, t.pool.iter().flatten().copied().collect())
}

/// Checks `kernel_map` against the copy on each construction for each
/// layout and pool; gives the number of inputs.
fn kernel_agrees<const N: usize>(layouts: &[Layout<'_>]) -> usize {
    let mut compared = 0;
    for (k, build) in builds::<N, false>().into_iter().enumerate() {
        for &l in layouts {
            for (base, bits) in POOLS {
                let new = run(build, |t| kernel_map(t, l, base, bits).map(kernel_steps));
                let old = run(build, |t| {
                    kernel_map_old(t, l, base, bits).map(kernel_steps)
                });
                assert_eq!(new, old, "{N} {k} {l:?} {base:#x} {bits}");
                compared += 1;
            }
        }
    }
    compared
}

/// Checks `direct_map` against the copy on each construction for each boot
/// memory map and pool; gives the number of inputs.
fn direct_agrees<const N: usize>(memories: &[MemoryPlan]) -> usize {
    let mut compared = 0;
    for (k, build) in builds::<N, true>().into_iter().enumerate() {
        for (i, m) in memories.iter().enumerate() {
            for (base, bits) in POOLS {
                let new = run(build, |t| direct_map(t, m, base, bits).map(direct_steps));
                let old = run(build, |t| {
                    direct_map_old(t, m, base, bits).map(direct_steps)
                });
                assert_eq!(new, old, "{N} {k} {i} {base:#x} {bits}");
                compared += 1;
            }
        }
    }
    compared
}

/// The steps of the plan of `kernel_map`.
fn kernel_steps<const N: usize>(mut plan: KernelMapPlan<'_, N>) -> Vec<Step> {
    std::iter::from_fn(|| plan.next()).collect()
}

/// The steps of the plan of `direct_map`.
fn direct_steps<const N: usize>(mut plan: DirectMapPlan<'_, N>) -> Vec<Step> {
    std::iter::from_fn(|| plan.next()).collect()
}

/// The layouts: none; one page under the root, under a level 2 table and
/// into a level 3 table of the constructions, also followed by one under a
/// level 2 table, on their page and on their block; pages across a 2 MiB
/// and a 1 GiB boundary, and 1,024 pages; a range that an earlier one
/// covers, also of the same start; a guard in a range and guards beside it;
/// ends off a page, above `2^39` and above `2^32`, after a range that
/// passed; ranges out of order; and 16 ranges, a page in each of 16 slots of
/// 2 MiB over four of 1 GiB, with a count of 16, 17 and `usize::MAX`.
fn layouts() -> Vec<Layout<'static>> {
    let gib = 1 << 30;
    let mut all = vec![
        layout(&[], &[]),
        layout(&[(0, 0x1000, RW)], &[]),
        layout(&[(0x40_0000, 0x1000, RW)], &[]),
        layout(&[(0x20_0000, 0x1000, RW)], &[]),
        layout(&[(0x20_0000, 0x1000, RW), (0x40_0000, 0x1000, RW)], &[]),
        layout(&[(0x20_1000, 0x1000, RW)], &[]),
        layout(&[(0x1000, 0x1000, RW)], &[]),
        layout(&[(0x1f_e000, 0x4000, RW)], &[]),
        layout(&[(gib - 0x2000, 0x4000, RW)], &[]),
        layout(&[(0, 0x40_0000, RW)], &[]),
        layout(&[(0x2000, 0x1000, RW), (0x1000, 0x2000, RX)], &[]),
        layout(&[(0x5000, 0x1000, RO), (0x5000, 0x1000, RW)], &[]),
        layout(&[(0x8000, 0x3000, RW)], &[0x9ff8]),
        layout(&[(0x8000, 0x3000, RW)], &[0x7ff8, 0xb000, 0x1_0000, 0]),
        layout(&[(0, 0x1000, RW), (0x2800, 0x1000, RW)], &[]),
        layout(&[(0, 0x1000, RW), (0x7f_ffff_f000, 0x2000, RW)], &[]),
        layout(&[(0, 0x1000, RW), (0x1_0000_0000, 0x1000, DV)], &[]),
        layout(
            &[
                (gib, 0x1000, DV),
                (0, 0x2000, RX),
                (0x20_0000, 0x1000, RW),
                (0x2000, 0x1000, RO),
            ],
            &[],
        ),
    ];
    let kinds = [RX, RO, RW, DV];
    let ranges: Vec<_> = (0..16)
        .map(|k| (k << 28, 0x1000, kinds[k as usize % 4]))
        .collect();
    for count in [16, 17, usize::MAX] {
        all.push(Layout {
            count,
            ..layout(&ranges, &[])
        });
    }
    all
}

#[test]
fn built_layouts_agree_with_the_code_before_the_count_from_zero() {
    let layouts = layouts();
    let compared = kernel_agrees::<1>(&layouts)
        + kernel_agrees::<2>(&layouts)
        + kernel_agrees::<3>(&layouts)
        + kernel_agrees::<4>(&layouts)
        + kernel_agrees::<5>(&layouts)
        + kernel_agrees::<20>(&layouts)
        + kernel_agrees::<21>(&layouts)
        + kernel_agrees::<KERNEL_TABLES>(&layouts);
    assert_eq!(compared, 8 * 9 * 21 * 6);
}

/// The firmware reservation of `size` bytes at `start`.
fn firmware(start: u64, size: u64, no_map: bool, reusable: bool) -> ReservedRegion {
    let span = span(start, size);
    ReservedRegion {
        span,
        no_map,
        reusable,
    }
}

/// A boot memory map or the error of its construction.
type Made = Result<MemoryPlan, crate::fdt::PlanError>;

/// The boot memory map of the bank `[start, start + size)`, with the boot
/// storage of the page at `held` and the firmware reservations `reserved`.
fn bank(start: u64, size: u64, held: u64, reserved: &[ReservedRegion]) -> Made {
    MemoryPlan::all_ram(&[span(start, size)], &[span(held, PAGE_SIZE)], reserved)
}

/// The boot memory maps: those of `dm-01` to `dm-04`; one without a usable
/// range; one page at 0 and one at `0x20_0000`; a block and a page in the
/// two 2 MiB slots after the block of the constructions in the second 1 GiB
/// slot; 511 pages, two blocks and 511 pages across the first 1 GiB
/// boundary; a range that ends above `2^39`; and 32 banks of 16 pages, each
/// in a 2 MiB slot of its own and split by four firmware reservations, and
/// the first four also by the boot storage: the most usable ranges that a
/// boot memory map has, 164.
fn memories() -> Vec<MemoryPlan> {
    let boot = [span(0x8_0000, 0x1000)];
    let dm01 = [firmware(0x60_0fff, 2, false, true)];
    let dm02 = [span(0, 0x20_0000), span(0x1_0000_0000, 0x40_0000)];
    let dm04 = [
        span(0, 0x3fc0_0000),
        span(0x4000_0000, 0xc000_0000),
        span(0x1_0000_0000, 0x1_0000_0000),
    ];
    let no_map = [firmware(0x1_ffff_f001, 1, true, false)];
    let tail = [firmware(0x405f_f000, 0x1000, true, false)];
    let banks: Vec<Span> = (0..32).map(|k| span(k << 22, 0x1_0000)).collect();
    let held: Vec<Span> = (0..4).map(|k| span((k << 22) + 0xa000, 0x1000)).collect();
    let reserved: Vec<ReservedRegion> = (0..128)
        .map(|k| firmware(((k / 4) << 22) + (k % 4 + 1) * 0x2000, 0x1000, true, false))
        .collect();
    let all: Vec<MemoryPlan> = [
        MemoryPlan::new(span(0, 0x100_0000), &[span(0, 0x100_0000)], &boot, &dm01),
        MemoryPlan::new(dm02[1], &dm02, &boot, &[]),
        MemoryPlan::new(span(0, 0x40_0000), &[span(0, 0x40_0000)], &boot, &[]),
        MemoryPlan::all_ram(&dm04, &boot, &no_map),
        bank(0, 0x1000, 0, &[]),
        bank(0, 0x2000, 0x1000, &[]),
        bank(0x20_0000, 0x2000, 0x20_1000, &[]),
        bank(0x4020_0000, 0x20_2000, 0x4040_0000, &[]),
        bank(0x3fe0_0000, 0x80_0000, 0x3fe0_0000, &tail),
        bank(0x7f_ffe0_0000, 0x40_0000, 0x7f_ffe0_0000, &[]),
        MemoryPlan::all_ram(&banks, &held, &reserved),
    ]
    .into_iter()
    .map(Result::unwrap)
    .collect();
    let (mut ranges, mut count) = (all[10].available_ranges(), 0);
    while ranges.next().is_some() {
        count += 1;
    }
    assert_eq!(count, 164);
    all
}

#[test]
fn built_direct_maps_agree_with_the_code_before_the_count_from_zero() {
    let memories = memories();
    let compared = direct_agrees::<1>(&memories)
        + direct_agrees::<2>(&memories)
        + direct_agrees::<3>(&memories)
        + direct_agrees::<4>(&memories)
        + direct_agrees::<8>(&memories)
        + direct_agrees::<16>(&memories)
        + direct_agrees::<33>(&memories)
        + direct_agrees::<34>(&memories)
        + direct_agrees::<DIRECT_MAP_TABLES>(&memories);
    assert_eq!(compared, 9 * 9 * 11 * 6);
}
