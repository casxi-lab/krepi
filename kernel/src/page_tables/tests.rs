//! The host tests of the page tables: the execution of a plan on the pool
//! of its set, the frozen vectors of the contract, the rows of the kind
//! table and the direct address, the kernel's mappings, the direct maps of
//! the Pi 5 models against a page model, and the capacity of the pool.
//!
//! Feature: krepi.kernel.kernel-memory
//!
//! The expected values come from the contract and its frozen vectors, never
//! from an earlier run.

extern crate std;

use super::*;
use crate::fdt::ReservedRegion;
use std::vec::Vec;

mod boot;
mod capacity;
mod kinds;
mod mapping;
mod models;
mod ownership;
mod paging;

/// The `base` of the sets of the tests unless one says otherwise.
const BASE: u64 = 0x1_0000_0000;

/// The physical width of the tests unless one says otherwise.
const BITS: u8 = 40;

/// A set of `N` tables of zero storage.
fn set<const N: usize, const UPPER: bool>() -> Tables<N, UPPER> {
    Tables::new([[0; ENTRIES]; N])
}

/// Executes one step on a pool, as the architecture crate does.
fn execute<const N: usize>(pool: &mut [[u64; ENTRIES]; N], step: Step) {
    match step {
        Step::Zero(table) => pool[table] = [0; ENTRIES],
        Step::Store(table, index, d) => pool[table][index] = d,
        Step::Fence | Step::Sync | Step::Invalidate(_) => {}
    }
}

/// Executes a write plan on the pool of its set.
fn apply<const N: usize, const UPPER: bool>(set: &mut Tables<N, UPPER>, plan: WritePlan) {
    for table in 0..plan.zero_tables {
        execute(&mut set.pool, Step::Zero(table));
    }
    for step in &plan.steps[..plan.len] {
        execute(&mut set.pool, *step);
    }
}

/// `map_page` with its plan executed.
fn map<const N: usize, const UPPER: bool>(
    set: &mut Tables<N, UPPER>,
    va: u64,
    pa: u64,
    kind: Kind,
    base: u64,
    bits: u8,
) -> Result<(), TableError> {
    let plan = set.map_page(va, pa, kind, base, bits)?;
    apply(set, plan);
    Ok(())
}

/// `map_block` with its plan executed.
fn block<const N: usize, const UPPER: bool>(
    set: &mut Tables<N, UPPER>,
    va: u64,
    pa: u64,
    base: u64,
    bits: u8,
) -> Result<(), TableError> {
    let plan = set.map_block(va, pa, base, bits)?;
    apply(set, plan);
    Ok(())
}

/// `unmap_page` with its plan executed.
fn unmap<const N: usize, const UPPER: bool>(
    set: &mut Tables<N, UPPER>,
    va: u64,
    base: u64,
    bits: u8,
) -> Result<u64, TableError> {
    let (plan, page) = set.unmap_page(va, base, bits)?;
    apply(set, plan);
    Ok(page)
}

/// `clone_kernel_from` with its plan executed on the target, once the plan
/// has given its last step and so no longer borrows the target.
fn copy<const N: usize, const UPPER: bool>(
    target: &mut Tables<N, UPPER>,
    source: &Tables<N, UPPER>,
    source_base: u64,
    base: u64,
    bits: u8,
) -> Result<(), TableError> {
    let mut plan = target.clone_kernel_from(source, source_base, base, bits)?;
    let steps: Vec<Step> = std::iter::from_fn(|| plan.next()).collect();
    for step in steps {
        execute(&mut target.pool, step);
    }
    Ok(())
}

/// `kernel_map` with its plan executed once the plan has given its last
/// step; the steps of the plan.
fn kernel<const N: usize>(
    set: &mut Tables<N, false>,
    layout: Layout<'_>,
    base: u64,
    bits: u8,
) -> Result<Vec<Step>, TableError> {
    let mut plan = kernel_map(set, layout, base, bits)?;
    let steps: Vec<Step> = std::iter::from_fn(|| plan.next()).collect();
    for step in &steps {
        execute(&mut set.pool, *step);
    }
    Ok(steps)
}

/// `direct_map` with its plan executed once the plan has given its last
/// step; the steps of the plan.
fn direct<const N: usize>(
    set: &mut Tables<N, true>,
    memory: &MemoryPlan,
    base: u64,
    bits: u8,
) -> Result<Vec<Step>, TableError> {
    let mut plan = direct_map(set, memory, base, bits)?;
    let steps: Vec<Step> = std::iter::from_fn(|| plan.next()).collect();
    for step in &steps {
        execute(&mut set.pool, *step);
    }
    Ok(steps)
}

/// The span `[start, start + size)`.
fn span(start: u64, size: u64) -> Span {
    Span { start, size }
}

/// The layout of the ranges `(start, len, kind)` and the guard addresses
/// `guards`.
fn layout<'a>(ranges: &[(u64, u64, LayoutKind)], guards: &'a [u64]) -> Layout<'a> {
    let unused = LayoutRange {
        range: PhysRange::new(0, PAGE_SIZE).unwrap(),
        kind: LayoutKind::ReadWrite,
    };
    let mut all = [unused; MAX_LAYOUT_RANGES];
    for (slot, &(start, len, kind)) in all.iter_mut().zip(ranges) {
        let range = PhysRange::new(start, len).unwrap();
        *slot = LayoutRange { range, kind };
    }
    Layout {
        ranges: all,
        count: ranges.len(),
        guards,
    }
}

/// The bytes, blocks and pages that the stores of a plan map: a block
/// descriptor has bits 1 and 0 `0b01`, and a page descriptor `0b11` and the
/// access flag, which no table descriptor has.
fn counts(steps: &[Step]) -> (u64, u64, u64) {
    let (mut blocks, mut pages) = (0, 0);
    for step in steps {
        if let Step::Store(_, _, d) = *step {
            if d & 3 == 1 {
                blocks += 1;
            }
            if d & 3 == 3 && d & (1 << 10) != 0 {
                pages += 1;
            }
        }
    }
    (blocks * BLOCK_SIZE + pages * PAGE_SIZE, blocks, pages)
}
