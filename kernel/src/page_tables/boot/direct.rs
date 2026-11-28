//! The kernel direct map: the checks of `direct_map` over the usable ranges
//! of the boot memory map and the steps of its plan.
//!
//! Feature: krepi.kernel.kernel-memory
//!
//! The usable ranges come from `MemoryPlan::available_ranges`, in address
//! order: the fdt module gives them through that iterator alone, so the
//! check of the ranges and the search of the plan each drive it in a loop
//! of their own. In a usable range, the leaf at a multiple of 2 MiB with at
//! least 2 MiB of the range left is a block, and every other leaf a page.

use super::super::encoding::block_descriptor;
use super::super::{
    BLOCK_SIZE, DirectMapPlan, Kind, PAGE_SIZE, Step, TableError, Tables, VA_LIMIT, descriptor,
};
use super::{Leaf, MapCheck, MapTurn, check_leaf};
use crate::fdt::{AvailableRanges, Span};

/// The leaf at `pa` of a usable range that ends at `end`.
fn leaf_at(pa: u64, end: u64) -> Leaf {
    if pa % BLOCK_SIZE == 0 && end - pa >= BLOCK_SIZE {
        Leaf {
            pa,
            desc: block_descriptor(pa),
            block: true,
        }
    } else {
        Leaf {
            pa,
            desc: descriptor(Kind::ReadWrite, pa),
            block: false,
        }
    }
}

/// The first leaf at or above `pa` of a usable range that ends at `end`, a
/// page when `pages`: after the blocks from `pa`, the pages at the end of
/// the range, if it has any.
fn range_leaf(pa: u64, end: u64, pages: bool) -> Option<Leaf> {
    let leaf = leaf_at(pa, end);
    if !leaf.block || !pages {
        return Some(leaf);
    }
    let tail = end & !(BLOCK_SIZE - 1);
    if tail < end {
        Some(leaf_at(tail, end))
    } else {
        None
    }
}

/// The checks of the leaves of the usable range `[start, end)` in address
/// order.
fn check_leaves<const N: usize>(
    set: &Tables<N, true>,
    check: &mut MapCheck,
    start: u64,
    end: u64,
    base: u64,
) -> Result<(), TableError> {
    let mut pa = start;
    while pa < end {
        let leaf = leaf_at(pa, end);
        check_leaf(set, base, check, pa, leaf.block, false)?;
        pa += if leaf.block { BLOCK_SIZE } else { PAGE_SIZE };
    }
    Ok(())
}

/// The checks of one usable range after the ranges before it: its ends off
/// a page, `Alignment`; its end above `2^39` or `2^bits`, `AddressWidth`;
/// then its leaves.
fn check_range<const N: usize>(
    set: &Tables<N, true>,
    check: &mut MapCheck,
    range: Span,
    base: u64,
    bits: u8,
) -> Result<(), TableError> {
    let end = range.start + range.size;
    if range.start % PAGE_SIZE != 0 || end % PAGE_SIZE != 0 {
        return Err(TableError::Alignment);
    }
    if end > VA_LIMIT || end > 1u64 << bits {
        return Err(TableError::AddressWidth);
    }
    check_leaves(set, check, range.start, end, base)?;
    check.passed(end);
    Ok(())
}

/// The checks of the usable ranges of `ranges` on the direct map's set at
/// `base` of physical width `bits`, after those of the pool.
pub(in crate::page_tables) fn check_usable<const N: usize>(
    set: &Tables<N, true>,
    ranges: AvailableRanges<'_>,
    base: u64,
    bits: u8,
) -> Result<MapCheck, TableError> {
    let mut ranges = ranges;
    let mut check = MapCheck::new();
    while let Some(range) = ranges.next() {
        check_range(set, &mut check, range, base, bits)?;
    }
    Ok(check)
}

/// The first leaf at or above `from` and below `limit`, a page when
/// `pages`, of the usable ranges from `range` on, which `ranges` follows;
/// with the range at which the search stopped and the ranges after it.
fn usable_leaf<'a>(
    ranges: AvailableRanges<'a>,
    range: Span,
    from: u64,
    limit: u64,
    pages: bool,
) -> (AvailableRanges<'a>, Span, Option<Leaf>) {
    let mut ranges = ranges;
    let mut range = range;
    let mut from = from;
    loop {
        let end = range.start + range.size;
        if from < end {
            let pa = if range.start > from {
                range.start
            } else {
                from
            };
            match range_leaf(pa, end, pages) {
                Some(leaf) => {
                    let found = if leaf.pa < limit { Some(leaf) } else { None };
                    return (ranges, range, found);
                }
                None => from = end,
            }
        } else {
            match ranges.next() {
                Some(next) => range = next,
                None => return (ranges, range, None),
            }
        }
    }
}

impl<const N: usize> DirectMapPlan<'_, N> {
    /// The next step of the plan, or none after its `Sync`. The entry that
    /// built the plan checked the usable ranges, so no step fails.
    // The iterator implements `next` alone: the provided methods of
    // `Iterator` would reach library functions without a model.
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Option<Step> {
        let (from, limit, pages) = self.cursor.search();
        let (ranges, range, found) = usable_leaf(self.ranges, self.range, from, limit, pages);
        let gib = self.cursor.gib;
        let turn = self.cursor.take(self.set, self.base, found);
        // In a new 1 GiB slot, the searches start from the range of its
        // first leaf.
        if self.cursor.gib != gib {
            self.ranges = ranges;
            self.range = range;
        }
        match turn {
            MapTurn::Give(step) => Some(step),
            MapTurn::End => None,
            MapTurn::Seek => {
                let (from, limit, pages) = self.cursor.search();
                let (_, _, found) = usable_leaf(self.ranges, self.range, from, limit, pages);
                Some(self.cursor.children(found))
            }
        }
    }
}

#[cfg(test)]
pub(in crate::page_tables) mod tests;
