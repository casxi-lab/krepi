//! The kernel's mappings of its image and its devices: the checks of
//! `kernel_map` over a layout and the steps of its plan.
//!
//! Feature: krepi.kernel.kernel-memory
//!
//! The ranges of a layout are sorted by their start, by insertion, the
//! ranges of one start in the order in which the board gives them. Once
//! every range has passed its checks, no two share a page, so the pages of
//! the sorted ranges are the leaves of the map in address order.

use super::super::{
    KernelMapPlan, Kind, LayoutKind, LayoutRange, MAX_LAYOUT_RANGES, PAGE_SIZE, Step, TableError,
    Tables, VA_LIMIT, descriptor,
};
use super::{Leaf, MapCheck, MapTurn, check_leaf};

impl LayoutKind {
    /// The kind of the leaves of a range of the layout kind.
    fn kind(self) -> Kind {
        match self {
            LayoutKind::ReadExecute => Kind::ReadExecute,
            LayoutKind::ReadOnly => Kind::ReadOnly,
            LayoutKind::ReadWrite => Kind::ReadWrite,
            LayoutKind::Device => Kind::Device,
        }
    }
}

/// The range at `index` moved down among the ranges before it, which are
/// sorted by their start, to its place after those of its start.
fn insert_range(ranges: &mut [LayoutRange; MAX_LAYOUT_RANGES], index: usize) {
    let mut at = index;
    while at > 0 && ranges[at - 1].range.start > ranges[at].range.start {
        let moved = ranges[at];
        ranges[at] = ranges[at - 1];
        ranges[at - 1] = moved;
        at -= 1;
    }
}

/// The first `count` ranges sorted by their start, by insertion; ranges of
/// one start keep their order.
pub(in crate::page_tables) fn sort_ranges(
    ranges: &mut [LayoutRange; MAX_LAYOUT_RANGES],
    count: usize,
) {
    let mut index = 1;
    while index < count {
        insert_range(ranges, index);
        index += 1;
    }
}

/// Whether one of the guard addresses lies in the page at `pa`.
fn holds_guard(guards: &[u64], pa: u64) -> bool {
    let mut index = 0;
    while index < guards.len() {
        if pa <= guards[index] && guards[index] < pa + PAGE_SIZE {
            return true;
        }
        index += 1;
    }
    false
}

/// The checks of the pages of `range` in address order.
fn check_pages<const N: usize>(
    set: &Tables<N, false>,
    check: &mut MapCheck,
    range: LayoutRange,
    guards: &[u64],
    base: u64,
) -> Result<(), TableError> {
    let end = range.range.end();
    let mut pa = range.range.start;
    while pa < end {
        check_leaf(set, base, check, pa, false, holds_guard(guards, pa))?;
        pa += PAGE_SIZE;
    }
    Ok(())
}

/// The checks of one range after the ranges before it: its ends off a page,
/// `Alignment`; its end above `2^39` or `2^bits`, `AddressWidth`; then its
/// pages.
fn check_range<const N: usize>(
    set: &Tables<N, false>,
    check: &mut MapCheck,
    range: LayoutRange,
    guards: &[u64],
    base: u64,
    bits: u8,
) -> Result<(), TableError> {
    let end = range.range.end();
    if range.range.start % PAGE_SIZE != 0 || end % PAGE_SIZE != 0 {
        return Err(TableError::Alignment);
    }
    if end > VA_LIMIT || end > 1u64 << bits {
        return Err(TableError::AddressWidth);
    }
    check_pages(set, check, range, guards, base)?;
    check.passed(end);
    Ok(())
}

/// The checks of the first `count` of the sorted `ranges` of a layout with
/// the guard addresses `guards`, on the lower kernel set at `base` of
/// physical width `bits`, after those of the pool.
pub(in crate::page_tables) fn check_layout<const N: usize>(
    set: &Tables<N, false>,
    ranges: &[LayoutRange; MAX_LAYOUT_RANGES],
    count: usize,
    guards: &[u64],
    base: u64,
    bits: u8,
) -> Result<MapCheck, TableError> {
    let mut check = MapCheck::new();
    let mut index = 0;
    while index < count {
        check_range(set, &mut check, ranges[index], guards, base, bits)?;
        index += 1;
    }
    Ok(check)
}

/// The first page at or above `from` and below `limit` of the first `count`
/// of the sorted ranges, which passed their checks, with the descriptor of
/// the kind of its range.
fn layout_leaf(
    ranges: &[LayoutRange; MAX_LAYOUT_RANGES],
    count: usize,
    from: u64,
    limit: u64,
) -> Option<Leaf> {
    let mut index = 0;
    while index < count {
        let range = ranges[index];
        if from < range.range.end() {
            let pa = if range.range.start > from {
                range.range.start
            } else {
                from
            };
            if pa < limit {
                let desc = descriptor(range.kind.kind(), pa);
                return Some(Leaf {
                    pa,
                    desc,
                    block: false,
                });
            }
            return None;
        }
        index += 1;
    }
    None
}

impl<const N: usize> KernelMapPlan<'_, N> {
    /// The next step of the plan, or none after its `Sync`. The entry that
    /// built the plan checked the layout, so no step fails.
    // The iterator implements `next` alone: the provided methods of
    // `Iterator` would reach library functions without a model.
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Option<Step> {
        let (from, limit, _) = self.cursor.search();
        let found = layout_leaf(&self.ranges, self.count, from, limit);
        match self.cursor.take(self.set, self.base, found) {
            MapTurn::Give(step) => Some(step),
            MapTurn::End => None,
            MapTurn::Seek => {
                let (from, limit, _) = self.cursor.search();
                let found = layout_leaf(&self.ranges, self.count, from, limit);
                Some(self.cursor.children(found))
            }
        }
    }
}
