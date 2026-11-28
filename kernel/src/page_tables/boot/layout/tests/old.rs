//! The checks of `kernel_map` before the count of the new tables started
//! from 0: the code of krepi commit d6d66bd at the lines below, copied
//! verbatim with the suffix `_old` added to each name and to each call of a
//! copied item, for the differential tests. `check_pages` and `check_range`
//! did not change and lead to the copy of `check_leaf`.
//!
//! - `kernel/src/page_tables/boot/layout.rs:66-81`: `check_pages`;
//! - `kernel/src/page_tables/boot/layout.rs:83-104`: `check_range`;
//! - `kernel/src/page_tables/boot/layout.rs:106-124`: `check_layout`.
//!
//! Feature: krepi.kernel.kernel-memory

use super::super::*;
use crate::page_tables::boot::tests::old::{MapCheck_old, check_leaf_old};

/// The checks of the pages of `range` in address order.
fn check_pages_old<const N: usize>(
    set: &Tables<N, false>,
    check: &mut MapCheck_old,
    range: LayoutRange,
    guards: &[u64],
    base: u64,
) -> Result<(), TableError> {
    let end = range.range.end();
    let mut pa = range.range.start;
    while pa < end {
        check_leaf_old(set, base, check, pa, false, holds_guard(guards, pa))?;
        pa += PAGE_SIZE;
    }
    Ok(())
}

/// The checks of one range after the ranges before it: its ends off a page,
/// `Alignment`; its end above `2^39` or `2^bits`, `AddressWidth`; then its
/// pages.
fn check_range_old<const N: usize>(
    set: &Tables<N, false>,
    check: &mut MapCheck_old,
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
    check_pages_old(set, check, range, guards, base)?;
    check.passed_old(end);
    Ok(())
}

/// The checks of the first `count` of the sorted `ranges` of a layout with
/// the guard addresses `guards`, on the lower kernel set at `base` of
/// physical width `bits`, after those of the pool.
pub(in crate::page_tables) fn check_layout_old<const N: usize>(
    set: &Tables<N, false>,
    ranges: &[LayoutRange; MAX_LAYOUT_RANGES],
    count: usize,
    guards: &[u64],
    base: u64,
    bits: u8,
) -> Result<MapCheck_old, TableError> {
    let mut check = MapCheck_old::new_old(set.used);
    let mut index = 0;
    while index < count {
        check_range_old(set, &mut check, ranges[index], guards, base, bits)?;
        index += 1;
    }
    Ok(check)
}
