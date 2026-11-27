//! The checks of `direct_map` before the count of the new tables started
//! from 0: the code of krepi commit d6d66bd at the lines below, copied
//! verbatim with the suffix `_old` added to each name and to each call of a
//! copied item, for the differential tests. `check_leaves` and `check_range`
//! did not change and lead to the copy of `check_leaf`.
//!
//! - `kernel/src/page_tables/boot/direct.rs:52-68`: `check_leaves`;
//! - `kernel/src/page_tables/boot/direct.rs:70-90`: `check_range`;
//! - `kernel/src/page_tables/boot/direct.rs:92-106`: `check_usable`.
//!
//! Feature: krepi.kernel.kernel-memory

use super::super::*;
use crate::page_tables::boot::tests::old::{MapCheck_old, check_leaf_old};

/// The checks of the leaves of the usable range `[start, end)` in address
/// order.
fn check_leaves_old<const N: usize>(
    set: &Tables<N, true>,
    check: &mut MapCheck_old,
    start: u64,
    end: u64,
    base: u64,
) -> Result<(), TableError> {
    let mut pa = start;
    while pa < end {
        let leaf = leaf_at(pa, end);
        check_leaf_old(set, base, check, pa, leaf.block, false)?;
        pa += if leaf.block { BLOCK_SIZE } else { PAGE_SIZE };
    }
    Ok(())
}

/// The checks of one usable range after the ranges before it: its ends off
/// a page, `Alignment`; its end above `2^39` or `2^bits`, `AddressWidth`;
/// then its leaves.
fn check_range_old<const N: usize>(
    set: &Tables<N, true>,
    check: &mut MapCheck_old,
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
    check_leaves_old(set, check, range.start, end, base)?;
    check.passed_old(end);
    Ok(())
}

/// The checks of the usable ranges of `ranges` on the direct map's set at
/// `base` of physical width `bits`, after those of the pool.
pub(in crate::page_tables) fn check_usable_old<const N: usize>(
    set: &Tables<N, true>,
    ranges: AvailableRanges<'_>,
    base: u64,
    bits: u8,
) -> Result<MapCheck_old, TableError> {
    let mut ranges = ranges;
    let mut check = MapCheck_old::new_old(set.used);
    while let Some(range) = ranges.next() {
        check_range_old(set, &mut check, range, base, bits)?;
    }
    Ok(check)
}
