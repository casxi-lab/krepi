//! `kernel_map` and `direct_map`, which did not change, as the code of krepi
//! commit d6d66bd at the lines below, copied verbatim with the suffix `_old`
//! added to each name and to each call of a copied item, so that the
//! differential tests run the copies of the checks from the entries on. The
//! paths `layout`, `direct` and `boot` of the calls name the modules of the
//! copies here.
//!
//! - `kernel/src/page_tables.rs:572-605`: `kernel_map`;
//! - `kernel/src/page_tables.rs:607-633`: `direct_map`.
//!
//! Feature: krepi.kernel.kernel-memory

use super::super::*;
use crate::page_tables::boot::direct::tests::old as direct;
use crate::page_tables::boot::tests::old as boot;

/// The functions that the copy of `kernel_map` calls by the path `layout`.
mod layout {
    pub(super) use crate::page_tables::boot::layout::sort_ranges;
    pub(super) use crate::page_tables::boot::layout::tests::old::check_layout_old;
}

/// Maps every page of every range of `layout` into the lower kernel set
/// `set`, whose pool is at `base`, at its physical address with the kind of
/// its range, and writes no entry of a guard page. It checks, in this order:
/// the pool; the ranges in the order of their starts, those of one start in
/// the order given, each with its ends off a page (`Alignment`), its end
/// above `2^39` or `2^bits` (`AddressWidth`) and its pages in address order,
/// first the walk (`TableBacking`, `AlreadyMapped`) and then a page that an
/// earlier range or a guard holds (`AlreadyMapped`); and last the tables of
/// the whole plan (`OutOfTables`). The boot wiring calls it once, before the
/// MMU is on.
pub fn kernel_map_old<'a, const N: usize>(
    set: &'a mut Tables<N, false>,
    layout: Layout<'a>,
    base: u64,
    bits: u8,
) -> Result<KernelMapPlan<'a, N>, TableError> {
    check_pool(N, base, bits)?;
    let count = if layout.count < MAX_LAYOUT_RANGES {
        layout.count
    } else {
        MAX_LAYOUT_RANGES
    };
    let mut ranges = layout.ranges;
    layout::sort_ranges(&mut ranges, count);
    let check = layout::check_layout_old(set, &ranges, count, layout.guards, base, bits)?;
    let cursor = boot::write_phase_old(set, check)?;
    Ok(KernelMapPlan {
        set,
        base,
        cursor,
        ranges,
        count,
    })
}

/// Maps every page of every usable range of the boot memory map `memory`
/// into the direct map's set `set`, whose pool is at `base`, at
/// `DIRECT_BASE | pa` as `ReadWrite`: a block at each multiple of 2 MiB with
/// at least 2 MiB of its range left, and a page elsewhere. It checks, in
/// this order: the pool; the usable ranges in address order, each with its
/// ends off a page (`Alignment`), its end above `2^39` or `2^bits`
/// (`AddressWidth`) and its leaves in address order, first the walk
/// (`TableBacking`, `AlreadyMapped`) and then a leaf that an earlier range
/// holds (`AlreadyMapped`); and last the tables of the whole plan
/// (`OutOfTables`). The boot wiring calls it once, before the MMU is on.
pub fn direct_map_old<'a, const N: usize>(
    set: &'a mut Tables<N, true>,
    memory: &'a MemoryPlan,
    base: u64,
    bits: u8,
) -> Result<DirectMapPlan<'a, N>, TableError> {
    check_pool(N, base, bits)?;
    let check = direct::check_usable_old(set, memory.available_ranges(), base, bits)?;
    let cursor = boot::write_phase_old(set, check)?;
    Ok(DirectMapPlan {
        set,
        base,
        cursor,
        ranges: memory.available_ranges(),
        range: Span { start: 0, size: 0 },
    })
}
