//! The checks of a map and its write phase before the count of the new
//! tables started from 0: the code of krepi commit d6d66bd at the lines
//! below, copied verbatim with the suffix `_old` added to each name and to
//! each call of a copied item, for the differential tests. As the copy lies
//! two modules down, each visibility names the scope of the original:
//! `pub(in crate::page_tables::boot)` for a private item of `boot`, and
//! `pub(in crate::page_tables)` for one `pub(super)`.
//!
//! - `kernel/src/page_tables/boot.rs:90-118`: `MapCheck`, `new`, `passed`;
//! - `kernel/src/page_tables/boot.rs:120-159`: `check_leaf`;
//! - `kernel/src/page_tables/boot.rs:161-184`: `write_phase`.
//!
//! Feature: krepi.kernel.kernel-memory

#![allow(non_camel_case_types)]

use super::super::*;

/// The checks of a map so far: the end of the ranges before the current
/// one, and the new tables of the leaves checked, as the next free index
/// with the 1 GiB slot of the latest new level 2 table and the 2 MiB slot of
/// the latest new level 3 table.
pub(in crate::page_tables) struct MapCheck_old {
    reach: u64,
    next: usize,
    gib: u64,
    slot: u64,
}

impl MapCheck_old {
    /// The checks before the first range, on a set of `used` tables in use.
    pub(in crate::page_tables::boot) fn new_old(used: usize) -> MapCheck_old {
        MapCheck_old {
            reach: 0,
            next: used,
            gib: NO_SLOT,
            slot: NO_SLOT,
        }
    }

    /// Records a range that passed its checks and ends at `end`.
    pub(in crate::page_tables::boot) fn passed_old(&mut self, end: u64) {
        if end > self.reach {
            self.reach = end;
        }
    }
}

/// The checks of the leaf at `pa`, a block when `block`, after the leaves
/// before it: its walk (`TableBacking`, `AlreadyMapped`), then
/// `AlreadyMapped` when an earlier range holds it or `guard` says that it
/// holds a guard address; then the count of the new tables that it needs.
pub(in crate::page_tables::boot) fn check_leaf_old<const N: usize, const UPPER: bool>(
    set: &Tables<N, UPPER>,
    base: u64,
    check: &mut MapCheck_old,
    pa: u64,
    block: bool,
    guard: bool,
) -> Result<(), TableError> {
    let place = set.place(base, pa, block)?;
    // The ranges come in the order of their starts, so an earlier range
    // shares an address with the leaf exactly when it ends above it.
    if pa < check.reach || guard {
        return Err(TableError::AlreadyMapped);
    }
    match place {
        LeafPlace::Root => {
            let gib = pa & !(GIB_SIZE - 1);
            if gib != check.gib {
                check.gib = gib;
                check.next += 1;
            }
        }
        LeafPlace::Level2(_) => {}
        LeafPlace::Level3(_, _) => return Ok(()),
    }
    // The negation is the condition itself: a flag from a `match` whose arms
    // give a negation and a literal does not type-check in Lean.
    if !block {
        let slot = pa & !(BLOCK_SIZE - 1);
        if slot != check.slot {
            check.slot = slot;
            check.next += 1;
        }
    }
    Ok(())
}

/// The write phase of a map whose leaves passed their checks:
/// `OutOfTables` when the pool has fewer free tables than the new tables of
/// the whole plan; otherwise the set records them, and the cursor of the
/// plan starts before the first leaf, with the new tables from the old
/// record on.
pub(in crate::page_tables) fn write_phase_old<const N: usize, const UPPER: bool>(
    set: &mut Tables<N, UPPER>,
    check: MapCheck_old,
) -> Result<MapCursor, TableError> {
    if set.free_tables() < check.next - set.used {
        return Err(TableError::OutOfTables);
    }
    let next = set.used;
    set.used = check.next;
    Ok(MapCursor {
        phase: MapPhase::Leaf,
        from: 0,
        next,
        gib: NO_SLOT,
        slot: NO_SLOT,
        t2: 0,
        t3: 0,
    })
}
