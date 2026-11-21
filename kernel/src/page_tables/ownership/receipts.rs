//! Receipts: the checks of a value that names held pages, the validation of
//! such a value and the release of a receipt.
//!
//! Feature: krepi.kernel.kernel-memory
//!
//! A value names its pages by its arena, its owner identity, its generation
//! and its range, and the table accepts it only for the extent that is
//! exactly its range, held by its owner identity with its generation in the
//! state that the value names. Freed pages merge with the free extents next
//! to them in the same bank, so a release never needs an extent.

use super::super::{Allocation, Extent, HoldState, Holding, Ownership, OwnershipError};
use super::is_free;

impl<const E: usize, const X: usize> Ownership<E, X> {
    /// The extent of the pages that `allocation` names, held by `owner` in
    /// the state `state`. It checks, in this order: another arena,
    /// `WrongArena`; another owner identity, `WrongOwner`; no extent that is
    /// exactly its range, held by `owner` with its generation in `state`,
    /// `InvalidAllocation`.
    fn find_held(
        &self,
        owner: u64,
        allocation: Allocation,
        state: HoldState,
    ) -> Result<usize, OwnershipError> {
        if allocation.arena != self.arena {
            return Err(OwnershipError::WrongArena);
        }
        if allocation.owner != owner {
            return Err(OwnershipError::WrongOwner);
        }
        match held_extent(&self.extents, self.extent_count, allocation, state) {
            Some(index) => Ok(index),
            None => Err(OwnershipError::InvalidAllocation),
        }
    }

    /// The checks of `release` without a write, for a value of the owner
    /// identity `owner` whose pages are in the state `state`: published for a
    /// receipt.
    // Called by the modules of the core that take pages, which are planned.
    #[allow(dead_code)]
    pub(crate) fn validate(
        &self,
        owner: u64,
        allocation: Allocation,
        state: HoldState,
    ) -> Result<(), OwnershipError> {
        self.find_held(owner, allocation, state)?;
        Ok(())
    }

    /// Frees the pages of `receipt`, of the owner identity `owner`, after
    /// the checks of a value whose pages are published; the counter does not
    /// change.
    // Called by the modules of the core that return pages, which are
    // planned.
    #[allow(dead_code)]
    pub(crate) fn release(
        &mut self,
        owner: u64,
        receipt: Allocation,
    ) -> Result<(), OwnershipError> {
        let index = self.find_held(owner, receipt, HoldState::Published)?;
        self.extent_count = merge_freed(&mut self.extents, self.extent_count, index);
        Ok(())
    }
}

/// Whether two states of a holder are the same.
fn same_state(a: HoldState, b: HoldState) -> bool {
    match (a, b) {
        (HoldState::Published, HoldState::Published) => true,
    }
}

/// Whether `holding` is the holder that `allocation` names, in the state
/// `state`.
fn holds_as(holding: Holding, allocation: Allocation, state: HoldState) -> bool {
    match holding {
        Holding::Held(owner, generation, held) => {
            owner == allocation.owner
                && generation == allocation.generation
                && same_state(held, state)
        }
        Holding::Free => false,
    }
}

/// The first of the first `count` extents that is exactly the range of
/// `allocation`, held as it names in the state `state`.
fn held_extent<const E: usize>(
    extents: &[Extent; E],
    count: usize,
    allocation: Allocation,
    state: HoldState,
) -> Option<usize> {
    let mut index = 0;
    while index < count && index < E {
        let extent = extents[index];
        if extent.range.start == allocation.range.start
            && extent.range.len == allocation.range.len
            && holds_as(extent.holding, allocation, state)
        {
            return Some(index);
        }
        index += 1;
    }
    None
}

/// Whether `a` and `b`, in address order, are free extents of one bank and
/// `a` ends where `b` starts.
fn joins(a: Extent, b: Extent) -> bool {
    is_free(a.holding) && is_free(b.holding) && a.bank == b.bank && a.range.end() == b.range.start
}

/// Removes the `by` extents from `index` of the first `count`: those after
/// them move down by `by` places.
fn close_gap<const E: usize>(extents: &mut [Extent; E], count: usize, index: usize, by: usize) {
    let mut at = index;
    while at + by < count {
        extents[at] = extents[at + by];
        at += 1;
    }
}

/// Frees the extent at `index` of the first `count`, merges it with the
/// free extent next to it on each side in the same bank, and gives the
/// extents in use after it. The extents after the merged ones move once.
fn merge_freed<const E: usize>(extents: &mut [Extent; E], count: usize, index: usize) -> usize {
    extents[index].holding = Holding::Free;
    let mut first = index;
    if index > 0 && joins(extents[index - 1], extents[index]) {
        first = index - 1;
    }
    let mut last = index;
    if index + 1 < count && joins(extents[index], extents[index + 1]) {
        last = index + 1;
    }
    extents[first].range.len = extents[last].range.end() - extents[first].range.start;
    close_gap(extents, count, first + 1, last - first);
    count - (last - first)
}
