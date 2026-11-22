//! Placement: the choice of the pages of a request, and the write that
//! takes them for a holder.
//!
//! Feature: krepi.kernel.kernel-memory
//!
//! The scan passes over the extents in address order, from the lowest for a
//! low placement and from the highest for a high one, and takes the first
//! free extent whose part inside the window holds an aligned range of the
//! request, unless taking the range would need more extents than the
//! capacity has free. Taking a range splits its free extent into the parts
//! before and after it, which stay free, and the range, held.

use super::super::{
    Allocation, Choice, Counter, Direction, Extent, HoldState, Holding, Ownership, OwnershipError,
    PAGE_SIZE, PhysRange, Placement, Reservation,
};
use super::is_free;

/// The pages of `2^64` bytes: a request or an alignment of as many pages or
/// more does not fit in 64 bits.
const PAGE_LIMIT: u64 = 1 << 52;

impl<const E: usize, const X: usize> Ownership<E, X> {
    /// The pages that an allocation of `pages` pages, aligned to `alignment`
    /// pages, would take for the owner identity `owner` with `placement`. It
    /// writes nothing. It checks, in this order: the request or its alignment
    /// of `2^64` bytes or more, `AddressOverflow`; 0 pages, `InvalidSize`; an
    /// alignment that is not a power of two, `InvalidAlignment`; the
    /// generation counter exhausted, `GenerationExhausted`; then the scan,
    /// which gives its first fit, `AddressOverflow` at a free extent whose
    /// rounded start or the end of whose range passes 64 bits, and at its end
    /// `MetadataExhausted` when it passed over a fit for capacity and
    /// `OutOfMemory` otherwise.
    pub fn choose(
        &self,
        owner: u64,
        pages: u64,
        alignment: u64,
        placement: Placement,
    ) -> Result<Choice, OwnershipError> {
        if pages >= PAGE_LIMIT || alignment >= PAGE_LIMIT {
            return Err(OwnershipError::AddressOverflow);
        }
        if pages == 0 {
            return Err(OwnershipError::InvalidSize);
        }
        if alignment == 0 || (alignment & (alignment - 1)) != 0 {
            return Err(OwnershipError::InvalidAlignment);
        }
        if let Counter::Exhausted = self.counter {
            return Err(OwnershipError::GenerationExhausted);
        }
        let range = scan(
            &self.extents,
            self.extent_count,
            self.room(),
            pages * PAGE_SIZE,
            alignment * PAGE_SIZE,
            placement,
        )?;
        Ok(Choice { owner, range })
    }

    /// Takes the pages of `choice` for its owner identity, published, with
    /// the generation of the counter, and gives the receipt, once the caller
    /// has zeroed them through the direct map; `zeroed` tells whether the
    /// zeroing completed. It checks, in this order: a failed zeroing,
    /// `ZeroFailed`, which leaves the pages free and consumes no generation;
    /// then that the choice still fits the table, as one of `choose` under the
    /// same token does: the counter exhausted, `GenerationExhausted`; the
    /// pages not inside one free extent, `OutOfMemory`; more extents than the
    /// capacity has free, `MetadataExhausted`.
    pub fn assign(&mut self, choice: Choice, zeroed: bool) -> Result<Allocation, OwnershipError> {
        if !zeroed {
            return Err(OwnershipError::ZeroFailed);
        }
        self.take(choice, HoldState::Published)
    }

    /// Holds the pages that `choose` gives at once, reserved, without zeroing
    /// them, for the owner identity `owner` with the generation of the
    /// counter, and gives the reservation, not attempted and with no failure.
    /// It makes the checks of `choose`.
    // Called by the modules of the core that take pages, which are planned.
    #[allow(dead_code)]
    pub(crate) fn reserve(
        &mut self,
        owner: u64,
        pages: u64,
        alignment: u64,
        placement: Placement,
    ) -> Result<Reservation, OwnershipError> {
        let choice = self.choose(owner, pages, alignment, placement)?;
        let allocation = self.take(choice, HoldState::Reserved)?;
        Ok(Reservation {
            allocation,
            attempted: false,
            failures: 0,
        })
    }

    /// Takes the pages of `choice` for its owner identity in the state
    /// `state`, with the checks of `assign` after the zeroing, and advances
    /// the counter, to exhausted after `2^64 - 1`.
    fn take(&mut self, choice: Choice, state: HoldState) -> Result<Allocation, OwnershipError> {
        let generation = match self.counter {
            Counter::Next(generation) => generation,
            Counter::Exhausted => return Err(OwnershipError::GenerationExhausted),
        };
        let index = match free_containing(&self.extents, self.extent_count, choice.range) {
            Some(index) => index,
            None => return Err(OwnershipError::OutOfMemory),
        };
        let extent = self.extents[index];
        let extra = extra_extents(extent.range, choice.range);
        if extra > self.room() {
            return Err(OwnershipError::MetadataExhausted);
        }
        open_gap(&mut self.extents, self.extent_count, index, extra);
        let holding = Holding::Held(choice.owner, generation, state);
        split(&mut self.extents, index, extent, choice.range, holding);
        self.extent_count += extra;
        self.counter = match generation.checked_add(1) {
            Some(next) => Counter::Next(next),
            None => Counter::Exhausted,
        };
        Ok(Allocation {
            arena: self.arena,
            owner: choice.owner,
            generation,
            range: choice.range,
        })
    }
}

/// The pages of a request of `bytes` at the lowest multiple of `align` from
/// `low` in `[low, high)`; `AddressOverflow` when that start or the end of
/// the range passes 64 bits.
fn low_fit(
    low: u64,
    high: u64,
    bytes: u64,
    align: u64,
) -> Result<Option<PhysRange>, OwnershipError> {
    let start = match low.checked_add(align - 1) {
        Some(up) => up & !(align - 1),
        None => return Err(OwnershipError::AddressOverflow),
    };
    match start.checked_add(bytes) {
        Some(end) => {
            if end <= high {
                Ok(Some(PhysRange { start, len: bytes }))
            } else {
                Ok(None)
            }
        }
        None => Err(OwnershipError::AddressOverflow),
    }
}

/// The pages of a request of `bytes` at the highest multiple of `align`
/// whose range ends in `[low, high)`.
fn high_fit(low: u64, high: u64, bytes: u64, align: u64) -> Option<PhysRange> {
    if high < bytes {
        return None;
    }
    let start = (high - bytes) & !(align - 1);
    if start >= low {
        Some(PhysRange { start, len: bytes })
    } else {
        None
    }
}

/// The pages of a request of `bytes`, aligned to `align` bytes, in the part
/// of the free extent `extent` inside the window of `placement`, or none
/// when the part holds none.
fn fit(
    placement: Placement,
    extent: PhysRange,
    bytes: u64,
    align: u64,
) -> Result<Option<PhysRange>, OwnershipError> {
    let mut low = extent.start;
    let mut high = extent.end();
    if let Some(window) = placement.window {
        if window.start > low {
            low = window.start;
        }
        if window.end() < high {
            high = window.end();
        }
    }
    if high <= low {
        return Ok(None);
    }
    match placement.direction {
        Direction::Low => low_fit(low, high, bytes, align),
        Direction::High => Ok(high_fit(low, high, bytes, align)),
    }
}

/// The extents that taking `range` from the free extent `extent` adds: one
/// for a part before it and one for a part after it.
fn extra_extents(extent: PhysRange, range: PhysRange) -> usize {
    let mut extra = 0;
    if extent.start < range.start {
        extra += 1;
    }
    if range.end() < extent.end() {
        extra += 1;
    }
    extra
}

/// The first fit of a request of `bytes`, aligned to `align` bytes, with
/// `placement` in the first `count` extents, when `room` extents are free in
/// the capacity.
fn scan<const E: usize>(
    extents: &[Extent; E],
    count: usize,
    room: usize,
    bytes: u64,
    align: u64,
    placement: Placement,
) -> Result<PhysRange, OwnershipError> {
    let mut limited = false;
    let mut step = 0;
    while step < count && step < E {
        let extent = match placement.direction {
            Direction::Low => extents[step],
            Direction::High => extents[count - 1 - step],
        };
        if is_free(extent.holding) {
            if let Some(range) = fit(placement, extent.range, bytes, align)? {
                if extra_extents(extent.range, range) > room {
                    limited = true;
                } else {
                    return Ok(range);
                }
            }
        }
        step += 1;
    }
    if limited {
        Err(OwnershipError::MetadataExhausted)
    } else {
        Err(OwnershipError::OutOfMemory)
    }
}

/// The first of the first `count` extents that is free and contains
/// `range`.
fn free_containing<const E: usize>(
    extents: &[Extent; E],
    count: usize,
    range: PhysRange,
) -> Option<usize> {
    let mut index = 0;
    while index < count && index < E {
        if is_free(extents[index].holding) && extents[index].range.contains(range) {
            return Some(index);
        }
        index += 1;
    }
    None
}

/// Moves the extents after `index`, of the first `count`, up by `by` places.
fn open_gap<const E: usize>(extents: &mut [Extent; E], count: usize, index: usize, by: usize) {
    let mut at = count;
    while at > index + 1 {
        at -= 1;
        extents[at + by] = extents[at];
    }
}

/// Writes, from `index`, what taking `range` with `holding` makes of the
/// free extent `extent`: the part before `range`, free, if any; `range`,
/// held; the part after it, free, if any.
fn split<const E: usize>(
    extents: &mut [Extent; E],
    index: usize,
    extent: Extent,
    range: PhysRange,
    holding: Holding,
) {
    let mut at = index;
    if extent.range.start < range.start {
        extents[at] = Extent {
            range: PhysRange {
                start: extent.range.start,
                len: range.start - extent.range.start,
            },
            bank: extent.bank,
            holding: Holding::Free,
        };
        at += 1;
    }
    extents[at] = Extent {
        range,
        bank: extent.bank,
        holding,
    };
    if range.end() < extent.range.end() {
        extents[at + 1] = Extent {
            range: PhysRange {
                start: range.end(),
                len: extent.range.end() - range.end(),
            },
            bank: extent.bank,
            holding: Holding::Free,
        };
    }
}
