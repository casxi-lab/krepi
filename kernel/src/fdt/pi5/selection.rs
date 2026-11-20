//! The selection of an available span of a Pi 5 boot memory, before the
//! page ownership table exists.
//!
//! Feature: krepi.platform.device-tree
//!
//! The search takes the RAM ranges in tree order and, in each, tries
//! candidates from the lowest aligned start: a candidate that touches an
//! exclusion is followed by one at the end of the furthest exclusion that
//! it touches, aligned up, since every start before that end touches that
//! exclusion too. A selected span describes memory and grants no ownership.

use super::super::span::touches;
use super::super::{Error, Pi5BootMemory, ReservedRegion, Span};

/// The least multiple of `alignment`, a power of two, that is at least
/// `address`, or `Overflow` when it leaves 64 bits.
fn align_up(address: u64, alignment: u64) -> Result<u64, Error> {
    match address.checked_add(alignment - 1) {
        Some(sum) => Ok(sum & !(alignment - 1)),
        None => Err(Error::Overflow),
    }
}

/// The end of the furthest of the image, the tree and the reserved regions
/// that `candidate` touches, or none when it touches none of them.
fn furthest_touched(
    image: Span,
    dtb: Span,
    regions: &[ReservedRegion],
    candidate: Span,
) -> Option<u64> {
    let mut touched = false;
    let mut end = 0;
    if touches(image, candidate) {
        end = image.start + image.size;
        touched = true;
    }
    if touches(dtb, candidate) && (!touched || dtb.start + dtb.size > end) {
        end = dtb.start + dtb.size;
        touched = true;
    }
    let mut index = 0;
    while index < regions.len() {
        let span = regions[index].span;
        if touches(span, candidate) && (!touched || span.start + span.size > end) {
            end = span.start + span.size;
            touched = true;
        }
        index += 1;
    }
    if touched { Some(end) } else { None }
}

/// The span of `size` bytes in one RAM range whose candidates start at
/// `start` and end at most at `bound`, trying at most `fuel` of them: a
/// candidate whose end leaves 64 bits or passes `bound` ends the search in
/// the range with none; one that touches no exclusion is the span.
fn search_range(
    memory: &Pi5BootMemory,
    size: u64,
    alignment: u64,
    bound: u64,
    start: u64,
    fuel: usize,
) -> Result<Option<Span>, Error> {
    let regions = memory.memory.reserved();
    let mut start = start;
    let mut tried = 0;
    while tried < fuel {
        let end = match start.checked_add(size) {
            Some(end) => end,
            None => return Ok(None),
        };
        if end > bound {
            return Ok(None);
        }
        let candidate = Span { start, size };
        match furthest_touched(memory.image, memory.dtb, regions, candidate) {
            Some(furthest) => start = align_up(furthest, alignment)?,
            None => return Ok(Some(candidate)),
        }
        tried += 1;
    }
    Err(Error::LimitExceeded)
}

/// The search through the RAM ranges in tree order: in each, the first
/// candidate is the greater of the start of the range and `minimum`,
/// aligned up, which fails with `Overflow`; the first range that has a span
/// gives it.
fn search_ranges(
    memory: &Pi5BootMemory,
    size: u64,
    alignment: u64,
    minimum: u64,
    limit: u64,
) -> Result<Option<Span>, Error> {
    let ranges = memory.memory.ram();
    let fuel = memory.memory.reserved().len() + 3;
    let mut index = 0;
    while index < ranges.len() {
        let range = ranges[index];
        let lowest = if range.start > minimum {
            range.start
        } else {
            minimum
        };
        let start = align_up(lowest, alignment)?;
        let range_end = range.start + range.size;
        let bound = if range_end < limit { range_end } else { limit };
        if let Some(span) = search_range(memory, size, alignment, bound, start, fuel)? {
            return Ok(Some(span));
        }
        index += 1;
    }
    Ok(None)
}

impl Pi5BootMemory {
    /// A span of `size` bytes aligned to `alignment`, within
    /// `[minimum, limit)` and inside one RAM range, that touches neither the
    /// image, nor the tree, nor any reserved region: the span with the
    /// lowest aligned start in the first RAM range, in tree order, that has
    /// one, and none when no range has one. A size of 0 or an empty bound,
    /// `EmptyRegion`; an alignment that is not a power of two,
    /// `BadAlignment`; then the search, whose alignments fail with
    /// `Overflow`.
    pub fn find_available(
        &self,
        size: u64,
        alignment: u64,
        minimum: u64,
        limit: u64,
    ) -> Result<Option<Span>, Error> {
        if size == 0 || minimum >= limit {
            return Err(Error::EmptyRegion);
        }
        if alignment == 0 || alignment & (alignment - 1) != 0 {
            return Err(Error::BadAlignment);
        }
        search_ranges(self, size, alignment, minimum, limit)
    }
}
