//! Spans: the entries `Span::new`, `end` and `contains`, and the
//! comparisons of spans at their exact ends that the other entries use.
//!
//! Feature: krepi.platform.device-tree
//!
//! A span may end beyond 64 bits. The comparisons take its exact end,
//! `start + size`, which a 64-bit addition does not always hold, so each
//! compares through a checked addition and never wraps.

use super::{Error, Span};

impl Span {
    /// The span `[start, start + size)`, or `Overflow` when its end leaves
    /// 64 bits. An empty span is a span; the entries that refuse one say so.
    pub fn new(start: u64, size: u64) -> Result<Span, Error> {
        match start.checked_add(size) {
            Some(_) => Ok(Span { start, size }),
            None => Err(Error::Overflow),
        }
    }

    /// The end `start + size`, or `Overflow` when it leaves 64 bits.
    pub fn end(self) -> Result<u64, Error> {
        match self.start.checked_add(self.size) {
            Some(end) => Ok(end),
            None => Err(Error::Overflow),
        }
    }

    /// Whether `other` lies inside the span; `Overflow` when `other`, and
    /// then the span itself, ends beyond 64 bits.
    pub fn contains(self, other: Span) -> Result<bool, Error> {
        let other_end = other.end()?;
        let end = self.end()?;
        Ok(self.start <= other.start && other_end <= end)
    }
}

/// Whether `address` lies below the exact end of `span`.
fn below_end(address: u64, span: Span) -> bool {
    match span.start.checked_add(span.size) {
        Some(end) => address < end,
        None => true,
    }
}

/// Whether each of two spans starts before the other ends, at their exact
/// ends: for two nonempty spans, whether they share an address.
pub(super) fn overlaps(a: Span, b: Span) -> bool {
    below_end(a.start, b) && below_end(b.start, a)
}

/// Whether the exact end of `inner` is at most that of `outer`. Two ends
/// beyond 64 bits are compared by what they exceed `2^64 - 1` by: for a
/// span whose end leaves 64 bits, `start - (u64::MAX - size)`, which is at
/// least 1.
fn ends_within(inner: Span, outer: Span) -> bool {
    match inner.start.checked_add(inner.size) {
        Some(inner_end) => match outer.start.checked_add(outer.size) {
            Some(outer_end) => inner_end <= outer_end,
            None => true,
        },
        None => match outer.start.checked_add(outer.size) {
            Some(_) => false,
            None => inner.start - (u64::MAX - inner.size) <= outer.start - (u64::MAX - outer.size),
        },
    }
}

/// Whether `inner` lies inside `outer`, as sets of addresses up to their
/// exact ends.
pub(super) fn holds(outer: Span, inner: Span) -> bool {
    outer.start <= inner.start && ends_within(inner, outer)
}
