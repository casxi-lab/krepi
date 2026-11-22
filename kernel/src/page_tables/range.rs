//! Physical ranges: the checked constructor and the comparisons.
//!
//! Feature: krepi.kernel.kernel-memory

use super::{OwnershipError, PhysRange};

impl PhysRange {
    /// The range `[start, start + len)`: a length of 0 is `InvalidRange`,
    /// and an end beyond `2^64 - 1` is `AddressOverflow`.
    pub fn new(start: u64, len: u64) -> Result<PhysRange, OwnershipError> {
        if len == 0 {
            return Err(OwnershipError::InvalidRange);
        }
        match start.checked_add(len) {
            Some(_) => Ok(PhysRange { start, len }),
            None => Err(OwnershipError::AddressOverflow),
        }
    }

    /// The exclusive end `start + len`, which fits in 64 bits.
    pub(crate) fn end(self) -> u64 {
        self.start + self.len
    }

    /// Whether every address of `other` lies in the range.
    // Called by the page ownership table, and by the modules of the core
    // that take pages, which are planned.
    pub(crate) fn contains(self, other: PhysRange) -> bool {
        self.start <= other.start && other.end() <= self.end()
    }

    /// Whether the two ranges share an address.
    // Called by the page ownership table, and by the modules of the core
    // that take pages, which are planned.
    pub(crate) fn overlaps(self, other: PhysRange) -> bool {
        self.start < other.end() && other.start < self.end()
    }
}
