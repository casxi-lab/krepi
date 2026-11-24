//! The boot memory of a hand-over tree: its memory discovery, checked
//! against the hand-over profile of its board and the spans that the board
//! gives for the tree and for the image, and the availability of a span in
//! it.
//!
//! Feature: krepi.platform.device-tree
//!
//! The result describes memory and grants no ownership: the page ownership
//! table of the page-tables component hands out pages. Its queries know only
//! the image and the tree as the board gives them; further boot storage,
//! such as the boot bundle when the board gives it as a span of its own, is
//! excluded only by the boot memory map.

mod selection;

use super::format::{find_nul, is_utf8, same_bytes};
use super::nodes::{address_cells_at, first_node, size_cells_at, value_at};
use super::span::{in_one_range, touches, valid};
use super::{BootMemory, Error, Fdt, HandOverProfile, MemoryMap, ReservedRegion, Span};

#[cfg(test)]
mod tests;

impl BootMemory {
    /// The RAM ranges of the memory map, in tree order.
    pub fn ram(&self) -> &[Span] {
        self.memory.ram()
    }

    /// The reserved regions of the memory map.
    pub fn reserved(&self) -> &[ReservedRegion] {
        self.memory.reserved()
    }

    /// The number of dynamic reservations of the memory map.
    pub fn dynamic(&self) -> u64 {
        self.memory.dynamic()
    }

    /// The span of the tree, `[dtb_address, dtb_address + totalsize)`.
    pub fn dtb(&self) -> Span {
        self.dtb
    }

    /// The span of the image with its BSS and stacks, as the board gave it.
    pub fn image(&self) -> Span {
        self.image
    }

    /// The sum of the sizes of the RAM ranges.
    pub fn ram_bytes(&self) -> u64 {
        self.ram_bytes
    }

    /// Whether `span` lies inside one RAM range and touches neither the
    /// tree, nor the image, nor any reserved region, `reusable` ones
    /// included: a span of size 0, `EmptyRegion`; then one whose end leaves
    /// 64 bits, `Overflow`. The answer describes memory; it is no
    /// ownership.
    pub fn is_available(&self, span: Span) -> Result<bool, Error> {
        if span.size == 0 {
            return Err(Error::EmptyRegion);
        }
        if !valid(span) {
            return Err(Error::Overflow);
        }
        if !in_one_range(self.memory.ram(), span)
            || touches(self.image, span)
            || touches(self.dtb, span)
        {
            return Ok(false);
        }
        Ok(!touches_region(self.memory.reserved(), span))
    }
}

/// Whether a reserved region of `regions` touches `span`.
fn touches_region(regions: &[ReservedRegion], span: Span) -> bool {
    let mut index = 0;
    while index < regions.len() {
        if touches(regions[index].span, span) {
            return true;
        }
        index += 1;
    }
    false
}

/// The entries of the `compatible` value `bytes`, which ends with a NUL, up
/// to `end`, the offset of that NUL, in order: an entry that is not UTF-8,
/// `BadString`, then an empty one, `BadProperty`.
fn compatible_entries(bytes: &[u8], end: usize) -> Result<(), Error> {
    let mut start = 0;
    let mut entries = 0;
    while entries <= end {
        let stop = match find_nul(bytes, start) {
            Some(nul) => nul,
            None => end,
        };
        if !is_utf8(bytes, start, stop) {
            return Err(Error::BadString);
        }
        if stop == start {
            return Err(Error::BadProperty);
        }
        if stop >= end {
            return Ok(());
        }
        start = stop + 1;
        entries += 1;
    }
    Ok(())
}

/// Whether an entry of the `compatible` value `bytes`, which ends with a NUL
/// at `end`, has the bytes `entry`.
fn has_entry(bytes: &[u8], end: usize, entry: &[u8]) -> bool {
    let mut start = 0;
    let mut entries = 0;
    while entries <= end {
        let stop = match find_nul(bytes, start) {
            Some(nul) => nul,
            None => end,
        };
        if same_bytes(bytes, start, stop, entry) {
            return true;
        }
        if stop >= end {
            return false;
        }
        start = stop + 1;
        entries += 1;
    }
    false
}

/// Whether the entries of the `compatible` value `bytes`, which ends with a
/// NUL at `end`, hold every entry that `required` requires: each nonempty
/// piece of `required` split at its NUL bytes.
fn holds_required(bytes: &[u8], end: usize, required: &[u8]) -> bool {
    let mut start = 0;
    let mut pieces = 0;
    while pieces <= required.len() {
        let stop = match find_nul(required, start) {
            Some(nul) => nul,
            None => required.len(),
        };
        if stop > start && !has_entry(bytes, end, &required[start..stop]) {
            return false;
        }
        if stop >= required.len() {
            return true;
        }
        start = stop + 1;
        pieces += 1;
    }
    true
}

/// The root `compatible` of a hand-over tree against the entries `required`
/// of its profile: a value that does not end with a NUL, `BadProperty`; then
/// each entry in order; then a list without an entry that the profile
/// requires, `BadProperty`.
fn check_compatible(bytes: &[u8], required: &[u8]) -> Result<(), Error> {
    if bytes.is_empty() || bytes[bytes.len() - 1] != 0 {
        return Err(Error::BadProperty);
    }
    compatible_entries(bytes, bytes.len() - 1)?;
    if !holds_required(bytes, bytes.len() - 1, required) {
        return Err(Error::BadProperty);
    }
    Ok(())
}

/// Whether `address` is a multiple of `2 ^ alignment_log2`: from an exponent
/// of 64 up only the address 0 is, and below it the bits under the
/// alignment are 0.
fn is_aligned(address: u64, alignment_log2: u8) -> bool {
    let shift = alignment_log2 as u64;
    if shift >= 64 {
        return address == 0;
    }
    address & ((1 << shift) - 1) == 0
}

/// The sum of the sizes of `ranges`, or `Overflow` when it leaves 64 bits.
fn ram_bytes(ranges: &[Span]) -> Result<u64, Error> {
    let mut sum: u64 = 0;
    let mut index = 0;
    while index < ranges.len() {
        sum = match sum.checked_add(ranges[index].size) {
            Some(sum) => sum,
            None => return Err(Error::Overflow),
        };
        index += 1;
    }
    Ok(sum)
}

/// The checks of the tree and of the image against the profile `hand_over`
/// before the memory discovery: the size of the tree, the address of the
/// tree, the cells and the `compatible` of the root, the span of the tree
/// and the image; the span of the tree.
fn check_hand_over(
    tree: Fdt<'_>,
    hand_over: HandOverProfile<'_>,
    dtb_address: u64,
    image: Span,
) -> Result<Span, Error> {
    if tree.total_size() > hand_over.max_blob_size {
        return Err(Error::LimitExceeded);
    }
    if !is_aligned(dtb_address, hand_over.alignment_log2) {
        return Err(Error::BadAlignment);
    }
    let root = match first_node(tree.structure) {
        Some(root) => root,
        None => return Err(Error::BadTree),
    };
    if address_cells_at(tree.structure, tree.strings, root)? != 2 {
        return Err(Error::UnsupportedCells);
    }
    if size_cells_at(tree.structure, tree.strings, root)? != 2 {
        return Err(Error::UnsupportedCells);
    }
    let (start, end) = match value_at(tree.structure, tree.strings, root, b"compatible") {
        Some(range) => range,
        None => return Err(Error::MissingProperty),
    };
    check_compatible(&tree.structure[start..end], hand_over.compatible)?;
    let dtb = Span::new(dtb_address, tree.total_size())?;
    if image.size == 0 {
        return Err(Error::EmptyRegion);
    }
    image.end()?;
    if touches(image, dtb) {
        return Err(Error::Overlap);
    }
    Ok(dtb)
}

impl Fdt<'_> {
    /// The boot memory of a hand-over tree at `dtb_address` against the
    /// profile `hand_over` of its board, with the span `image` of the image
    /// and its BSS and stacks, or the error of the first rule that it
    /// breaks: `totalsize` above the `max_blob_size` of the profile,
    /// `LimitExceeded`; the address of the tree not a multiple of
    /// `2 ^ alignment_log2`, `BadAlignment`; the address cells and then the
    /// size cells of the root, `BadProperty` or a number other than 2
    /// `UnsupportedCells`; the root `compatible`: absent, `MissingProperty`,
    /// a value that does not end with a NUL, `BadProperty`, an entry that is
    /// not UTF-8, `BadString`, an empty entry, `BadProperty`, and without an
    /// entry that the profile requires, `BadProperty`; the span of the tree,
    /// `Overflow`; the image, `EmptyRegion` then `Overflow`; the image on
    /// the tree, `Overlap`; [`Fdt::discover_memory`]; the tree, then the
    /// image, outside every single RAM range, `Unmapped`; the sum of the RAM
    /// ranges, `Overflow`.
    pub fn discover_boot_memory(
        self,
        hand_over: HandOverProfile<'_>,
        dtb_address: u64,
        image: Span,
    ) -> Result<BootMemory, Error> {
        let dtb = check_hand_over(self, hand_over, dtb_address, image)?;
        let memory = self.discover_memory()?;
        check_storage(&memory, dtb, image)?;
        let ram_bytes = ram_bytes(memory.ram())?;
        Ok(BootMemory {
            memory,
            dtb,
            image,
            ram_bytes,
            max_blob_size: hand_over.max_blob_size,
            alignment_log2: hand_over.alignment_log2,
        })
    }
}

/// The tree, then the image, inside one RAM range of `memory`, or
/// `Unmapped`.
fn check_storage(memory: &MemoryMap, dtb: Span, image: Span) -> Result<(), Error> {
    if !in_one_range(memory.ram(), dtb) {
        return Err(Error::Unmapped);
    }
    if !in_one_range(memory.ram(), image) {
        return Err(Error::Unmapped);
    }
    Ok(())
}
