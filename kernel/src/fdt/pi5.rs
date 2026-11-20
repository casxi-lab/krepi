//! The Pi 5 boot memory: the memory discovery of a Raspberry Pi 5
//! hand-over tree, checked against the spans that the board gives for the
//! tree and for the image, and the availability of a span in it.
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
use super::{Error, Fdt, MemoryMap, PI5_MAX_BLOB_SIZE, Pi5BootMemory, ReservedRegion, Span};

#[cfg(test)]
mod tests;

impl Pi5BootMemory {
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
/// `BadString`, then an empty one, `BadProperty`; whether they hold
/// `raspberrypi,5-model-b` and `brcm,bcm2712`.
fn compatible_entries(bytes: &[u8], end: usize) -> Result<bool, Error> {
    let mut board = false;
    let mut soc = false;
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
        board = board || same_bytes(bytes, start, stop, b"raspberrypi,5-model-b");
        soc = soc || same_bytes(bytes, start, stop, b"brcm,bcm2712");
        if stop >= end {
            return Ok(board && soc);
        }
        start = stop + 1;
        entries += 1;
    }
    Ok(board && soc)
}

/// The root `compatible` of a Pi 5 hand-over tree: a value that does not
/// end with a NUL, `BadProperty`; then each entry in order; then a list
/// without `raspberrypi,5-model-b` or without `brcm,bcm2712`,
/// `BadProperty`.
fn check_compatible(bytes: &[u8]) -> Result<(), Error> {
    if bytes.is_empty() || bytes[bytes.len() - 1] != 0 {
        return Err(Error::BadProperty);
    }
    if !compatible_entries(bytes, bytes.len() - 1)? {
        return Err(Error::BadProperty);
    }
    Ok(())
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

/// The checks of the tree and of the image before the memory discovery:
/// the size of the tree, the address of the tree, the cells and the
/// `compatible` of the root, the span of the tree and the image; the span
/// of the tree.
fn check_hand_over(tree: Fdt<'_>, dtb_address: u64, image: Span) -> Result<Span, Error> {
    if tree.total_size() > PI5_MAX_BLOB_SIZE {
        return Err(Error::LimitExceeded);
    }
    if dtb_address % 8 != 0 {
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
    check_compatible(&tree.structure[start..end])?;
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
    /// The Pi 5 boot memory of a hand-over tree at `dtb_address`, with the
    /// span `image` of the image and its BSS and stacks, or the error of
    /// the first rule that it breaks: `totalsize` above
    /// [`PI5_MAX_BLOB_SIZE`], `LimitExceeded`; the address of the tree not a
    /// multiple of 8, `BadAlignment`; the address cells and then the size
    /// cells of the root, `BadProperty` or a number other than 2
    /// `UnsupportedCells`; the root `compatible`: absent, `MissingProperty`,
    /// a value that does not end with a NUL, `BadProperty`, an entry that is
    /// not UTF-8, `BadString`, an empty entry, `BadProperty`, and without
    /// `raspberrypi,5-model-b` or without `brcm,bcm2712`, `BadProperty`; the
    /// span of the tree, `Overflow`; the image, `EmptyRegion` then
    /// `Overflow`; the image on the tree, `Overlap`;
    /// [`Fdt::discover_memory`]; the tree, then the image, outside every
    /// single RAM range, `Unmapped`; the sum of the RAM ranges, `Overflow`.
    pub fn discover_pi5_boot_memory(
        self,
        dtb_address: u64,
        image: Span,
    ) -> Result<Pi5BootMemory, Error> {
        let dtb = check_hand_over(self, dtb_address, image)?;
        let memory = self.discover_memory()?;
        check_storage(&memory, dtb, image)?;
        let ram_bytes = ram_bytes(memory.ram())?;
        Ok(Pi5BootMemory {
            memory,
            dtb,
            image,
            ram_bytes,
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
