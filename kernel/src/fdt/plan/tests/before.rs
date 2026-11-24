//! The boot memory of a hand-over tree before its profile became a value:
//! the code of krepi commit 5ffa296 at the lines below, copied verbatim
//! with the suffix `_before` added to the name of each item and of each call
//! of a copied item, for the differential tests, which compare it with the
//! code that replaced it. The copy lies below the boot memory map, whose
//! private functions the copy of `MemoryPlan::from_pi5` calls, since it
//! reads the private fields of the copy of `Pi5BootMemory`; the private
//! functions of the hand-over module and of its selection that the copy
//! calls are copied with it, as `touches_region`, `ram_bytes`,
//! `check_storage`, `align_up` and `furthest_touched` show.
//!
//! - `kernel/src/fdt.rs:85-86`: `PI5_MAX_BLOB_SIZE`;
//! - `kernel/src/fdt.rs:351-364`: `Pi5BootMemory`;
//! - `kernel/src/fdt/pi5.rs:23-74`: `Pi5BootMemory::ram`, `reserved`,
//!   `dynamic`, `dtb`, `image`, `ram_bytes` and `is_available`;
//! - `kernel/src/fdt/pi5.rs:76-86`: `touches_region`;
//! - `kernel/src/fdt/pi5.rs:88-117`: `compatible_entries`;
//! - `kernel/src/fdt/pi5.rs:119-131`: `check_compatible`;
//! - `kernel/src/fdt/pi5.rs:133-145`: `ram_bytes`;
//! - `kernel/src/fdt/pi5.rs:147-182`: `check_hand_over`;
//! - `kernel/src/fdt/pi5.rs:184-215`: `Fdt::discover_pi5_boot_memory`;
//! - `kernel/src/fdt/pi5.rs:217-227`: `check_storage`;
//! - `kernel/src/fdt/pi5/selection.rs:15-22`: `align_up`;
//! - `kernel/src/fdt/pi5/selection.rs:24-52`: `furthest_touched`;
//! - `kernel/src/fdt/pi5/selection.rs:54-85`: `search_range`;
//! - `kernel/src/fdt/pi5/selection.rs:87-117`: `search_ranges`;
//! - `kernel/src/fdt/pi5/selection.rs:119-143`:
//!   `Pi5BootMemory::find_available`;
//! - `kernel/src/fdt/plan.rs:287-309`: `MemoryPlan::from_pi5`.
//!
//! Feature: krepi.platform.device-tree

#![allow(non_camel_case_types, non_upper_case_globals, dead_code)]

use super::super::*;
use crate::fdt::format::{find_nul, is_utf8, same_bytes};
use crate::fdt::nodes::{address_cells_at, first_node, size_cells_at, value_at};
use crate::fdt::span::touches;
use crate::fdt::{Error, Fdt, MemoryMap};

/// The largest `totalsize` of a Pi 5 hand-over tree, 128 KiB.
pub const PI5_MAX_BLOB_SIZE_before: u64 = 0x2_0000;

/// The result of [`Fdt::discover_pi5_boot_memory`]: the memory map of a
/// Pi 5 hand-over tree, checked against the spans of the image and of the
/// tree.
#[derive(Debug)]
pub struct Pi5BootMemory_before {
    /// The memory map of the tree.
    memory: MemoryMap,
    /// The span of the tree.
    dtb: Span,
    /// The span of the image with its BSS and stacks.
    image: Span,
    /// The sum of the RAM ranges.
    ram_bytes: u64,
}

impl Pi5BootMemory_before {
    /// The RAM ranges of the memory map, in tree order.
    pub fn ram_before(&self) -> &[Span] {
        self.memory.ram()
    }

    /// The reserved regions of the memory map.
    pub fn reserved_before(&self) -> &[ReservedRegion] {
        self.memory.reserved()
    }

    /// The number of dynamic reservations of the memory map.
    pub fn dynamic_before(&self) -> u64 {
        self.memory.dynamic()
    }

    /// The span of the tree, `[dtb_address, dtb_address + totalsize)`.
    pub fn dtb_before(&self) -> Span {
        self.dtb
    }

    /// The span of the image with its BSS and stacks, as the board gave it.
    pub fn image_before(&self) -> Span {
        self.image
    }

    /// The sum of the sizes of the RAM ranges.
    pub fn ram_bytes_before(&self) -> u64 {
        self.ram_bytes
    }

    /// Whether `span` lies inside one RAM range and touches neither the
    /// tree, nor the image, nor any reserved region, `reusable` ones
    /// included: a span of size 0, `EmptyRegion`; then one whose end leaves
    /// 64 bits, `Overflow`. The answer describes memory; it is no
    /// ownership.
    pub fn is_available_before(&self, span: Span) -> Result<bool, Error> {
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
        Ok(!touches_region_before(self.memory.reserved(), span))
    }
}

/// Whether a reserved region of `regions` touches `span`.
fn touches_region_before(regions: &[ReservedRegion], span: Span) -> bool {
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
fn compatible_entries_before(bytes: &[u8], end: usize) -> Result<bool, Error> {
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
fn check_compatible_before(bytes: &[u8]) -> Result<(), Error> {
    if bytes.is_empty() || bytes[bytes.len() - 1] != 0 {
        return Err(Error::BadProperty);
    }
    if !compatible_entries_before(bytes, bytes.len() - 1)? {
        return Err(Error::BadProperty);
    }
    Ok(())
}

/// The sum of the sizes of `ranges`, or `Overflow` when it leaves 64 bits.
fn ram_bytes_before(ranges: &[Span]) -> Result<u64, Error> {
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
fn check_hand_over_before(tree: Fdt<'_>, dtb_address: u64, image: Span) -> Result<Span, Error> {
    if tree.total_size() > PI5_MAX_BLOB_SIZE_before {
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
    check_compatible_before(&tree.structure[start..end])?;
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
    pub fn discover_pi5_boot_memory_before(
        self,
        dtb_address: u64,
        image: Span,
    ) -> Result<Pi5BootMemory_before, Error> {
        let dtb = check_hand_over_before(self, dtb_address, image)?;
        let memory = self.discover_memory()?;
        check_storage_before(&memory, dtb, image)?;
        let ram_bytes = ram_bytes_before(memory.ram())?;
        Ok(Pi5BootMemory_before {
            memory,
            dtb,
            image,
            ram_bytes,
        })
    }
}

/// The tree, then the image, inside one RAM range of `memory`, or
/// `Unmapped`.
fn check_storage_before(memory: &MemoryMap, dtb: Span, image: Span) -> Result<(), Error> {
    if !in_one_range(memory.ram(), dtb) {
        return Err(Error::Unmapped);
    }
    if !in_one_range(memory.ram(), image) {
        return Err(Error::Unmapped);
    }
    Ok(())
}

/// The least multiple of `alignment`, a power of two, that is at least
/// `address`, or `Overflow` when it leaves 64 bits.
fn align_up_before(address: u64, alignment: u64) -> Result<u64, Error> {
    match address.checked_add(alignment - 1) {
        Some(sum) => Ok(sum & !(alignment - 1)),
        None => Err(Error::Overflow),
    }
}

/// The end of the furthest of the image, the tree and the reserved regions
/// that `candidate` touches, or none when it touches none of them.
fn furthest_touched_before(
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
fn search_range_before(
    memory: &Pi5BootMemory_before,
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
        match furthest_touched_before(memory.image, memory.dtb, regions, candidate) {
            Some(furthest) => start = align_up_before(furthest, alignment)?,
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
fn search_ranges_before(
    memory: &Pi5BootMemory_before,
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
        let start = align_up_before(lowest, alignment)?;
        let range_end = range.start + range.size;
        let bound = if range_end < limit { range_end } else { limit };
        if let Some(span) = search_range_before(memory, size, alignment, bound, start, fuel)? {
            return Ok(Some(span));
        }
        index += 1;
    }
    Ok(None)
}

impl Pi5BootMemory_before {
    /// A span of `size` bytes aligned to `alignment`, within
    /// `[minimum, limit)` and inside one RAM range, that touches neither the
    /// image, nor the tree, nor any reserved region: the span with the
    /// lowest aligned start in the first RAM range, in tree order, that has
    /// one, and none when no range has one. A size of 0 or an empty bound,
    /// `EmptyRegion`; an alignment that is not a power of two,
    /// `BadAlignment`; then the search, whose alignments fail with
    /// `Overflow`.
    pub fn find_available_before(
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
        search_ranges_before(self, size, alignment, minimum, limit)
    }
}

impl MemoryPlan {
    /// [`MemoryPlan::new`] with the RAM ranges of the Pi 5 boot memory
    /// `memory`, the boot storage of its image, its tree and then the
    /// further spans `more` of the board, such as the boot bundle, in this
    /// order, and its reserved regions as firmware reservations; more than
    /// two further spans make more than 4 spans of boot storage,
    /// `Capacity`.
    pub fn from_pi5_before(
        memory: &Pi5BootMemory_before,
        window: Span,
        more: &[Span],
    ) -> Result<MemoryPlan, PlanError> {
        check_window(window)?;
        let mut boot = [memory.image, memory.dtb, EMPTY, EMPTY];
        if more.len() <= 2 {
            let mut index = 0;
            while index < more.len() {
                boot[2 + index] = more[index];
                index += 1;
            }
        }
        let plan = build(memory.ram_before(), &boot, 2 + more.len(), memory.reserved_before())?;
        manage_window(plan, window)
    }
}
