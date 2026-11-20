//! Cells and address translation: the regions of a `reg` value and the
//! maps of `ranges` and `dma-ranges` with the translation of a span through
//! them, each value checked whole when it is built.
//!
//! Feature: krepi.platform.device-tree
//!
//! A number is read in 0, 1 or 2 cells and never truncated: an address of
//! three cells, such as one of PCI, fails with `UnsupportedCells`. An
//! address of one cell lies in the first 4 GiB, and one of two cells within
//! 64 bits.

use super::span::{holds, overlaps};
use super::{AddressMap, Error, MappingKind, Reg, Span, cells_u64};

/// The width of an address of `cells` cells: the span ends within 64 bits,
/// and with one cell it starts and ends within the first 4 GiB; otherwise
/// `Overflow`.
fn check_width(span: Span, cells: u32) -> Result<(), Error> {
    let end = match span.start.checked_add(span.size) {
        Some(end) => end,
        None => return Err(Error::Overflow),
    };
    if cells == 1 && (span.start > 0xffff_ffff || end > 0x1_0000_0000) {
        return Err(Error::Overflow);
    }
    Ok(())
}

/// The entry at `at` of a `reg` value: its address in `address_cells` cells
/// and its size in `size_cells`, a span whose end leaves 64 bits or, with
/// one address cell, the first 4 GiB, `Overflow`.
pub(super) fn reg_entry(
    bytes: &[u8],
    at: usize,
    address_cells: u32,
    size_cells: u32,
) -> Result<Span, Error> {
    let split = at + address_cells as usize * 4;
    let end = split + size_cells as usize * 4;
    let start = cells_u64(&bytes[at..split], address_cells)?;
    let size = cells_u64(&bytes[split..end], size_cells)?;
    let span = Span::new(start, size)?;
    check_width(span, address_cells)?;
    Ok(span)
}

/// The number of bytes of an entry of a `reg` value.
pub(super) fn reg_stride(address_cells: u32, size_cells: u32) -> usize {
    (address_cells + size_cells) as usize * 4
}

/// Each entry of a `reg` value of whole entries of `stride` bytes, in order.
fn check_reg_entries(
    bytes: &[u8],
    address_cells: u32,
    size_cells: u32,
    stride: usize,
) -> Result<(), Error> {
    let mut at = 0;
    while at < bytes.len() {
        reg_entry(bytes, at, address_cells, size_cells)?;
        at += stride;
    }
    Ok(())
}

/// The rules of [`Reg::new`]: address cells other than 1 or 2 or size cells
/// above 2, `UnsupportedCells`; an empty value or one that is not a whole
/// number of entries, `BadProperty`; then each entry in order.
pub(super) fn check_reg(bytes: &[u8], address_cells: u32, size_cells: u32) -> Result<(), Error> {
    if (address_cells != 1 && address_cells != 2) || size_cells > 2 {
        return Err(Error::UnsupportedCells);
    }
    let stride = reg_stride(address_cells, size_cells);
    if bytes.is_empty() || bytes.len() % stride != 0 {
        return Err(Error::BadProperty);
    }
    check_reg_entries(bytes, address_cells, size_cells, stride)
}

/// The entry at `cursor` of a checked `reg` value and the offset of the
/// next, or none after the last.
fn reg_step(
    bytes: &[u8],
    address_cells: u32,
    size_cells: u32,
    cursor: usize,
) -> (usize, Option<Span>) {
    let stride = reg_stride(address_cells, size_cells);
    if stride == 0 || cursor >= bytes.len() || bytes.len() - cursor < stride {
        return (cursor, None);
    }
    match reg_entry(bytes, cursor, address_cells, size_cells) {
        Ok(span) => (cursor + stride, Some(span)),
        Err(_) => (cursor, None),
    }
}

impl<'a> Reg<'a> {
    /// The regions of the `reg` value `bytes` in `address_cells` and
    /// `size_cells` cells, after a check of every entry: address cells other
    /// than 1 or 2 or size cells above 2, `UnsupportedCells`; an empty value
    /// or one that is not a whole number of entries, `BadProperty`; then
    /// each entry in order, `Overflow` for one whose span ends beyond
    /// 64 bits or, with one address cell, beyond the first 4 GiB.
    pub fn new(bytes: &'a [u8], address_cells: u32, size_cells: u32) -> Result<Reg<'a>, Error> {
        check_reg(bytes, address_cells, size_cells)?;
        Ok(Reg {
            bytes,
            address_cells,
            size_cells,
            cursor: 0,
        })
    }

    /// The next entry, or none after the last. [`Reg::new`] checked the
    /// entries, so the walk does not fail.
    // The iterator implements `next` alone: the provided methods of
    // `Iterator` would reach library functions without a model.
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Option<Span> {
        let (cursor, entry) =
            reg_step(self.bytes, self.address_cells, self.size_cells, self.cursor);
        self.cursor = cursor;
        entry
    }
}

/// The window at `at` of a map value: its child address, its parent address
/// and its size, in their cells. A size of 0, `EmptyRegion`; then a child or
/// parent span whose end leaves 64 bits or the width of its side,
/// `Overflow`. It gives the child and the parent span.
fn window(
    bytes: &[u8],
    at: usize,
    child_cells: u32,
    parent_cells: u32,
    size_cells: u32,
) -> Result<(Span, Span), Error> {
    let child_end = at + child_cells as usize * 4;
    let parent_end = child_end + parent_cells as usize * 4;
    let end = parent_end + size_cells as usize * 4;
    let child = cells_u64(&bytes[at..child_end], child_cells)?;
    let parent = cells_u64(&bytes[child_end..parent_end], parent_cells)?;
    let size = cells_u64(&bytes[parent_end..end], size_cells)?;
    if size == 0 {
        return Err(Error::EmptyRegion);
    }
    let child = Span::new(child, size)?;
    let parent = Span::new(parent, size)?;
    check_width(child, child_cells)?;
    check_width(parent, parent_cells)?;
    Ok((child, parent))
}

/// The number of bytes of a window.
fn stride(child_cells: u32, parent_cells: u32, size_cells: u32) -> usize {
    (child_cells + parent_cells + size_cells) as usize * 4
}

/// Each window of a map value of whole windows, in order.
fn check_windows(
    bytes: &[u8],
    child_cells: u32,
    parent_cells: u32,
    size_cells: u32,
) -> Result<(), Error> {
    let stride = stride(child_cells, parent_cells, size_cells);
    let mut at = 0;
    while at < bytes.len() {
        window(bytes, at, child_cells, parent_cells, size_cells)?;
        at += stride;
    }
    Ok(())
}

/// The rules of [`AddressMap::new`] for the value `bytes`, absent unless
/// `present`: child or parent address cells other than 1 or 2, or size
/// cells above 2, `UnsupportedCells`; an absent or empty value is no
/// window; any other value without size cells or that is not a whole number
/// of windows, `BadProperty`; then each window in order.
pub(super) fn check_map(
    bytes: &[u8],
    present: bool,
    child_cells: u32,
    parent_cells: u32,
    size_cells: u32,
) -> Result<(), Error> {
    if (child_cells != 1 && child_cells != 2)
        || (parent_cells != 1 && parent_cells != 2)
        || size_cells > 2
    {
        return Err(Error::UnsupportedCells);
    }
    if !present || bytes.is_empty() {
        return Ok(());
    }
    if size_cells == 0 || bytes.len() % stride(child_cells, parent_cells, size_cells) != 0 {
        return Err(Error::BadProperty);
    }
    check_windows(bytes, child_cells, parent_cells, size_cells)
}

/// The translation of `request` through the windows of a checked map value,
/// from the child side to the parent side or, with `reverse`, back: a
/// second window that holds the request, `AmbiguousMapping`; a window that
/// holds part of it, `Unmapped`; the translated span, `Overflow`; no window
/// that holds it, `Unmapped`.
fn through_windows(
    bytes: &[u8],
    child_cells: u32,
    parent_cells: u32,
    size_cells: u32,
    request: Span,
    reverse: bool,
) -> Result<Span, Error> {
    let stride = stride(child_cells, parent_cells, size_cells);
    let mut found = None;
    let mut seen = false;
    let mut at = 0;
    while at < bytes.len() {
        let (child, parent) = window(bytes, at, child_cells, parent_cells, size_cells)?;
        let (from, to) = if reverse {
            (parent, child)
        } else {
            (child, parent)
        };
        if holds(from, request) {
            if seen {
                return Err(Error::AmbiguousMapping);
            }
            let start = match to.start.checked_add(request.start - from.start) {
                Some(start) => start,
                None => return Err(Error::Overflow),
            };
            found = Some(Span::new(start, request.size)?);
            seen = true;
        } else if overlaps(from, request) {
            return Err(Error::Unmapped);
        }
        at += stride;
    }
    match found {
        Some(span) => Ok(span),
        None => Err(Error::Unmapped),
    }
}

/// The translation of `request` through a checked map value, absent unless
/// `present`, from the child side to the parent side or, with `reverse`,
/// back: the request of size 0, `EmptyRegion`; its width, `Overflow`; an
/// absent map, `Unmapped`; an identity map, the width of the target side,
/// `Overflow`; then the windows in order.
pub(super) fn translate_map(
    bytes: &[u8],
    present: bool,
    child_cells: u32,
    parent_cells: u32,
    size_cells: u32,
    request: Span,
    reverse: bool,
) -> Result<Span, Error> {
    if request.size == 0 {
        return Err(Error::EmptyRegion);
    }
    let (source_cells, target_cells) = if reverse {
        (parent_cells, child_cells)
    } else {
        (child_cells, parent_cells)
    };
    check_width(request, source_cells)?;
    if !present {
        return Err(Error::Unmapped);
    }
    if bytes.is_empty() {
        check_width(request, target_cells)?;
        return Ok(request);
    }
    through_windows(
        bytes,
        child_cells,
        parent_cells,
        size_cells,
        request,
        reverse,
    )
}

/// The empty value of an absent map.
const NO_VALUE: &[u8] = &[];

impl<'a> AddressMap<'a> {
    /// The map of the `ranges` or `dma-ranges` value `bytes`, none for an
    /// absent property, in `child_cells`, `parent_cells` and `size_cells`
    /// cells, after a check of every window: child or parent address cells
    /// other than 1 or 2, or size cells above 2, `UnsupportedCells`; an
    /// absent value is the kind `Absent` and an empty one the kind
    /// `Identity`; any other value without size cells or that is not a
    /// whole number of windows, `BadProperty`; then each window in order,
    /// `EmptyRegion` for one of size 0 and then `Overflow` for a child or
    /// parent span beyond 64 bits or the width of its side.
    pub fn new(
        bytes: Option<&'a [u8]>,
        child_cells: u32,
        parent_cells: u32,
        size_cells: u32,
    ) -> Result<AddressMap<'a>, Error> {
        // Each arm checks and builds its own map: a `match` that gives the
        // borrowed value or the constant before the check is not translated.
        match bytes {
            Some(value) => {
                check_map(value, true, child_cells, parent_cells, size_cells)?;
                Ok(AddressMap {
                    bytes: value,
                    present: true,
                    child_cells,
                    parent_cells,
                    size_cells,
                })
            }
            None => {
                check_map(NO_VALUE, false, child_cells, parent_cells, size_cells)?;
                Ok(AddressMap {
                    bytes: NO_VALUE,
                    present: false,
                    child_cells,
                    parent_cells,
                    size_cells,
                })
            }
        }
    }

    /// The kind of the map: `Absent`, `Identity` or `Windows`.
    pub fn kind(self) -> MappingKind {
        if !self.present {
            return MappingKind::Absent;
        }
        if self.bytes.is_empty() {
            return MappingKind::Identity;
        }
        MappingKind::Windows
    }

    /// A span of the child's addresses as one of the parent's: the request
    /// of size 0, `EmptyRegion`; its width, `Overflow`; an absent map,
    /// `Unmapped`; an identity map gives the same span within the width of
    /// the parent side, `Overflow`; a map of windows translates through the
    /// one window that holds the whole request, and fails with
    /// `AmbiguousMapping` when two hold it and with `Unmapped` when one
    /// holds part of it or none holds it.
    pub fn to_parent(self, span: Span) -> Result<Span, Error> {
        translate_map(
            self.bytes,
            self.present,
            self.child_cells,
            self.parent_cells,
            self.size_cells,
            span,
            false,
        )
    }

    /// A span of the parent's addresses as one of the child's, with the
    /// rules of [`AddressMap::to_parent`] from the other side.
    pub fn to_child(self, span: Span) -> Result<Span, Error> {
        translate_map(
            self.bytes,
            self.present,
            self.child_cells,
            self.parent_cells,
            self.size_cells,
            span,
            true,
        )
    }
}
