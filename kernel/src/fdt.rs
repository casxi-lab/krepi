//! The device tree: the bounded parsing of the flattened device tree that
//! the firmware hands to the kernel, and the access to its nodes and
//! properties with the translation of their addresses.
//!
//! Feature: krepi.platform.device-tree
//!
//! The rules are those of the component's contract,
//! `docs/domains/boot-platform/fdt/contract.md`. The module reads byte
//! slices and values, never an address: the board crate forms the slice of
//! the hand-over tree. Every entry checks its input before it returns a
//! value, fails with one error and nothing else, and never panics.
//!
//! The module follows the provable Rust subset
//! (`docs/conventions/provable-subset.md`) in the code shapes of the
//! component's proof path (`docs/domains/boot-platform/fdt/proof.md`). Every
//! type that an entry names is defined in this file, so that the roots of
//! the proof target name it here, and the submodules hold the behaviour. The
//! types whose values keep an invariant have private fields, so that only
//! the functions of this module build them. Words are put together from
//! single bytes, names and strings are checked and compared as bytes, a
//! function holds at most one loop, every loop walks slices of plain data
//! and scalars, the views of a tree are taken by value, and the iterators
//! implement `next` alone.

// The code shapes of the proof path write a `match` where Clippy suggests a
// combinator, the `?` of an `Option`, `matches!` or a library method such as
// `is_some` or `swap`, and compare with `<` and `>` where it suggests a range
// or `is_multiple_of`: each of those would reach a library function without
// a model.
#![allow(
    clippy::implicit_saturating_sub,
    clippy::manual_is_multiple_of,
    clippy::manual_map,
    clippy::manual_range_contains,
    clippy::manual_swap,
    clippy::match_like_matches_macro,
    clippy::question_mark,
    clippy::redundant_pattern_matching
)]

mod format;
mod nodes;
mod parser;
mod span;
mod translation;

#[cfg(test)]
mod tests;

/// The largest `totalsize` that [`Fdt::parse`] accepts, 2 MiB.
pub const MAX_BLOB_SIZE: u64 = 0x20_0000;

/// The most nodes on a path from the root, the root included, so that no
/// node lies deeper than 31.
pub const MAX_DEPTH: u64 = 32;

/// The most tokens of a structure block that [`Fdt::parse`] reads, the end
/// token included.
pub const MAX_TOKENS: u64 = 65_536;

/// The most properties of one node; it covers the 334 properties of the
/// `/__symbols__` node of the Pi 5 tree.
pub const MAX_PROPERTIES: u64 = 512;

/// The most bytes of a property name, its NUL not counted: above the 31
/// characters of DTSpec v0.4, since vendor names reach 32.
pub const MAX_PROPERTY_NAME: u64 = 64;

/// The most entries of the reservation map before its terminator.
pub const MAX_RESERVATIONS: u64 = 128;

/// The most RAM ranges of a memory discovery.
pub const MAX_MEMORY_REGIONS: u64 = 32;

/// The most reserved regions of a memory discovery: the entries of the
/// reservation map and the spans of `/reserved-memory` together.
pub const MAX_RESERVED_REGIONS: u64 = 128;

/// The largest `totalsize` of a Pi 5 hand-over tree, 128 KiB.
pub const PI5_MAX_BLOB_SIZE: u64 = 0x2_0000;

/// [`MAX_DEPTH`] as a length.
const DEPTH: usize = MAX_DEPTH as usize;

/// [`MAX_TOKENS`] as a count.
const TOKENS: usize = MAX_TOKENS as usize;

/// An error of the parse, the node access, the translation, the memory
/// discovery, the CPU nodes or the Pi 5 boot memory: the rule that the
/// input breaks, as the error table of the contract names it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    /// The input holds fewer than 40 bytes or fewer than `totalsize`, or a
    /// block, a reservation entry, a token, a property value or its padding
    /// runs past the end of its block or of the tree.
    Truncated,
    /// The first word of the header is not `0xd00d_feed`.
    BadMagic,
    /// The version is below 17, or the last compatible version is not 16 or
    /// 17 or is above the version.
    UnsupportedVersion,
    /// The blocks do not lie where the format puts them.
    BadLayout,
    /// A block, the reservation map, a Pi 5 hand-over tree or a selection is
    /// not aligned as the rules require.
    BadAlignment,
    /// A token other than 1, 2, 3, 4 and 9.
    BadToken,
    /// The tokens do not form one tree, or a node has no parent where an
    /// entry needs one.
    BadTree,
    /// A name or a string is not a NUL-terminated UTF-8 string of its set.
    BadString,
    /// A nonzero byte in the padding after a node name.
    BadPadding,
    /// Two properties of one name in a node.
    DuplicateProperty,
    /// A limit of the format, the discovery or the Pi 5 tree is exceeded.
    LimitExceeded,
    /// A number of cells that the entry does not support.
    UnsupportedCells,
    /// A property whose value breaks its binding.
    BadProperty,
    /// A required node or property is absent.
    MissingProperty,
    /// An offset, span, translated address, page rounding or sum leaves
    /// 64 bits, or a span of one address cell leaves the first 4 GiB.
    Overflow,
    /// A region, window, request, image or selection of size 0.
    EmptyRegion,
    /// Two reservation entries or RAM ranges, or the image and a Pi 5
    /// hand-over tree, share an address.
    Overlap,
    /// A translation that no single window holds, or a Pi 5 hand-over tree
    /// or image outside every single RAM range.
    Unmapped,
    /// A path that matches two sibling nodes, or a request that two windows
    /// hold.
    AmbiguousMapping,
    /// A path that is not absolute, ends in `/` other than the root or holds
    /// `//`.
    BadPath,
    /// No enabled RAM range.
    NoMemory,
}

/// The addresses `[start, start + size)`. A value may be any pair, also one
/// whose end leaves 64 bits; the entries that take a span refuse such a
/// pair.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    /// The first address.
    pub start: u64,
    /// The number of addresses.
    pub size: u64,
}

/// A tree that [`Fdt::parse`] checked: a view of the bytes of a device tree
/// whose header, blocks, reservation map and tokens passed every check of
/// the format. It borrows the bytes and copies none of them.
#[derive(Clone, Copy, Debug)]
pub struct Fdt<'a> {
    /// The first `totalsize` bytes of the input.
    blob: &'a [u8],
    /// The structure block.
    structure: &'a [u8],
    /// The strings block.
    strings: &'a [u8],
    /// The entries of the reservation map before its terminator.
    reservations: &'a [u8],
}

/// A node of a tree: a begin-node token of its checked structure block.
#[derive(Clone, Copy, Debug)]
pub struct Node<'a> {
    /// The tree of the node.
    tree: Fdt<'a>,
    /// Where the node lies in the structure block.
    at: NodeAt,
}

/// Where a node lies in the structure block of its tree.
#[derive(Clone, Copy, Debug)]
struct NodeAt {
    /// The offset of its begin-node token.
    offset: usize,
    /// The offset of the token after its begin-node token, where its
    /// properties start.
    properties: usize,
    /// The offset of the begin-node token of its parent, none for the root.
    parent: Option<usize>,
    /// The offset of the first byte of its name.
    name_start: usize,
    /// The offset of the NUL after its name.
    name_end: usize,
}

/// The state of a walk over the nodes of a structure block: the cursor and
/// the begin-node tokens of the open nodes.
#[derive(Clone, Copy, Debug)]
struct Walker {
    /// The offset of the next token.
    cursor: usize,
    /// The number of open nodes.
    depth: usize,
    /// The offsets of the begin-node tokens of the open nodes, the root
    /// first.
    ancestors: [usize; DEPTH],
}

/// The iterator of [`Fdt::nodes`]: every node in the order of the structure
/// block.
#[derive(Clone, Copy, Debug)]
pub struct Nodes<'a> {
    /// The tree whose nodes it gives.
    tree: Fdt<'a>,
    /// Its walk over the structure block.
    walker: Walker,
}

/// The iterator of [`Fdt::reservations`]: the entries of the reservation
/// map in their order.
#[derive(Clone, Copy, Debug)]
pub struct Reservations<'a> {
    /// The entries before the terminator, 16 bytes each.
    entries: &'a [u8],
    /// The offset of the next entry.
    cursor: usize,
}

/// The regions of a `reg` value, which [`Reg::new`] checked, and the
/// iterator of its entries.
#[derive(Clone, Copy, Debug)]
pub struct Reg<'a> {
    /// The value.
    bytes: &'a [u8],
    /// The cells of an address.
    address_cells: u32,
    /// The cells of a size.
    size_cells: u32,
    /// The offset of the next entry.
    cursor: usize,
}

/// The kind of an address map.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MappingKind {
    /// An absent property, which maps nothing.
    Absent,
    /// An empty property, the identity.
    Identity,
    /// A list of windows.
    Windows,
}

/// The map of a `ranges` or `dma-ranges` value with the cells of its two
/// sides, which [`AddressMap::new`] checked.
#[derive(Clone, Copy, Debug)]
pub struct AddressMap<'a> {
    /// The value; empty when the property is absent.
    bytes: &'a [u8],
    /// Whether the property is present.
    present: bool,
    /// The cells of a child address.
    child_cells: u32,
    /// The cells of a parent address.
    parent_cells: u32,
    /// The cells of a size.
    size_cells: u32,
}

/// The number of `cells` big-endian cells in `bytes`: 0, 1 or 2 cells, and
/// `UnsupportedCells` for more; `BadProperty` when the bytes are not exactly
/// that many cells. It never drops a high cell.
pub fn cells_u64(bytes: &[u8], cells: u32) -> Result<u64, Error> {
    if cells > 2 {
        return Err(Error::UnsupportedCells);
    }
    if bytes.len() != cells as usize * 4 {
        return Err(Error::BadProperty);
    }
    if cells == 0 {
        return Ok(0);
    }
    if cells == 1 {
        let value = format::u32_at(bytes, 0)?;
        return Ok(value as u64);
    }
    format::u64_at(bytes, 0)
}
