//! The device tree: the bounded parsing of the flattened device tree that
//! the firmware hands to the kernel, the access to its nodes and properties
//! with the translation of their addresses, the discovery of its memory and
//! of its CPU nodes, the Pi 5 boot memory, and the boot memory map, which the
//! page-tables component takes as its input.
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

mod cpus;
mod discovery;
mod format;
mod nodes;
mod parser;
mod pi5;
mod plan;
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

/// [`MAX_MEMORY_REGIONS`] as a length.
const RAM_RANGES: usize = MAX_MEMORY_REGIONS as usize;

/// [`MAX_RESERVED_REGIONS`] as a length.
const RESERVED_REGIONS: usize = MAX_RESERVED_REGIONS as usize;

/// The most RAM banks of a boot memory map.
const BANKS: usize = 32;

/// The most spans of boot storage of a boot memory map.
const BOOT_SPANS: usize = 4;

/// The most firmware reservations of a boot memory map.
const FIRMWARE: usize = 128;

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

/// An error of the boot memory map: the rule that its input breaks, as the
/// error table of the contract names it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PlanError {
    /// A managed window, RAM bank, boot storage span or firmware reservation
    /// of size 0.
    InvalidRange,
    /// A span, its rounding to pages or the sum of the RAM banks leaves
    /// 64 bits.
    Overflow,
    /// A managed window whose ends are not on 4 KiB pages, or RAM banks
    /// without one complete page.
    Alignment,
    /// No RAM bank or more than 32, no boot storage or more than 4 spans of
    /// it, or more than 128 firmware reservations.
    Capacity,
    /// Two RAM banks share an address, two spans of boot storage share a
    /// page, or a firmware reservation shares a page with boot storage.
    Overlap,
    /// The pages of a boot storage span, or a managed window, lie outside
    /// every single RAM bank.
    OutsideRam,
    /// A managed window above 128 MiB, or RAM banks of more than 16 GiB
    /// together.
    ArenaTooLarge,
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

/// A span that the kernel does not hand out, with the flags `no-map` and
/// `reusable`: an entry of the reservation map, which counts as `no-map`, or
/// a span of the `reg` of an enabled child of `/reserved-memory`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReservedRegion {
    /// The addresses of the region.
    pub span: Span,
    /// Whether the region is not to be mapped as part of the standard
    /// mapping of system memory.
    pub no_map: bool,
    /// Whether the operating system may use the region; it stays reserved.
    pub reusable: bool,
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

/// The result of [`Fdt::discover_memory`]: the RAM ranges, the reserved
/// regions and the number of dynamic reservations of a tree.
#[derive(Debug)]
pub struct MemoryMap {
    /// The RAM ranges, in tree order.
    ram: [Span; RAM_RANGES],
    /// The number of RAM ranges.
    ram_count: usize,
    /// The reserved regions: those of the reservation map, then those of
    /// `/reserved-memory` in tree order.
    reserved: [ReservedRegion; RESERVED_REGIONS],
    /// The number of reserved regions.
    reserved_count: usize,
    /// The number of dynamic reservations.
    dynamic: u64,
}

/// The result of [`Fdt::discover_pi5_boot_memory`]: the memory map of a
/// Pi 5 hand-over tree, checked against the spans of the image and of the
/// tree.
#[derive(Debug)]
pub struct Pi5BootMemory {
    /// The memory map of the tree.
    memory: MemoryMap,
    /// The span of the tree.
    dtb: Span,
    /// The span of the image with its BSS and stacks.
    image: Span,
    /// The sum of the RAM ranges.
    ram_bytes: u64,
}

/// The PSCI conduit of a CPU profile.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PsciConduit {
    /// The hypervisor call.
    Hvc,
    /// The secure monitor call.
    Smc,
}

/// The CPU profile of a board: it fixes the affinity level of the CPU IDs
/// and the PSCI conduit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CpuProfile {
    /// QEMU virt with PSCI over HVC.
    QemuHvc,
    /// QEMU virt with EL2 and PSCI over SMC.
    QemuSmc,
    /// The Raspberry Pi 5.
    Pi5,
}

/// The result of [`Fdt::discover_cpus`]: the profile and the number of
/// CPUs, whose logical IDs are 0 to `count - 1`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CpuTopology {
    /// The profile.
    profile: CpuProfile,
    /// The number of CPUs: 1, 2 or 4.
    count: u64,
}

/// The boot memory map: the RAM banks, sorted by their start; the boot
/// storage and the firmware reservations, each rounded outward to whole
/// 4 KiB pages; and the managed banks, the complete pages of the banks that
/// it manages.
#[derive(Debug)]
pub struct MemoryPlan {
    /// The RAM banks, sorted by their start.
    ram: [Span; BANKS],
    /// The number of RAM banks.
    ram_count: usize,
    /// The managed banks, in address order.
    managed: [Span; BANKS],
    /// The number of managed banks.
    managed_count: usize,
    /// The pages of the boot storage and then those of the firmware
    /// reservations, each in input order.
    reserved: [Span; BOOT_SPANS + FIRMWARE],
    /// The number of spans of boot storage.
    boot_count: usize,
    /// The number of reservations.
    reserved_count: usize,
}

/// The position of an iterator of usable ranges.
#[derive(Clone, Copy, Debug)]
struct Cursor {
    /// The index of the managed bank.
    bank: usize,
    /// The address from which it looks for the next usable range.
    at: u64,
}

/// The iterator of [`MemoryPlan::available_ranges`]: the usable ranges in
/// address order.
#[derive(Clone, Copy, Debug)]
pub struct AvailableRanges<'a> {
    /// The managed banks of the map.
    managed: &'a [Span],
    /// The reservations of the map.
    reservations: &'a [Span],
    /// Its position.
    cursor: Cursor,
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
