//! The memory discovery of a tree: the RAM ranges of the enabled memory
//! nodes below the root, the reserved regions of the reservation map and of
//! the static children of `/reserved-memory`, and the number of dynamic
//! reservations.
//!
//! Feature: krepi.platform.device-tree
//!
//! The discovery fills a local memory map while it checks, in the order of
//! step 4 of the contract's error order, and returns it only when every
//! rule holds; on a failure the caller receives the error alone. A dynamic
//! reservation, an enabled child of `/reserved-memory` with `size` and
//! without `reg`, is counted and is no error and no reserved region; its
//! `size` and `alloc-ranges` are not read.

use super::format::{same_bytes, starts_with, u64_at};
use super::nodes::{
    START, address_cells_at, enabled_at, find_path, first_node, flag_at, has_property, is_child,
    node_step, reg_at, size_cells_at, string_at, value_at,
};
use super::span::{EMPTY, prefix, touches_any};
use super::translation::{reg_entry, reg_stride};
use super::{
    Error, Fdt, MemoryMap, NodeAt, RAM_RANGES, RESERVED_REGIONS, ReservedRegion, Span, TOKENS,
};

/// The region with which the memory map fills its table.
const NO_REGION: ReservedRegion = ReservedRegion {
    span: EMPTY,
    no_map: false,
    reusable: false,
};

/// The memory map before the discovery adds anything.
const NO_MEMORY: MemoryMap = MemoryMap {
    ram: [EMPTY; RAM_RANGES],
    ram_count: 0,
    reserved: [NO_REGION; RESERVED_REGIONS],
    reserved_count: 0,
    dynamic: 0,
};

impl MemoryMap {
    /// The RAM ranges, in tree order.
    pub fn ram(&self) -> &[Span] {
        prefix(&self.ram, self.ram_count)
    }

    /// The reserved regions: those of the reservation map, in its order,
    /// and then those of `/reserved-memory`, in tree order.
    pub fn reserved(&self) -> &[ReservedRegion] {
        prefix(&self.reserved, self.reserved_count)
    }

    /// The number of dynamic reservations.
    pub fn dynamic(&self) -> u64 {
        self.dynamic
    }
}

impl Fdt<'_> {
    /// The RAM ranges, the reserved regions and the dynamic reservations of
    /// the tree, or the error of the first rule that it breaks: the entries
    /// of the reservation map, in order, as reserved regions, beyond
    /// [`MAX_RESERVED_REGIONS`](super::MAX_RESERVED_REGIONS)
    /// `LimitExceeded`; the children of the root, in tree order, with their
    /// memory bindings; no RAM range, `NoMemory`; then `/reserved-memory`
    /// with its binding, its `status` and its children.
    pub fn discover_memory(self) -> Result<MemoryMap, Error> {
        let mut map = NO_MEMORY;
        add_map_entries(&mut map, self.reservations)?;
        let root = match first_node(self.structure) {
            Some(root) => root,
            None => return Err(Error::BadTree),
        };
        add_ram_children(&mut map, self.structure, self.strings, root)?;
        if map.ram_count == 0 {
            return Err(Error::NoMemory);
        }
        add_reserved_memory(&mut map, self.structure, self.strings, root)?;
        Ok(map)
    }
}

/// One reserved region added after those of `map`: beyond
/// [`MAX_RESERVED_REGIONS`](super::MAX_RESERVED_REGIONS) regions,
/// `LimitExceeded`.
fn push_reserved(map: &mut MemoryMap, region: ReservedRegion) -> Result<(), Error> {
    if map.reserved_count >= RESERVED_REGIONS {
        return Err(Error::LimitExceeded);
    }
    map.reserved[map.reserved_count] = region;
    map.reserved_count += 1;
    Ok(())
}

/// The entries of the reservation map, in order, as reserved regions with
/// `no-map` set and `reusable` clear.
fn add_map_entries(map: &mut MemoryMap, entries: &[u8]) -> Result<(), Error> {
    let mut at = 0;
    while at < entries.len() {
        let span = Span {
            start: u64_at(entries, at)?,
            size: u64_at(entries, at + 8)?,
        };
        let region = ReservedRegion {
            span,
            no_map: true,
            reusable: false,
        };
        push_reserved(map, region)?;
        at += 16;
    }
    Ok(())
}

/// One RAM range added after those of `map`: of size 0, `EmptyRegion`;
/// sharing an address with an earlier range, `Overlap`; beyond
/// [`MAX_MEMORY_REGIONS`](super::MAX_MEMORY_REGIONS) ranges,
/// `LimitExceeded`.
fn add_ram(map: &mut MemoryMap, span: Span) -> Result<(), Error> {
    if span.size == 0 {
        return Err(Error::EmptyRegion);
    }
    if touches_any(prefix(&map.ram, map.ram_count), span) {
        return Err(Error::Overlap);
    }
    if map.ram_count >= RAM_RANGES {
        return Err(Error::LimitExceeded);
    }
    map.ram[map.ram_count] = span;
    map.ram_count += 1;
    Ok(())
}

/// Each span of a checked `reg` value as a RAM range, in order.
fn add_ram_entries(
    map: &mut MemoryMap,
    bytes: &[u8],
    address_cells: u32,
    size_cells: u32,
) -> Result<(), Error> {
    let stride = reg_stride(address_cells, size_cells);
    let mut at = 0;
    while at < bytes.len() {
        let span = reg_entry(bytes, at, address_cells, size_cells)?;
        add_ram(map, span)?;
        at += stride;
    }
    Ok(())
}

/// Whether the name at `[start, end)` of the structure block is a memory
/// name: `memory`, or a name that starts with `memory@`.
fn memory_name(structure: &[u8], start: usize, end: usize) -> bool {
    same_bytes(structure, start, end, b"memory") || starts_with(structure, start, end, b"memory@")
}

/// One child of the root: its `device_type`; a child that has neither a
/// memory name nor the `device_type` `memory` is no memory node. A memory
/// node: its `status`, and a disabled one is skipped before its binding is
/// checked; then an enabled one without both the memory name and the
/// `device_type` `memory`, `BadProperty`; its whole `reg`, in the cells of
/// the root; then each of its ranges in order.
fn ram_of_child(
    map: &mut MemoryMap,
    structure: &[u8],
    strings: &[u8],
    node: NodeAt,
) -> Result<(), Error> {
    let device_type = string_at(structure, strings, node, b"device_type")?;
    let by_name = memory_name(structure, node.name_start, node.name_end);
    let by_type = match device_type {
        Some((start, end)) => same_bytes(structure, start, end, b"memory"),
        None => false,
    };
    if !by_name && !by_type {
        return Ok(());
    }
    if !enabled_at(structure, strings, node)? {
        return Ok(());
    }
    if !by_name || !by_type {
        return Err(Error::BadProperty);
    }
    let reg = reg_at(structure, strings, node)?;
    add_ram_entries(
        map,
        &structure[reg.start..reg.end],
        reg.address_cells,
        reg.size_cells,
    )
}

/// The children of the root, in tree order, as memory nodes.
fn add_ram_children(
    map: &mut MemoryMap,
    structure: &[u8],
    strings: &[u8],
    root: NodeAt,
) -> Result<(), Error> {
    let mut walker = START;
    let mut count = 0;
    while count < TOKENS {
        let (next, found) = node_step(structure, walker);
        match found {
            Some(node) => {
                if is_child(node, root.offset) {
                    ram_of_child(map, structure, strings, node)?;
                }
            }
            None => return Ok(()),
        }
        walker = next;
        count += 1;
    }
    Ok(())
}

/// The binding of `/reserved-memory`, the node `parent`: its own
/// `#address-cells` and `#size-cells`, present and equal to those of the
/// root, and an empty `ranges`; any other, `BadProperty`.
fn reserved_memory_binding(
    structure: &[u8],
    strings: &[u8],
    parent: NodeAt,
    root: NodeAt,
) -> Result<(), Error> {
    if !has_property(structure, strings, parent, b"#address-cells")
        || !has_property(structure, strings, parent, b"#size-cells")
    {
        return Err(Error::BadProperty);
    }
    if address_cells_at(structure, strings, parent)? != address_cells_at(structure, strings, root)?
    {
        return Err(Error::BadProperty);
    }
    if size_cells_at(structure, strings, parent)? != size_cells_at(structure, strings, root)? {
        return Err(Error::BadProperty);
    }
    match value_at(structure, strings, parent, b"ranges") {
        Some((start, end)) => {
            if start != end {
                return Err(Error::BadProperty);
            }
            Ok(())
        }
        None => Err(Error::BadProperty),
    }
}

/// Each span of a checked `reg` value as a reserved region with the flags
/// of its node: of size 0, `EmptyRegion`; then the capacity.
fn add_reserved_entries(
    map: &mut MemoryMap,
    bytes: &[u8],
    address_cells: u32,
    size_cells: u32,
    no_map: bool,
    reusable: bool,
) -> Result<(), Error> {
    let stride = reg_stride(address_cells, size_cells);
    let mut at = 0;
    while at < bytes.len() {
        let span = reg_entry(bytes, at, address_cells, size_cells)?;
        if span.size == 0 {
            return Err(Error::EmptyRegion);
        }
        let region = ReservedRegion {
            span,
            no_map,
            reusable,
        };
        push_reserved(map, region)?;
        at += stride;
    }
    Ok(())
}

/// One child of an enabled `/reserved-memory`: its `status`, and a disabled
/// child is skipped; its flags `no-map` and `reusable`, each without a
/// value, and not both, `BadProperty`; neither `reg` nor `size`,
/// `MissingProperty`; `size` without `reg`, a dynamic reservation, which is
/// counted and whose `size` is not read; otherwise its whole `reg`, in the
/// cells of `/reserved-memory`, and each of its spans in order.
fn reserved_of_child(
    map: &mut MemoryMap,
    structure: &[u8],
    strings: &[u8],
    node: NodeAt,
) -> Result<(), Error> {
    if !enabled_at(structure, strings, node)? {
        return Ok(());
    }
    let no_map = flag_at(structure, strings, node, b"no-map")?;
    let reusable = flag_at(structure, strings, node, b"reusable")?;
    if no_map && reusable {
        return Err(Error::BadProperty);
    }
    if !has_property(structure, strings, node, b"reg") {
        if !has_property(structure, strings, node, b"size") {
            return Err(Error::MissingProperty);
        }
        map.dynamic += 1;
        return Ok(());
    }
    let reg = reg_at(structure, strings, node)?;
    add_reserved_entries(
        map,
        &structure[reg.start..reg.end],
        reg.address_cells,
        reg.size_cells,
        no_map,
        reusable,
    )
}

/// The children of `/reserved-memory`, the node `parent`, in tree order.
fn add_reserved_children(
    map: &mut MemoryMap,
    structure: &[u8],
    strings: &[u8],
    parent: NodeAt,
) -> Result<(), Error> {
    let mut walker = START;
    let mut count = 0;
    while count < TOKENS {
        let (next, found) = node_step(structure, walker);
        match found {
            Some(node) => {
                if is_child(node, parent.offset) {
                    reserved_of_child(map, structure, strings, node)?;
                }
            }
            None => return Ok(()),
        }
        walker = next;
        count += 1;
    }
    Ok(())
}

/// The reserved regions and the dynamic reservations of `/reserved-memory`:
/// none when the tree has none, and two siblings of that name,
/// `AmbiguousMapping`; otherwise its binding, then its `status`, and a
/// disabled one holds no reservation; then its children in tree order.
fn add_reserved_memory(
    map: &mut MemoryMap,
    structure: &[u8],
    strings: &[u8],
    root: NodeAt,
) -> Result<(), Error> {
    let parent = match find_path(structure, b"/reserved-memory")? {
        Some(parent) => parent,
        None => return Ok(()),
    };
    reserved_memory_binding(structure, strings, parent, root)?;
    if !enabled_at(structure, strings, parent)? {
        return Ok(());
    }
    add_reserved_children(map, structure, strings, parent)
}
