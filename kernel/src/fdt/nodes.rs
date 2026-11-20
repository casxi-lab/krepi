//! The node access of a tree that the parse accepted: the walk over its
//! nodes, the lookup of an absolute path, and of a node its name, parent,
//! properties, string properties, status, cell counts, `reg`, `ranges` and
//! `dma-ranges`, with the translation of a span up to the root.
//!
//! Feature: krepi.platform.device-tree
//!
//! The functions with a loop take the blocks of the tree as byte slices
//! and give offsets into them; the entries on a [`Fdt`] or a [`Node`] call
//! them and form the slices and views that they return. A walk reads only
//! the tokens that the parse checked, so it never meets an error of the
//! format; where an index would leave a block, it ends.

use super::format::{align4, find_nul, is_utf8, name_at, same_bytes, u32_at, u64_at};
use super::translation::{check_map, check_reg, translate_map};
use super::{
    AddressMap, DEPTH, Error, Fdt, Node, NodeAt, Nodes, Reg, Reservations, Span, TOKENS, Walker,
};

/// A token of a checked structure block, read without checking it again.
#[derive(Clone, Copy)]
pub(super) enum Piece {
    /// A begin node, whose name ends at `name_end`.
    Begin {
        /// The offset of the NUL after its name.
        name_end: usize,
    },
    /// An end node.
    EndNode,
    /// A property.
    Property {
        /// The offset of its name in the strings block.
        name: usize,
        /// The offset of its value.
        value_start: usize,
        /// The offset after its value.
        value_end: usize,
    },
    /// A no-operation.
    Nop,
    /// The end token.
    End,
}

/// The token at `cursor` of the structure block and the offset of the next,
/// or none where the block ends.
pub(super) fn piece_at(structure: &[u8], cursor: usize) -> Option<(Piece, usize)> {
    let tag = match u32_at(structure, cursor) {
        Ok(tag) => tag,
        Err(_) => return None,
    };
    let next = cursor + 4;
    if tag == 1 {
        return match find_nul(structure, next) {
            Some(nul) => Some((Piece::Begin { name_end: nul }, align4(nul + 1))),
            None => None,
        };
    }
    if tag == 3 {
        let length = match u32_at(structure, next) {
            Ok(length) => length as usize,
            Err(_) => return None,
        };
        let name = match u32_at(structure, next + 4) {
            Ok(name) => name as usize,
            Err(_) => return None,
        };
        let value_start = next + 8;
        let value_end = value_start + length;
        if value_end > structure.len() {
            return None;
        }
        let piece = Piece::Property {
            name,
            value_start,
            value_end,
        };
        return Some((piece, align4(value_end)));
    }
    if tag == 2 {
        return Some((Piece::EndNode, next));
    }
    if tag == 4 {
        return Some((Piece::Nop, next));
    }
    Some((Piece::End, next))
}

/// A walk before the first token.
pub(super) const START: Walker = Walker {
    cursor: 0,
    depth: 0,
    ancestors: [0; DEPTH],
};

/// The offset of the begin-node token of the innermost open node of
/// `walker`, none outside every node.
fn innermost(walker: Walker) -> Option<usize> {
    if walker.depth == 0 || walker.depth > DEPTH {
        return None;
    }
    Some(walker.ancestors[walker.depth - 1])
}

/// The next node of a walk and the walk after it, or none at the end of
/// the structure block.
pub(super) fn node_step(structure: &[u8], walker: Walker) -> (Walker, Option<NodeAt>) {
    let mut walker = walker;
    let mut read = 0;
    while read < TOKENS {
        let (piece, next) = match piece_at(structure, walker.cursor) {
            Some(found) => found,
            None => return (walker, None),
        };
        match piece {
            Piece::Begin { name_end } => {
                let node = NodeAt {
                    offset: walker.cursor,
                    properties: next,
                    parent: innermost(walker),
                    name_start: walker.cursor + 4,
                    name_end,
                };
                if walker.depth < DEPTH {
                    walker.ancestors[walker.depth] = walker.cursor;
                }
                walker.depth += 1;
                walker.cursor = next;
                return (walker, Some(node));
            }
            Piece::EndNode => {
                if walker.depth > 0 {
                    walker.depth -= 1;
                }
                walker.cursor = next;
            }
            Piece::End => return (walker, None),
            _ => walker.cursor = next,
        }
        read += 1;
    }
    (walker, None)
}

/// The root of a structure block: its first node.
pub(super) fn first_node(structure: &[u8]) -> Option<NodeAt> {
    let (_, root) = node_step(structure, START);
    root
}

/// Whether `node` is a child of the node whose begin-node token is at
/// `parent`.
pub(super) fn is_child(node: NodeAt, parent: usize) -> bool {
    match node.parent {
        Some(offset) => offset == parent,
        None => false,
    }
}

/// The node whose begin-node token is at `offset`.
fn node_at_offset(structure: &[u8], offset: usize) -> Option<NodeAt> {
    let mut walker = START;
    let mut count = 0;
    while count < TOKENS {
        let (next, found) = node_step(structure, walker);
        match found {
            Some(node) => {
                if node.offset == offset {
                    return Some(node);
                }
            }
            None => return None,
        }
        walker = next;
        count += 1;
    }
    None
}

/// The parent of `node`, none for the root.
pub(super) fn parent_at(structure: &[u8], node: NodeAt) -> Option<NodeAt> {
    match node.parent {
        Some(offset) => node_at_offset(structure, offset),
        None => None,
    }
}

/// The child of the node at `parent` whose name is `[start, end)` of `path`:
/// none when no child has it, and `AmbiguousMapping` when two have.
fn child_named(
    structure: &[u8],
    parent: usize,
    path: &[u8],
    start: usize,
    end: usize,
) -> Result<Option<NodeAt>, Error> {
    let name = &path[start..end];
    let mut walker = START;
    let mut found = None;
    let mut seen = false;
    let mut count = 0;
    while count < TOKENS {
        let (next, node) = node_step(structure, walker);
        match node {
            Some(node) => {
                if is_child(node, parent)
                    && same_bytes(structure, node.name_start, node.name_end, name)
                {
                    if seen {
                        return Err(Error::AmbiguousMapping);
                    }
                    found = Some(node);
                    seen = true;
                }
            }
            None => return Ok(found),
        }
        walker = next;
        count += 1;
    }
    Ok(found)
}

/// Whether `path` holds `//`.
fn double_slash(path: &[u8]) -> bool {
    let mut index = 1;
    while index < path.len() {
        if path[index - 1] == b'/' && path[index] == b'/' {
            return true;
        }
        index += 1;
    }
    false
}

/// Whether `path` has the form that [`Fdt::find_node`] takes: it starts with
/// `/`, ends in `/` only when it is the root, and holds no `//`.
fn path_valid(path: &[u8]) -> bool {
    if path.is_empty() || path[0] != b'/' {
        return false;
    }
    if path.len() > 1 && path[path.len() - 1] == b'/' {
        return false;
    }
    !double_slash(path)
}

/// The end of the component of `path` that starts at `start`: the next `/`
/// or the end of the path.
fn component_end(path: &[u8], start: usize) -> usize {
    let mut index = start;
    while index < path.len() {
        if path[index] == b'/' {
            return index;
        }
        index += 1;
    }
    path.len()
}

/// The node of the components of `path` from `start` below `current`: for
/// each component, the child of the node so far with its name, of which two
/// fail with `AmbiguousMapping` and none give none.
fn descend(
    structure: &[u8],
    path: &[u8],
    start: usize,
    current: Option<NodeAt>,
) -> Result<Option<NodeAt>, Error> {
    let mut start = start;
    let mut current = current;
    while start <= path.len() {
        let end = component_end(path, start);
        current = match current {
            Some(node) => child_named(structure, node.offset, path, start, end)?,
            None => return Ok(None),
        };
        start = end + 1;
    }
    Ok(current)
}

/// The node of `path`, a path of the form that [`path_valid`] accepts.
pub(super) fn find_path(structure: &[u8], path: &[u8]) -> Result<Option<NodeAt>, Error> {
    let root = first_node(structure);
    if path.len() == 1 {
        return Ok(root);
    }
    descend(structure, path, 1, root)
}

/// The node of `found` in `tree`.
fn node_of(tree: Fdt<'_>, found: Option<NodeAt>) -> Option<Node<'_>> {
    match found {
        Some(at) => Some(Node { tree, at }),
        None => None,
    }
}

/// The offsets `[start, end)` of the value of the property `name` of the
/// node whose properties start at `from`, or none.
fn property_range(
    structure: &[u8],
    strings: &[u8],
    from: usize,
    name: &[u8],
) -> Option<(usize, usize)> {
    let mut cursor = from;
    let mut read = 0;
    while read < TOKENS {
        match piece_at(structure, cursor) {
            Some((
                Piece::Property {
                    name: offset,
                    value_start,
                    value_end,
                },
                next,
            )) => {
                if name_at(strings, offset, name) {
                    return Some((value_start, value_end));
                }
                cursor = next;
            }
            Some((Piece::Nop, next)) => cursor = next,
            _ => return None,
        }
        read += 1;
    }
    None
}

/// The offsets of the value of the property `name` of `node`, or none.
pub(super) fn value_at(
    structure: &[u8],
    strings: &[u8],
    node: NodeAt,
    name: &[u8],
) -> Option<(usize, usize)> {
    property_range(structure, strings, node.properties, name)
}

/// The offsets of the string of the property `name` of `node`, before its
/// NUL, or none without the property: a value without a NUL, or whose bytes
/// before the NUL are not UTF-8, `BadString`; then a byte after the NUL,
/// `BadProperty`.
pub(super) fn string_at(
    structure: &[u8],
    strings: &[u8],
    node: NodeAt,
    name: &[u8],
) -> Result<Option<(usize, usize)>, Error> {
    let (start, end) = match value_at(structure, strings, node, name) {
        Some(range) => range,
        None => return Ok(None),
    };
    let value = &structure[start..end];
    let nul = match find_nul(value, 0) {
        Some(nul) => nul,
        None => return Err(Error::BadString),
    };
    if !is_utf8(value, 0, nul) {
        return Err(Error::BadString);
    }
    if nul + 1 != value.len() {
        return Err(Error::BadProperty);
    }
    Ok(Some((start, start + nul)))
}

/// Whether `node` is enabled: its `status` is absent, `okay` or `ok`, with
/// the errors of [`string_at`].
pub(super) fn enabled_at(structure: &[u8], strings: &[u8], node: NodeAt) -> Result<bool, Error> {
    match string_at(structure, strings, node, b"status")? {
        Some((start, end)) => {
            Ok(same_bytes(structure, start, end, b"okay")
                || same_bytes(structure, start, end, b"ok"))
        }
        None => Ok(true),
    }
}

/// The cell count `name` of the node's own: `default` when the property is
/// absent, the value of 4 bytes, or `BadProperty` for a value of another
/// length.
pub(super) fn cells_at(
    structure: &[u8],
    strings: &[u8],
    node: NodeAt,
    name: &[u8],
    default: u32,
) -> Result<u32, Error> {
    match value_at(structure, strings, node, name) {
        Some((start, end)) => {
            if end - start != 4 {
                return Err(Error::BadProperty);
            }
            u32_at(structure, start)
        }
        None => Ok(default),
    }
}

/// The `#address-cells` of `node`, 2 when absent.
pub(super) fn address_cells_at(
    structure: &[u8],
    strings: &[u8],
    node: NodeAt,
) -> Result<u32, Error> {
    cells_at(structure, strings, node, b"#address-cells", 2)
}

/// The `#size-cells` of `node`, 1 when absent.
pub(super) fn size_cells_at(structure: &[u8], strings: &[u8], node: NodeAt) -> Result<u32, Error> {
    cells_at(structure, strings, node, b"#size-cells", 1)
}

/// A `reg` value that [`check_reg`] accepted: its offsets and its cells.
#[derive(Clone, Copy)]
pub(super) struct RegAt {
    /// The offset of the value.
    pub(super) start: usize,
    /// The offset after the value.
    pub(super) end: usize,
    /// The cells of an address.
    pub(super) address_cells: u32,
    /// The cells of a size.
    pub(super) size_cells: u32,
}

/// The `reg` of `node` in the cells of its parent: the root, which has no
/// parent, `BadTree`; no `reg`, `MissingProperty`; the address cells and
/// then the size cells of the parent, `BadProperty`; then the rules of
/// [`Reg::new`].
pub(super) fn reg_at(structure: &[u8], strings: &[u8], node: NodeAt) -> Result<RegAt, Error> {
    let parent = match parent_at(structure, node) {
        Some(parent) => parent,
        None => return Err(Error::BadTree),
    };
    let (start, end) = match value_at(structure, strings, node, b"reg") {
        Some(range) => range,
        None => return Err(Error::MissingProperty),
    };
    let address_cells = address_cells_at(structure, strings, parent)?;
    let size_cells = size_cells_at(structure, strings, parent)?;
    check_reg(&structure[start..end], address_cells, size_cells)?;
    Ok(RegAt {
        start,
        end,
        address_cells,
        size_cells,
    })
}

/// An address map that [`check_map`] accepted: its offsets, whether its
/// property is present, and its cells.
#[derive(Clone, Copy)]
struct MapAt {
    /// The offset of the value; that of the node when the property is
    /// absent.
    start: usize,
    /// The offset after the value.
    end: usize,
    /// Whether the property is present.
    present: bool,
    /// The cells of a child address.
    child_cells: u32,
    /// The cells of a parent address.
    parent_cells: u32,
    /// The cells of a size.
    size_cells: u32,
}

/// The map of the property `name` of `node`, whose parent is `parent`, with
/// the node's own address cells on the child side, its parent's on the
/// parent side and the node's own size cells: each of the three counts,
/// `BadProperty`; then the rules of [`AddressMap::new`].
fn map_at(
    structure: &[u8],
    strings: &[u8],
    node: NodeAt,
    parent: NodeAt,
    name: &[u8],
) -> Result<MapAt, Error> {
    let (start, end, present) = match value_at(structure, strings, node, name) {
        Some((start, end)) => (start, end, true),
        None => (node.offset, node.offset, false),
    };
    let child_cells = address_cells_at(structure, strings, node)?;
    let parent_cells = address_cells_at(structure, strings, parent)?;
    let size_cells = size_cells_at(structure, strings, node)?;
    check_map(
        &structure[start..end],
        present,
        child_cells,
        parent_cells,
        size_cells,
    )?;
    Ok(MapAt {
        start,
        end,
        present,
        child_cells,
        parent_cells,
        size_cells,
    })
}

/// The span `span` of the bus `bus` translated through the `ranges` of
/// `bus` and of each bus above it, the nearest first, up to the root, which
/// translates nothing; at most [`MAX_DEPTH`](super::MAX_DEPTH) buses.
fn climb(structure: &[u8], strings: &[u8], bus: NodeAt, span: Span) -> Result<Span, Error> {
    let mut bus = bus;
    let mut span = span;
    let mut steps = 0;
    while steps < DEPTH {
        let up = match parent_at(structure, bus) {
            Some(up) => up,
            None => return Ok(span),
        };
        let map = map_at(structure, strings, bus, up, b"ranges")?;
        span = translate_map(
            &structure[map.start..map.end],
            map.present,
            map.child_cells,
            map.parent_cells,
            map.size_cells,
            span,
            false,
        )?;
        bus = up;
        steps += 1;
    }
    Err(Error::LimitExceeded)
}

/// The reservation entry at `cursor` of `entries` and the offset of the
/// next, or none after the last.
fn reservation_step(entries: &[u8], cursor: usize) -> (usize, Option<Span>) {
    let start = match u64_at(entries, cursor) {
        Ok(start) => start,
        Err(_) => return (cursor, None),
    };
    let size = match u64_at(entries, cursor + 8) {
        Ok(size) => size,
        Err(_) => return (cursor, None),
    };
    (cursor + 16, Some(Span { start, size }))
}

impl<'a> Fdt<'a> {
    /// Every node of the tree, in the order of the structure block.
    pub fn nodes(self) -> Nodes<'a> {
        Nodes {
            tree: self,
            walker: START,
        }
    }

    /// The node of an absolute path with exact unit addresses, `/` for the
    /// root: a path that does not start with `/`, ends in `/` other than the
    /// root or holds `//`, `BadPath`; then each component in order, one that
    /// matches two sibling nodes, `AmbiguousMapping`; a path that matches
    /// nothing gives none. Aliases and abbreviated names are not resolved.
    pub fn find_node(self, path: &str) -> Result<Option<Node<'a>>, Error> {
        let path = path.as_bytes();
        if !path_valid(path) {
            return Err(Error::BadPath);
        }
        let found = find_path(self.structure, path)?;
        Ok(node_of(self, found))
    }
}

impl<'a> Nodes<'a> {
    /// The next node, or none after the last. The walk reads only the tokens
    /// that the parse checked and does not fail.
    // The iterator implements `next` alone: the provided methods of
    // `Iterator` would reach library functions without a model.
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Option<Node<'a>> {
        let (walker, found) = node_step(self.tree.structure, self.walker);
        self.walker = walker;
        node_of(self.tree, found)
    }
}

impl Reservations<'_> {
    /// The next entry of the reservation map, or none after the last. The
    /// parse checked the entries, so the walk does not fail.
    // The iterator implements `next` alone, as `Nodes::next` does.
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> Option<Span> {
        let (cursor, entry) = reservation_step(self.entries, self.cursor);
        self.cursor = cursor;
        entry
    }
}

impl<'a> Node<'a> {
    /// The name of the node, without its NUL; empty for the root.
    pub fn name(self) -> &'a [u8] {
        &self.tree.structure[self.at.name_start..self.at.name_end]
    }

    /// The parent of the node, none for the root.
    pub fn parent(self) -> Option<Node<'a>> {
        node_of(self.tree, parent_at(self.tree.structure, self.at))
    }

    /// The value of the property `name` of the node, or none.
    pub fn property(self, name: &str) -> Option<&'a [u8]> {
        match value_at(
            self.tree.structure,
            self.tree.strings,
            self.at,
            name.as_bytes(),
        ) {
            Some((start, end)) => Some(&self.tree.structure[start..end]),
            None => None,
        }
    }

    /// The bytes of the string of the property `name`, before its NUL, or
    /// none without the property: a value without a NUL, or whose bytes
    /// before the NUL are not UTF-8, `BadString`; then a byte after the NUL,
    /// `BadProperty`.
    pub fn string_property(self, name: &str) -> Result<Option<&'a [u8]>, Error> {
        match string_at(
            self.tree.structure,
            self.tree.strings,
            self.at,
            name.as_bytes(),
        )? {
            Some((start, end)) => Ok(Some(&self.tree.structure[start..end])),
            None => Ok(None),
        }
    }

    /// Whether the node is enabled: its `status` is absent, `okay` or `ok`,
    /// with the errors of [`Node::string_property`].
    pub fn enabled(self) -> Result<bool, Error> {
        enabled_at(self.tree.structure, self.tree.strings, self.at)
    }

    /// The node's own `#address-cells`, 2 when absent, or `BadProperty` for
    /// a value that is not 4 bytes; never inherited.
    pub fn address_cells(self) -> Result<u32, Error> {
        address_cells_at(self.tree.structure, self.tree.strings, self.at)
    }

    /// The node's own `#size-cells`, 1 when absent, or `BadProperty` for a
    /// value that is not 4 bytes; never inherited.
    pub fn size_cells(self) -> Result<u32, Error> {
        size_cells_at(self.tree.structure, self.tree.strings, self.at)
    }

    /// The `reg` of the node in the cells of its parent: the root,
    /// `BadTree`; no `reg`, `MissingProperty`; the address cells and then
    /// the size cells of the parent, `BadProperty`; then the rules of
    /// [`Reg::new`].
    pub fn reg(self) -> Result<Reg<'a>, Error> {
        let reg = reg_at(self.tree.structure, self.tree.strings, self.at)?;
        Ok(Reg {
            bytes: &self.tree.structure[reg.start..reg.end],
            address_cells: reg.address_cells,
            size_cells: reg.size_cells,
            cursor: 0,
        })
    }

    /// The `ranges` of the node, the translation of CPU addresses below it.
    pub fn ranges(self) -> Result<AddressMap<'a>, Error> {
        self.address_map(b"ranges")
    }

    /// The `dma-ranges` of the node, the separate map of the addresses that
    /// devices below it use; absent when the node has none.
    pub fn dma_ranges(self) -> Result<AddressMap<'a>, Error> {
        self.address_map(b"dma-ranges")
    }

    /// The map of the property `name`: the root, `BadTree`; then the rules
    /// of [`map_at`].
    fn address_map(self, name: &[u8]) -> Result<AddressMap<'a>, Error> {
        let parent = match parent_at(self.tree.structure, self.at) {
            Some(parent) => parent,
            None => return Err(Error::BadTree),
        };
        let map = map_at(
            self.tree.structure,
            self.tree.strings,
            self.at,
            parent,
            name,
        )?;
        Ok(AddressMap {
            bytes: &self.tree.structure[map.start..map.end],
            present: map.present,
            child_cells: map.child_cells,
            parent_cells: map.parent_cells,
            size_cells: map.size_cells,
        })
    }

    /// A span of the node's parent bus as a CPU address, through the
    /// `ranges` of each bus above the node: the root, which has no parent
    /// bus, `BadTree`; then each bus from the nearest; a result whose end
    /// leaves 64 bits, `Overflow`.
    pub fn translate_reg(self, span: Span) -> Result<Span, Error> {
        let bus = match parent_at(self.tree.structure, self.at) {
            Some(bus) => bus,
            None => return Err(Error::BadTree),
        };
        let translated = climb(self.tree.structure, self.tree.strings, bus, span)?;
        translated.end()?;
        Ok(translated)
    }
}
