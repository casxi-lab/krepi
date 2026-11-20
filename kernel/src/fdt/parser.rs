//! The parse of a device tree: the header and its blocks, the reservation
//! map entry by entry and every token of the structure block, each checked
//! in the error order of the contract before the parse returns a tree.
//!
//! Feature: krepi.platform.device-tree

use super::format::{
    HEADER_SIZE, MAGIC, c_string, intersects, name_at, name_bytes, padded_end, u32_at, u64_at,
};
use super::nodes::{Piece, piece_at};
use super::span::overlaps;
use super::{
    DEPTH, Error, Fdt, MAX_BLOB_SIZE, MAX_PROPERTIES, MAX_PROPERTY_NAME, MAX_RESERVATIONS,
    Reservations, Span, TOKENS,
};

/// The offsets of the blocks of a tree, read from its header.
#[derive(Clone, Copy)]
struct Layout {
    /// `totalsize`.
    total: usize,
    /// The start of the structure block.
    structure: usize,
    /// The end of the structure block.
    structure_end: usize,
    /// The start of the strings block.
    strings: usize,
    /// The end of the strings block.
    strings_end: usize,
    /// The start of the reservation map.
    reservations: usize,
}

/// A token of the structure block, decoded and checked.
#[derive(Clone, Copy)]
enum Token {
    /// A begin node with an empty name or with one.
    Begin {
        /// Whether its name is empty.
        empty: bool,
    },
    /// An end node.
    EndNode,
    /// A property whose name lies at `[name, name_end)` of the strings
    /// block.
    Property {
        /// The offset of its name.
        name: usize,
        /// The offset of the NUL after its name.
        name_end: usize,
    },
    /// A no-operation.
    Nop,
    /// The end token.
    End,
}

/// An open node of the walk over the tokens: where its properties start,
/// how many it has so far and whether a child has begun in it.
#[derive(Clone, Copy)]
struct Frame {
    /// The offset of the token after its begin-node token.
    properties: usize,
    /// The number of its properties so far.
    count: u64,
    /// Whether a child has begun in it.
    children: bool,
}

/// The state of the walk over the tokens: the open nodes, innermost last,
/// and whether the root has begun.
struct Walk {
    /// The open nodes.
    frames: [Frame; DEPTH],
    /// The number of open nodes.
    open: usize,
    /// Whether the root has begun.
    seen_root: bool,
}

/// The frame with which the walk fills its table.
const NO_FRAME: Frame = Frame {
    properties: 0,
    count: 0,
    children: false,
};

impl<'a> Fdt<'a> {
    /// The tree of the device tree in `input`, or the error of the first
    /// rule that it breaks: the header and the blocks, then the reservation
    /// map, then every token of the structure block. Only the first
    /// `totalsize` bytes belong to the tree.
    pub fn parse(input: &'a [u8]) -> Result<Fdt<'a>, Error> {
        let layout = header(input)?;
        let blob = &input[0..layout.total];
        let terminator = reservation_map(blob, layout)?;
        let structure = &blob[layout.structure..layout.structure_end];
        let strings = &blob[layout.strings..layout.strings_end];
        walk_tokens(structure, strings)?;
        Ok(Fdt {
            blob,
            structure,
            strings,
            reservations: &blob[layout.reservations..terminator],
        })
    }

    /// The `totalsize` of the tree.
    pub fn total_size(self) -> u64 {
        self.blob.len() as u64
    }

    /// The entries of the reservation map, in their order.
    pub fn reservations(self) -> Reservations<'a> {
        Reservations {
            entries: self.reservations,
            cursor: 0,
        }
    }
}

/// The block of `size` bytes at `start` of the tree `blob`: `BadLayout` when
/// it starts inside the header, `Overflow` when its end leaves 64 bits and
/// `Truncated` when it ends past the tree; otherwise its end.
fn block(blob: &[u8], start: usize, size: usize) -> Result<usize, Error> {
    if start < HEADER_SIZE {
        return Err(Error::BadLayout);
    }
    let end = match start.checked_add(size) {
        Some(end) => end,
        None => return Err(Error::Overflow),
    };
    if blob.len() < end {
        return Err(Error::Truncated);
    }
    Ok(end)
}

/// Step 1 of the error order: the header and the blocks.
fn header(input: &[u8]) -> Result<Layout, Error> {
    if input.len() < HEADER_SIZE {
        return Err(Error::Truncated);
    }
    if u32_at(input, 0)? != MAGIC {
        return Err(Error::BadMagic);
    }
    let total = u32_at(input, 4)? as usize;
    if total < HEADER_SIZE {
        return Err(Error::BadLayout);
    }
    if total as u64 > MAX_BLOB_SIZE {
        return Err(Error::LimitExceeded);
    }
    if input.len() < total {
        return Err(Error::Truncated);
    }
    let blob = &input[0..total];
    let version = u32_at(blob, 20)?;
    let compatible = u32_at(blob, 24)?;
    if version < 17 || (compatible != 16 && compatible != 17) || version < compatible {
        return Err(Error::UnsupportedVersion);
    }
    let structure = u32_at(blob, 8)? as usize;
    let strings = u32_at(blob, 12)? as usize;
    let reservations = u32_at(blob, 16)? as usize;
    let strings_size = u32_at(blob, 32)? as usize;
    let structure_size = u32_at(blob, 36)? as usize;
    if structure % 4 != 0 || structure_size % 4 != 0 || reservations % 8 != 0 {
        return Err(Error::BadAlignment);
    }
    let structure_end = block(blob, structure, structure_size)?;
    let strings_end = block(blob, strings, strings_size)?;
    if structure_size < 12 || reservations < HEADER_SIZE {
        return Err(Error::BadLayout);
    }
    if intersects(structure, structure_end, strings, strings_end) {
        return Err(Error::BadLayout);
    }
    Ok(Layout {
        total,
        structure,
        structure_end,
        strings,
        strings_end,
        reservations,
    })
}

/// Step 2 of the error order: the reservation map, entry by entry, at most
/// [`MAX_RESERVATIONS`] entries and the terminator; the offset of the
/// terminator.
fn reservation_map(blob: &[u8], layout: Layout) -> Result<usize, Error> {
    let mut cursor = layout.reservations;
    let mut count = 0;
    while count <= MAX_RESERVATIONS {
        if reservation_entry(blob, layout, cursor, count)? {
            return Ok(cursor);
        }
        cursor += 16;
        count += 1;
    }
    Err(Error::LimitExceeded)
}

/// The entry at `cursor` after `count` entries, true for the terminator:
/// past the tree, `Overflow` or `Truncated`; on the structure or strings
/// block, `BadLayout`; then, unless it is the terminator, more than
/// [`MAX_RESERVATIONS`] entries, `LimitExceeded`; its end, `Overflow`; its
/// size, `EmptyRegion`; overlap with an earlier entry, `Overlap`.
fn reservation_entry(
    blob: &[u8],
    layout: Layout,
    cursor: usize,
    count: u64,
) -> Result<bool, Error> {
    let end = match cursor.checked_add(16) {
        Some(end) => end,
        None => return Err(Error::Overflow),
    };
    if layout.total < end {
        return Err(Error::Truncated);
    }
    if intersects(cursor, end, layout.structure, layout.structure_end)
        || intersects(cursor, end, layout.strings, layout.strings_end)
    {
        return Err(Error::BadLayout);
    }
    let start = u64_at(blob, cursor)?;
    let size = u64_at(blob, cursor + 8)?;
    if start == 0 && size == 0 {
        return Ok(true);
    }
    if count + 1 > MAX_RESERVATIONS {
        return Err(Error::LimitExceeded);
    }
    let span = Span::new(start, size)?;
    if size == 0 {
        return Err(Error::EmptyRegion);
    }
    if overlaps_earlier(blob, layout.reservations, cursor, span)? {
        return Err(Error::Overlap);
    }
    Ok(false)
}

/// Whether an entry of the reservation map from `first` up to `cursor`
/// shares an address with `span`.
fn overlaps_earlier(blob: &[u8], first: usize, cursor: usize, span: Span) -> Result<bool, Error> {
    let mut earlier = first;
    while earlier < cursor {
        let entry = Span {
            start: u64_at(blob, earlier)?,
            size: u64_at(blob, earlier + 8)?,
        };
        if overlaps(entry, span) {
            return Ok(true);
        }
        earlier += 16;
    }
    Ok(false)
}

/// Step 3 of the error order: the tokens, in the order of the structure
/// block, at most [`MAX_TOKENS`](super::MAX_TOKENS) of them, the end token
/// included. Each token is decoded and then placed in the tree.
fn walk_tokens(structure: &[u8], strings: &[u8]) -> Result<(), Error> {
    let mut walk = Walk {
        frames: [NO_FRAME; DEPTH],
        open: 0,
        seen_root: false,
    };
    let mut cursor = 0;
    let mut read = 0;
    while read < TOKENS {
        let (token, next) = decode_token(structure, strings, cursor)?;
        if place(&mut walk, structure, strings, token, cursor, next)? {
            return Ok(());
        }
        cursor = next;
        read += 1;
    }
    Err(Error::LimitExceeded)
}

/// The token at `cursor` of the structure block and the offset of the next:
/// its tag past the end of the block, `Truncated`; a tag other than 1, 2,
/// 3, 4 and 9, `BadToken`; then the rules of its kind.
fn decode_token(structure: &[u8], strings: &[u8], cursor: usize) -> Result<(Token, usize), Error> {
    let tag = u32_at(structure, cursor)?;
    let next = cursor + 4;
    if tag == 1 {
        return decode_begin(structure, next);
    }
    if tag == 2 {
        return Ok((Token::EndNode, next));
    }
    if tag == 3 {
        return decode_property(structure, strings, next);
    }
    if tag == 4 {
        return Ok((Token::Nop, next));
    }
    if tag == 9 {
        return Ok((Token::End, next));
    }
    Err(Error::BadToken)
}

/// A begin node whose name starts at `start`: its name without a NUL in the
/// block or not UTF-8, `BadString`; the padding after the name past the end
/// of the block, `Truncated`, then a nonzero byte in it, `BadPadding`; then
/// a character of the name outside its set, `BadString`.
fn decode_begin(structure: &[u8], start: usize) -> Result<(Token, usize), Error> {
    let nul = c_string(structure, start)?;
    let next = padded_end(structure, nul + 1, true)?;
    if !name_bytes(structure, start, nul, false) {
        return Err(Error::BadString);
    }
    Ok((
        Token::Begin {
            empty: nul == start,
        },
        next,
    ))
}

/// A property whose header starts at `start`: its length and name offset
/// past the end of the block, `Truncated`; the end of its value beyond
/// 64 bits, `Overflow`, then past the end of the block, `Truncated`; its
/// name, empty, longer than [`MAX_PROPERTY_NAME`], not a NUL-terminated
/// UTF-8 string within the strings block or with a character outside its
/// set, `BadString`; then the padding after the value past the end of the
/// block, `Truncated`.
fn decode_property(
    structure: &[u8],
    strings: &[u8],
    start: usize,
) -> Result<(Token, usize), Error> {
    let length = u32_at(structure, start)? as usize;
    let name = u32_at(structure, start + 4)? as usize;
    let value_end = match (start + 8).checked_add(length) {
        Some(end) => end,
        None => return Err(Error::Overflow),
    };
    if structure.len() < value_end {
        return Err(Error::Truncated);
    }
    let name_end = c_string(strings, name)?;
    if name_end == name
        || (name_end - name) as u64 > MAX_PROPERTY_NAME
        || !name_bytes(strings, name, name_end, true)
    {
        return Err(Error::BadString);
    }
    let next = padded_end(structure, value_end, false)?;
    Ok((Token::Property { name, name_end }, next))
}

/// The place in the tree of the token at `cursor`, whose successor is at
/// `next`, true for the end token that ends the walk: `BadTree`, the depth
/// `LimitExceeded`, the properties of its node `LimitExceeded`, then
/// `DuplicateProperty`.
fn place(
    walk: &mut Walk,
    structure: &[u8],
    strings: &[u8],
    token: Token,
    cursor: usize,
    next: usize,
) -> Result<bool, Error> {
    match token {
        Token::Begin { empty } => begin_node(walk, empty, next),
        Token::Property { name, name_end } => {
            property(walk, structure, strings, cursor, name, name_end)
        }
        Token::EndNode => end_node(walk),
        Token::Nop => Ok(false),
        Token::End => end_structure(walk, next, structure.len()),
    }
}

/// A begin node: outside every node it is the root, which must be the first
/// and have an empty name; inside a node it is a child, which must have a
/// name; and no node lies deeper than `MAX_DEPTH - 1`.
fn begin_node(walk: &mut Walk, empty: bool, next: usize) -> Result<bool, Error> {
    if walk.open == 0 {
        if walk.seen_root || !empty {
            return Err(Error::BadTree);
        }
    } else if empty {
        return Err(Error::BadTree);
    }
    if walk.open >= DEPTH {
        return Err(Error::LimitExceeded);
    }
    if walk.open > 0 {
        walk.frames[walk.open - 1].children = true;
    }
    walk.frames[walk.open] = Frame {
        properties: next,
        count: 0,
        children: false,
    };
    walk.open += 1;
    walk.seen_root = true;
    Ok(false)
}

/// A property at `cursor`, whose name lies at `[name, name_end)` of the
/// strings block: it belongs to the innermost open node and precedes its
/// children, and no other property of the node has its name.
fn property(
    walk: &mut Walk,
    structure: &[u8],
    strings: &[u8],
    cursor: usize,
    name: usize,
    name_end: usize,
) -> Result<bool, Error> {
    if walk.open == 0 {
        return Err(Error::BadTree);
    }
    let frame = walk.frames[walk.open - 1];
    if frame.children {
        return Err(Error::BadTree);
    }
    if frame.count + 1 > MAX_PROPERTIES {
        return Err(Error::LimitExceeded);
    }
    if repeats_name(structure, strings, frame.properties, cursor, name, name_end) {
        return Err(Error::DuplicateProperty);
    }
    walk.frames[walk.open - 1].count = frame.count + 1;
    Ok(false)
}

/// Whether a property from `from` up to `cursor`, where its node has only
/// properties and no-operation tokens, has the name at `[name, name_end)`
/// of the strings block.
fn repeats_name(
    structure: &[u8],
    strings: &[u8],
    from: usize,
    cursor: usize,
    name: usize,
    name_end: usize,
) -> bool {
    let wanted = &strings[name..name_end];
    let mut at = from;
    while at < cursor {
        match piece_at(structure, at) {
            Some((Piece::Property { name: earlier, .. }, after)) => {
                if name_at(strings, earlier, wanted) {
                    return true;
                }
                at = after;
            }
            Some((_, after)) => at = after,
            None => return false,
        }
    }
    false
}

/// An end node: it closes the innermost open node.
fn end_node(walk: &mut Walk) -> Result<bool, Error> {
    if walk.open == 0 {
        return Err(Error::BadTree);
    }
    walk.open -= 1;
    Ok(false)
}

/// The end token, whose successor is at `next` of a block of `length`
/// bytes: without a root, with open nodes or before the end of the block,
/// `BadTree`.
fn end_structure(walk: &Walk, next: usize, length: usize) -> Result<bool, Error> {
    if !walk.seen_root || walk.open != 0 || next != length {
        return Err(Error::BadTree);
    }
    Ok(true)
}
