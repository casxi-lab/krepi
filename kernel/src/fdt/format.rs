//! The reading of the bytes of a tree: big-endian words put together from
//! single bytes, NUL-terminated strings with their UTF-8 check, the padding
//! up to a multiple of 4, the character sets of names and the comparison of
//! byte strings.
//!
//! Feature: krepi.platform.device-tree
//!
//! Every read takes a slice and an index and compares the index with the
//! length of the slice before it reads a byte, so no read leaves the slice
//! and none panics.

use super::Error;

/// The size of the header in bytes.
pub(super) const HEADER_SIZE: usize = 40;

/// The magic of a device tree.
pub(super) const MAGIC: u32 = 0xd00d_feed;

/// Whether `count` bytes from `at` lie in `bytes`.
pub(super) fn fits(bytes: &[u8], at: usize, count: usize) -> bool {
    at <= bytes.len() && count <= bytes.len() - at
}

/// The big-endian 32-bit word at `at`, or `Truncated` when it runs past the
/// end of `bytes`.
pub(super) fn u32_at(bytes: &[u8], at: usize) -> Result<u32, Error> {
    if !fits(bytes, at, 4) {
        return Err(Error::Truncated);
    }
    Ok(((bytes[at] as u32) << 24)
        | ((bytes[at + 1] as u32) << 16)
        | ((bytes[at + 2] as u32) << 8)
        | (bytes[at + 3] as u32))
}

/// The big-endian 64-bit word at `at`, or `Truncated` when it runs past the
/// end of `bytes`.
pub(super) fn u64_at(bytes: &[u8], at: usize) -> Result<u64, Error> {
    if !fits(bytes, at, 8) {
        return Err(Error::Truncated);
    }
    let high = u32_at(bytes, at)?;
    let low = u32_at(bytes, at + 4)?;
    Ok(((high as u64) << 32) | (low as u64))
}

/// The least multiple of 4 that is at least `offset`, an offset inside a
/// tree of at most 2 MiB.
pub(super) fn align4(offset: usize) -> usize {
    (offset + 3) & !3
}

/// The first index at or after `start` that holds a NUL byte: a string is
/// read up to the end of its block and no further.
pub(super) fn find_nul(bytes: &[u8], start: usize) -> Option<usize> {
    let mut at = start;
    while at < bytes.len() {
        if bytes[at] == 0 {
            return Some(at);
        }
        at += 1;
    }
    None
}

/// Whether `byte` continues the UTF-8 encoding of a scalar value.
fn continues(byte: u8) -> bool {
    byte >= 0x80 && byte <= 0xbf
}

/// The index after the UTF-8 encoding of the scalar value at `at`, which
/// lies before `end`, or none when the bytes there encode none: an overlong
/// encoding, a surrogate and a value above `U+10FFFF` are not UTF-8.
fn scalar_end(bytes: &[u8], at: usize, end: usize) -> Option<usize> {
    let first = bytes[at];
    if first < 0x80 {
        return Some(at + 1);
    }
    let (length, low, high) = if first >= 0xc2 && first <= 0xdf {
        (2, 0x80, 0xbf)
    } else if first == 0xe0 {
        (3, 0xa0, 0xbf)
    } else if first == 0xed {
        (3, 0x80, 0x9f)
    } else if first >= 0xe1 && first <= 0xef {
        (3, 0x80, 0xbf)
    } else if first == 0xf0 {
        (4, 0x90, 0xbf)
    } else if first >= 0xf1 && first <= 0xf3 {
        (4, 0x80, 0xbf)
    } else if first == 0xf4 {
        (4, 0x80, 0x8f)
    } else {
        return None;
    };
    if end - at < length {
        return None;
    }
    let second = bytes[at + 1];
    if second < low || second > high {
        return None;
    }
    if length >= 3 && !continues(bytes[at + 2]) {
        return None;
    }
    if length == 4 && !continues(bytes[at + 3]) {
        return None;
    }
    Some(at + length)
}

/// Whether the bytes `[start, end)` of `bytes`, which lie inside it, are
/// UTF-8.
pub(super) fn is_utf8(bytes: &[u8], start: usize, end: usize) -> bool {
    let mut at = start;
    while at < end {
        match scalar_end(bytes, at, end) {
            Some(next) => at = next,
            None => return false,
        }
    }
    true
}

/// The index of the NUL of the string at `start` of the block `bytes`;
/// `BadString` when no NUL follows within the block, which holds for a
/// start at or past its end, or when the bytes before the NUL are not
/// UTF-8.
pub(super) fn c_string(bytes: &[u8], start: usize) -> Result<usize, Error> {
    match find_nul(bytes, start) {
        Some(nul) => {
            if is_utf8(bytes, start, nul) {
                Ok(nul)
            } else {
                Err(Error::BadString)
            }
        }
        None => Err(Error::BadString),
    }
}

/// Whether the bytes `[start, end)` of `bytes`, which lie inside it, are
/// zero.
fn zeros(bytes: &[u8], start: usize, end: usize) -> bool {
    let mut at = start;
    while at < end {
        if bytes[at] != 0 {
            return false;
        }
        at += 1;
    }
    true
}

/// The end of the padding after `end`, up to the next multiple of 4:
/// `Truncated` when the padding runs past the end of the block `bytes`,
/// and, with `zero`, `BadPadding` for a nonzero byte in it.
pub(super) fn padded_end(bytes: &[u8], end: usize, zero: bool) -> Result<usize, Error> {
    let aligned = align4(end);
    if bytes.len() < aligned {
        return Err(Error::Truncated);
    }
    if zero && !zeros(bytes, end, aligned) {
        return Err(Error::BadPadding);
    }
    Ok(aligned)
}

/// Whether `byte` is an ASCII letter or digit.
fn alphanumeric(byte: u8) -> bool {
    (byte >= b'0' && byte <= b'9')
        || (byte >= b'a' && byte <= b'z')
        || (byte >= b'A' && byte <= b'Z')
}

/// Whether `byte` is a character of a property name, of Table 2.2 of DTSpec
/// v0.4, or with `property` false of a node name, of Table 2.1.
fn name_byte(byte: u8, property: bool) -> bool {
    if alphanumeric(byte)
        || byte == b','
        || byte == b'.'
        || byte == b'_'
        || byte == b'+'
        || byte == b'-'
    {
        return true;
    }
    if property {
        byte == b'?' || byte == b'#'
    } else {
        byte == b'@'
    }
}

/// Whether every byte of `[start, end)` of `bytes`, which lies inside it, is
/// a character of a property name or, with `property` false, of a node
/// name.
pub(super) fn name_bytes(bytes: &[u8], start: usize, end: usize, property: bool) -> bool {
    let mut at = start;
    while at < end {
        if !name_byte(bytes[at], property) {
            return false;
        }
        at += 1;
    }
    true
}

/// Whether the bytes `[start, end)` of `bytes` are those of `other`.
pub(super) fn same_bytes(bytes: &[u8], start: usize, end: usize, other: &[u8]) -> bool {
    if start > end || end > bytes.len() || end - start != other.len() {
        return false;
    }
    let mut index = 0;
    while index < other.len() {
        if bytes[start + index] != other[index] {
            return false;
        }
        index += 1;
    }
    true
}

/// Whether the bytes `[start, end)` of `bytes` start with those of
/// `prefix`.
pub(super) fn starts_with(bytes: &[u8], start: usize, end: usize, prefix: &[u8]) -> bool {
    if start > end || end > bytes.len() || end - start < prefix.len() {
        return false;
    }
    same_bytes(bytes, start, start + prefix.len(), prefix)
}

/// Whether the string at `offset` of the strings block `strings`, up to its
/// NUL, is `name`, which holds no NUL.
pub(super) fn name_at(strings: &[u8], offset: usize, name: &[u8]) -> bool {
    if !fits(strings, offset, name.len()) || !fits(strings, offset + name.len(), 1) {
        return false;
    }
    if strings[offset + name.len()] != 0 {
        return false;
    }
    let mut index = 0;
    while index < name.len() {
        if name[index] == 0 || strings[offset + index] != name[index] {
            return false;
        }
        index += 1;
    }
    true
}

/// Whether the offsets `[a, a_end)` and `[b, b_end)` intersect: both are
/// nonempty and each starts before the other ends.
pub(super) fn intersects(a: usize, a_end: usize, b: usize, b_end: usize) -> bool {
    a < a_end && b < b_end && a < b_end && b < a_end
}
