//! The cache lines that a range of bytes touches: the walks that the cache
//! maintenance by address follows, as plain arithmetic without any
//! maintenance instruction.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! A line size is given as `CTR_EL0` encodes it, the base-2 logarithm of
//! the number of 4-byte words in a line, so a field of 4 is a line of 64
//! bytes. A walk gives the address of each line that a byte of the range
//! lies in, from the line of the first byte to the line of the last, and
//! refuses a range before it walks: an empty range, one longer than its
//! limit, one that wraps past the end of the address space and a field
//! above 15 give `None`. The module is compiled on the host too, where its
//! tests run.

use core::iter::StepBy;
use core::ops::Range;

/// The longest range that one call of the cache maintenance by address
/// walks, 64 KiB: at 64-byte lines, at most 1,025 lines.
pub const MAX_RANGE_BYTES: u64 = 0x1_0000;

/// The address of every cache line that a byte of `[start, start + bytes)`
/// lies in, for lines of `4 << log2_words` bytes, from the line of `start`
/// up: `None` when `bytes` is 0 or above `limit`, when `log2_words` is
/// above 15 or when the range wraps past the end of the address space,
/// before any line is given.
pub fn lines(start: u64, bytes: u64, log2_words: u8, limit: u64) -> Option<StepBy<Range<u64>>> {
    if bytes == 0 || bytes > limit || log2_words > 15 {
        return None;
    }
    let end = start.checked_add(bytes)?;
    let line = 4_u64 << log2_words;
    Some(((start & !(line - 1))..end).step_by(line as usize))
}

/// The cache lines of a whole image that firmware hands over, `bytes` from
/// `start`, within the reserved window of its platform, `window`: the walk
/// of [`lines`] with the window's length as its limit, and `None` unless the
/// image starts at the start of the window, its start, its length and the
/// end of the window are multiples of 4 KiB, the window is not empty, the
/// line field is at most 10, a line of 4 KiB, and the image ends within the
/// window. The length covers the whole linked image, its BSS and stacks
/// too, not only the bytes that the firmware loaded.
pub fn handoff_lines(
    start: u64,
    bytes: u64,
    log2_words: u8,
    window: Range<u64>,
) -> Option<StepBy<Range<u64>>> {
    if start != window.start
        || window.start >= window.end
        || (start | bytes | window.end) & 4095 != 0
        || log2_words > 10
        || start.checked_add(bytes)? > window.end
    {
        return None;
    }
    lines(start, bytes, log2_words, window.end - window.start)
}

#[cfg(test)]
mod tests;
