//! Ordered writes of bytes with a fixed budget of attempts.
//!
//! Feature: krepi.platform.qemu-virt-boot

/// What a bounded write did.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Emission {
    /// The bytes written, a prefix of those given.
    pub bytes_written: usize,
    /// The attempts made, successful or not.
    pub attempts: usize,
}

/// Tries to write `bytes` in order, with at most `max_attempts` attempts in
/// all. A failed attempt retries the same byte. The callback must be bounded
/// itself: this function cannot bound the time of an arbitrary callback or
/// device. The bytes are written unchanged, including any CR and LF that the
/// caller gives.
pub fn emit_bounded(
    bytes: &[u8],
    max_attempts: usize,
    mut try_write: impl FnMut(u8) -> bool,
) -> Emission {
    let mut result = Emission {
        bytes_written: 0,
        attempts: 0,
    };
    while result.bytes_written < bytes.len() && result.attempts < max_attempts {
        result.attempts += 1;
        if try_write(bytes[result.bytes_written]) {
            result.bytes_written += 1;
        }
    }
    result
}

#[cfg(test)]
mod tests;
