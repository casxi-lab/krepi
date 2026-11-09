//! Foreground writes with a deadline on a counter and a bound on the
//! attempts for each byte.
//!
//! Feature: krepi.platform.qemu-virt-boot

use core::fmt::{self, Write};

/// Why a polled write failed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PolledError {
    /// The attempts per byte are 0, or the ticks are 0 or at least `2^63`.
    InvalidBudget,
    /// The record is longer than its byte limit.
    ByteLimit,
    /// The deadline on the counter passed.
    Deadline,
    /// The device refused one byte as often as the attempts per byte allow.
    PollLimit,
    /// A formatter failed without a failure of the write.
    Formatting,
}

struct Writer<C, W> {
    now: C,
    try_write: W,
    started: u64,
    ticks: u64,
    bytes_left: usize,
    attempts_per_byte: usize,
    written: usize,
    failure: Option<PolledError>,
}

impl<C: FnMut() -> u64, W: FnMut(u8) -> bool> Writer<C, W> {
    /// A writer whose deadline starts now, or `InvalidBudget` without a look
    /// at the counter or the device.
    fn start(
        max_bytes: usize,
        attempts_per_byte: usize,
        ticks: u64,
        mut now: C,
        try_write: W,
    ) -> Result<Self, PolledError> {
        if attempts_per_byte == 0 || ticks == 0 || ticks >= 1 << 63 {
            return Err(PolledError::InvalidBudget);
        }
        let started = now();
        Ok(Writer {
            now,
            try_write,
            started,
            ticks,
            bytes_left: max_bytes,
            attempts_per_byte,
            written: 0,
            failure: None,
        })
    }

    fn fail(&mut self, reason: PolledError) -> fmt::Result {
        self.failure.get_or_insert(reason);
        Err(fmt::Error)
    }

    fn put(&mut self, byte: u8) -> fmt::Result {
        if self.failure.is_some() {
            return Err(fmt::Error);
        }
        if self.bytes_left == 0 {
            return self.fail(PolledError::ByteLimit);
        }
        for _ in 0..self.attempts_per_byte {
            if (self.now)().wrapping_sub(self.started) >= self.ticks {
                return self.fail(PolledError::Deadline);
            }
            if (self.try_write)(byte) {
                self.bytes_left -= 1;
                self.written += 1;
                return Ok(());
            }
            core::hint::spin_loop();
        }
        self.fail(PolledError::PollLimit)
    }
}

impl<C: FnMut() -> u64, W: FnMut(u8) -> bool> Write for Writer<C, W> {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        for byte in text.bytes() {
            if byte == b'\n' {
                self.put(b'\r')?;
            }
            self.put(byte)?;
        }
        Ok(())
    }
}

/// Formats `args` without allocation, writing LF as CR LF, within
/// `max_bytes`; the bytes written.
///
/// `ticks` is a positive interval below half the range of the wrapping `u64`
/// counter. Every attempt to write a byte first checks that deadline. The
/// bound on the attempts for each byte also ends a write to a blocked device
/// when the counter stops advancing; a written byte renews that bound, never
/// the deadline. A failure is final even when a formatter ignores the error
/// of a write. A failure can leave a written prefix; callers must not report
/// the record as complete.
///
/// The caller owns the device and passes callbacks and formatters that are
/// bounded themselves. This is foreground polling, not a writer for an
/// interrupt handler or a fallback for a broken clock.
pub fn write_polled(
    args: fmt::Arguments<'_>,
    max_bytes: usize,
    attempts_per_byte: usize,
    ticks: u64,
    now: impl FnMut() -> u64,
    try_write: impl FnMut(u8) -> bool,
) -> Result<usize, PolledError> {
    let mut writer = Writer::start(max_bytes, attempts_per_byte, ticks, now, try_write)?;
    let formatted = writer.write_fmt(args);
    match (writer.failure, formatted) {
        (Some(reason), _) => Err(reason),
        (None, Err(_)) => Err(PolledError::Formatting),
        (None, Ok(())) => Ok(writer.written),
    }
}

/// Writes `bytes` unchanged and in order, with the bounds of
/// [`write_polled`]: no LF becomes CR LF, and a write cannot fail with
/// `Formatting`.
pub fn write_bytes_polled(
    bytes: &[u8],
    max_bytes: usize,
    attempts_per_byte: usize,
    ticks: u64,
    now: impl FnMut() -> u64,
    try_write: impl FnMut(u8) -> bool,
) -> Result<usize, PolledError> {
    let mut writer = Writer::start(max_bytes, attempts_per_byte, ticks, now, try_write)?;
    for &byte in bytes {
        if writer.put(byte).is_err() {
            break;
        }
    }
    match writer.failure {
        Some(reason) => Err(reason),
        None => Ok(writer.written),
    }
}

#[cfg(test)]
mod tests;
