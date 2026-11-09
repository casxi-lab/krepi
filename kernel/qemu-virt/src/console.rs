//! The serial console of the kernel: bounded writes of records and of echoed
//! bytes to a UART that the caller polls, the panic record, and the marker
//! that reports a failed write.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! The functions take the device as a callback, `try_write`, which writes one
//! byte or reports that the device cannot take it yet, and the clock as a
//! counter, `now`, with its frequency. A write fails when the record is
//! longer than [`RECORD_BYTES`], when one byte is refused more often than the
//! board's bound allows, when the record takes longer than the board's window
//! on the counter, or when its formatting fails. A failed write can leave a
//! prefix of the record on the device; the caller then reports the failure
//! with [`report_failure`] and halts. Nothing here allocates, takes a lock or
//! is called from an interrupt handler.

pub mod emitter;
pub mod polled;

use core::fmt;

pub use emitter::Emission;
pub use polled::PolledError;

/// The longest record, in bytes after LF is written as CR LF.
pub const RECORD_BYTES: usize = 1024;

/// The bounds of console output on one board, which the board support gives
/// for its UART and its counter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Bounds {
    /// How often one byte of a record may be refused before the write fails.
    pub attempts_per_byte: usize,
    /// How many attempts the failure marker may take in all.
    pub failure_attempts: usize,
    /// The longest time that one record may take, in milliseconds on the
    /// counter.
    pub window_ms: u64,
}

/// The ticks of a counter that runs at `frequency` ticks per second in
/// `window_ms` milliseconds, rounded down; `u64::MAX`, which no write
/// accepts, when they do not fit.
pub fn window_ticks(frequency: u64, window_ms: u64) -> u64 {
    let ticks = u128::from(frequency) * u128::from(window_ms) / 1000;
    u64::try_from(ticks).unwrap_or(u64::MAX)
}

/// Writes the record `args` with LF written as CR LF, within `bounds` on a
/// counter `now` that runs at `frequency`; the bytes written, or why the
/// write failed.
pub fn print(
    args: fmt::Arguments<'_>,
    bounds: &Bounds,
    frequency: u64,
    now: impl FnMut() -> u64,
    try_write: impl FnMut(u8) -> bool,
) -> Result<usize, PolledError> {
    polled::write_polled(
        args,
        RECORD_BYTES,
        bounds.attempts_per_byte,
        window_ticks(frequency, bounds.window_ms),
        now,
        try_write,
    )
}

/// Writes `bytes` unchanged, within the same bounds as [`print`].
pub fn write(
    bytes: &[u8],
    bounds: &Bounds,
    frequency: u64,
    now: impl FnMut() -> u64,
    try_write: impl FnMut(u8) -> bool,
) -> Result<usize, PolledError> {
    polled::write_bytes_polled(
        bytes,
        RECORD_BYTES,
        bounds.attempts_per_byte,
        window_ticks(frequency, bounds.window_ms),
        now,
        try_write,
    )
}

/// The bytes that the console writes back for the received `byte`, and how
/// many of the two there are: the byte itself, and after a carriage return
/// (`0x0d`) also a line feed (`0x0a`). No other byte is changed or added.
pub fn echo(byte: u8) -> ([u8; 2], usize) {
    if byte == b'\r' {
        (*b"\r\n", 2)
    } else {
        ([byte, 0], 1)
    }
}

/// The marker that reports the failed write `error`: a line
/// `CASXI_UART_FAIL reason=<reason>` after a line break, then
/// `CASXI_HALTED`, each ending in CR LF.
pub fn failure_marker(error: PolledError) -> &'static [u8] {
    match error {
        PolledError::InvalidBudget => b"\r\nCASXI_UART_FAIL reason=clock\r\nCASXI_HALTED\r\n",
        PolledError::ByteLimit => b"\r\nCASXI_UART_FAIL reason=length\r\nCASXI_HALTED\r\n",
        PolledError::Deadline => b"\r\nCASXI_UART_FAIL reason=deadline\r\nCASXI_HALTED\r\n",
        PolledError::PollLimit => b"\r\nCASXI_UART_FAIL reason=stalled\r\nCASXI_HALTED\r\n",
        PolledError::Formatting => b"\r\nCASXI_UART_FAIL reason=format\r\nCASXI_HALTED\r\n",
    }
}

/// Writes the marker of `error` with at most `bounds.failure_attempts`
/// attempts in all, without formatting or the counter, so that a broken
/// clock cannot keep it from ending; what was written.
pub fn report_failure(
    error: PolledError,
    bounds: &Bounds,
    try_write: impl FnMut(u8) -> bool,
) -> Emission {
    emitter::emit_bounded(failure_marker(error), bounds.failure_attempts, try_write)
}

/// The text of the panic record in place of a panic message that is not a
/// static string, whose formatting could run arbitrary code on a fatal path.
pub const DYNAMIC_PANIC_MESSAGE: &str = "dynamic_panic_message_omitted";

/// Where a panic happened, as the panic record names it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PanicLocation<'a> {
    /// The path of the source file.
    pub file: &'a str,
    /// The line in the file, from 1.
    pub line: u32,
    /// The column in the line, from 1.
    pub column: u32,
}

/// Writes the panic record within `bounds` on a counter `now` that runs at
/// `frequency`: after a line break, `CASXI_PANIC` and `message`, or
/// [`DYNAMIC_PANIC_MESSAGE`] for a panic without a static message; then,
/// when the location is known, `CASXI_PANIC_LOCATION file=<file>
/// line=<line> column=<column>`; then `CASXI_HALTED`. Each line is a record
/// of its own, written as [`print`] writes it. The bytes written, or why the
/// first record that failed failed; no record follows a failed one.
pub fn report_panic(
    message: Option<&str>,
    location: Option<PanicLocation<'_>>,
    bounds: &Bounds,
    frequency: u64,
    mut now: impl FnMut() -> u64,
    mut try_write: impl FnMut(u8) -> bool,
) -> Result<usize, PolledError> {
    let message = message.unwrap_or(DYNAMIC_PANIC_MESSAGE);
    let mut written = print(
        format_args!("\nCASXI_PANIC {message}\n"),
        bounds,
        frequency,
        &mut now,
        &mut try_write,
    )?;
    if let Some(location) = location {
        written += print(
            format_args!(
                "CASXI_PANIC_LOCATION file={} line={} column={}\n",
                location.file, location.line, location.column
            ),
            bounds,
            frequency,
            &mut now,
            &mut try_write,
        )?;
    }
    written += print(
        format_args!("CASXI_HALTED\n"),
        bounds,
        frequency,
        &mut now,
        &mut try_write,
    )?;
    Ok(written)
}

#[cfg(test)]
mod tests;
