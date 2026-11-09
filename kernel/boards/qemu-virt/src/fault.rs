//! The exception record of the kernel: the line that reports an exception
//! that the vectors of EL1 took, and the halt record after it on a fatal
//! path.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! The functions take the frame that the vectors saved and write through the
//! bounded console writes of [`crate::console`], with the device and the
//! counter as callbacks, so that the host tests hold the bytes of each
//! record. The PL011 driver writes them on the board and halts after a
//! failed write.

use crate::console::{self, Bounds, PolledError};
use krepi_arch::exception::{Class, Frame};

/// Writes the exception record of `frame` within `bounds` on a counter `now`
/// that runs at `frequency`: after a line break, `CASXI_EXCEPTION vector=<n>
/// ESR=0x<16> ELR=0x<16> FAR=0x<16> SPSR=0x<16> class=<class>`, the vector
/// number in decimal, the four registers of the frame in 16 lowercase
/// hexadecimal digits and the name of the [`Class`] of the vector and the
/// syndrome. The bytes written, or why the write failed.
pub fn report(
    frame: &Frame,
    bounds: &Bounds,
    frequency: u64,
    now: impl FnMut() -> u64,
    try_write: impl FnMut(u8) -> bool,
) -> Result<usize, PolledError> {
    let class = Class::of(frame.vector, frame.esr).name();
    console::print(
        format_args!(
            "\nCASXI_EXCEPTION vector={} ESR={:#018x} ELR={:#018x} FAR={:#018x} SPSR={:#018x} class={class}\n",
            frame.vector, frame.esr, frame.elr, frame.far, frame.spsr
        ),
        bounds,
        frequency,
        now,
        try_write,
    )
}

/// Writes the exception record of `frame` as [`report`] does, then
/// `CASXI_HALTED`, each a record of its own within `bounds`. The bytes
/// written, or why the first record that failed failed; no record follows
/// a failed one.
pub fn report_fatal(
    frame: &Frame,
    bounds: &Bounds,
    frequency: u64,
    mut now: impl FnMut() -> u64,
    mut try_write: impl FnMut(u8) -> bool,
) -> Result<usize, PolledError> {
    let written = report(frame, bounds, frequency, &mut now, &mut try_write)?;
    let halted = console::print(
        format_args!("CASXI_HALTED\n"),
        bounds,
        frequency,
        &mut now,
        &mut try_write,
    )?;
    Ok(written + halted)
}

#[cfg(test)]
mod tests;
