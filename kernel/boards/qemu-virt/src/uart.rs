//! The PL011 UART of QEMU virt, which the kernel polls: its setup, single
//! bytes in each direction, and the bounded console writes on top of them.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! The address and the clock of the UART are those of QEMU virt, not of the
//! Raspberry Pi 5. One CPU owns the device; no interrupt handler accesses it.

use core::{fmt, ptr};

use crate::console::{self, PanicLocation, PolledError};
use crate::{CONSOLE_BOUNDS, UART_BASE, counter};
use krepi_arch::cpu;

/// The data register.
const DR: usize = 0x00;
/// The flag register.
const FR: usize = 0x18;
/// The integer part of the baud rate divisor.
const IBRD: usize = 0x24;
/// The fractional part of the baud rate divisor.
const FBRD: usize = 0x28;
/// The line control register.
const LCRH: usize = 0x2c;
/// The control register.
const CR: usize = 0x30;
/// The interrupt mask set and clear register.
const IMSC: usize = 0x38;
/// The interrupt clear register.
const ICR: usize = 0x44;
/// The DMA control register.
const DMACR: usize = 0x48;

/// The transmit FIFO is full (`FR.TXFF`).
const TX_FULL: u32 = 1 << 5;
/// The receive FIFO is empty (`FR.RXFE`).
const RX_EMPTY: u32 = 1 << 4;

fn read(offset: usize) -> u32 {
    // SAFETY: `UART_BASE + offset` is a 4-byte aligned register of the PL011
    // of QEMU virt, which the MMU, while it is off, reaches as Device memory;
    // a later MMU setup keeps the range mapped with Device attributes. One CPU
    // owns the device and no interrupt handler accesses it, so the read races
    // with no other access.
    unsafe { ptr::read_volatile((UART_BASE + offset) as *const u32) }
}

fn write(offset: usize, value: u32) {
    // SAFETY: the same mapped, aligned and exclusively used register range as
    // in `read`.
    unsafe { ptr::write_volatile((UART_BASE + offset) as *mut u32, value) }
}

/// Sets the UART up for 115200 baud, 8 data bits, no parity and 1 stop bit
/// with its FIFOs, without interrupts, DMA or flow control.
pub fn init() {
    write(CR, 0);
    write(IMSC, 0);
    write(DMACR, 0);
    write(ICR, 0x7ff);
    // The QEMU virt device tree declares a 24 MHz UART clock: 115200 baud
    // gives the divisor 13 + 1/64. QEMU does not model the baud rate of the
    // bytes it transports.
    write(IBRD, 13);
    write(FBRD, 1);
    // 8 data bits (WLEN), FIFOs enabled (FEN).
    write(LCRH, (3 << 5) | (1 << 4));
    // UART, transmitter and receiver enabled; no flow control.
    write(CR, 1 | (1 << 8) | (1 << 9));
}

/// Writes `byte` unless the transmit FIFO is full; whether it was written.
pub fn try_put(byte: u8) -> bool {
    if read(FR) & TX_FULL != 0 {
        return false;
    }
    write(DR, byte.into());
    true
}

/// The next received byte, or `None` while the receive FIFO is empty.
pub fn get() -> Option<u8> {
    if read(FR) & RX_EMPTY != 0 {
        None
    } else {
        // The low 8 bits of the data register are the byte; the bits above
        // them are its error flags.
        Some(read(DR) as u8)
    }
}

/// Writes the record `args` within [`CONSOLE_BOUNDS`], with LF written as
/// CR LF. A write that fails writes the failure marker within its own bound
/// and halts the CPU.
pub fn print(args: fmt::Arguments<'_>) {
    let result = console::print(
        args,
        &CONSOLE_BOUNDS,
        cpu::counter_frequency(),
        counter,
        try_put,
    );
    if let Err(error) = result {
        fail(error);
    }
}

/// Echoes the received `byte` within [`CONSOLE_BOUNDS`]: the byte itself,
/// and after a carriage return a line feed. A write that fails writes the
/// failure marker within its own bound and halts the CPU.
pub fn write_echo(byte: u8) {
    let (bytes, count) = console::echo(byte);
    let result = console::write(
        &bytes[..count],
        &CONSOLE_BOUNDS,
        cpu::counter_frequency(),
        counter,
        try_put,
    );
    if let Err(error) = result {
        fail(error);
    }
}

/// Writes the panic record of `message`, the static message of the panic if
/// it has one, and `location` within [`CONSOLE_BOUNDS`], as
/// [`console::report_panic`] describes it. A write that fails writes the
/// failure marker within its own bound and halts the CPU.
pub fn report_panic(message: Option<&str>, location: Option<PanicLocation<'_>>) {
    let result = console::report_panic(
        message,
        location,
        &CONSOLE_BOUNDS,
        cpu::counter_frequency(),
        counter,
        try_put,
    );
    if let Err(error) = result {
        fail(error);
    }
}

/// Writes the marker of the failed write `error` and halts. The marker needs
/// neither formatting nor the counter; a broken UART may lose it, but cannot
/// keep the CPU from halting.
fn fail(error: PolledError) -> ! {
    let _ = console::report_failure(error, &CONSOLE_BOUNDS, try_put);
    cpu::halt()
}
