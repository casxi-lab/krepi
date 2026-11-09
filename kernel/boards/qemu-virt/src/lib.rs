//! The QEMU virt board support of the krepi kernel: the PL011 serial
//! console, the exception record, the wiring of the interrupt controller
//! and the timer, and the platform parameters of the machine.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! The addresses and values here are those of the QEMU virt machine with one
//! Cortex-A76. They are not Raspberry Pi 5 values and are never used for it.
//!
//! The console logic in [`console`] and the exception record in [`fault`]
//! are plain code that the host tests run. The PL011 driver, [`uart`], and
//! the interrupt wiring, `irq`, are compiled only for the bare-metal target.

#![cfg_attr(not(test), no_std)]

pub mod console;
pub mod fault;
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
pub mod irq;
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
pub mod uart;

use console::Bounds;

/// The base address of the 4 KiB register frame of the PL011 UART of QEMU
/// virt, whose input and output are QEMU's serial port.
pub const UART_BASE: usize = 0x0900_0000;

/// The bounds of console output on QEMU virt. At 115200 baud with 8 data
/// bits, no parity and 1 stop bit, a record of [`console::RECORD_BYTES`]
/// bytes takes about 89 ms on the wire; a record gets 250 ms in all, and a
/// byte one million attempts, which only a device that never accepts it
/// uses up. The failure marker gets one million attempts in all.
pub const CONSOLE_BOUNDS: Bounds = Bounds {
    attempts_per_byte: 1_000_000,
    failure_attempts: 1_000_000,
    window_ms: 250,
};

/// The CPU model that the image requires, as the CPU identity record names
/// it.
pub const CPU_MODEL: &str = "cortex-a76";

/// The bits of `MIDR_EL1` that identify the CPU: the implementer and the part
/// number, without the variant and the revision.
pub const MIDR_PART_MASK: u64 = 0xff00_fff0;

/// The identifying bits of a Cortex-A76: implementer `0x41` (Arm) and part
/// number `0xd0b`.
pub const MIDR_CORTEX_A76: u64 = 0x4100_d0b0;

/// The base address of the distributor of the GICv2 of QEMU virt.
pub const GIC_DISTRIBUTOR: usize = 0x0800_0000;

/// The base address of the CPU interface of the GICv2 of QEMU virt.
pub const GIC_CPU: usize = 0x0801_0000;

/// The interrupt ID of the virtual timer of the CPU on QEMU virt, the
/// private peripheral interrupt 27.
pub const TIMER_INTID: u32 = 27;

/// The priority of the timer interrupt in the GIC, in the middle of the
/// range that the priority mask lets through.
pub const TIMER_PRIORITY: u8 = 0x80;

/// The ticks of the timer interrupt per second, a platform parameter of
/// QEMU virt: the period is the counter frequency divided by it, rounded
/// up, so 10 ms.
pub const TIMER_RATE: u64 = 100;
