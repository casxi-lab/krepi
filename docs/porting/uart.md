---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - src/board/qemu/uart.rs
destination:
  - kernel/boards/qemu-virt/src/uart.rs
treatment: ported
features:
  - krepi.platform.qemu-virt-boot
---

# Porting record: kernel/boards/qemu-virt/src/uart.rs

## Summary

The PL011 UART of QEMU virt, which the kernel polls: `read` and `write` of
one register by volatile MMIO, `init`, which sets the UART up for 115200
baud, 8N1 with its FIFOs and without interrupts, DMA or flow control,
`try_put`, which writes a byte unless the transmit FIFO is full, `get`,
which reads a byte unless the receive FIFO is empty, and `print`, which
writes a record within the console bounds of the board. The module is
compiled only for the bare-metal target. It also takes the failure path of
the legacy console, which wrote the failure marker and halted, as
`fail`, and adds `write_echo`, which writes the echo of a received byte
within the same bounds, and `report_panic`, which writes the panic record;
the [console](console.md) holds the logic of all three on the host.

## Changes

- The base address is `UART_BASE` of the crate root, `0x0900_0000`, in place
  of the start of the legacy `UART` span, and the DMA control register at
  `0x48`, which `init` clears, is named `DMACR`; the flag bits are named
  `TX_FULL` and `RX_EMPTY`. The values are unchanged.
- `try_put` and `get` do not ask the console lease of the legacy board,
  which arbitrated the UART between the kernel and an EL0 UART service; no
  such service exists, and the lease is not ported.
- `print` calls `console::print` with the console bounds of QEMU virt, the
  counter frequency and the virtual counter; when the write fails, `fail`
  writes the failure marker with `console::report_failure` and halts. The
  legacy board console did the same in `src/board/console.rs`, with the
  bounds as constants; the halt and the device are target-only, so they
  are in this module and the logic in [console](console.md).
- `write_echo` is new: it writes the echo of a received byte, the byte and,
  after a carriage return, a line feed, within the bounds of a record. The
  legacy echo belonged to its runtime, which is not ported.
- `report_panic` is new: it writes the panic record of
  `console::report_panic` within the console bounds of QEMU virt and, when a
  line fails, writes the failure marker and halts, as `print` does. The
  legacy panic record was written by `src/fault.rs` through its own
  emitter; the [qemu-virt](qemu-virt.md) record describes the change.
- The `SAFETY` comments keep their content and name the Device memory that
  the MMU gives the range while it is off; the module and each function have
  documentation, and the line `//! Feature: krepi.platform.qemu-virt-boot`
  names the feature.

## Tests carried over

None: the legacy module had no host tests.

## Behaviour changes

- Without the console lease, `try_put` and `get` always reach the device.
  The case `cold-boot-echo` of `cargo xtask qemu-boot` fixes the records and
  the echo that reach the transcript.
- A received byte is echoed by the kernel, with a line feed after a carriage
  return; the same case fixes it.

## Hardware evidence to re-obtain

- Output and input through the PL011 of QEMU virt, which the case
  `cold-boot-echo` obtains.

## Not carried over

- The checks of the console lease in `try_put` and `get`.
- `PollingSerial`, the `SerialIo` implementation of the legacy runtime,
  which is not ported.
