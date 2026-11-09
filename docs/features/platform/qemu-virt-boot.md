---
id: krepi.platform.qemu-virt-boot
title: QEMU virt boot
status: partial
modules:
  - kernel/arch/src/boot.rs
  - kernel/arch/src/boot.S
  - kernel/arch/src/cpu.rs
  - kernel/boards/qemu-virt/build.rs
  - kernel/boards/qemu-virt/src/lib.rs
  - kernel/boards/qemu-virt/src/main.rs
  - kernel/boards/qemu-virt/src/uart.rs
  - kernel/boards/qemu-virt/src/console.rs
  - kernel/boards/qemu-virt/src/console/polled.rs
  - kernel/boards/qemu-virt/src/console/emitter.rs
tests:
  - kernel/boards/qemu-virt/src/console/tests.rs
  - kernel/boards/qemu-virt/src/console/polled/tests.rs
  - kernel/boards/qemu-virt/src/console/emitter/tests.rs
suites:
  - qemu-boot
theorems: none
---

# QEMU virt boot

## Summary

The QEMU virt default image of krepi starts from a cold boot on QEMU virt:
its cold entry brings the boot CPU from the ELF entry point into Rust at
EL1, the image checks the state that it finds, writes its boot records to
the PL011 serial console and then echoes the bytes that it receives, with
every console write bounded by the platform parameters of the machine. The
feature belongs to the kernel at EL1. It does not boot a Raspberry Pi 5,
start secondary CPUs, read the device tree, turn the MMU or the caches on or
handle exceptions.

## Interface

- **Image.** `krepi-qemu-virt`, the binary of `kernel/boards/qemu-virt`,
  built in `kernel/` for `aarch64-unknown-none-softfloat` in release:

  ```sh
  cd kernel
  cargo build --locked --release --target aarch64-unknown-none-softfloat -p krepi-qemu-virt --bin krepi-qemu-virt
  ```

  QEMU loads it with `-kernel` and enters it at `_start`, `0x4020_0000`.
- **Serial console.** The PL011 of QEMU virt at `0x0900_0000`, which QEMU
  connects to its standard streams. The image writes the records
  `CASXI_CPU`, `CASXI_BOOT` and `CASXI_READY` and, on a fatal path,
  `CASXI_PANIC`, `CASXI_PANIC_LOCATION`, `CASXI_UART_FAIL` and
  `CASXI_HALTED`, in the forms of the
  [records of the boot contract](../../domains/boot-platform/boot/contract.md#records).
  After `CASXI_READY` it echoes each received byte.
- **Kernel functions.** `krepi_qemu_virt::uart::print` writes a record,
  `krepi_qemu_virt::uart::write_echo` echoes a byte,
  `krepi_qemu_virt::uart::report_panic` writes the panic record, and the
  host-testable `krepi_qemu_virt::console` functions do so for any device
  and counter;
  `krepi_arch::cpu` reads the processor registers of EL1 and halts the CPU.
  The [entry points of the boot contract](../../domains/boot-platform/boot/contract.md#entry-points)
  list them.
- **Suite.** `cargo xtask qemu-boot` builds the image and runs the QEMU
  boot suite on it ([testing](../../conventions/testing.md#entry-points)).

## Semantics

- **Entry.** Only the boot CPU at EL1 enters Rust; any other CPU, and a CPU
  at another exception level, parks in the cold entry. Every exception
  stays masked, and FP/SIMD instructions trap.
- **Checks.** The image requires a cleared BSS, an initialized data
  section, EL1, the MMU and the caches off, little-endian data accesses, an
  Arm Cortex-A76 and FP/SIMD trapping. A check that fails panics: the image
  writes `CASXI_PANIC` with the check's message, the location and
  `CASXI_HALTED`, and halts.
- **Records.** The boot records hold no count, time or address, so every
  cold boot of an image writes the same bytes.
- **Echo.** Each received byte comes back unchanged; after a carriage return
  the image also writes a line feed. No received byte triggers anything
  else: the image has no command.
- **Bounds.** A record is at most 1,024 bytes after each LF has become CR
  LF. A console write fails when one byte is refused one million times, also
  with a stopped counter, or when the record takes longer than 250 ms on the
  counter; the image then writes `CASXI_UART_FAIL` with the reason and
  `CASXI_HALTED` within one million attempts and halts. A failed write never
  restarts and can leave a prefix of the record.
- **Undefined.** An exception after the cold entry is not handled: the image
  installs no exception vector table.

## Examples

### ex1: A record ends in CR LF

The record `CASXI_READY` and LF, written to a device that takes every byte,
comes out as the 13 bytes `CASXI_READY`, CR and LF.

### ex2: A stalled device fails the write and is reported

A device that never takes a byte, with a counter that does not move, fails
the write of a record after one million attempts at its first byte with the
reason `stalled`. The failure marker, the 48 bytes CR LF,
`CASXI_UART_FAIL reason=stalled`, CR LF, `CASXI_HALTED`, CR LF, then takes
48 attempts on a device that takes them.

### ex3: The echo adds LF after CR only

The received bytes `o`, `k`, CR, LF and `0xff` come back as `o`, `k`, CR,
LF, LF and `0xff`: only the carriage return gains a line feed.

## Design

- The cold entry is the prototype's QEMU entry: it masks exceptions first,
  parks every CPU but the boot CPU at EL1, makes FP/SIMD trap so that the
  softfloat kernel never touches FP/SIMD state by mistake, and clears BSS
  and the whole stack before the first Rust frame, so that a bounded walk
  of frame records never meets stale bytes.
- The console polls the PL011 and bounds each record twice: by attempts per
  byte, which ends the write even when the counter has stopped, and by a
  window on the counter, which a fast device cannot renew. The failure
  marker needs neither formatting nor the counter, so a broken clock cannot
  keep the CPU from halting. The bounds are platform parameters of the
  board, not constants tuned on one machine.
- The records keep the `CASXI_` names of the prototype's records, which
  the host tools parse, and hold no count, time or address, so that
  transcripts of cold boots compare byte for byte.
- One CPU owns the PL011, and no interrupt handler uses it. Secondary CPUs
  stay parked; their start needs entries of their own, which do not clear
  BSS again.
- Excluded: a console that waits without a bound, an interrupt-driven
  console, commands on the serial input and image variants chosen at build
  time.

## References

- Arm Limited, *Arm Architecture Reference Manual for A-profile
  architecture*, DDI 0487,
  <https://developer.arm.com/documentation/ddi0487/latest/>.
- Arm Limited, *Arm Cortex-A76 Core Technical Reference Manual*, revision
  r4p1, document 100798_0401_00_en, 2020,
  <https://documentation-service.arm.com/static/5f562083235b3560a01e03bc>.
- Arm Limited, *PrimeCell UART (PL011) Technical Reference Manual*, revision
  r1p5, DDI 0183G, 2007,
  <https://documentation-service.arm.com/static/5e8e36c2fd977155116a90b5>.
- The QEMU Project, *'virt' generic virtual platform*,
  <https://www.qemu.org/docs/master/system/arm/virt.html>.

## Implementation

- `kernel/arch/src/boot.S`, included by `kernel/arch/src/boot.rs`: the cold
  entry `_start`.
- `kernel/arch/src/cpu.rs`: the readers of `CurrentEL`, `MIDR_EL1`,
  `SCTLR_EL1`, `CNTFRQ_EL0`, `CNTVCT_EL0` and `CPACR_EL1`, and `halt`.
- `kernel/boards/qemu-virt/link.ld`, which
  `kernel/boards/qemu-virt/build.rs` hands the linker for the bare-metal
  target: the layout of the image at `0x4020_0000`, its 64 KiB stack with a
  guard page and its build-id note.
  The `.cargo/config.toml` of the repository root gives the target its
  build-id, relocation model and frame pointers.
- `kernel/boards/qemu-virt/src/lib.rs`: the PL011 address, the console bounds of
  QEMU virt and the CPU identity check `verify_cpu`.
- `kernel/boards/qemu-virt/src/main.rs`: `kernel_main` with the initialization
  checks, the boot records and the echo loop, and the panic handler.
- `kernel/boards/qemu-virt/src/uart.rs`: the PL011 setup, `try_put`, `get`, and
  `print`, `write_echo` and `report_panic`, which write within the bounds
  and report a failure.
- `kernel/boards/qemu-virt/src/console.rs` with `console/polled.rs` and
  `console/emitter.rs`: the bounded writes of a record and of bytes, the echo
  rule, the panic record and the failure markers.

## Verification

- **Host.** The tests of `kernel/boards/qemu-virt/src/console/` run in the
  `test` step of `cargo xtask check`: the examples above, the boundaries of a
  write and of the failure marker, and the tests taken from the prototype
  tree with their expected values. They establish the logic of the bounds
  with a device and a counter that the tests drive, not the PL011 or a
  machine's counter.
- **QEMU.** The case `cold-boot-echo` of the QEMU boot suite,
  `cargo xtask qemu-boot`, runs in the `check` workflow on QEMU virt
  `virt-8.2` with one Cortex-A76, 128 MiB and the host clock, at the QEMU
  version that `toolchains.toml` pins. It boots the release image three
  times, sends the 16 bytes `casxi-sim-check` and CR after `CASXI_READY`, and
  holds every transcript against the records of the boot contract and the
  three against each other; the receipts of the runs and of the suite are
  the evidence. It establishes the cold boot, the checks, the records and
  the echo on QEMU virt; it does not establish them on a Raspberry Pi 5, and
  a QEMU result is not a board result.
- **Proofs.** None: no theorem covers the feature, and the boot contract
  lists its code as [open obligations](../../domains/boot-platform/boot/contract.md#open-obligations).
- **Unverified.** The paths that QEMU's PL011 never takes, a full transmit
  FIFO and a stalled device, are shown only by the host tests.

## Limitations

- QEMU virt with one Cortex-A76 only; the Raspberry Pi 5 is not booted.
- Secondary CPUs park forever.
- No exception vectors: an exception after the cold entry is not reported.
- The MMU and the caches stay off, and the device tree is not read.
- The panic record has no backtrace and no build-id.
