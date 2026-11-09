---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - src/fault.rs
destination:
  - kernel/boards/qemu-virt/src/fault.rs
  - kernel/boards/qemu-virt/src/fault/tests.rs
treatment: ported
features:
  - krepi.platform.qemu-virt-boot
---

# Porting record: kernel/boards/qemu-virt/src/fault.rs

## Summary

The exception record of the kernel: the line `CASXI_EXCEPTION` that
`fault::exception` of the legacy `src/fault.rs` wrote for an exception that
the vectors took, and `CASXI_HALTED` after it on a fatal path. The module
`fault` of `krepi-qemu-virt` formats the record from the frame of
[exception](exception.md) and writes it through the bounded console writes
of [console](console.md), with the device and the counter as callbacks, so
that the host tests hold its bytes. The PL011 driver, [uart](uart.md),
writes it on the board within the console bounds and halts after a fatal
record or a failed write. The legacy file `src/fault.rs` lies at the root of
the legacy `src/` tree, outside the areas that
[porting](../conventions/porting.md#classification-of-the-legacy-areas)
lists; the panic record taken from it is in the
[qemu-virt](qemu-virt.md) and [console](console.md) records.

## Changes

- The record keeps the legacy fields and their order and form, `vector=`
  in decimal and `ESR=`, `ELR=`, `FAR=` and `SPSR=` with `0x` and 16
  lowercase hexadecimal digits, after a line break, and adds the class of
  the exception, `class=<name>`, at the end, so that the record parsers of
  the host tools read it as before.
- The record and `CASXI_HALTED` are each a record of their own, written by
  `console::print` within the console bounds of the board: the attempts per
  byte and the window on the counter of the
  [boot contract](../domains/boot-platform/boot/contract.md#platform-parameters).
  The legacy record gathered its whole text in a fixed-capacity buffer and
  wrote it with a fixed allowance of 131,072 attempts per byte,
  `TX_ATTEMPTS_PER_BYTE`, and no window.
- The record is written for an exception after which the dispatch returns
  as well as for a fatal one: `report` writes the record, `report_fatal` the
  record and `CASXI_HALTED`. The legacy function always halted.
- The formatting is host-testable: the functions take the device and the
  counter as callbacks, as the console functions do, and the PL011 glue,
  `uart::report_exception` and `uart::report_fatal`, lives in the driver
  with the panic glue.
- The legacy path masked IRQs and took the console over from its lease
  first. The dispatch runs with every exception masked already, and the
  console has no lease.
- The line `//! Feature: krepi.platform.qemu-virt-boot` names the feature.

## Tests carried over

None: the legacy tree had no host test of the fault record. The new tests
of `kernel/boards/qemu-virt/src/fault/tests.rs` hold the bytes of the
records, written from the record table of the boot contract, among them the
examples ex4 to ex6 of the
[QEMU virt boot feature](../features/platform/qemu-virt-boot.md#examples).

## Behaviour changes

| Change | Evidence |
| --- | --- |
| The record ends in `class=<name>` | `fault::tests::examples::ex4_a_breakpoint_is_reported_with_its_registers`, `fault::tests::each_kind_of_entry_names_its_class` |
| The record and `CASXI_HALTED` are records within the console bounds, and no record follows a failed one | `fault::tests::examples::ex5_a_fatal_exception_ends_in_the_halt_record`, `fault::tests::a_failed_record_writes_no_halt_record` |
| No frame trace, `CASXI_DIAG`, `CASXI_BT` or `CASXI_TRACE`, and no build-id follow the record | `fault::tests::examples::ex5_a_fatal_exception_ends_in_the_halt_record` |

## Hardware evidence to re-obtain

- The records of a breakpoint, an FP/SIMD trap, a virtual SError and timer
  IRQs on QEMU virt with one Cortex-A76: the cases `el1-brk`, `el1-fp-trap`,
  `injected-serror`, `timer-irq` and `irq-preserves-registers` of
  `cargo xtask qemu-boot`, in CI.
- The records on the Pi 5, on the HIL bench (planned).

## Not carried over

- The frame trace of the fault record, `append_trace` with `stack_bounds`
  and the frame walk, and the build-id of `build_id`: they come with fault
  symbolization.
- `trace_probe`, a diagnostic probe: the default image holds none.
- `emit`, which wrote through `emit_progress_bounded`, and the record
  buffer: see the [console](console.md#not-carried-over) record.
- The console takeover of the lease: the console has no lease.
- The panic record, which the [qemu-virt](qemu-virt.md) and
  [console](console.md) records cover.
- The legacy feature annotation `system.kernel.foundations` of
  `src/fault.rs`.
