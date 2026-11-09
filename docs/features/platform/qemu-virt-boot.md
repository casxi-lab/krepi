---
id: krepi.platform.qemu-virt-boot
title: QEMU virt boot
status: partial
modules:
  - kernel/arch/src/boot.rs
  - kernel/arch/src/boot.S
  - kernel/arch/src/cpu.rs
  - kernel/arch/src/exception.rs
  - kernel/arch/src/exception.S
  - kernel/boards/qemu-virt/build.rs
  - kernel/boards/qemu-virt/src/lib.rs
  - kernel/boards/qemu-virt/src/main.rs
  - kernel/boards/qemu-virt/src/uart.rs
  - kernel/boards/qemu-virt/src/console.rs
  - kernel/boards/qemu-virt/src/console/polled.rs
  - kernel/boards/qemu-virt/src/console/emitter.rs
  - kernel/boards/qemu-virt/src/fault.rs
tests:
  - kernel/arch/src/exception/tests.rs
  - kernel/boards/qemu-virt/src/console/tests.rs
  - kernel/boards/qemu-virt/src/console/polled/tests.rs
  - kernel/boards/qemu-virt/src/console/emitter/tests.rs
  - kernel/boards/qemu-virt/src/fault/tests.rs
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
every console write bounded by the platform parameters of the machine. Its
exception vectors take the exceptions of EL1, save their frame and report
each in an exception record; the default image then halts, and test images
of the QEMU boot suite return from the exceptions that they cause. The
feature belongs to the kernel at EL1. It does not boot a Raspberry Pi 5,
start secondary CPUs, read the device tree, turn the MMU or the caches on or
handle an exception of EL0.

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
  `CASXI_CPU`, `CASXI_BOOT` and `CASXI_READY`, for an exception
  `CASXI_EXCEPTION` and, on a fatal path, `CASXI_PANIC`,
  `CASXI_PANIC_LOCATION`, `CASXI_UART_FAIL` and `CASXI_HALTED`, in the forms
  of the
  [records of the boot contract](../../domains/boot-platform/boot/contract.md#records).
  After `CASXI_READY` it echoes each received byte.
- **Exception vectors.** `__exception_vectors` of `krepi-arch`, which the
  cold entry installs in `VBAR_EL1`, calls the image's
  `exception_dispatch(&mut Frame)` with the frame of the exception; the
  [boot contract](../../domains/boot-platform/boot/contract.md#exception-vectors)
  states the frame and the rules of the saved and restored state.
- **Kernel functions.** `krepi_qemu_virt::uart::print` writes a record,
  `krepi_qemu_virt::uart::write_echo` echoes a byte,
  `krepi_qemu_virt::uart::report_panic` writes the panic record,
  `krepi_qemu_virt::uart::report_exception` and `report_fatal` write the
  exception record, the second with `CASXI_HALTED` and the halt, and the
  host-testable `krepi_qemu_virt::console` and `krepi_qemu_virt::fault`
  functions do so for any device and counter;
  `krepi_arch::cpu` reads the processor registers of EL1 and halts the CPU,
  and `krepi_arch::exception` gives the frame and the class of an
  exception.
  The [entry points of the boot contract](../../domains/boot-platform/boot/contract.md#entry-points)
  list them.
- **Suite.** `cargo xtask qemu-boot` builds the default image and the test
  images, the examples of `kernel/boards/qemu-virt`, and runs the QEMU boot
  suite on them ([testing](../../conventions/testing.md#entry-points)).

## Semantics

- **Entry.** Only the boot CPU at EL1 enters Rust; any other CPU, and a CPU
  at another exception level, parks in the cold entry. The exception
  vectors are installed, every exception stays masked, and FP/SIMD
  instructions trap.
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
- **Exceptions.** An exception taken to EL1 enters one of the 16 vectors,
  which save the frame on `SP_EL1` and call the dispatch with every
  exception masked. The dispatch of the default image writes the exception
  record, with the vector, `ESR`, `ELR`, `FAR`, `SPSR` and the class `brk`,
  `fp`, `sync`, `irq`, `fiq` or `serror`, then `CASXI_HALTED`, and halts.
  Only the four vectors of the current level with `SP_EL1` can return:
  after their dispatch returns, `ELR_EL1`, `SPSR_EL1` and `x0` to `x30` are
  loaded from the frame. FP/SIMD state is never saved, as FP/SIMD
  instructions trap.
- **Undefined.** An exception before the cold entry has installed the
  vectors is not handled, and one that leaves `SP_EL1` without 304 bytes of
  room overwrites what lies below it.

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

### ex4: A breakpoint is reported with its registers

The frame of `BRK #0xc5` at vector 4, with `ESR` `0xf20000c5`, `ELR`
`0x4020_1000`, `FAR` 0 and `SPSR` `0x3c5`, gives the record CR LF,
`CASXI_EXCEPTION vector=4 ESR=0x00000000f20000c5 ELR=0x0000000040201000
FAR=0x0000000000000000 SPSR=0x00000000000003c5 class=brk`, CR LF.

### ex5: A fatal exception ends in the halt record

An FP/SIMD trap at vector 4, `ESR` `0x1fe00000`, on a fatal path gives its
record with `class=fp` and then `CASXI_HALTED`, CR LF.

### ex6: A breakpoint through another entry is sync

The syndrome of a breakpoint taken through vector 0, the current level with
`SP_EL0`, is not a breakpoint of the kernel: the record names the class
`sync`. This is the degenerate input of the class table.

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
- The exception vectors are the prototype's: one save path for the 16
  entries, a frame of 304 bytes on `SP_EL1` that the dispatch receives and
  may change, and a return that loads the exception registers and every
  general register from the frame, after clearing them, so that no value of
  the dispatch leaks into the interrupted code. Only the entries of the
  current level with `SP_EL1` return; the others, which need `SP_EL0` and
  rules of their own, halt.
- The exception record keeps the fields of the prototype's record, which the
  host tools parse, and adds the class of the exception at the end. It is
  written through the same bounded writes as every other record.
- One CPU owns the PL011. A dispatch writes it only through the exception
  record, with every exception masked, between two accesses of the code
  that it interrupted. Secondary CPUs stay parked; their start needs entries
  of their own, which do not clear BSS again.
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
  entry `_start`, which installs the exception vectors.
- `kernel/arch/src/exception.S`, included by
  `kernel/arch/src/exception.rs`: the vector table `__exception_vectors`;
  `exception.rs` also holds `Frame` and `Class`.
- `kernel/arch/src/cpu.rs`: the readers of `CurrentEL`, `MIDR_EL1`,
  `SCTLR_EL1`, `CNTFRQ_EL0`, `CNTVCT_EL0` and `CPACR_EL1`, and `halt`.
- `kernel/boards/qemu-virt/link.ld`, which
  `kernel/boards/qemu-virt/build.rs` hands the linker for the bare-metal
  target: the layout of the images at `0x4020_0000`, with the vectors after
  the cold entry, the 64 KiB stack with a guard page and the build-id note.
  The build script also gives the test images their entry
  `krepi_test_entry`.
  The `.cargo/config.toml` of the repository root gives the target its
  build-id, relocation model and frame pointers.
- `kernel/boards/qemu-virt/src/lib.rs`: the PL011 address, the console bounds
  of QEMU virt and the constants of the CPU identity check.
- `kernel/boards/qemu-virt/src/main.rs`: `kernel_main` with the initialization
  checks, the CPU identity check `verify_cpu`, the boot records and the echo
  loop, the exception dispatch and the panic handler.
- `kernel/boards/qemu-virt/src/uart.rs`: the PL011 setup, `try_put`, `get`, and
  `print`, `write_echo`, `report_panic`, `report_exception` and
  `report_fatal`, which write within the bounds and report a failure.
- `kernel/boards/qemu-virt/src/fault.rs`: the exception record and the
  record of the fatal path.
- `kernel/boards/qemu-virt/src/console.rs` with `console/polled.rs` and
  `console/emitter.rs`: the bounded writes of a record and of bytes, the echo
  rule, the panic record and the failure markers.

## Verification

- **Host.** The tests of `kernel/boards/qemu-virt/src/console/`,
  `kernel/boards/qemu-virt/src/fault/` and `kernel/arch/src/exception/` run
  in the `test` step of `cargo xtask check`: the examples above, the
  boundaries of a write and of the failure marker, the exception record of
  each kind of entry, the classes of the vectors and syndromes, and the
  tests taken from the prototype tree with their expected values. They
  establish the logic of the bounds and of the records with a device and a
  counter that the tests drive, not the PL011, a machine's counter or the
  vectors.
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
- **QEMU, exceptions.** The cases `el1-brk`, `injected-serror` and
  `el1-fp-trap` of the same suite boot a test image each, in release, on the
  same machine or, for `injected-serror`, on the machine with EL2, and hold
  the transcript against the exact records of the case: the exception
  record with its vector, class, syndrome and an `ELR` at a symbol of the
  image, then the halt or the self-checks of the frame and of the return,
  each with no failure. They establish the vectors, the frame, the return
  of a synchronous exception, the virtual SError and the FP/SIMD trap on
  QEMU virt, not on a Raspberry Pi 5; the virtual SError needs EL2, which
  the default image does not run with.
- **Proofs.** None: no theorem covers the feature, and the boot contract
  lists its code as [open obligations](../../domains/boot-platform/boot/contract.md#open-obligations).
- **Unverified.** The paths that QEMU's PL011 never takes, a full transmit
  FIFO and a stalled device, are shown only by the host tests.

## Limitations

- QEMU virt with one Cortex-A76 only; the Raspberry Pi 5 is not booted.
- Secondary CPUs park forever.
- Every exception of the default image halts; no exception of EL0 or with
  `SP_EL0` is handled.
- The MMU and the caches stay off, and the device tree is not read.
- The panic record has no backtrace and no build-id.
