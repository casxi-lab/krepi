---
features:
  - krepi.platform.qemu-virt-boot
---

# Boot requirements

The observable behaviour of the `boot` component of the
[boot and platform](../README.md) domain. The rules that its code and tests
follow are in the [contract](contract.md).

## Sources

- The cold entry, the processor primitives, the PL011 driver, the console
  with its bounded writes and the QEMU virt board support are ported from
  the prototype tree, with their host tests; the porting records
  [boot](../../../porting/boot.md), [cpu](../../../porting/cpu.md),
  [uart](../../../porting/uart.md), [console](../../../porting/console.md),
  [arch](../../../porting/arch.md) and
  [qemu-virt](../../../porting/qemu-virt.md) name the taken paths and the
  changes.
- The records, the checks and the bounds follow the Arm Architecture
  Reference Manual, the Cortex-A76 and PL011 manuals and the QEMU virt
  documentation that the [contract](contract.md#references) cites.
- The echo challenge and the shape of the boot case come from the
  prototype's QEMU boot suite; the
  [porting record of the suite](../../../porting/tools-qemu_boot.md) names
  it.

## Configurations

- **QEMU virt.** The machine `virt-8.2` without EL2 and EL3, with GICv2,
  one Cortex-A76, 128 MiB of RAM and no network card, under single-threaded
  TCG on the host clock, with the PL011 on QEMU's standard streams: the
  machine of `cargo xtask qemu`. The QEMU version is the one that
  `toolchains.toml` pins for the host.
- **Default image.** The release build, with overflow checks, of
  `krepi-qemu-virt` for `aarch64-unknown-none-softfloat`.
- **Host.** The host tests of the console run on the development host and
  in CI.
- The Raspberry Pi 5 is not a configuration of these requirements, and
  neither is more than one CPU.

## Requirements

### BOOT-R01

**Cold boot to the serial console.** A cold boot of the default image on
QEMU virt enters Rust at EL1 on the boot CPU, passes its initialization
checks and writes, each ending in CR LF, the CPU identity record of a
Cortex-A76, `CASXI_BOOT kernel=krepi board=qemu-virt el=1` and
`CASXI_READY`, in this order and nothing before them. It then echoes every
byte that it receives: the byte unchanged, and after a carriage return also
a line feed, so that the 16 bytes `casxi-sim-check` and CR come back as
those bytes followed by LF. Nothing else follows while no byte arrives. The
criterion: three cold boots, each in a new QEMU process, of the same image
give equal image digests and transcripts that are identical byte for byte,
each the three records followed by exactly the echo of the 16 bytes sent
after `CASXI_READY`.

- **Examples.** [ex3](../../../features/platform/qemu-virt-boot.md#ex3-the-echo-adds-lf-after-cr-only)
  of the QEMU virt boot feature document.
- **Entry points.** `_start`, `kernel_main`, `krepi_qemu_virt::uart::print`,
  `krepi_qemu_virt::uart::write_echo` and `krepi_qemu_virt::verify_cpu`.
- **Contract.** [Cold entry](contract.md#cold-entry),
  [Initialization checks](contract.md#initialization-checks),
  [Records](contract.md#records) and [Echo](contract.md#echo).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: the [open obligations](contract.md#open-obligations)
  of the contract carry its code.
- **Evidence.** The case `cold-boot-echo` of the QEMU boot suite,
  `cargo xtask qemu-boot`, in the `check` workflow of CI. It shows that the
  default image boots on the QEMU virt configuration into EL1, passes its
  checks, writes the three records and echoes the 16 bytes, and that three
  cold boots give the same transcript. It does not show the behaviour on a
  Raspberry Pi 5, on more than one CPU or with the MMU and the caches on,
  any exception handling, or the bounds of a console write, which QEMU's
  PL011 never reaches.

### BOOT-R02

**Bounded console output.** A console write of a record writes at most
1,024 bytes after each LF has become CR LF; it fails once a byte has been
refused `attempts_per_byte` times, also when the counter stops, or once the
record's window has passed on the counter, and it never restarts after a
failure. The PL011 driver then writes the failure marker,
`CASXI_UART_FAIL reason=<reason>` after a line break and `CASXI_HALTED`, with
at most `failure_attempts` attempts in all, and halts the CPU. The bounds
are platform parameters, on QEMU virt one million attempts per byte, one
million attempts for the marker and a window of 250 ms. A panic writes the
panic record of the [contract](contract.md#records), its static message or
a fixed text in place of any other, its location when it has one and
`CASXI_HALTED`, each line a record within the same bounds. The criterion:
the host tests of the console reach each failure and the marker of each,
count the attempts and hold the panic record byte for byte.

- **Examples.** [ex1](../../../features/platform/qemu-virt-boot.md#ex1-a-record-ends-in-cr-lf)
  and [ex2](../../../features/platform/qemu-virt-boot.md#ex2-a-stalled-device-fails-the-write-and-is-reported)
  of the QEMU virt boot feature document.
- **Entry points.** `krepi_qemu_virt::console::print`, `write`,
  `report_panic`, `report_failure` and `window_ticks`, and
  `krepi_qemu_virt::uart::print` and `report_panic`.
- **Contract.** [Console output](contract.md#console-output),
  [Records](contract.md#records) and
  [Platform parameters](contract.md#platform-parameters).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: the [open obligations](contract.md#open-obligations)
  of the contract carry its code.
- **Evidence.** The host tests of `kernel/boards/qemu-virt/src/console/`: the
  examples, boundaries and panic records of `console/tests.rs` and the
  tests taken from the prototype tree in `console/polled/tests.rs` and
  `console/emitter/tests.rs`, with their expected values. They show the
  bounds of the logic with a device and a counter that the tests drive.
  They do not show the PL011 or a counter of a machine.

## Liveness, time and performance

- A cold boot reaches `CASXI_READY` without waiting for input. The echo
  loop runs forever and answers every received byte.
- A console write ends within its window on a running counter and within
  `attempts_per_byte` refusals of one byte on a stopped one.
- The QEMU boot suite ends each run at its window of 20 s, a platform
  parameter of QEMU virt that leaves ample room for a boot that takes well
  under a second, and judges no time.

## Scope

- One CPU of QEMU virt: secondary CPUs park in the cold entry and never run
  kernel code.
- The MMU and the caches stay off, and the device tree is not read.
- No exception vector is installed, so an exception is not reported.
- The Raspberry Pi 5 entry, its firmware handoff and its UART are not
  covered.

## Contract sections without a requirement

- [Processor registers](contract.md#processor-registers): the functions
  serve the checks and the console of BOOT-R01 and BOOT-R02 and have no
  behaviour of their own that a requirement states.
- [Check and execute](contract.md#check-and-execute),
  [Work bounds](contract.md#work-bounds),
  [Determinism](contract.md#determinism) and
  [State fields](contract.md#state-fields) bind the code without an
  observable behaviour of their own.
