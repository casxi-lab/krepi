---
features:
  - krepi.platform.qemu-virt-boot
---

# Boot requirements

The observable behaviour of the `boot` component of the
[boot and platform](../README.md) domain. The rules that its code and tests
follow are in the [contract](contract.md).

## Sources

- The cold entry, the exception vectors with their frame, the processor
  primitives, the PL011 driver, the console with its bounded writes, the
  exception record and the QEMU virt board support are ported from the
  prototype tree, with their host tests; the porting records
  [boot](../../../porting/boot.md),
  [exception](../../../porting/exception.md), [cpu](../../../porting/cpu.md),
  [uart](../../../porting/uart.md), [console](../../../porting/console.md),
  [fault](../../../porting/fault.md), [arch](../../../porting/arch.md) and
  [qemu-virt](../../../porting/qemu-virt.md) name the taken paths and the
  changes.
- The records, the checks and the bounds follow the Arm Architecture
  Reference Manual, the Cortex-A76 and PL011 manuals and the QEMU virt
  documentation that the [contract](contract.md#references) cites.
- The echo challenge and the shape of the boot case come from the
  prototype's QEMU boot suite, and the expected fields of the FP/SIMD trap
  from its suite of interrupts; the
  [porting record of the suite](../../../porting/tools-qemu_boot.md) names
  them. The test images and their self-checks are new.

## Configurations

- **QEMU virt.** The machine `virt-8.2` without EL2 and EL3, with GICv2,
  one Cortex-A76, 128 MiB of RAM and no network card, under single-threaded
  TCG on the host clock, with the PL011 on QEMU's standard streams: the
  machine of `cargo xtask qemu`. The QEMU version is the one that
  `toolchains.toml` pins for the host.
- **QEMU virt with EL2.** The same machine with EL2,
  `virt-8.2,secure=off,virtualization=on,gic-version=2`, which enters an
  image at EL2: only for the test image of the SError.
- **Default image.** The release build, with overflow checks, of
  `krepi-qemu-virt` for `aarch64-unknown-none-softfloat`.
- **Test images.** The release builds of the examples of the QEMU virt
  board crate for the same target: each links the cold entry, the
  exception vectors, the console and the exception record of the default
  image and adds its own `kernel_main`, dispatch and trigger sequence.
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
  the exception handling, which the requirements below cover, or the bounds
  of a console write, which QEMU's PL011 never reaches.

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

### BOOT-R03

**A breakpoint at EL1 is reported and returned from.** A `BRK #imm` at EL1
with `SP_EL1` enters vector 4. The entry saves the frame of the
[contract](contract.md#frames) on `SP_EL1` just below the interrupted stack
pointer, with `x0` to `x30` as they were, that stack pointer, `ELR_EL1`,
`SPSR_EL1`, `ESR_EL1`, `FAR_EL1` and the vector number. The exception
record names the vector, the four registers and the class `brk`, with the
syndrome of EC `0x3c` and the immediate as its ISS and the address of the
`BRK` as `ELR`. When the dispatch moves the frame's `ELR` past the `BRK` and
returns, execution continues after it with the `PSTATE` of the frame's
`SPSR` and the stack pointer of before the exception. The criterion: the
case `el1-brk` passes, and the host tests of the record and of the classes
hold their bytes and classes.

- **Examples.** [ex4](../../../features/platform/qemu-virt-boot.md#ex4-a-breakpoint-is-reported-with-its-registers)
  and
  [ex6](../../../features/platform/qemu-virt-boot.md#ex6-a-breakpoint-through-another-entry-is-sync)
  of the QEMU virt boot feature document.
- **Entry points.** `__exception_vectors`, `exception_dispatch`,
  `krepi_qemu_virt::uart::report_exception`, `krepi_qemu_virt::fault::report`
  and `krepi_arch::exception::Class::of`.
- **Contract.** [Exception vectors](contract.md#exception-vectors),
  [Frames](contract.md#frames), [Dispatch](contract.md#dispatch) and
  [Records](contract.md#records).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: the [open obligations](contract.md#open-obligations)
  of the contract carry its code and its rules of saved and restored state.
- **Evidence.** The case `el1-brk` of `cargo xtask qemu-boot`, in CI, with
  the five self-checks of its test image: `frame-records-interrupted-sp`,
  that the frame lies 304 bytes below the stack pointer of before the
  breakpoint, 16-byte aligned, and records it; `entry-saves-general-registers`,
  that the frame holds the distinct values that the code put into `x0` to
  `x30`; `frame-records-system-registers`, that the frame holds the four
  exception registers as the dispatch reads them, the vector number 4, a
  reserved word of 0, the address of the `BRK`, its syndrome and the NZCV,
  DAIF and mode of before it; `return-restores-elr-and-pstate`, that the code
  continues after the `BRK`, once, with the NZCV that the dispatch wrote into
  the frame and the DAIF, exception level and stack selection of before it;
  and `return-restores-sp`, that the stack pointer after the return is that
  of before. The case checks the record's vector, class, syndrome and the
  address of the symbol of the `BRK` in the image. The host tests of
  `kernel/boards/qemu-virt/src/fault/` and `kernel/arch/src/exception/`
  hold the record and the classes. It shows the save and return of vectors
  4 to 7 for a synchronous exception on QEMU virt: a register stored after
  the entry changed it, such as `x0` after the vector number, would fail
  `entry-saves-general-registers`. It does not show the behaviour of the
  other vectors, which no image takes, or the vectors on a Raspberry Pi 5.

### BOOT-R04

**An SError at EL1 is reported and halts.** On QEMU virt with EL2, a
virtual SError that EL2 makes pending through `HCR_EL2.VSE`, with
`HCR_EL2.AMO` set and EL1 in AArch64, is taken at EL1 through vector 7 once
the code unmasks SErrors. The exception record names vector 7, the class
`serror`, a syndrome of EC `0x2f` and an `ELR` in the code that unmasked
SErrors, and `CASXI_HALTED` follows it; nothing comes after. The criterion:
the case `injected-serror` passes on the machine with EL2.

- **Examples.** None of its own: the record is that of BOOT-R03.
- **Entry points.** `__exception_vectors`, `exception_dispatch` and
  `krepi_qemu_virt::uart::report_fatal`.
- **Contract.** [Exception vectors](contract.md#exception-vectors),
  [Dispatch](contract.md#dispatch) and [Records](contract.md#records).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: the [open obligations](contract.md#open-obligations)
  of the contract carry its code.
- **Evidence.** The case `injected-serror` of `cargo xtask qemu-boot`, in
  CI. Its test image enters at EL2 with an entry of its own, sets `HCR_EL2`
  to RW, AMO and VSE, the virtual SError syndrome to 0 and the virtual
  offset to 0, and returns to `_start` at EL1; it then unmasks SErrors, and
  its dispatch is that of the default image. The case checks the machine
  with EL2 in the receipt, the record's vector, class and exception class,
  an `ELR` between the symbols that bound the unmasking code, and the halt
  with nothing after it. It shows that the vector of SErrors of EL1 takes
  the virtual SError and that the fatal path reports and halts, on QEMU.
  It does not show a physical SError, which QEMU virt without EL2 has no
  source for, the behaviour on a Raspberry Pi 5, or the default image on
  the machine with EL2.

### BOOT-R05

**An FP/SIMD access at EL1 traps and halts.** With `CPACR_EL1.FPEN` 0, as
the cold entry leaves it, an FP/SIMD instruction at EL1 traps to vector 4.
The exception record names the class `fp`, a syndrome of EC `0x07` and the
address of the instruction as `ELR`, and `CASXI_HALTED` follows it; nothing
comes after. The kernel saves no FP/SIMD state on exception entry or
return. The criterion: the case `el1-fp-trap` passes.

- **Examples.** [ex5](../../../features/platform/qemu-virt-boot.md#ex5-a-fatal-exception-ends-in-the-halt-record)
  of the QEMU virt boot feature document.
- **Entry points.** `_start`, `__exception_vectors`, `exception_dispatch`,
  `krepi_qemu_virt::uart::report_fatal` and
  `krepi_qemu_virt::fault::report_fatal`.
- **Contract.** [Cold entry](contract.md#cold-entry),
  [Exception vectors](contract.md#exception-vectors),
  [Dispatch](contract.md#dispatch) and [Records](contract.md#records).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: the [open obligations](contract.md#open-obligations)
  of the contract carry its code and the rule that no FP/SIMD state is
  saved.
- **Evidence.** The case `el1-fp-trap` of `cargo xtask qemu-boot`, in CI,
  which is also the test of the rule `no-fp-state`. Its test image executes
  `FMOV D0, XZR` at a symbol of its own, and its dispatch is that of the
  default image. The case checks the record's vector, class, exception
  class and the address of the symbol, and the halt with nothing after it.
  It shows that FP/SIMD instructions at EL1 trap on QEMU and that the fatal
  path reports and halts. It does not show that no other code of the
  kernel enables FP/SIMD, which the review of `CPACR_EL1` writes holds, or
  the trap on a Raspberry Pi 5.

## Liveness, time and performance

- A cold boot reaches `CASXI_READY` without waiting for input. The echo
  loop runs forever and answers every received byte.
- A console write ends within its window on a running counter and within
  `attempts_per_byte` refusals of one byte on a stopped one.
- The QEMU boot suite ends each run at its window of 20 s, a platform
  parameter of QEMU virt that leaves ample room for a boot that takes well
  under a second, and judges no time. A test image either halts or ends in
  `CASXI_RESUMED` and then waits, so its run ends at its window too.

## Scope

- One CPU of QEMU virt: secondary CPUs park in the cold entry and never run
  kernel code.
- The MMU and the caches stay off, and the device tree is not read.
- The vectors of the current level with `SP_EL0` and of a lower level halt
  after their dispatch returns; the kernel handles no such exception, and
  no image takes one. Every exception of the default image halts, and only
  test images return from an exception.
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
