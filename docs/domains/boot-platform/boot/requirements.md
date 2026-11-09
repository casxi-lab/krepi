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
  primitives, the GICv2 and timer drivers with the interrupt wiring of QEMU
  virt, the PL011 driver, the console with its bounded writes, the
  exception record and the QEMU virt board support are ported from the
  prototype tree, with their host tests; the porting records
  [boot](../../../porting/boot.md),
  [exception](../../../porting/exception.md), [cpu](../../../porting/cpu.md),
  [gic](../../../porting/gic.md), [timer](../../../porting/timer.md),
  [irq](../../../porting/irq.md), [uart](../../../porting/uart.md),
  [console](../../../porting/console.md), [fault](../../../porting/fault.md),
  [cache](../../../porting/cache.md),
  [cache_range](../../../porting/cache_range.md),
  [arch](../../../porting/arch.md) and
  [qemu-virt](../../../porting/qemu-virt.md) name the taken paths and the
  changes. The cache and TLB maintenance takes the clean, the invalidations
  and the line walks of the prototype tree; its TLB invalidation of a page
  is new.
- The records, the checks and the bounds follow the Arm Architecture
  Reference Manual, the Cortex-A76 and PL011 manuals and the QEMU virt
  documentation that the [contract](contract.md#references) cites.
- The echo challenge and the shape of the boot case come from the
  prototype's QEMU boot suite, and the expected fields of the timer IRQ, of
  the registers across it and of the FP/SIMD trap from its suite of
  interrupts; the
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
  image and adds its own `kernel_main`, dispatch and trigger sequence. The
  test image of BOOT-R13 turns the MMU on with translation tables of its
  own and keeps the data and instruction caches off; every other image
  runs with the MMU and the caches off, as QEMU leaves them.
- **Host.** The host tests of the console, of the exception record, of
  the exception classes and of the cache-line walks run on the development
  host and in CI.
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
  `krepi_qemu_virt::uart::write_echo` and `verify_cpu` in
  `kernel/boards/qemu-virt/src/main.rs`.
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
  hold the record and the classes. It shows the save and return of vector
  4 for a synchronous exception on QEMU virt: a register stored after the
  entry changed it, such as `x0` after the vector number, would fail
  `entry-saves-general-registers`. It does not show the return of vectors 6
  and 7, which no image returns from, the vectors 1 to 3 and 8 to 15, which
  no image takes, or the vectors on a Raspberry Pi 5; BOOT-R06 and BOOT-R08
  show vectors 5 and 0.

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

### BOOT-R06

**The timer interrupt is taken, ended and returned from.** With the
interrupts set up by `irq::init`, the virtual timer of QEMU virt interrupts
through the GICv2 as interrupt 27 once a period, 10 ms, has passed, and the
IRQ vector of the current level with `SP_EL1`, vector 5, takes it when the
code unmasks IRQs. The dispatch runs with D, A, I and F masked. Each
interrupt is reported in an exception record with vector 5, the class
`irq` and an `ELR` in the interrupted code; `irq::handle` acknowledges it,
re-arms the timer and ends it, and the dispatch returns to the interrupted
code, which a second interrupt reaches again. The criterion: the case
`timer-irq` passes.

- **Examples.** None of its own: the record is that of BOOT-R03.
- **Entry points.** `__exception_vectors`, `exception_dispatch`,
  `krepi_qemu_virt::irq::init` and `krepi_qemu_virt::irq::handle`, with the
  GICv2 and timer functions of `krepi-arch`.
- **Contract.** [Interrupts](contract.md#interrupts),
  [Exception vectors](contract.md#exception-vectors),
  [Dispatch](contract.md#dispatch) and [Records](contract.md#records).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: the [open obligations](contract.md#open-obligations)
  of the contract carry its code and the rule `mask`.
- **Evidence.** The case `timer-irq` of `cargo xtask qemu-boot`, in CI, with
  the two self-checks of its test image: `timer-irq`, that exactly two
  timer interrupts came within the wait and no other interrupt, and that
  the second entered the dispatch at least one period, on the virtual
  count, after the first; and `dispatch-masks-daif`, the test of the rule
  `mask`, that `DAIF` had D, A, I and F set at each entry of the dispatch.
  Taking an exception to EL1 sets the four bits, and the save path sets
  them again, so the check shows that they are set during the dispatch but
  not which of the two set them; it does not show that the return path sets
  them again, which matters only for a dispatch that unmasks, and none
  does. The image waits with IRQs unmasked in code of its own and stops the
  timer after the second interrupt. The case checks two IRQ records with an
  `ELR` between the symbols of the waiting code. The second interrupt shows
  that the end of interrupt of the first took effect, as the GICv2 signals
  no interrupt that is still active, and its distance from the first shows
  the re-arm: without it the timer keeps its level up after the end of
  interrupt, and the second interrupt comes at once. It does not show that
  the period is 10 ms, as the check bounds the distance only from below, an
  interrupt other than the timer interrupt, which BOOT-R09 covers, or the
  GIC-400 of a Raspberry Pi 5.

### BOOT-R07

**An IRQ leaves the interrupted registers unchanged.** When the timer
interrupt is taken at an instruction L of the interrupted code, the frame
holds L as `ELR` and the interrupted `PSTATE` as `SPSR`: NZCV as set, D, A
and F masked, I unmasked, and EL1 with `SP_EL1`. After the dispatch
returns, execution continues at L with `x0` to `x30`, the stack pointer and
NZCV as they were before the interrupt, and `ELR_EL1` and `SPSR_EL1` equal
to the frame's. The criterion: the case `irq-preserves-registers` passes.

- **Examples.** None of its own.
- **Entry points.** `__exception_vectors`, `exception_dispatch` and
  `krepi_qemu_virt::irq::handle`.
- **Contract.** [Exception vectors](contract.md#exception-vectors),
  [Frames](contract.md#frames) and [Dispatch](contract.md#dispatch).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: the [open obligations](contract.md#open-obligations)
  of the contract carry its code and the rule `clear-and-load`.
- **Evidence.** The case `irq-preserves-registers` of
  `cargo xtask qemu-boot`, in CI, which is also the test of the rule
  `clear-and-load`. Its test image waits with IRQs masked until `ISR_EL1`
  shows the timer interrupt pending, puts a different known value into
  each of `x0` to `x30`, sets NZCV and unmasks IRQs; the instruction after
  the unmask, the symbol `krepi_test_irq_resume`, masks them again and
  starts recording. Its self-check holds `ELR` and `SPSR` of the frame,
  the registers read after the return, the stack pointer and NZCV, and the
  case checks the IRQ record's `ELR` against the symbol. That QEMU takes a
  pending IRQ right after the unmask is a property of QEMU, which the case
  relies on; the architecture only requires that the IRQ be taken in finite
  time. A missed load would leave a register at 0, and a load from the
  wrong place another value, so both fail the check; the clear before the
  loads, which no load misses, has no effect that the check can see. It
  does not show a second interrupt during the return, which the masking of
  the return path excludes, or the behaviour on a Raspberry Pi 5.

### BOOT-R08

**An exception with `SP_EL0` is reported and halts.** A `BRK #imm` at EL1
with `SP_EL0` selected enters vector 0. The entry saves the frame on
`SP_EL1`, and the frame records the stack pointer above it on `SP_EL1`, not
`SP_EL0`. The exception record names vector 0, the class `sync`, the
syndrome of EC `0x3c` with the immediate and the address of the `BRK` as
`ELR`. When the dispatch returns, even with the frame's `ELR` moved past the
`BRK`, the vectors do not return to the interrupted code: they halt with
every exception masked, and nothing follows the records of the dispatch.
The criterion: the case `sp-el0-brk` passes.

- **Examples.** [ex6](../../../features/platform/qemu-virt-boot.md#ex6-a-breakpoint-through-another-entry-is-sync)
  of the QEMU virt boot feature document.
- **Entry points.** `__exception_vectors`, `exception_dispatch`,
  `krepi_qemu_virt::uart::report_exception` and
  `krepi_arch::exception::Class::of`.
- **Contract.** [Exception vectors](contract.md#exception-vectors),
  [Frames](contract.md#frames), [Dispatch](contract.md#dispatch) and
  [Records](contract.md#records).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: the [open obligations](contract.md#open-obligations)
  of the contract carry its code.
- **Evidence.** The case `sp-el0-brk` of `cargo xtask qemu-boot`, in CI,
  with the self-check of its test image, `sp-el0-frame-records-sp-el1`:
  that the frame records the address just above it, the `SP_EL1` of before
  the breakpoint and not the value that the image put into `SP_EL0`, and
  that `SPSR` names EL1 with `SP_EL0`. The dispatch writes the record and
  the self-check, moves the frame's `ELR` past the `BRK` and returns; had
  the vectors returned, the image would write `CASXI_RESUMED`. The case
  checks the record's vector, class, syndrome and the address of the symbol
  of the `BRK`, and that nothing follows the self-check. It shows the halt
  of vector 0 after its dispatch on QEMU virt. It does not show vectors 1 to
  3 and 8 to 15, which share its path but which no image takes, or the
  vectors on a Raspberry Pi 5.

### BOOT-R09

**An interrupt other than the timer interrupt is disabled and ended.**
With the interrupts set up by `irq::init`, an interrupt that the board does
not expect, here the physical timer of the CPU, interrupt 30, enabled by the
code, is taken through vector 5 when the code unmasks IRQs and reported in
an exception record with vector 5, the class `irq` and an `ELR` in the
interrupted code. `irq::handle` acknowledges it, disables it in the GICv2
and ends it, so that it does not come again although its source keeps its
level up, and the dispatch returns. The criterion: the case
`unexpected-irq` passes.

- **Examples.** None of its own: the record is that of BOOT-R03.
- **Entry points.** `__exception_vectors`, `exception_dispatch`,
  `krepi_qemu_virt::irq::init` and `krepi_qemu_virt::irq::handle`, with the
  GICv2 functions of `krepi-arch`.
- **Contract.** [Interrupts](contract.md#interrupts),
  [Exception vectors](contract.md#exception-vectors) and
  [Records](contract.md#records).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: the [open obligations](contract.md#open-obligations)
  of the contract carry its code.
- **Evidence.** The case `unexpected-irq` of `cargo xtask qemu-boot`, in CI,
  with the self-check of its test image, `unexpected-irq-disabled`: that
  the dispatch was entered once, that `irq::handle` returned the
  interrupt 30 as unexpected and that `GICD_ISENABLER0` no longer enables
  it. The image stops the virtual timer after `irq::init`, enables
  interrupt 30 with `Gic::enable_ppi` and arms the physical timer to fire at
  once, so that its level stays up until the image stops it after the wait.
  The case checks one IRQ record with an `ELR` between the symbols of the
  waiting code. It shows the path of an unexpected interrupt on QEMU virt.
  It does not show a special interrupt ID, which QEMU gives only when no
  interrupt is pending, a device interrupt, or the GIC-400 of a Raspberry Pi
  5.

### BOOT-R10

**Cache-line walks of a range.** The walk of `[start, start + bytes)` at
lines of `4 << field` bytes gives the address of the line of `start`,
rounded down to a multiple of the line size, and of every line after it that
starts below `start + bytes`, and nothing else; it refuses a range that is
empty, longer than its limit or that wraps past the end of the address
space, and a field above 15, before it gives any address. The walk of an
image that firmware hands over gives the same lines and also refuses an
image that does not start at the start of its window, is not page aligned,
ends beyond the window or has lines of more than 4 KiB. The walks of the
cache maintenance take their line size from a value of `CTR_EL0`, the data
walk from `DminLine`, bits 16 to 19, and the instruction walk from
`IminLine`, bits 0 to 3, and walk at most 64 KiB. The criterion: the host
tests of `kernel/arch/src/cache_range/` pass.

- **Examples.**
  [ex7](../../../features/platform/qemu-virt-boot.md#ex7-a-range-with-unaligned-ends-covers-each-line-it-touches)
  and
  [ex8](../../../features/platform/qemu-virt-boot.md#ex8-an-empty-or-oversized-range-is-refused)
  of the QEMU virt boot feature document.
- **Entry points.** `krepi_arch::cache_range::lines`, `data_lines`,
  `instruction_lines`, `handoff_lines` and `MAX_RANGE_BYTES`.
- **Contract.** [Cache-line walks](contract.md#cache-line-walks) and
  [Work bounds](contract.md#work-bounds).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: the [open obligations](contract.md#open-obligations)
  of the contract carry its code.
- **Evidence.** The host tests of `kernel/arch/src/cache_range/`, in the
  `test` step of `cargo xtask check`: the three tests taken from the
  prototype tree with their expected values, of partial lines and exact
  boundaries, of empty, oversized, wrapping and wide-field requests and of
  the walk of a whole image in the windows of the Raspberry Pi 5 and of QEMU
  virt, the examples ex7 and ex8, and the walks of the maintenance at a
  value of `CTR_EL0` whose four line and granule fields differ, which hold
  the field and the limit of each walk. They show the arithmetic of the
  walks. They show no maintenance instruction and nothing of a machine.

### BOOT-R11

**Clean to the point of unification.**
`cache::clean_code_to_pou(start, bytes)` executes `DC CVAU` on each line of
the walk of the range at the smallest data cache line size that
`CTR_EL0.DminLine` reports, then `DSB ISH`, at EL1, and returns. For Inner
or Outer Shareable memory, which includes every data access with the MMU
off, the cleans reach the data caches of every CPU of the inner-shareable
domain of the executing CPU, and `DSB ISH` waits for them there; the
executing CPU calls it for code that it wrote itself. A range that is empty,
wraps or is longer than 64 KiB panics before any maintenance. The criterion:
the case `clean-code-to-pou` passes.

- **Examples.** None of its own: the walk is that of BOOT-R10.
- **Entry points.** `krepi_arch::cache::clean_code_to_pou`.
- **Contract.**
  [Cache and TLB maintenance](contract.md#cache-and-tlb-maintenance),
  [Check and execute](contract.md#check-and-execute) and
  [Work bounds](contract.md#work-bounds).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: the [open obligations](contract.md#open-obligations)
  of the contract carry its code.
- **Evidence.** The case `clean-code-to-pou` of `cargo xtask qemu-boot`, in
  CI, with the self-check of its test image, `clean-keeps-data`: that the
  range starts and ends inside data cache lines of the size that `CTR_EL0`
  reports, that it touches more than one line, and that the buffer of the
  range reads back unchanged. The image cleans 200 bytes that cross the
  boundary of 2 KiB in the middle of a page-aligned buffer, with the MMU and
  the caches off. It shows that `clean_code_to_pou` executes at EL1 on QEMU
  virt over a range with unaligned ends and returns without an exception: an
  exception would add its record and halt. It does not show that any line
  was cleaned. QEMU's TCG does not model data or instruction caches: by its
  implementation it executes the data and instruction cache maintenance
  instructions without an effect that a guest can observe. This is an
  inference from QEMU's implementation, not a documented guarantee. It does
  not show which lines the walk covers or the field of `CTR_EL0` that sizes
  them, as the line sizes and granules of `CTR_EL0` are all 64 bytes on the
  Cortex-A76 that QEMU models: the host tests of BOOT-R10 show those of
  `data_lines`, which the function calls. It does not show the panic on a
  refused range, which no test takes; the host tests of BOOT-R10 show that
  the walk refuses the range. Nor does it show the broadcast to other CPUs,
  or the effect with the caches on, which needs a run on the Raspberry Pi 5
  (planned).

### BOOT-R12

**Invalidate to the point of coherency.**
`cache::invalidate_to_poc(start, bytes)` executes `DSB SY`, `DC IVAC` on
each line of the walk of the range at `CTR_EL0.DminLine`, `DSB SY`,
`IC IALLU`, `DSB SY` and `ISB` at EL1, and returns. Each `DC IVAC` acts in
the data caches, up to the point of coherency, of every CPU of the
shareability domain of the address, the Outer Shareable domain for every
data access with the MMU off; `IC IALLU` and `ISB` act on the executing CPU
only, which calls it for itself. Its caller owns every block of 2 KiB that
the range touches, and no cache holds data of them that must be kept. A
range that is empty, wraps or is longer than 64 KiB panics before any
maintenance. The criterion: the case `invalidate-to-poc` passes.

- **Examples.** None of its own: the walk is that of BOOT-R10.
- **Entry points.** `krepi_arch::cache::invalidate_to_poc`.
- **Contract.**
  [Cache and TLB maintenance](contract.md#cache-and-tlb-maintenance),
  [Check and execute](contract.md#check-and-execute) and
  [Work bounds](contract.md#work-bounds).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: the [open obligations](contract.md#open-obligations)
  of the contract carry its code.
- **Evidence.** The case `invalidate-to-poc` of `cargo xtask qemu-boot`, in
  CI, with the self-check of its test image, `invalidate-keeps-data`: that
  `SCTLR_EL1` has the MMU and both caches off, that the range starts and
  ends inside data cache lines and touches more than one line, and that the
  data that the image wrote before the invalidation reads back unchanged.
  The image invalidates only when the caches are off, the condition under
  which no cache holds data that must be kept. It shows that
  `invalidate_to_poc` executes at EL1 on QEMU virt over a range with
  unaligned ends and returns without an exception, and that data written
  with the caches off survives it. It does not show that a stale line is
  discarded or that the instruction caches are invalidated. QEMU's TCG does
  not model data or instruction caches: by its implementation it executes
  the data and instruction cache maintenance instructions without an effect
  that a guest can observe. This is an inference from QEMU's implementation,
  not a documented guarantee. As for BOOT-R11, it does not show which lines
  the walk covers or the field of `CTR_EL0` that sizes them, which the host
  tests of BOOT-R10 show for `data_lines`. It does not show the panic on a
  refused range, which no test takes; the host tests of BOOT-R10 show that
  the walk refuses the range. It does not show the behaviour with the
  caches on, which needs a run on the Raspberry Pi 5 (planned).

### BOOT-R13

**Invalidate the TLB entries of a page.**
`cache::invalidate_tlb_page(address)` executes `DSB ISH`, `TLBI VAAE1IS`
with bits 12 to 55 of the address, `DSB ISH` and `ISB` at EL1, and returns;
it never raises an abort. The invalidation removes the cached entries of the
EL1&0 translation regime for the address, with any ASID and from any level
of the walk, on every CPU of the inner-shareable domain, and the second
`DSB ISH` waits for it; the `ISB` synchronizes the executing CPU, which
calls it for a translation that it changed. After a page's entry is replaced
by break-before-make with the invalidation between the invalid and the new
entry, the executing CPU translates the page through the new entry. The
criterion: the case `invalidate-tlb-page` passes.

- **Examples.** None of its own.
- **Entry points.** `krepi_arch::cache::invalidate_tlb_page`.
- **Contract.**
  [Cache and TLB maintenance](contract.md#cache-and-tlb-maintenance) and
  [Work bounds](contract.md#work-bounds).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: the [open obligations](contract.md#open-obligations)
  of the contract carry its code.
- **Evidence.** The case `invalidate-tlb-page` of `cargo xtask qemu-boot`,
  in CI. Its test image builds translation tables of its own, with the 4 KiB
  granule from level 1: blocks that map the first GiB, with the devices, as
  Device-nGnRnE memory and the second GiB, with the RAM, as Normal
  Non-cacheable memory, each to itself, and one page at `0x40_0000_0000`,
  256 GiB, on a first frame. It turns the MMU on with the caches off, reads
  the page, writes an invalid entry in its place, calls
  `invalidate_tlb_page`, writes the entry of a second frame with `DSB ISH`
  and `ISB`, and reads the page again. Its self-check
  `remap-reads-new-frame` holds that the MMU is on, that the first read
  returned the word of the first frame and the second read that of the
  second frame, and that both frames still hold their words. It shows that
  after the invalidation the executing CPU translates the page through its
  new entry on QEMU virt. QEMU keeps the translations that it has used in a
  software TLB until a TLB invalidation, or an event of its own, removes
  them, so without the invalidation the second read could still give the
  first frame. QEMU also flushes its whole software TLB when an invalidated
  address falls in the region of the blocks that it has used, so the page
  lies far from the blocks; an invalidation of a wrong address that falls in
  that region would still go unnoticed. These are inferences from QEMU's
  implementation, not documented guarantees. It does not show the
  invalidation on other CPUs, which one CPU cannot show, the need for the
  barriers, which the in-order execution of TCG does not exercise, the
  invalidation for every ASID, as the entry is global and the ASID is 0, the
  invalidation of the entries of the walk above the last level, as only the
  page entry changes, the TLB of a Cortex-A76 on a board, or translation
  with the caches on.

### BOOT-R14

**Publish code.** Code that the executing CPU wrote is published by
`cache::clean_code_to_pou` and then `cache::invalidate_code_to_pou` of the
same range. `invalidate_code_to_pou(start, bytes)` executes `IC IVAU` on
each line of the walk at the smallest instruction cache line size that
`CTR_EL0.IminLine` reports, then `DSB ISH` and `ISB` at EL1, and returns;
for Inner or Outer Shareable memory, which includes Non-cacheable memory and
every instruction fetch with the MMU off, the invalidations reach the
instruction caches of every CPU of the inner-shareable domain. The `ISB`
synchronizes the executing CPU, which calls it for code that it published
itself; another CPU executes its own context synchronization before it runs
the code. After the publication the executing CPU runs the new instructions,
also over instructions that it ran before. A range that is empty, wraps or
is longer than 64 KiB panics before any maintenance. The criterion: the case
`code-publication` passes.

- **Examples.** None of its own: the walk is that of BOOT-R10.
- **Entry points.** `krepi_arch::cache::clean_code_to_pou` and
  `krepi_arch::cache::invalidate_code_to_pou`.
- **Contract.**
  [Cache and TLB maintenance](contract.md#cache-and-tlb-maintenance),
  [Check and execute](contract.md#check-and-execute) and
  [Work bounds](contract.md#work-bounds).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: the [open obligations](contract.md#open-obligations)
  of the contract carry its code.
- **Evidence.** The case `code-publication` of `cargo xtask qemu-boot`, in
  CI. Its test image writes `MOVZ W0, #0x2a` and `RET` in the last word of
  an instruction cache line of the size that `CTR_EL0` reports and the first
  word of the next, in a page-aligned buffer, publishes them with
  `clean_code_to_pou` and `invalidate_code_to_pou` and calls them; it then
  writes `MOVZ W0, #0x55` and `RET` at the same address, publishes them and
  calls them again. Its self-check `published-code-runs` holds the placement
  across the two lines and both results. It shows that the publication
  sequence runs at EL1 on QEMU virt, with the MMU and the caches off, and
  that the second call executes the rewritten instructions. It does not show
  that the clean and the invalidation are needed. QEMU's TCG does not model
  data or instruction caches: by its implementation it executes the data and
  instruction cache maintenance instructions without an effect that a guest
  can observe. This is an inference from QEMU's implementation, not a
  documented guarantee. TCG also notices writes to code that it has
  translated, so the new instructions would run without them. It does not
  show which lines the walks cover or the fields of `CTR_EL0` that size
  them, which the host tests of BOOT-R10 show for `data_lines` and
  `instruction_lines`, or the panic on a refused range, which no test
  takes; the host tests of BOOT-R10 show that the walks refuse the range.
  It does not show the effect on a board, where instruction fetches can be
  held in an instruction cache even with the caches off, which is why the
  sequence is needed there.

## Liveness, time and performance

- A cold boot reaches `CASXI_READY` without waiting for input. The echo
  loop runs forever and answers every received byte.
- A console write ends within its window on a running counter and within
  `attempts_per_byte` refusals of one byte on a stopped one.
- A test image that waits for an interrupt waits for at most 1,000 ms on
  the counter, a platform parameter of QEMU virt for these images, and then
  reports what it saw.
- A call of the cache maintenance over a range walks at most 64 KiB of
  lines and ends; the TLB invalidation runs a fixed sequence.
- The QEMU boot suite ends each run at its window of 20 s, a platform
  parameter of QEMU virt that leaves ample room for a boot that takes well
  under a second, and judges no time. A test image either halts or ends in
  `CASXI_RESUMED` and then waits, so its run ends at its window too.

## Scope

- One CPU of QEMU virt: secondary CPUs park in the cold entry and never run
  kernel code.
- The MMU and the caches stay off, except that the test image of BOOT-R13
  turns the MMU on with tables of its own; the caches stay off in every
  image. The device tree is not read.
- Cache and TLB maintenance on behalf of another CPU, with its
  acknowledgement, is not provided.
- The vectors of the current level with `SP_EL0` and of a lower level halt
  after their dispatch returns; the kernel handles no such exception, and
  only the test image of BOOT-R08 takes one. Every exception of the default
  image halts, and only test images return from an exception.
- The default image sets no interrupt up and takes no IRQ; only test images
  take the timer interrupt and the interrupt of BOOT-R09, and no device
  interrupt is handled.
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
