# Boot and platform

## Overview

The boot and platform domain takes a board from the hand-over of its
firmware to a kernel that runs at EL1 with its exceptions, memory map,
caches, interrupts and serial console in a known state, on each supported
board. It covers the firmware handoff, the EL1 entry, the exception vectors,
cache and TLB maintenance, the parsing of the device tree, the physical
memory ranges, the support of QEMU virt and the Raspberry Pi 5, the
interrupt controllers, the PCIe link to RP1, the errata of the CPU and the
symbolization of fault addresses.

Two machines bound the domain. QEMU virt with a Cortex-A76 is a generic
ARM64 machine with its own addresses, interrupt routing and entry
conditions; generic mechanisms are shown there first. The Raspberry Pi 5,
with a BCM2712 of four Cortex-A76 cores, a GIC-400 and the RP1 behind PCIe,
is the target. A result on one machine says nothing about the other, and
no address, route or entry condition of QEMU virt is used for the Pi 5. The
domain relies on the architecture as the Arm Architecture Reference Manual
states it and on the board as its firmware leaves it; what the firmware
does before the handoff, and the trust in it, lie outside the kernel.

The domain hands its results to other domains, listed in the
[subject-domain index](../README.md): the memory domain takes the physical
ranges and builds the page tables and the kernel direct map on the cache and
TLB primitives; the multicore domain starts the secondary CPUs and
acknowledges TLB invalidation across them; the devices and DMA domain gives
EL0 drivers authority over devices and delivers their interrupts; the
security and lifecycle domain decides which images a board may boot. The
[boot](boot/requirements.md) component holds the cold entry, the processor
primitives and the QEMU virt board support with its console.

## Conventions

- **Platform parameters.** Spin limits, timeouts and windows of boot and
  board code are platform parameters with a documented value for each
  board, never constants tuned on one machine.
- **Records.** The kernel reports boot and fault progress on the serial
  console as records: lines that start with `CASXI_`, have fixed fields and
  end in CR LF, and that hold no count, time or address unless a field names
  it, so that the transcripts of cold boots compare byte for byte.
- **Boot CPU.** Only the boot CPU runs kernel code until secondary startup;
  every other CPU waits where the firmware or the cold entry leaves it.
- **Bounded paths.** Every loop of the boot path and of a fatal path has a
  bound; a fatal path neither allocates nor waits for the console without a
  bound.
- **One image per board.** A board has one image, which serves every product
  function and holds no diagnostic operation or fault probe.
- **Board facts with their board.** Addresses, interrupt numbers, clocks and
  entry conditions belong to the support of one board and carry the
  reference or the measurement that established them.

## Feature index

| Feature | Scope | Feature documents | Components |
| --- | --- | --- | --- |
| [Firmware handoff](#firmware-handoff) | What the firmware leaves for the kernel: the image, the device tree, the exception level and the resident firmware services | - | The entry of each board |
| [EL1 entry](#el1-entry) | From the ELF entry point to Rust at EL1 on the boot CPU, with the entry state checked | [QEMU virt boot](../../features/platform/qemu-virt-boot.md) | [boot](boot/requirements.md) |
| [Exception vectors](#exception-vectors) | The vector table of EL1, the exception frame, its save and restore, and the report of an exception | [QEMU virt boot](../../features/platform/qemu-virt-boot.md) | [boot](boot/requirements.md) |
| [Cache and TLB maintenance](#cache-and-tlb-maintenance) | Cleaning and invalidating caches by address, TLB invalidation with its barriers and the publication of code, by the executing CPU | [QEMU virt boot](../../features/platform/qemu-virt-boot.md) | [boot](boot/requirements.md) |
| [Device-tree parsing](#device-tree-parsing) | Bounded parsing of the flattened device tree that the firmware hands over | - | The device-tree parser |
| [Physical memory ranges](#physical-memory-ranges) | The banks of RAM and the reserved ranges, from the device tree and the image | - | The boot memory map |
| [QEMU virt and Pi 5 board support](#qemu-virt-and-pi-5-board-support) | The constants and bring-up of each board, its serial console and its image | [QEMU virt boot](../../features/platform/qemu-virt-boot.md) | [boot](boot/requirements.md) |
| [Interrupt controllers](#interrupt-controllers) | The GICv2 of QEMU virt and the GIC-400 of the Pi 5: configuration, acknowledgement and end of interrupt | [QEMU virt boot](../../features/platform/qemu-virt-boot.md) | [boot](boot/requirements.md) |
| [PCIe and RP1 links](#pcie-and-rp1-links) | The bring-up of the PCIe link to RP1 and the baseline that EL0 drivers receive | - | The PCIe and RP1 bring-up |
| [CPU errata](#cpu-errata) | The errata of the Cortex-A76 that affect kernel code, and their workarounds | - | The errata register of each CPU model |
| [Fault symbolization](#fault-symbolization) | Resolving the addresses of a fault record to functions and source lines of the image | - | The symbolization of the host tools |

## Firmware handoff

**Description.** The firmware loads the image and the device tree and
enters the kernel on one CPU, with the other CPUs held by the firmware. The
handoff fixes, for each board, the exception level of the entry, the state
of the MMU and the caches, where the image and the device tree lie and how
the kernel finds the device tree, and which firmware services stay
resident. On QEMU virt, QEMU's loader is the firmware: it loads the ELF
segments, places the device tree at the start of RAM and enters the ELF
entry point on the first CPU, at EL1 when the machine has the secure state
and virtualization off, and at EL2 when it has the secure state off and
virtualization on. On the Pi 5 the boot firmware enters the kernel at EL2
with the MMU and the caches off, and BL31 stays resident at EL3 with the
PSCI services. The handoff does not start secondary CPUs and does not check
the integrity of the image.

**Design background.** The kernel takes the handoff as a contract of the
board and checks what it can: the exception level, the control registers and
the CPU identity. The firmware's own state, its coherence conventions and
its configuration are trusted items of the board, recorded with their
versions.

**Consumers.** The EL1 entry, which starts from this state; the device-tree
parser and the physical memory ranges, which read what the firmware left;
the multicore domain, which asks the resident firmware to start secondary
CPUs.

**Interface.** None at run time: the handoff is the state at the entry
point. A handoff that breaks its contract is an entry failure, which the
EL1 entry reports or, for a CPU that is not the boot CPU, answers by
parking.

**Prerequisites.** [QEMU virt and Pi 5 board support](#qemu-virt-and-pi-5-board-support),
which names the handoff of each board.

**Engineering notes.** The device tree must not overlap the image: on QEMU
virt the image leaves the first 2 MiB of RAM to it. Every Pi 5 result names
the firmware, EEPROM and BL31 versions, and a change of any of them makes
earlier board results stale.

**Verification.** The handoff is observed, not proved: the EL1 entry checks
its exception level and control registers on every boot, a QEMU virt boot
shows QEMU's handoff, and a Pi 5 boot on the bench shows the firmware's,
each with its versions.

## EL1 entry

**Description.** The cold entry brings the boot CPU from the ELF entry point
into Rust at EL1. It masks every exception, parks every CPU but the boot CPU
and a CPU at an unexpected exception level, makes FP/SIMD instructions trap,
selects the EL1 stack, clears BSS, installs the exception vectors, clears
the stack and calls the Rust entry, which never returns. The Rust entry
sets the serial console up and checks the entry state: BSS cleared, data
initialized, EL1, the MMU and the caches off, little-endian data, the
expected CPU and FP/SIMD trapping. A failed check halts the CPU with a
record. A board whose firmware enters at EL2
first drops to EL1. The entry does not set up memory translation or
interrupts.

**Design background.** The entry runs before any memory is mapped and
before any exception can be taken, so it touches only registers, the image
and its own stack, with the MMU off and memory accesses of Device type.
Clearing the whole stack before the first Rust frame lets a bounded walk of
frame records rely on the stack contents.

**Consumers.** Every other feature of the kernel, which starts after the
entry; the QEMU boot suite, which holds the records of a cold boot.

**Interface.** The ELF entry point `_start` and the Rust entry
`kernel_main`; the records `CASXI_CPU`, `CASXI_BOOT` and `CASXI_READY`, and
`CASXI_PANIC` with `CASXI_HALTED` for a failed check, in the forms of the
[boot contract](boot/contract.md#records). A failed check is an error that
ends the boot; a parked CPU is a state, not an error.

**Prerequisites.** [Firmware handoff](#firmware-handoff);
[QEMU virt and Pi 5 board support](#qemu-virt-and-pi-5-board-support) for
the console; the [boot](boot/contract.md) component and the
[QEMU virt boot](../../features/platform/qemu-virt-boot.md) feature document.

**Engineering notes.** The stack of the boot CPU is 64 KiB with a 4 KiB
guard below it. The kernel is built softfloat, so FP/SIMD trapping at EL1
catches an FP/SIMD instruction that should not exist. The state of the
entry is classified in the [State fields](boot/contract.md#state-fields) of
the boot contract.

**Verification.** The QEMU boot suite boots the default image on QEMU virt
three times and holds the transcripts against the records of the contract
and against each other. A Pi 5 entry needs its own board run. Counterexamples
that the checks must reject are an image entered at another exception level,
with the MMU on or on another CPU model.

## Exception vectors

**Description.** The vector table of EL1 has sixteen entries: synchronous,
IRQ, FIQ and SError exceptions from the current exception level with `SP_EL0`
and with `SP_ELx`, and from a lower exception level in AArch64 and in
AArch32. Every entry saves the general registers and `ELR_EL1`, `SPSR_EL1`,
`ESR_EL1` and `FAR_EL1` in an exception frame on the stack and calls the
dispatch of the image; after the dispatch, an entry from the current level
with `SP_ELx` restores the frame and returns. The report of a fatal
exception is a record with the exception class, the syndrome, the return
address, the fault address, the saved program status and the vector, after
which the CPU halts. Entries that the
kernel does not handle report and halt. The vectors do not save FP/SIMD
state, which traps at EL1.

**Design background.** The architecture fixes the table layout, a 2 KiB
aligned base in `VBAR_EL1` with 128 bytes per entry, and the syndrome
encoding of `ESR_EL1`. Each save, restore and clear rule of exception entry
and return is a separate obligation with a test that observes it, because
the rules are assembly that no extraction reaches.

**Consumers.** Interrupt delivery, the timer and preemption of the
scheduling domain, system calls and user faults of the runtime domain, and
fault symbolization, which reads the records.

**Interface.** The table, the frame layout, the dispatch function of the
image and the exception record. A fatal exception is reported and halts; an
interrupt returns to the interrupted code.

**Prerequisites.** [EL1 entry](#el1-entry), which installs the table;
[Interrupt controllers](#interrupt-controllers) for IRQs; the
[boot](boot/contract.md) component.

**Engineering notes.** The frame lies below the interrupted stack pointer
and records it; the dispatch and the return run with every exception
masked, so no SError, IRQ or FIQ nests, while a synchronous exception of
the dispatch itself would. The fatal path writes its record within the
console bounds and does not allocate. Exceptions from EL0, with the save and
restore of `SP_EL0`, belong to the user context of the runtime domain.

**Verification.** QEMU tests trigger each handled kind once, a breakpoint,
a timer interrupt, an injected SError and an FP/SIMD access, check the
fields of the record against the Arm encodings, and check that the
registers, the stack pointer, `ELR_EL1`, `SPSR_EL1` and the condition flags
survive an interrupt unchanged.

## Cache and TLB maintenance

**Description.** The executing CPU cleans data cache lines to the point of
unification by virtual address, invalidates data cache lines by virtual
address, invalidates TLB entries of a virtual address with the barriers
around it, and invalidates instruction cache lines when it publishes code.
Each primitive acts on a stated shareability domain and is called by the CPU
for itself. The primitives cover every line of an address range whose ends
are not aligned to a cache line. They do not invalidate TLB entries of other
CPUs and wait for their acknowledgement, which the multicore domain does.

**Design background.** The sequences follow the Arm Architecture Reference
Manual: `DC CVAU` by line and `DSB ISH` before instruction fetch sees new
code, `IC IVAU` with `DSB ISH` and `ISB` to publish it, and for a changed
translation `DSB ISH`, the inner-shareable `TLBI`, `DSB ISH` and `ISB`, as
the [SMP design rules](../../conventions/smp.md#s6c-tlb-invalidation)
require. The cache line sizes come from `CTR_EL0`.

**Consumers.** Page-table changes and code publication of the memory domain,
the turning on of the MMU and the caches, and image loading.

**Interface.** One primitive per maintenance operation, each taking an
address range and reporting nothing: the instructions do not fail.

**Prerequisites.** [EL1 entry](#el1-entry); the
[boot](boot/contract.md) component.

**Engineering notes.** The range arithmetic is plain code that host tests
cover for unaligned ends and empty ranges; the instructions are assembly in
adapters. QEMU's TCG does not model data and instruction caches, so a QEMU
test shows that a primitive executes over a range, not its effect on a
cache.

**Verification.** Host tests of the line coverage of a range; QEMU tests
that each primitive executes, that a remapped page is read through its new
frame after the TLB invalidation and that published code runs; the effect
with the caches on is shown on the Pi 5.

## Device-tree parsing

**Description.** The kernel parses the flattened device tree that the
firmware hands over, within fixed bounds on its size, depth, property count
and string lengths. It finds the memory nodes, the reserved ranges, the CPU
nodes with their enable method and the devices that boot code needs, and it
rejects a tree that breaks the format or a bound. It does not apply
overlays or change the tree.

**Design background.** The format is that of the Devicetree Specification.
The Pi 5 firmware tree has 334 symbol properties, vendor names of 32
characters and a reserved range for the contiguous memory allocator that
changes with the configuration, so the bounds are set from the trees of the
supported firmware versions with a margin. The parser follows the
[provable Rust subset](../../conventions/provable-subset.md).

**Consumers.** The physical memory ranges, the start of secondary CPUs in the
multicore domain and device discovery in the devices and DMA domain.

**Interface.** A parse of the tree at the handed address, which yields its
nodes and properties or an error that names the broken rule.

**Prerequisites.** [Firmware handoff](#firmware-handoff).

**Engineering notes.** Every loop over the tree has a bound, and every
offset is checked before it is read. The tree is read with the MMU off or
through a read-only mapping.

**Verification.** Host tests on trees of each supported firmware version and
on mutated trees that break each bound; proofs of the parser against its
specification.

## Physical memory ranges

**Description.** From the memory nodes, the reserved ranges, the image and
the device tree itself, the kernel builds the list of usable RAM ranges and
of the ranges that it must not hand out. Ranges are page aligned, sorted and
disjoint. It does not allocate pages: the memory domain owns them.

**Design background.** On the Pi 5 the upstream memory node is a placeholder
of 640 MiB; the 8 GiB of the board come in three banks with a hole of 4 MiB,
and using all of them needs block mappings and a kernel direct map. QEMU
virt has one bank at `0x4000_0000`.

**Consumers.** The physical page ownership and the kernel direct map of the
memory domain.

**Interface.** The list of usable and reserved ranges, or an error for
overlapping or misaligned input.

**Prerequisites.** [Device-tree parsing](#device-tree-parsing).

**Engineering notes.** The image, its stack, the device tree and every
reserved range stay out of the usable ranges. The list has a fixed capacity
that covers the supported boards.

**Verification.** Host tests with the memory nodes of each supported
board and with overlapping, unaligned and empty ranges; a board run that
uses the whole RAM.

## QEMU virt and Pi 5 board support

**Description.** Each board has its own support: its addresses, interrupt
numbers and clocks, the bring-up of its devices that the kernel needs, its
serial console and its one image. The QEMU virt support has the PL011 at
`0x0900_0000` as the serial console, the GICv2 and the virtual timer, and
the image `krepi-qemu-virt`. The Pi 5 support has UART10, the GIC-400, the
physical timer and the PCIe link to RP1. Board support does not share an
address or a route between the two boards.

**Design background.** QEMU virt is described by QEMU's documentation of
the machine; the Pi 5 by the BCM2712, RP1 and firmware documentation and by
the measurements of the prototype, recorded with their firmware versions.
UART10 of the Pi 5 keeps the divisor that the firmware set. The serial
console polls its UART within platform parameters.

**Consumers.** Every feature that touches a device at EL1; the QEMU and
board suites, which read the console.

**Interface.** The console records, the image of each board and the
functions of its support. A console write that fails reports the failure
and halts.

**Prerequisites.** [EL1 entry](#el1-entry),
[Interrupt controllers](#interrupt-controllers); the
[boot](boot/contract.md) component and the
[QEMU virt boot](../../features/platform/qemu-virt-boot.md) feature document
for QEMU virt.

**Engineering notes.** Console bounds on QEMU virt: one million attempts
per byte, a window of 250 ms per record and one million attempts for the
failure marker. The state of the QEMU virt support is classified in the
[State fields](boot/contract.md#state-fields) of the boot contract.

**Verification.** The QEMU boot suite for QEMU virt; board runs on the bench
for the Pi 5, each with its firmware and bench configuration. A QEMU result
is not a board result.

## Interrupt controllers

**Description.** The kernel configures the distributor and the CPU
interface of the interrupt controller of each board, enables the interrupts
that it owns, acknowledges an interrupt, signals its end and keeps every
other interrupt disabled. QEMU virt has a GICv2 with its distributor at
`0x0800_0000` and its CPU interface at `0x0801_0000`; the virtual timer of
the boot CPU is the private interrupt 27. The Pi 5 has a GIC-400, which
implements GICv2, not a GICv3. The controllers do not route device
interrupts to EL0 drivers, which the devices and DMA domain does.

**Design background.** The GICv2 architecture specification fixes the
registers, the acknowledgement through the interrupt acknowledge register
and the end of interrupt; an acknowledged interrupt is ended exactly once.
On the Pi 5 the Group 1 routing of interrupt 30 can only be configured by the
firmware.

**Consumers.** The timer and preemption of the scheduling domain, interrupt
delivery of the devices and DMA domain and inter-processor interrupts of the
multicore domain.

**Interface.** Configuration at boot, then acknowledgement and end of
interrupt on each IRQ. A spurious interrupt number is a state that the
handler ignores, not an error.

**Prerequisites.** [Exception vectors](#exception-vectors),
[QEMU virt and Pi 5 board support](#qemu-virt-and-pi-5-board-support); the
[boot](boot/contract.md) component for the GICv2 of QEMU virt.

**Engineering notes.** The distributor is configured once, with IRQs
masked, before the first interrupt is taken. The handler of an interrupt is
bounded and does not allocate. The GICv2 driver is shared by the boards that
have one, and each board gives its addresses and interrupt IDs. The state of the
controller is classified in the state fields of the contract of its
board's support: for the GICv2 of QEMU virt, the
[State fields](boot/contract.md#state-fields) of the boot contract; for the
GIC-400 of the Pi 5, those of the Pi 5 board support.

**Verification.** QEMU tests that take the timer interrupt, acknowledge
and end it and return to the interrupted code, twice, and that take it at
one known instruction and find every register unchanged after it; on the
Pi 5 the same through the GIC-400 on the bench.

## PCIe and RP1 links

**Description.** On the Pi 5 the kernel brings up the PCIe link to RP1 and
hands EL0 drivers a known baseline: the reset is released through the
independent reset controller, the resistor calibration and the PHY are set
up, the link trains to Gen2 with four lanes, and every base address register
is zero with every bridge window closed. RP1 interrupts reach the kernel on
one shared line. QEMU virt has no RP1. The link bring-up does not drive any
RP1 device.

**Design background.** The reset inside the root complex reads back
`0xdeaddead` and is not used. RP1 interrupts are demultiplexed by masking
the interrupt status of each vector with its enable bit; the shared line
also carries an Ethernet interrupt source that krepi does not own.

**Consumers.** The EL0 drivers of RP1 devices, such as the UART, GPIO,
storage and USB, through the devices and DMA domain.

**Interface.** A bring-up at boot that ends with the link up and the
baseline set, or a failure record that names the step.

**Prerequisites.** [QEMU virt and Pi 5 board support](#qemu-virt-and-pi-5-board-support),
[Interrupt controllers](#interrupt-controllers),
[Physical memory ranges](#physical-memory-ranges).

**Engineering notes.** Every wait for the link or a register has a bound
that is a platform parameter of the Pi 5. A failed bring-up leaves the link
down and no BAR mapped.

**Verification.** Board runs on the bench that train the link, read the
baseline back and show the interrupt line, with the firmware versions.

## CPU errata

**Description.** For each CPU model and revision that a board has, the
kernel knows the errata that affect code that it runs and applies their
workarounds at entry or in the affected paths. An erratum that does not
apply to the kernel is recorded with the reason. The kernel reads the model
and revision from `MIDR_EL1`.

**Design background.** The errata of the Cortex-A76 are those of its
Software Developer Errata Notice, by revision. QEMU models no erratum, so a
QEMU run cannot show a workaround.

**Consumers.** Every feature of the kernel that executes an affected
sequence, such as cache and TLB maintenance and the exception vectors.

**Interface.** None at run time beyond the workarounds; the record of each
erratum names its workaround or its reason.

**Prerequisites.** [EL1 entry](#el1-entry), which reads the CPU identity.

**Engineering notes.** A workaround changes a sequence only for the
revisions that the notice names. A new CPU revision on a board needs its
errata reviewed before the board is supported.

**Verification.** Review against the errata notice; board runs on each
supported revision.

## Fault symbolization

**Description.** The host tools resolve the program counter, the link
register and the frame records of a fault record to functions and source
lines of the image that wrote it, after checking that the build-id in the
record equals that of the image. The symbolization runs on the host, never
in the kernel.

**Design background.** The image carries a GNU build-id note of SHA-1 and
the symbols of its functions; the fault record carries the build-id and a
bounded chain of frame records walked by frame pointers.

**Consumers.** Developers and the suites that analyse a fatal record.

**Interface.** A host command that takes an image and a transcript and
prints the resolved frames, or an error when the build-ids differ.

**Prerequisites.** [Exception vectors](#exception-vectors), which write the
records.

**Engineering notes.** A record from another image is rejected, not
resolved against the wrong symbols. The frame walk in the kernel is bounded
by the stack range and by monotonic progress.

**Verification.** Host tests on images that the tests build or write and on
records with matching and mismatching build-ids.

## Dependencies

| Feature | Depends on | Reason |
| --- | --- | --- |
| EL1 entry | Firmware handoff | The entry starts from the state that the firmware leaves |
| Exception vectors | EL1 entry | The entry installs the table and the stack |
| Cache and TLB maintenance | EL1 entry | The primitives run at EL1 |
| Physical memory ranges | Device-tree parsing | The memory nodes and reserved ranges come from the tree |
| QEMU virt and Pi 5 board support | EL1 entry | The console and devices are set up from the Rust entry |
| Interrupt controllers | Exception vectors | An interrupt enters through the IRQ vector |
| PCIe and RP1 links | Interrupt controllers, Physical memory ranges | RP1 interrupts and BARs need both |
| CPU errata | EL1 entry | The workarounds depend on the CPU identity |
| Fault symbolization | Exception vectors | The records come from the fatal paths |

## Exclusions

- Secondary CPU startup, per-CPU state and acknowledged TLB invalidation
  across CPUs belong to the multicore domain.
- Page tables, the kernel direct map and physical page ownership belong to
  the memory domain.
- Device authority for EL0 drivers, interrupt delivery to them and DMA
  belong to the devices and DMA domain.
- Signed boot and the choice of the image a board may boot belong to the
  security and lifecycle domain.
- The FP/SIMD state of user threads belongs to the runtime ABI and SDK
  domain.

## References

- Arm Limited, *Arm Architecture Reference Manual for A-profile
  architecture*, DDI 0487,
  <https://developer.arm.com/documentation/ddi0487/latest/>.
- Arm Limited, *Arm Cortex-A76 Core Technical Reference Manual*, revision
  r4p1, document 100798_0401_00_en, 2020,
  <https://documentation-service.arm.com/static/5f562083235b3560a01e03bc>.
- Arm Limited, *Arm Cortex-A76 Software Developer Errata Notice*.
- Arm Limited, *PrimeCell UART (PL011) Technical Reference Manual*, revision
  r1p5, DDI 0183G, 2007,
  <https://documentation-service.arm.com/static/5e8e36c2fd977155116a90b5>.
- Arm Limited, *ARM Generic Interrupt Controller Architecture Specification,
  version 2.0*, IHI 0048B.
- Arm Limited, *CoreLink GIC-400 Generic Interrupt Controller Technical
  Reference Manual*, DDI 0471.
- Arm Limited, *Arm Power State Coordination Interface*, DEN 0022.
- Arm Limited, *SMC Calling Convention*, DEN 0028.
- devicetree.org, *Devicetree Specification*, release v0.4,
  <https://www.devicetree.org/specifications/>.
- The QEMU Project, *'virt' generic virtual platform*,
  <https://www.qemu.org/docs/master/system/arm/virt.html>.
- Raspberry Pi Ltd, *Raspberry Pi documentation: config.txt*,
  <https://www.raspberrypi.com/documentation/computers/config_txt.html>.
- Raspberry Pi Ltd, *RP1 Peripherals*,
  <https://datasheets.raspberrypi.com/rp1/rp1-peripherals.pdf>.
