---
features: none
---

# Address-space requirements

The observable behaviour of the `address-space` component of the
[memory and address spaces](../README.md) domain: the address spaces of
processes with their ASIDs and table pools, the layout of EL0 and the
range check of user buffers, the entry from EL0 and the return to it, the
classes of exceptions and user faults, the first process with its boot
information and the boot-bundle directory, the EL0 controls, and the
kernel stacks with blocking calls. The rules that its code and tests
follow are in the [contract](contract.md). No feature document covers the
component, so the metadata lists none.

## Sources

- The ASID allocator, the range check of user buffers and the address
  spaces of the prototype's execution manager give the rules of ASIDs and
  of user buffers, with their host tests as the frozen
  [vectors](contract.md#legacy-test-vectors); the prototype's layout of a
  domain, its user faults and its boot information page, which the
  [references](contract.md#references) of the contract list, give the
  starting point of the layout, of the cause classes and of the boot
  information.
- The EL0 window, the table pool carved at boot, the boot-bundle directory,
  the release of an ASID as a plan, the one-way return to EL0 and the EL0
  controls are new; the
  [behaviour changes](contract.md#legacy-test-vectors) of the contract list
  where the rules differ from the prototype.
- The execution model, the boot bundle as a segment of the image and the
  observable outputs follow the [architecture](../../../architecture.md)
  and the [security model](../../../security.md); the registers, their
  fields and their encodings follow the Arm Architecture Reference Manual
  and the Cortex-A76 manual, and the bits of `SCTLR_EL1` that govern EL0
  the initial value of Linux 6.12.

## Configurations

- **QEMU virt.** The machine `virt-8.2` without EL2 and EL3, with GICv2,
  one Cortex-A76 and 128 MiB of RAM at `0x4000_0000`: the machine of
  `cargo xtask qemu`, with the QEMU version that `toolchains.toml` pins for
  the host.
- **Raspberry Pi 5.** The models with 1, 2, 4, 8 and 16 GB of RAM, each
  with its four Cortex-A76 cores of which one runs. The rules depend on the
  core and on the load layout of the board, which every model shares. Only
  the 8 GB model is run on a board in release 0.1; the other four are not
  run on a board in that release.
- **Host.** The host tests of the module `address_space` of the core
  (planned) run on the development host and in CI, with the frozen vectors
  and the tests that the [contract](contract.md#testing-obligations) adds.
- One CPU: no requirement here covers the invalidation of an ASID on
  another CPU or a thread that moves between CPUs.

## Requirements

### ASP-R01

**ASIDs.** Each address space of a process has its own ASID, 8 bits wide on
both boards, taken from 1 to the process capacity: an address space takes
the lowest free ASID whose generation is not exhausted, ASID 0 is never a
process's, and no two live address spaces share an ASID. A boot whose
process capacity exceeds the 255 ASIDs stops with `AsidCapacity` before any
storage is carved. The criterion: the frozen vectors hold, among them the
full range of 255 ASIDs, the capacities 0 and 256 refused with
`AsidCapacity`, and an ASID whose generation is exhausted that is never
taken again.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `address_space::asid_capacity`, `check_processes`,
  `Asids::new`, `choose` and `take` (planned).
- **Contract.** [Address spaces and ASIDs](contract.md#address-spaces-and-asids).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `as-01`, `as-04` to `as-09`, `as-11`,
  `as-13`, `as-17`, `as-19` and `as-20` as host tests, and the host tests
  of `asid_capacity` and `check_processes` of the
  [contract](contract.md#testing-obligations). They show the allocator; the
  QEMU test of the reuse of ASIDs shows them on QEMU virt.

### ASP-R02

**Release and reuse of an ASID.** An ASID returns to the free ASIDs only
after its address space is loaded on no CPU and the TLB entries of the ASID
are invalidated on every CPU of its CPU record; until then it stays held,
and no new address space takes it. A release of a token that names no held
ASID of its generation is refused and changes nothing. The criterion: the
frozen vectors hold, and on QEMU virt a test that creates and destroys more
processes than the allocator has ASIDs finds every reused ASID free of the
translations of its earlier address space.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Asids::release_plan`, `Asids::release`, `Space::join`
  and `krepi_arch::el0::invalidate_asid` (planned).
- **Contract.** [Address spaces and ASIDs](contract.md#address-spaces-and-asids).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path; the invalidation
  is an [open obligation](contract.md#open-obligations).
- **Evidence.** The frozen vectors `as-02`, `as-03`, `as-18` and `as-21` as
  host tests, and the QEMU test of the reuse of ASIDs of the
  [contract](contract.md#testing-obligations). They show the order on
  QEMU virt with one CPU; they do not show the invalidation on another CPU.

### ASP-R03

**Table pools.** The lower tables of each process are the 32 tables of the
segment of its process slot, in a pool that the boot carves once for the
process capacity and that adds at most two extents to the page ownership
table. A process creation and reclamation take and return no page; a
mapping that would need more tables than the 32 less those of the copy of
the lower kernel set is refused before any write. A boot whose bundle the
root cannot map within its tables stops with `RootTables`. The criterion:
the host tests of the pool and of the root's tables of the contract hold,
and on QEMU virt and the 8 GB Pi 5 the root maps its whole bundle.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `TablePool::pages`, `TablePool::new`,
  `TablePool::segment` and `Directory::root_plan` (planned).
- **Contract.** [Table pools](contract.md#table-pools).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The host tests of the carving of the pool and of
  `root_plan` of the [contract](contract.md#testing-obligations), the
  frozen vectors `as-15` and `as-20`, and the QEMU test of the boot
  information, whose root reads its bundle. They show the counts on the
  layouts of the boards; the limit of the image with its bundle rests on an
  inferred size of the kernel apart from its bundle.

### ASP-R04

**EL0 window.** Every page of a process at EL0 lies in
`[0x4000000000, 0x8000000000)`, which no mapping of the lower kernel set
touches, and a boot whose kernel layout reaches that window stops with
`KernelLayout` before the lower kernel set is written. The boot
information, the root's segments, its stack with a guard below it and its
bundle lie at the fixed ranges of the contract. A saved context whose
return address or stack pointer lies outside the window is not restored.
The criterion: the host test of `check_kernel_ranges` holds, and on QEMU
virt the root finds its boot information and its bundle at their
addresses.

- **Examples.** None: no feature document covers the component.
- **Entry points.** The constants of the layout and
  `address_space::check_kernel_ranges` (planned).
- **Contract.** [EL0 address layout](contract.md#el0-address-layout).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The host test of `check_kernel_ranges` and the QEMU test of
  the boot information of the [contract](contract.md#testing-obligations).
  They show the layout of QEMU virt; the layout of the Pi 5 is shown by the
  check at its boot.

### ASP-R05

**The range of a user buffer.** A buffer longer than its limit is refused
with `TooLong` whatever its address; an empty buffer is accepted with no
range whatever its address; a nonempty buffer is accepted exactly when it
lies in its window without wrapping, and refused with `Address`
otherwise. The criterion: the frozen vectors hold, among them both ends of
the window, the limit itself and the largest addresses.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `address_space::check_range` (planned).
- **Contract.** [EL0 address layout](contract.md#el0-address-layout).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `as-22` to `as-31` as host tests. They
  show the arithmetic of the check; the copies that follow it belong to
  the user copies of the kernel.

### ASP-R06

**Entry and return.** Every entry from EL0 starts at the top of the kernel
stack of its CPU and saves the user registers into the saved context of
the current thread before any of them changes; every return to EL0 loads
the address space of the thread that is to run, with its ASID, restores a
saved context that `validate` accepted and executes `ERET`, after which no
register that EL0 can read holds a value of the kernel or of another
process. The criterion: on QEMU virt, the test of two interleaving
processes of the context component holds, and each rule of the entry and
the return has a test that holds.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `__el0_entry`, `el0_dispatch` and `__el0_return`
  (planned), with `Space::ttbr0`.
- **Contract.** [Entry and return](contract.md#entry-and-return).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path; the rules of the
  entry and the return are [open obligations](contract.md#open-obligations).
- **Evidence.** The tests that the open obligations name for the rules of
  the entry and the return, and the QEMU test of two interleaving processes
  of the [context](../../boot-platform/context/requirements.md#ctx-r06)
  component. They show the entry and the return on QEMU virt with one CPU;
  the Raspberry Pi 5 needs a board run of its own.

### ASP-R07

**Exception classes.** Each entry from EL0 has exactly one of the ten
classes of the contract, from its vector and its exception class: a system
call, eight classes of synchronous exceptions that are user faults, and an
IRQ. A system call with an `SVC`
immediate other than 0 returns `UNSUPPORTED_OPERATION` and is not a fault.
FIQs, SErrors and AArch32 exceptions are never taken from EL0. The
criterion: the host test of `classify` holds for every exception class, and
on QEMU virt each of the ten classes is taken once from EL0 and classified
as the contract states.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `address_space::classify` (planned).
- **Contract.** [Exception classes](contract.md#exception-classes).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The host test of `classify` and the QEMU test of the ten
  classes of the [contract](contract.md#testing-obligations). They show the
  classes on QEMU virt; the Pi 5 needs a board run of its own.

### ASP-R08

**User faults.** Every synchronous exception of a thread at EL0 other than
a system call has exactly one of the nine cause classes of the contract,
which a later release passes to a fault handler. In release 0.1 the fault
ends the process of the thread as faulted, with a fault record that holds
the cause class, the exception class bits of `ESR_EL1` and, where it is
defined, the user virtual address of `FAR_EL1`; the thread never runs
again, and no other process ends. A kernel sentinel that EL0 writes stays
unchanged. The criterion: on QEMU virt, the case of each of the nine causes
gives that cause and its fault record, and the process does not run again.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `address_space::classify` (planned), with the end of a
  process that the component of the termination of processes governs
  (planned).
- **Contract.** [User faults](contract.md#user-faults).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The QEMU cases of the nine causes and the host test of
  `classify` of the [contract](contract.md#testing-obligations). They show
  the causes on QEMU virt; the end of the process and its fault record are
  shown by the component of the termination of processes.

### ASP-R09

**The first process.** The kernel creates the root at boot from the root's
segments of the directory: its code and read-only data map pages of the
bundle, its writable data are private copies, its stack has 16 pages with a
guard below it, it reads its boot information at `BOOT_INFO` and its whole
bundle at `BUNDLE_WINDOW`, read-only, and its first instruction is the root
entry of the directory with the initial context of the context component.
The criterion: on QEMU virt, the root of a test image reads the fields of
its boot information and the directory through its bundle, and its first
instruction finds the initial context.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Directory::root_plan`, `BootInfo::new` and
  `Space::new` (planned), with the boot of the root.
- **Contract.** [First process and boot information](contract.md#first-process-and-boot-information).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The QEMU test of the boot information of the
  [contract](contract.md#testing-obligations) and the QEMU test of a new
  process of the
  [context](../../boot-platform/context/contract.md#testing-obligations)
  component. They show the root of a test image on QEMU virt; the Pi 5 and
  the image of the largest size need board runs of their own.

### ASP-R10

**The boot-bundle directory.** The kernel reads the directory at the start
of the bundle once, as untrusted input, before it carves any storage, and
stops the boot with the fixed error of the first check that fails: the
bundle, the magic, the version, the size of the directory, a reserved
field, the kind, the range and the form of each entry, the root's segments
and the root entry, and the number of capacity records. A directory without
a capacity record makes the boot use the default of the board. The
criterion: the host tests of the directory of the contract hold, each check
at its limit and one beyond, and each pair of consecutive checks with the
error of the earlier.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `Directory::parse`, `Directory::entry` and
  `Directory::capacity_record` (planned).
- **Contract.** [Boot-bundle directory](contract.md#boot-bundle-directory).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The host tests of the directory of the
  [contract](contract.md#testing-obligations). They show the checks on
  directories that the tests build; the directory of a built image is
  shown by the boot of the root.

### ASP-R11

**EL0 controls.** EL0 reads `CNTVCT_EL0` and `CNTFRQ_EL0` without a trap,
and an access at EL0 to the physical counter, to the physical or virtual
timer, to the performance monitors or to the debug communications channel
traps with the exception class `0x18`; EL0 cannot mask an interrupt, its
stack pointer is checked for alignment, its data accesses are
little-endian, it reads `CTR_EL0`, executes `DC ZVA`, cache maintenance by
address and `WFE` without a trap, and a `WFI` that would wait traps. Every
CPU has these controls before it first enters EL0. The criterion: on QEMU
virt, the reads of `CNTVCT_EL0` and `CNTFRQ_EL0` succeed at EL0, and the
three traps of the contract and the cases of `SpAlignment` and of a read
of `PMCCNTR_EL0` hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `krepi_arch::el0::write_controls` (planned).
- **Contract.** [EL0 controls](contract.md#el0-controls).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path; the write is an
  [open obligation](contract.md#open-obligations).
- **Evidence.** The QEMU tests of the timer reads and of the three traps,
  and the QEMU cases of the classes `SpAlignment` and `TrappedAccess`, of
  the [contract](contract.md#testing-obligations). They show the controls
  on QEMU virt; on the Pi 5, whose drop from EL2 leaves other bits, a board
  run shows them.

### ASP-R12

**Kernel stacks and blocking.** Every CPU has one kernel stack with a guard
and one emergency stack, and no thread owns a kernel stack; no kernel frame
survives a return to EL0. A blocked call writes back two or six result
registers when it completes, and a call that stops at a preemption point
writes no result and is dispatched again from its saved registers before
its thread returns to EL0. The criterion: on QEMU virt, the test of
`entry-stack` holds, and the tests of the blocking calls, which their
components name, find the results in the result registers.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `__el0_entry` and `__el0_return` (planned), with
  `Context::set_return_values` and `set_return_registers` of the context
  component.
- **Contract.** [Kernel stacks and blocking](contract.md#kernel-stacks-and-blocking).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The test of the rule `entry-stack` that its
  [open obligation](contract.md#open-obligations) names, and the tests of
  the components of waits and of long operations (planned). They show the
  kernel stack of the boot CPU; the stacks of other CPUs and the emergency
  stacks are shown by the components that give them.

## Liveness, time and performance

- Every entry of the component runs to its end within the bounds of the
  [contract](contract.md#work-bounds); none waits, retries or takes a lock
  of its own.
- A switch between address spaces invalidates no TLB entry; an ASID is
  invalidated once, at its release.
- No requirement bounds the time that a step takes.

## Scope

- One CPU: the invalidation of an ASID on another CPU with its
  acknowledgement, and 16-bit ASIDs, are not covered.
- The writes of the tables, the kernel's own mappings and the direct map
  belong to the [page-tables](../page-tables/requirements.md) component; the
  saved context, its validation and the FP/SIMD and TLS state to the
  [context](../../boot-platform/context/requirements.md) component.
- The capacity record, the objects, the quotas and the state of processes
  and threads belong to the
  [objects](../../objects-capabilities/objects/requirements.md) component
  and to the components of creation and of the lifecycle of processes; the
  image windows, the VM windows, the loading of images and the wait records
  to the components of loading, of VM and of waits (planned). The frozen
  vectors that assert those states are inputs of those components, and the
  [contract](contract.md#legacy-test-vectors) gives them no case.
- The copies of user memory, Privileged Access Never, fault handlers,
  upcalls and the restart of interrupted calls by EL0 belong to later
  releases.
- The size and the probe of the emergency stacks, and the stacks of the
  other CPUs, belong to the components of diagnostics and stacks and of
  multicore.

## Contract sections without a requirement

- [Terms](contract.md#terms): definitions only.
- [Check and execute](contract.md#check-and-execute),
  [Determinism](contract.md#determinism) and
  [State fields](contract.md#state-fields) bind the code without an
  observable behaviour of their own; the errors of
  [Check and execute](contract.md#errors) are those of the requirements
  above.
- [Work bounds](contract.md#work-bounds) states the bounds that
  [Liveness, time and performance](#liveness-time-and-performance) relies
  on.
