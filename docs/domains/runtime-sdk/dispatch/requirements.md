---
features: none
---

# Dispatch requirements

The observable behaviour of the dispatch component of the
[runtime ABI and SDK](../README.md) domain: the decoding of every native
system call by its operation number and version, the refusal of the calls
that the dispatch table does not serve and of reserved and unused
registers that are not 0, the order of errors and the rights of the
operations, the results of a call, the composition of every entry from EL0
into one transition with the round trip of its plans, the validation of
the segments and of the commit of a request to load an image, the image
window of a child, and the loading part of the capacity record. The rules
that its code and tests follow are in the [contract](contract.md). No
feature document covers the component, so the metadata lists none.

## Sources

- The register contract of native calls, the operation in `x8` and the
  version in `x7` with a reserved `x6`, the checks of reserved and unused
  arguments at full width, results that replace `x0` to `x5` and keep every
  other register, and the checks of the segments of a request to load an
  image, page-aligned ranges with R, RX and RW access, equal sizes of R and
  RX segments, the zero tail of an RW segment and the refusal of overlap,
  overflow, other permissions and an entry outside RX, take the rules of
  the prototype's ABI module and loader, which the
  [references](contract.md#references) of the contract list, with the host
  tests of its loader and of its ABI as the frozen
  [vectors](contract.md#legacy-test-vectors).
- The version 1 and the table keyed by the version and the number with its
  production and diagnostic ranges, the order of the checks of a call, the
  result registers of every call, the composition of a transition with the
  round trip of its plans, the validation by steps, the one image window
  and the loading part of the capacity record are new, from the kernel's
  [system calls and the ABI](../../../architecture.md#system-calls-and-the-abi),
  its [capacities](../../../architecture.md#kernel-objects-and-capabilities)
  and its
  [address spaces](../../../architecture.md#address-spaces-and-vm-objects);
  the [current deviations](contract.md#current-deviations) of the contract
  list where they differ from the prototype.
- The order of errors, the observable outputs and the permitted
  nondeterminism follow the
  [security model](../../../security.md#internal-choices),
  and the source of loaded code its
  [integrity policy](../../../security.md#integrity-policy); the classes of
  state follow the
  [SMP design rules](../../../conventions/smp.md#s5-state-field-tables).
- The operations are those of the
  [capabilities](../../objects-capabilities/capabilities/requirements.md),
  [IPC](../../ipc-waits/ipc/requirements.md),
  [waits](../../ipc-waits/waits/requirements.md),
  [scheduler](../../scheduling/scheduler/requirements.md),
  [creation](../../objects-capabilities/creation/requirements.md),
  [VM](../../memory/vm/requirements.md) and
  [lifecycle](../../objects-capabilities/lifecycle/requirements.md)
  components; the entry from EL0 and the return to it, the classes of its
  exceptions and user faults and the boot-bundle directory those of the
  [address-space](../../memory/address-space/requirements.md) component;
  the saved context and the writing of results that of the
  [context](../../boot-platform/context/requirements.md) component; and the
  write plans those of the
  [page-tables](../../memory/page-tables/requirements.md) component.

## Configurations

- **QEMU virt.** The machine `virt-8.2` without EL2 and EL3, with GICv2,
  one Cortex-A76 and 128 MiB of RAM at `0x4000_0000`: the machine of
  `cargo xtask qemu`, with the QEMU version that `toolchains.toml` pins for
  the host, booted with the default capacity record of the board.
- **Raspberry Pi 5.** Only the 8 GB model is run on a board in release
  0.1, with one of its four Cortex-A76 cores running and the default
  capacity record of the board.
- **Host.** The host tests of the modules `dispatch` and `loader` of the
  core (planned) run on the development host and in CI, with the frozen
  vectors and the tests that the
  [contract](contract.md#testing-obligations) adds, each with the dispatch
  table, the capacity record and the plans that it passes, and with a
  double of the architecture crate that executes the plans.
- One CPU. The limits of the loading part are shared state, read-only
  after boot, and the composition of a transition runs on the CPU of the
  entry, also while one CPU runs; no requirement here covers the order in
  which several CPUs enter the kernel or take tokens.

## Requirements

### DISP-R01

**Operation numbers and versions.** A native system call is `svc #0` with
the operation number in bits 0 to 15 of `x8`, every bit above them 0, and
the major version of the ABI in `x7`. Release 0.1 accepts the version 1
alone. The production operations take the numbers `0x0001` to `0x7FFF`
and the diagnostic operations `0x8000` to `0xFFFF`; the dispatch table of
the default image has no diagnostic row, and a number is never reused. The
criterion: every operation of the ABI inventory is reached through its
number with the version 1; the version 0, of the prototype, and every
other version are refused; and every diagnostic number is refused in the
default image, and a diagnostic number with a row of the test build
reaches its operation there.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `dispatch::syscall` (planned), with the constant
  `dispatch::VERSION` (planned).
- **Contract.** [Operation numbers and versions](contract.md#operation-numbers-and-versions).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vector `abi-validation-1` as a host test, the
  host tests of rejection of the [contract](contract.md#testing-obligations),
  among them a diagnostic number in the default image and in a test build,
  and its QEMU tests of an unknown operation number and of an unknown
  version from EL0.

### DISP-R02

**Rejection.** Every value of the immediate of the `SVC`, of `x7` and of
`x8` has one fixed result: an immediate other than 0 is refused with
`UNSUPPORTED_OPERATION` and does not end the caller; with the immediate 0,
a version other than 1 is refused with `UNSUPPORTED_VERSION`; with both, a
value of `x8` without a row of the dispatch table, a bit above bit 15 or
the number 0 among them, is refused with `UNSUPPORTED_OPERATION`. These
three checks come in this order and before any check of the reserved
register, the arguments or the rights of an operation. A refused call
changes no state. The criterion: a call for each row of the table of
rejection of the contract gets its result and leaves every field of the
kernel state as it was; a call that breaks two of the checks gets the
error of the earlier; and the results of random registers equal those of
an independent model of the table.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `dispatch::syscall` (planned).
- **Contract.** [Rejection](contract.md#rejection) and
  [Errors](contract.md#errors).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vector `abi-validation-1` as a host test, with
  `abi-ipc-validation-1` of the
  [IPC contract](../../ipc-waits/ipc/contract.md#legacy-test-vectors) and
  `waits-transfers-5`, `abi-notification-3` and `abi-waits-3` of the
  [waits contract](../../ipc-waits/waits/contract.md#legacy-test-vectors),
  whose cases of the dispatch this component replays; and the host tests of
  rejection and order and the property test of the table of the
  [contract](contract.md#testing-obligations).

### DISP-R03

**Reserved and unused registers.** A call whose reserved register `x6` is
not 0, or one of whose argument registers `x0` to `x5` that its operation
does not use is not 0, is refused with `INVALID_ARGUMENT`, `x6` first and
then the unused registers in ascending order, before every check of the
operation, and changes nothing. The criterion: for each operation of the
dispatch table, `x6` and each unused argument register with 1, $2^{63}$
and $2^{64} - 1$ give `INVALID_ARGUMENT` and leave the state as it was,
and the same call with these registers 0 reaches its operation.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `dispatch::syscall` (planned).
- **Contract.** [Rejection](contract.md#rejection) and
  [Order of errors](contract.md#order-of-errors).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vector `abi-validation-2` as a host test, with
  `abi-ipc-validation-2` of the
  [IPC contract](../../ipc-waits/ipc/contract.md#legacy-test-vectors) and
  `abi-notification-3` and `abi-waits-3` of the
  [waits contract](../../ipc-waits/waits/contract.md#legacy-test-vectors);
  the host tests of rejection of the
  [contract](contract.md#testing-obligations); and its QEMU tests, one call
  for each operation of the inventory with an argument that its checks
  refuse.

### DISP-R04

**Order of errors.** When a call breaks several rules, its error is that of
the first place in the order of errors of the security model: the
operation number and version, the form of the register arguments, handle
resolution, rights, user buffers and argument structures, object state,
the caller's quota and shared capacity. An argument in a register is
checked for its form before any handle is resolved; an argument in a
structure that the kernel copies in would be checked after the rights and
the range of its buffer, and no operation of release 0.1 has one. The
criterion: for each pair of consecutive checks of the dispatch and of the
loading component, a call that breaks both gets the error of the earlier;
a call that breaks a check of the dispatch and one of its operation gets
the error of the dispatch; and a malformed mask with a handle that names
no capability gets the error of the mask.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `dispatch::syscall` and `loader::validate` (planned).
- **Contract.** [Order of errors](contract.md#order-of-errors).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `abi-validation-3` and `loader-6` as
  host tests, with `waits-transfers-5` of the
  [waits contract](../../ipc-waits/waits/contract.md#legacy-test-vectors),
  and the host tests of order of the
  [contract](contract.md#testing-obligations).

### DISP-R05

**Rights of the operations.** The rights that an operation needs are
constants of the operation, which the lookups of its handles check; no
value that EL0 passes selects them, and the dispatch adds no right. A
handle names a slot of the caller's own table only. The criterion: a call
that passes the checks before the rights, through a capability with fewer
rights than its operation needs, is refused with `PermissionDenied` and
changes nothing, and no value of another register supplies the right;
a capability derived with OBSERVE alone queries a process and neither
kills nor revokes it; one with CONTROL alone kills a process and does not
query it; GRANT and REVOKE imply no other right; and the same value of a
handle in another process names a slot of that process's table.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `dispatch::syscall` and `dispatch::entry` (planned).
- **Contract.** [Rights](contract.md#rights).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `abi-authority-1`, `abi-authority-2`,
  `abi-authority-3`, `abi-authority-5` and `abi-lifecycle-3` as host
  tests, which reach the lookups of the capabilities component and the
  operations of the lifecycle component through the dispatch, and the QEMU
  tests of the [contract](contract.md#testing-obligations).

### DISP-R06

**Results and no change on failure.** A call that completes in its
transition gets `OK` in `x0` and its results in `x1` to `x5`, 0 in the
result registers that its operation does not use; a refused call gets the
status of its error in `x0` and 0 in `x1` to `x5`. After either, every
other register and field of the saved context keeps its value. A refused
call, by the dispatch or by its operation, changes no field of the kernel
state; the settlements of expired waits before it in its transition stay.
The criterion: after a success and after each kind of failure, the result
registers hold what the contract states and every other field of the saved
context and of the kernel state is unchanged; a call whose capability table
is full is refused by the slot that it names and keeps every capability
that it held.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `dispatch::entry` (planned).
- **Contract.** [Results](contract.md#results),
  [Rejection](contract.md#rejection) and
  [Check and execute](contract.md#check-and-execute).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `abi-validation-1`, `abi-validation-2`,
  `abi-validation-3` and `abi-authority-4` as host tests, and the host tests
  of results of the [contract](contract.md#testing-obligations).

### DISP-R07

**Composition of a transition.** Each entry from EL0 is one transition,
which reads the time once: it first settles every wait whose deadline has
passed, then handles its event, a system call by its operation, a user
fault by the end of the process of the thread, an interrupt, and then
composes the return to the thread that the scheduler chooses, whose saved
context is validated; a refused context ends its process, and the return is
composed again. An interrupt pending at the return is handled, in a
transition of its own, before the thread returns. A CPU with no thread to
run waits for an interrupt. The end of the root halts the system on the
fatal path. The criterion: with a host double of the architecture crate,
the expiry of a wait settles before the operation of its transition; a user
fault and a refused context end only their process; an interrupt pending at
the return is handled before the thread returns; a CPU with no ready thread
waits and chooses again at its wake; and the exit of the root ends on the
fatal path with `CASXI_HALTED`.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `dispatch::entry` and `dispatch::compose_return`
  (planned).
- **Contract.** [Composition of a transition](contract.md#composition-of-a-transition).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vector `abi-lifecycle-1` as a host test, the host
  tests of composition of the [contract](contract.md#testing-obligations),
  and the QEMU tests of user faults and of the end of the root of the
  [lifecycle contract](../../objects-capabilities/lifecycle/contract.md#testing-obligations),
  which run through this composition.

### DISP-R08

**Plans and execution again.** The kernel changes a table, invalidates an
ASID and writes a frame only through plans that the architecture crate
executes one at a time, each after the write-back of the operation that
fixed it, and none fails; a frame returns to the page pool only after the
plan that zeroed it. A long operation, a revocation, a destruction or the
release of a region, takes one bounded step in each transition, stores its
progress in its object and is executed again from the saved user registers,
at once unless an interrupt is pending or the step has made a thread of a
higher class ready. The criterion: a commit of pages, a commit of a child
and the steps of a kill give their plans in order, one in flight at a time;
each step of a kill and of a release ends with the address of the `SVC` in
`elr` and continues from its progress when it is executed again; and no
frame of the pool is reused before its zero plan has been executed.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `dispatch::entry` and `dispatch::resume` (planned).
- **Contract.** [The round trip of plans](contract.md#the-round-trip-of-plans)
  and [Execution again](contract.md#execution-again).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vector `abi-lifecycle-2` as a host test, whose
  revocation runs in steps through the dispatch, and the host tests of
  composition and of results of the
  [contract](contract.md#testing-obligations), with a double of the
  architecture crate that executes the plans.

### DISP-R09

**Segments of a request to load.** Each segment that a creator stages for
the image of its child is checked when it is staged, against the segments
staged before it: its sizes, its alignment to pages, the overflow of its
additions, its access, R, RX or RW, the equal sizes of an R or RX segment,
its range within the segment range of the image window, a creation in
progress, its range of bytes within the entry of its image, no page shared
with another segment, the number of segments and the private pages of the
image, in this order, each with its fixed error. A refused segment changes
nothing, and the plan keeps the segments accepted before. The criterion:
each refusal of the contract through a segment that breaks only its rule,
with the plan unchanged after it; segments at the edges of the segment
range accepted and one page beyond refused; and the frozen vectors of the
prototype's loader hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `loader::validate` (planned), with the value types of
  its row.
- **Contract.** [Load validation](contract.md#load-validation) and
  [Segments](contract.md#segments).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `loader-1`, `loader-2`, `loader-3`,
  `loader-4`, `loader-5`, `loader-6` and `loader-7` as host tests, with
  `as-16` of the
  [address-space contract](../../memory/address-space/contract.md#legacy-test-vectors);
  the host tests of load validation of the
  [contract](contract.md#testing-obligations); and its QEMU tests of
  children whose segments overlap, are writable and executable, lie
  outside the window or are unaligned.

### DISP-R10

**The commit of an image and W^X.** The commit of a child is accepted only
when its entry is a multiple of 4 and lies in an RX segment, its plan holds
at least one segment, and its private pages, those of its RW segments and
of its initial stack, are within the limit of the capacity record. Only R,
RX and RW segments are accepted: the pages of R and RX segments are pages
of the boot bundle and those of RW segments and the stack private pages,
so no page of a loaded image is writable and executable. The criterion: a
commit with an entry in an R or RW segment, outside every segment or not a
multiple of 4, and one without a segment, are refused; a commit of private
pages one page beyond the limit is refused; and no plan that the loading
component accepts, among random plans, holds a page that would be mapped
writable and executable.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `loader::validate` (planned).
- **Contract.** [Commit](contract.md#commit) and
  [Load validation](contract.md#load-validation).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `loader-2`, `loader-3`, `loader-4`,
  `loader-7` and `loader-9` as host tests, and the host tests of load
  validation of the [contract](contract.md#testing-obligations), among them
  the property test of W^X.

### DISP-R11

**The image window.** Every child maps its segments and its initial stack
in the image window, from `IMAGE_BASE`, `0x4020000000`, for the pages of
the capacity record, at most to `0x4040000000`, the start of the VM
window: its stack is the highest pages of the window, with an unmapped
guard below it, and its segments lie below the guard. The window lies in
the EL0 window, outside the boot ranges of the root and below the VM
window. The criterion: a segment at `IMAGE_BASE` and one that ends at the
guard are accepted, and segments below `IMAGE_BASE`, on the guard and in
the stack are refused; the initial stack pointer of a child is the top of
its window; and the constants keep their relations with the boot ranges
and the VM window.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `loader::validate` (planned), with the constants
  `loader::IMAGE_BASE`, `IMAGE_END` and `MAX_WINDOW_PAGES` (planned).
- **Contract.** [The image window](contract.md#the-image-window).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `loader-7` and `loader-9` as host tests,
  the host tests of load validation and of the image window of the
  [contract](contract.md#testing-obligations), and the QEMU test of a child
  that runs its entry and reads its stack of the
  [creation contract](../../objects-capabilities/creation/contract.md#testing-obligations).

### DISP-R12

**The loading configuration.** The loading part of the capacity record,
bytes 64 to 91, gives the pages of the image window, the segments of an
image, the private pages of an image, the pages of the initial stack, the
root's limit of private pages of loaded images, and the pages and entries
of the boot bundle; the default record of each board gives them when the
directory holds no record. The boot checks them once, before it carves any
storage: each at least 1, and each but the root's limit within its hard
limit, the stack within the window and the private pages, the tables of a
child within its table pool, the root's limit at least the root's own
private pages, and the bundle within its limits. A record that breaks a
check stops the boot with its error, without a fallback to the defaults.
The criterion: a record that breaks each check stops the boot with its
error; the largest window that the tables admit is accepted and one page
more refused; the default record of each board passes; and a change of the
values of a record changes neither the checks nor the bounds of the code.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `loader::validate` (planned), its step `Limits`, with
  the constants `loader::MAX_SEGMENTS`, `MAX_WINDOW_PAGES` and
  `MAX_BUNDLE_PAGES` (planned).
- **Contract.** [Loading configuration](contract.md#loading-configuration).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The host tests of the loading configuration of the
  [contract](contract.md#testing-obligations), and the boots of the default
  record of each board on QEMU virt and on the 8 GB Pi 5. No frozen vector
  covers it: the prototype fixed its limits in its code. The tests of the
  limits of loading (planned) measure the default values.

## Liveness, time and performance

- Every transition runs to its result without a preemption point, within
  the bounds of the [contract](contract.md#work-bounds); its time grows
  with the expired waits that it settles, at most the thread capacity, and
  with the plans that its operation gives.
- A long operation takes one step in each transition, and the composer
  returns to its thread at once unless an interrupt is pending or the step
  has made a thread of a higher class ready, so an interrupt waits at most
  for one step.
- `syscall` and `validate` take a number of steps that the hard limits
  bound, whatever the values of the capacity record.
- No requirement bounds the time of a transition.

## Scope

- One CPU. The order in which several CPUs enter the kernel, the tokens
  and their locks are not covered.
- The operation numbers, the registers of arguments and results, the codes
  of errors and statuses, the mapping of the errors of the contracts to
  statuses and the check that the dispatch table, the inventory and
  `krepi-abi` agree belong to the ABI inventory (planned).
- The operations that the table reaches belong to their components; the
  creation of a child, with the mapping of its image and the copy of its
  file bytes, to the creation component; the parsing of ELF files and the
  start of a program to the runtime of EL0
  ([Application entry and CRT](../README.md#application-entry-and-crt)).
- The binding of interrupts to notifications and the windows of device
  grants belong to the devices and DMA domain; the Linux path of an `SVC`
  to Linux compatibility; user buffers and argument structures copied in
  to a later release.
- The measured values of the defaults of the loading part and the check of
  the boot bundle against its limits at build time belong to the tests of
  the limits of loading (planned).

## Contract sections without a requirement

- [Terms](contract.md#terms): definitions only.
- [Entry points](contract.md#entry-points) lists the entries that the
  requirements name.
- [Extractability](contract.md#extractability) states the modules, their
  layers and the modules that they do not refer to, which no requirement
  observes.
- [Work bounds](contract.md#work-bounds) states the bounds that
  [Liveness, time and performance](#liveness-time-and-performance) relies
  on.
- [Determinism](contract.md#determinism) states the order of a transition
  and the sources of nondeterminism, which DISP-R07 observes in part.
- [State fields](contract.md#state-fields) binds the code without an
  observable behaviour of its own.
- [Open obligations](contract.md#open-obligations) lists the effects across
  components that no target covers.
- [Current deviations](contract.md#current-deviations) states where the
  rules differ from the prototype, which the requirements state directly.
