---
features: none
---

# Lifecycle requirements

The observable behaviour of the `lifecycle` component of the
[kernel objects and capabilities](../README.md) domain: the states of a
process and its exit reasons, of which the first to arrive decides; the
end of a process by its exit, a user fault and a kill; the destruction of a
dying process and of its children in bounded steps; the reaping of a dead
process by its owner; the queries of a process, with its CPU time and its
fault record; its death notifications; and the end of the root. The rules
that its code and tests follow are in the [contract](contract.md). No
feature document covers the component, so the metadata lists none.

## Sources

- The lifecycle alive, dying, dead and reaped, the first terminal reason
  that later operations keep, the distinct reasons of an exit, a kill and a
  fault, the termination that ends the waits of a thread and keeps those
  already completed, the reclamation after the thread no longer runs, with
  the invalidation of the ASID before the reuse of its pages, and the
  independent observation of an exit, take the rules of the prototype's
  object pool, execution manager and join registry, which the
  [references](contract.md#references) of the contract list, with their
  host tests as the frozen [vectors](contract.md#legacy-test-vectors).
- The destruction advanced by kills in bounded steps with its progress in
  the process, the cascade to children in the order of their creation, the
  reaping by the owner gated by Dead and not by references, the return of
  limits to the owner, the death notification as a signal of a notification
  with a slot kept for the owner, the fault record of a query, and the halt
  of the system at the end of the root are new, from the kernel's
  [process lifetime](../../../architecture.md#kernel-objects-and-capabilities),
  its [execution model](../../../architecture.md#system-calls-and-the-abi)
  and its
  [process services](../../../architecture.md#processes-posix-and-linux-compatibility);
  the [current deviations](contract.md#current-deviations) of the contract
  list where they differ from the prototype.
- The first cause that decides the exit reason, the order of errors, the
  order of destruction and the observable outputs of a process, with its
  death notification delivered once and its fault record, follow the
  [security model](../../../security.md#internal-choices) and its
  [observable outputs](../../../security.md#observable-outputs); the
  classes of state follow the
  [SMP design rules](../../../conventions/smp.md#s5-state-field-tables).
- The objects, owners, quota records and write sets are those of the
  [objects](../objects/requirements.md) component; the rights, lookups and
  the teardown of a table those of the
  [capabilities](../capabilities/requirements.md) component; the
  settlement of calls and the drains of endpoints those of the
  [IPC](../../ipc-waits/ipc/requirements.md) component; the waits, their
  cancellation, the drains and signals of notifications those of the
  [waits](../../ipc-waits/waits/requirements.md) component; the removal of
  a thread and its holdings and CPU time those of the
  [scheduler](../../scheduling/scheduler/requirements.md) and
  [budget-ledger](../../scheduling/budget-ledger/requirements.md)
  components; the user faults, the release of an ASID and the reset of the
  tables those of the
  [address-space](../../memory/address-space/requirements.md) and
  [page-tables](../../memory/page-tables/requirements.md) components; and
  the revocation of the frames of a process that of the
  [VM](../../memory/vm/requirements.md) component.

## Configurations

- **QEMU virt.** The machine `virt-8.2` without EL2 and EL3, with GICv2,
  one Cortex-A76 and 128 MiB of RAM at `0x4000_0000`: the machine of
  `cargo xtask qemu`, with the QEMU version that `toolchains.toml` pins for
  the host.
- **Raspberry Pi 5.** Only the 8 GB model is run on a board in release
  0.1, with one of its four Cortex-A76 cores running.
- **Host.** The host tests of the module `lifecycle` of the core (planned)
  run on the development host and in CI, with the frozen vectors and the
  tests that the [contract](contract.md#testing-obligations) adds, each
  with the processes, objects and plans that it builds.
- One CPU. The fields of this component are shared state under the token
  of each process slot, also while one CPU runs; no requirement here
  covers the kill of a thread that runs on another CPU, several threads of
  one process or the locks that provide the tokens.

## Requirements

### LIFE-R01

**States and the first cause.** A process is alive from its creation,
leaves Alive exactly once, by its exit, a user fault of its thread, its
kill or the destruction of its owner, and is then dying, then dead, until
its owner reaps it, after which it no longer exists. Its exit reason is
Exited, with its exit code, Killed, or Faulted, with its fault record, and
the first cause to arrive decides it: a later exit, fault, kill or
destruction of the owner changes neither the reason nor the code nor the
record. Once it has left Alive, its thread never runs again. The criterion:
for each pair of causes in both orders, the first decides the reason, and
the second changes nothing; a process never returns to Alive; and the
frozen vectors of the order of causes hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `lifecycle::init`, `lifecycle::is_alive`,
  `lifecycle::exit`, `lifecycle::fault` and `lifecycle::kill` (planned).
- **Contract.** [States and exit reasons](contract.md#states-and-exit-reasons).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `execution-lifecycle-9`,
  `execution-lifecycle-10`, `joins-1`, `joins-3`, `objects-lifecycle-2` and
  `objects-lifecycle-7` as host tests, and the host tests of states and
  reasons of the [contract](contract.md#testing-obligations). The QEMU
  tests of exit, faults and kills show that a thread that has left Alive
  does not run at EL0 again.

### LIFE-R02

**Exit.** `exit` ends the caller's own process with the reason Exited and
the exit code, a 32-bit value, which reaches every observer unchanged; the
thread does not return. The exit removes the thread and makes the death
notifications, and the rest of the destruction waits for a kill. The
criterion: the exit codes 0, 1, 2 and 255 are read back unchanged by a
query, a code beyond 32 bits is refused, and the frozen vectors of exits
hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `lifecycle::exit` (planned).
- **Contract.** [Exit](contract.md#exit).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `execution-lifecycle-1`,
  `objects-lifecycle-2`, `objects-lifecycle-7` and `joins-14` as host
  tests, and the tests of exit codes of the
  [contract](contract.md#testing-obligations), on the host and as QEMU
  tests from EL0.

### LIFE-R03

**User faults.** A user fault of a thread ends only its process, with the
reason Faulted and a fault record that holds the cause class, the
exception class bits and, for the causes that have one, the faulting user
address; the kernel is unchanged and other processes run on. The
criterion: each of the eleven fault cases of the contract ends its process
with the record of its row while the kernel sentinel is unchanged and
another process runs on, and the frozen vectors of faults hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `lifecycle::fault` (planned).
- **Contract.** [Faults](contract.md#faults).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `execution-lifecycle-1` and
  `execution-lifecycle-10` as host tests, and the tests of faults of the
  [contract](contract.md#testing-obligations): the host test of each cause
  through `fault`, and the eleven QEMU cases from EL0 on QEMU virt. The
  8 GB Pi 5 runs the same cases with the caches on.

### LIFE-R04

**Kill.** A holder of CONTROL on a process kills it: the kill makes an
alive process dying with the reason Killed, ends the wait of its thread,
which no thread observes, withdraws the loans of its context, which returns
whole, and keeps EL0 from running in it again; it then advances the
destruction, and gives
its result once the process is dead. A kill of a dead process succeeds and
changes nothing, and a kill without CONTROL is refused and changes nothing.
The criterion: for each of the five states of a target, a busy loop, a
receive, a call with its context lent, a wait on a notification or a wait
set, and a sleep with a deadline, the kill stops EL0 in the target, as a
sentinel page shows, returns the lent context whole and ends the wait with
`Cancelled`; a second kill of the dead process gives the same result; a
kill without CONTROL is `PermissionDenied`; and the frozen vectors of kills
hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `lifecycle::kill` and `lifecycle::destroy_step`
  (planned).
- **Contract.** [Kill](contract.md#kill).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `execution-lifecycle-6`,
  `execution-lifecycle-9`, `joins-3`, `joins-failures-3`,
  `objects-lifecycle-3`, `objects-lifecycle-4` and `objects-lifecycle-6`
  as host tests, and the tests of kills of the
  [contract](contract.md#testing-obligations), as QEMU tests from EL0.
  They also show the kill whose part the
  [waits](../../ipc-waits/waits/requirements.md#wait-r09) requirements
  leave to this component.

### LIFE-R05

**Destruction in bounded steps.** A dying process is destroyed in steps:
its device grants, the endpoints that it owns, the endpoints bound to its
thread, the notifications that it owns, its capability table, its address
space, with the invalidation of its ASID before its tables are reset and
its frames return, and then its children; each step stays within a fixed
bound of work and writes, and between two steps is a preemption point, at
which the progress stays in the process and a later kill continues from
it. The calls and waits on the objects of the process end with
`PeerClosed` in these steps. The criterion: a property test of trees of
processes, killed with preemption at random steps, finds the steps in the
order of the contract, every write set within its bound, no frame back
before the reset and the invalidation of its process, and the same final
state with and without preemption; and the frozen vectors of destruction
hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `lifecycle::destroy_step`, `lifecycle::acknowledge`
  and `lifecycle::kill` (planned).
- **Contract.** [Destruction](contract.md#destruction) and
  [Work bounds](contract.md#work-bounds).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `execution-lifecycle-3` and
  `execution-lifecycle-4` as host tests, the property test of destruction
  and the test of peers of the
  [contract](contract.md#testing-obligations), and a QEMU test of the kill
  of a process with many objects that a timer interrupt preempts. They
  show the steps of the destruction that the requirements of
  [IPC](../../ipc-waits/ipc/requirements.md#ipc-r09),
  [waits](../../ipc-waits/waits/requirements.md#wait-r11),
  [capabilities](../capabilities/requirements.md#caps-r09) and
  [VM](../../memory/vm/requirements.md#vm-r07) leave to this component. It
  samples sequences and does not prove the order for every one.

### LIFE-R06

**Children.** The destruction of a process destroys its children after its
other objects, children before their parents and siblings in the order of
their creation; a child that it reaches alive is killed, with the reason
Killed, and one that ended before keeps its reason; the dying process
reaps each dead child, whose limits return to it. A kill that reaches the
caller's own process ends the call there. The criterion: trees of depth 3,
killed from their root and from a middle process, are destroyed in that
order whatever the order of their slots; a child that exited first keeps
Exited; and a child that kills its owner ends its own call at its phase 0.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `lifecycle::destroy_step`, `lifecycle::init` and
  `lifecycle::kill` (planned).
- **Contract.** [Children](contract.md#children).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The host tests of children of the
  [contract](contract.md#testing-obligations), and a QEMU test that kills
  a process with two levels of children. No frozen vector covers the
  cascade.

### LIFE-R07

**Reaping.** Only the owner of a process, holding CONTROL on it, reaps it,
and only once it is dead; the reap releases its process and thread, returns
its limits and its holdings to the owner, and leaves every capability to it
stale. No capability, reference or binding holds back the reap, and every
object, page, slot and limit of the process has returned once it is dead.
An owner that no longer holds CONTROL on a child cannot reap it, and that
child is reclaimed only with the destruction of the owner. The criterion: a
reap by a holder of CONTROL that is not the owner is `NotOwner`, a reap of
a process that is alive or dying is `InvalidState`, each changing nothing;
after a reap, the counts of pages, endpoints, notifications, capabilities
and ASIDs and the quota records of the owner are those before the creation,
over three rounds; and the frozen vectors of reaping hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `lifecycle::reap` (planned).
- **Contract.** [Reaping](contract.md#reaping).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `execution-lifecycle-1`,
  `execution-lifecycle-2`, `execution-lifecycle-3`,
  `execution-lifecycle-5`, `joins-14`, `joins-failures-3`,
  `joins-failures-13`, `objects-lifecycle-1`, `objects-lifecycle-2` and
  `objects-lifecycle-5` as host tests, and the tests of reaping and of the
  baseline of the [contract](contract.md#testing-obligations), on the host
  and as QEMU tests from EL0. They show the gate of reaping that the
  [VM](../../memory/vm/requirements.md#vm-r07) requirements leave to this
  component.

### LIFE-R08

**Queries and CPU time.** A holder of OBSERVE on a process reads its
state, its exit reason, its exit code and its CPU time, and, with another
selector, its fault record, empty when it did not fault; these stay
readable until the reap. CONTROL alone does not read them. The criterion:
the query gives the values of the contract in each state, before and after
the kill of an exited process; a faulted process gives its record and
another the empty one; an invalid selector is refused; a holder of
CONTROL alone is refused; and the frozen vectors of queries hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `lifecycle::query` (planned).
- **Contract.** [Queries and CPU time](contract.md#queries-and-cpu-time).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `joins-1`, `joins-2` and
  `joins-failures-3` as host tests, with the vectors `abi-lifecycle-1` and
  `abi-lifecycle-3` of the dispatch component (planned), which the contract
  replays, and the tests of faults and exit codes of the
  [contract](contract.md#testing-obligations), which read their results by
  `query` from EL0. They show the query of the CPU time from EL0 that the
  [budget-ledger](../../scheduling/budget-ledger/requirements.md#ledg-r07)
  requirements leave to this component.

### LIFE-R09

**Death notifications.** A holder of OBSERVE on a process and of SIGNAL on
a notification registers the notification for the death of the process,
and when the process leaves Alive, the notification is signalled with the
registered bits exactly once. A registration made after the death is
signalled at once; one whose notification is released first lapses and
never reaches a notification that takes its place; when an exit and a kill
compete, one notification is made, for the first. One slot of every
process is kept for its owner, so other observers cannot keep the owner
from its notification, and a registration that finds no free slot is
refused with an error of shared capacity. The criterion: one case for each
of these five rules, among them a deterministic exit and kill in the same
order every run, a notification registered as a source of a wait set,
and a full set of observers beside the owner's registration; and the
frozen vectors of observation hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `lifecycle::watch`, `lifecycle::exit`,
  `lifecycle::fault` and `lifecycle::kill` (planned).
- **Contract.** [Death notifications](contract.md#death-notifications).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `joins-1`, `joins-4`, `joins-5`,
  `joins-6`, `joins-10`, `joins-12`, `joins-13`, `joins-14`,
  `joins-failures-2`, `joins-failures-6` and `joins-failures-9` as host
  tests, and the tests of death notifications of the
  [contract](contract.md#testing-obligations), on the host and as QEMU
  tests from EL0.

### LIFE-R10

**The end of the root.** The root never becomes dying: its exit, a user
fault of its thread and a kill of it, by itself or by another holder of
CONTROL on it, halt the system through the fatal path of the boot, which
writes its record and `CASXI_HALTED` to the serial console. The root is
never destroyed or reaped. The criterion: a root that exits and a root
that another process kills through a derived capability with CONTROL each
end in the fatal path, and no step of a destruction runs for the root.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `lifecycle::exit`, `lifecycle::fault` and
  `lifecycle::kill` (planned).
- **Contract.** [The root](contract.md#the-root).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The QEMU tests of the root of the
  [contract](contract.md#testing-obligations), and the host tests of the
  halt that `exit`, `fault` and `kill` give for the root. The serial
  diagnostics are not an output; the tests read the marker of the fatal
  path.

### LIFE-R11

**No change on failure.** Every error of the component leaves the kernel
state as it was: a refused operation writes nothing, signals nothing,
gives no plan and counts nothing. The errors follow the order of the
security model: the form of the register arguments, handle resolution,
rights, object state, shared capacity. The criterion: for each error of
the contract, a call that gives it leaves every field compared before and
after unchanged; for each pair of consecutive checks whose errors differ,
a call that breaks both gets the error of the earlier; and the frozen
vectors of refusals hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** Every row of the
  [entry table](contract.md#entry-points).
- **Contract.** [Errors](contract.md#errors) and
  [Check and execute](contract.md#check-and-execute).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `execution-lifecycle-6`,
  `joins-failures-2`, `joins-failures-3`, `joins-failures-9` and
  `joins-failures-13` as host tests, and the host tests of the errors of
  the [contract](contract.md#testing-obligations).

## Liveness, time and performance

- Every entry of the component runs to its end within the bounds of the
  [contract](contract.md#work-bounds); none waits, retries or takes a lock
  of its own.
- The destruction of a process is the only long operation: it takes a
  number of steps that grows with what the process holds and with its
  descendants, each step within a fixed bound and with a preemption point
  between two steps. The longest step without a preemption point is the
  release of one endpoint or notification, with at most the thread
  capacity drains of its waiters.
- The destruction advances only while a holder of CONTROL calls `kill`;
  no requirement bounds the time until an owner does so, and a process
  stays dying, with the calls on its endpoints and the waits on its
  notifications, until then.
- No requirement bounds the time that a step takes.

## Scope

- One CPU. The kill of a thread that runs on another CPU, the tokens and
  their locks are not covered.
- A process has one thread. Further threads of a process, the exit of one
  thread, joins and their cycles, the interrupt of a wait, upcalls and
  user fault handlers belong to later releases.
- POSIX waits, signals and the records of exited processes belong to the
  process services of EL0, not to this component.
- The draining of the device grants that a process uses belongs to the
  device-authority rules of the devices and DMA domain; this component
  gives it its place among the steps.
- The creation of processes, their admission and the staging of their
  images belong to the creation component; the operation numbers, the
  registers of arguments and results and the numeric codes of errors of
  the ABI inventory are not covered.

## Contract sections without a requirement

- [Terms](contract.md#terms): definitions only.
- [Extractability](contract.md#extractability) states the module, its layer
  and the modules that it does not refer to, which no requirement observes.
- [Work bounds](contract.md#work-bounds) states the bounds that
  [Liveness, time and performance](#liveness-time-and-performance) relies
  on.
- [Determinism](contract.md#determinism) states the fixed rules of the
  internal choices that the requirements above observe through their
  results.
- [State fields](contract.md#state-fields) binds the code without an
  observable behaviour of its own.
- [Open obligations](contract.md#open-obligations) lists the effects across
  components that no target covers.
- [Current deviations](contract.md#current-deviations) states where the
  rules differ from the prototype, which the requirements state directly.
