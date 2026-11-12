# Lifecycle contract

This page governs the code of the `lifecycle` component of the
[kernel objects and capabilities](../README.md) domain: the states of a
process, alive, dying and dead, and the end of its identity when it is
reaped; the three exit reasons, of which the first to arrive decides; the
operations `exit`, `kill`, `query`, `reap` and `watch`; the end of a
process by a user fault of its thread; the destruction of a dying process
in bounded steps, with the destruction of its children in the order of
their creation; the reaping of a dead process by its owner, which returns
its limits; the queries of the state, the exit reason and code, the CPU
time and the fault record of a process; its death notifications; and the
end of the root, which halts the system. The creation of processes,
endpoints and notifications belongs to the
[creation](../creation/contract.md) component, which links a new process
into the chain of the children of its creator with an entry of this page;
the objects, the quota records and the write sets belong to the
[objects](../objects/contract.md) component; the teardown of a capability
table to the [capabilities](../capabilities/contract.md) component; the
settlement of calls, the drains of endpoints and notifications, the
cancellation of waits and the signals of notifications to the
[IPC](../../ipc-waits/ipc/contract.md) and
[waits](../../ipc-waits/waits/contract.md) components; the removal of a
thread from scheduling and the return of its holdings to the
[scheduler](../../scheduling/scheduler/contract.md) and
[budget-ledger](../../scheduling/budget-ledger/contract.md) components; the
release of the ASID and the reset of the lower tables of a process to the
[address-space](../../memory/address-space/contract.md) and
[page-tables](../../memory/page-tables/contract.md) components; and the
return of its frames to the [VM](../../memory/vm/contract.md) component.
This page orders their entries into the destruction of a process. The
observable behaviour that these rules serve, with its evidence, is in the
[requirements](requirements.md), the other document of the component.

## Terms

- **Process and thread.** An object of the process pool of the
  [objects](../objects/contract.md#object-kinds-and-pools) component and
  its one thread, an object of the thread pool, which the creation
  component creates together. A process has one thread in release 0.1, so
  "the thread of P" names one thread.
- **Owner.** The owner of a process, a field of its slot that the objects
  component keeps: the process that created it, or the kernel domain for
  the root; it never changes
  ([metadata quotas](../objects/contract.md#metadata-quotas)). A process is
  a **child** of its owner; the **descendants** of a process and the
  **process tree** follow.
- **State.** Alive, Dying or Dead, a field of the process slot
  ([States and exit reasons](#states-and-exit-reasons)). **Reaped** is not a
  stored state: the reap releases the process slot and the thread slot,
  after which every reference to them is stale, and a specification models
  it as the end of the identity.
- **Exit reason and exit code.** Exited, with the exit code that the
  process gave to `exit`; Killed; or Faulted, with a fault record. An alive
  process has neither.
- **Fault record.** The cause class of a user fault, the exception class
  bits of `ESR_EL1` and the user virtual address of `FAR_EL1`, where the
  [address-space](../../memory/address-space/contract.md#user-faults)
  component records them ([Faults](#faults)).
- **Leaving Alive.** The transaction that makes an alive process dying: its
  exit, a user fault of its thread, its kill, or the destruction of its
  owner reaching it. It is phase 0 of the destruction.
- **Destruction.** What a process undergoes from leaving Alive until it is
  dead: phase 0, and then phases 1 to 8 of [Destruction](#destruction).
- **Step.** One transaction of a destruction after phase 0, with the plans
  that it gives and their acknowledgement; between two steps is a
  preemption point. `lifecycle::Step` (planned) is also the value that an
  entry of this page gives the dispatch of the core: a plan; `Again`, the
  end of a step of a long operation whose progress is stored and which has
  no result yet; `Halt`, the halt of the system ([The root](#the-root)); or
  the result of the operation, which for an `exit` and for a kill of the
  caller's own process is that its thread does not return.
- **Progress.** The field of a process slot that holds where its
  destruction stands: the phase, the cursor in a pool, the progress of the
  teardown of its table, and the sub-step of the reclamation of its address
  space with whether its plan has been given
  ([Destruction](#destruction)).
- **Working process.** The process whose destruction a step of a kill
  advances: the target of the kill, or, while the target destroys its
  children, one of its descendants ([Children](#children)).
- **Plan.** A write plan of the page-tables component, the release plan of
  an ASID of the address-space component, or a frame plan of the VM
  component, which a step gives the dispatch of the core for the
  architecture crate to execute, as the
  [VM](../../memory/vm/contract.md#acknowledgement-and-reclamation)
  contract states for its own plans.
- **Chain of children.** The children of a process that are not reaped, in
  the order of their creation, linked through their process slots; the
  **first child** is the earliest of them ([Children](#children)).
- **Registration.** One of the `WATCH_SLOTS` positions of a process slot,
  which holds the reference of a notification and nonzero bits, written by
  `watch` ([Death notifications](#death-notifications)). The process that
  made it is an **observer**.
- **Death notification.** The signal of the notification of each
  registration of a process, with its bits, when the process leaves Alive.
- **Composer.** The module of the core above this one that calls an entry
  of this page: `dispatch` (planned), for the operations, the user faults
  and the acknowledgement of plans, and for whether an endpoint is served
  ([dispatch](../../runtime-sdk/dispatch/contract.md#composition-of-a-transition));
  and `creation` (planned), for a new process and for the bound thread of a
  new endpoint ([creation](../creation/contract.md#entry-points)).
- **Token.** What an access to state that is not per-CPU holds, as the
  [SMP design rules](../../../conventions/smp.md#s1-state-classes) state;
  with one CPU, the executing CPU holds every token.

## Entry points

The entries of the core are in the module `lifecycle` of `krepi-kernel`
(planned). Five of them are operations of the ABI inventory, in its
production range: `exit`, `kill`, `query`, `reap` and `watch` (planned).
Their operation numbers, the registers of their arguments and results and
the numeric values of their errors belong to the inventory; this page
names the arguments and the results and fixes the values of the results.
The other entries are called by the composers. The first row holds
constants.

| Entry point | Kind | Called by | ABI operation | Rules |
| --- | --- | --- | --- | --- |
| `lifecycle::WATCH_SLOTS` and `SCAN_BATCH` (planned) | Constants, host-testable | The entries of this page | None | [Death notifications](#death-notifications), [Destruction](#destruction), [Work bounds](#work-bounds) |
| `lifecycle::init` (planned) | Write entry on the copies of a write set, host-testable | `creation::spawn_commit` (planned), in the write set of the commit of a child process, after `ObjectTable::occupy` of its process slot; `creation::boot_root` (planned), in the write set of the boot of the root | None | [States and exit reasons](#states-and-exit-reasons), [Children](#children) |
| `lifecycle::is_alive` (planned) | Read entry, host-testable | `creation::create_endpoint` (planned), for the process of the thread that a new endpoint binds; `dispatch::entry` (planned) of the [dispatch](../../runtime-sdk/dispatch/contract.md#entry-points) component, for whether an endpoint is served, which it passes to `ipc` as a value | None | [States and exit reasons](#states-and-exit-reasons) |
| `lifecycle::exit` (planned) | Write entry on the copies of a write set, host-testable | `dispatch::entry` (planned) of the [dispatch](../../runtime-sdk/dispatch/contract.md#entry-points) component, for the operation `exit` | `exit` | [Exit](#exit), [The root](#the-root) |
| `lifecycle::fault` (planned), with the value type `lifecycle::FaultRecord` | Write entry on the copies of a write set, host-testable | `dispatch::entry` (planned) of the [dispatch](../../runtime-sdk/dispatch/contract.md#entry-points) component, at a user fault that `address_space::classify` gives; `dispatch::compose_return` (planned), at a saved context that `validate` refuses at a return to EL0 | None | [Faults](#faults), [The root](#the-root) |
| `lifecycle::kill` (planned), with the value type `lifecycle::Step` | Write entry on the copies of a write set, host-testable; one step of a long operation, which gives plans | `dispatch::entry` (planned) of the [dispatch](../../runtime-sdk/dispatch/contract.md#entry-points) component, for the operation `kill`, also when the call is executed again | `kill` | [Kill](#kill), [Destruction](#destruction), [The root](#the-root) |
| `lifecycle::destroy_step` (planned) | Write entry on the copies of a write set, host-testable; one step of the destruction of a process, which gives plans | `kill` of this page, for a target that is dying | None | [Destruction](#destruction), [Children](#children) |
| `lifecycle::acknowledge` (planned) | Write entry on the copies of a write set, host-testable; gives the next step | `dispatch::resume` (planned) of the [dispatch](../../runtime-sdk/dispatch/contract.md#entry-points) component, after the architecture crate has executed a plan that a step of a destruction gave, with the target of the kill | None | [Destruction](#destruction) |
| `lifecycle::reap` (planned) | Write entry on the copies of a write set, host-testable | `dispatch::entry` (planned) of the [dispatch](../../runtime-sdk/dispatch/contract.md#entry-points) component, for the operation `reap` | `reap` | [Reaping](#reaping) |
| `lifecycle::query` (planned), with the value type `lifecycle::Status` | Read entry, host-testable | `dispatch::entry` (planned) of the [dispatch](../../runtime-sdk/dispatch/contract.md#entry-points) component, for the operation `query` | `query` | [Queries and CPU time](#queries-and-cpu-time) |
| `lifecycle::watch` (planned) | Write entry on the copies of a write set, host-testable | `dispatch::entry` (planned) of the [dispatch](../../runtime-sdk/dispatch/contract.md#entry-points) component, for the operation `watch` | `watch` | [Death notifications](#death-notifications) |

The five operations, with the rights that each needs, as the
[capabilities](../capabilities/contract.md#rights) component fixes them for
a capability to a process:

| Operation | Arguments | Results | Rights | Errors, in the order of errors |
| --- | --- | --- | --- | --- |
| `exit` | `code`, the exit code | None: the thread does not return | None: it ends the caller's own process | The form of the register arguments: `InvalidExitCode` |
| `kill` | `process`, a handle | None, once the target is dead | CONTROL on the process | Handle resolution: the errors of the lookup; rights: `PermissionDenied`; object state: `RevocationPending`, `TransferPending` |
| `query` | `process`, a handle; `selector`, 0 or 1 | For the selector 0, `state`, `reason`, `code` and `cpu`; for 1, `cause`, `flags`, `ec` and `address` | OBSERVE on the process | The form of the register arguments: `InvalidSelector`; handle resolution; rights: `PermissionDenied`; object state: those of the lookup |
| `reap` | `process`, a handle | None | CONTROL on the process, with the caller's process its owner | Handle resolution; rights: `PermissionDenied`; object state: those of the lookup, `NotOwner`, `InvalidState` |
| `watch` | `process`, a handle; `notification`, a handle; `bits`, nonzero | None | OBSERVE on the process and SIGNAL on the notification | The form of the register arguments: `InvalidBits`; handle resolution, the process first; rights: `PermissionDenied`; object state: those of the lookups; shared capacity: `WatchCapacity` |

## Extractability

The module `lifecycle` of the core (planned), in `kernel/src/lifecycle.rs`
(planned), follows the
[provable Rust subset](../../../conventions/provable-subset.md): the
states, the exit reasons and codes, the fault records, the registrations,
the progress and the chains of children of the processes; the five
operations; the end of a process by a fault; the steps of a destruction
with their acknowledgement; and the reaping. It is in layer 7 of the
[module order](../../../architecture.md#module-order-in-the-core). It
refers to `objects` and `address_space` of layer 1, for references, write
sets, quota records, the ASID allocator and the table pool; to
`page_tables` of layer 2, for the reset of the lower tables of a process;
to the kernel root; to `capabilities` and `ledger` of layer 4, for
lookups, the teardown of a table, the CPU time and the return of holdings;
to `vm`, `waits` and `scheduler` of layer 5, for the revocation of the
frames of a process, the cancellation of a wait, the drains and signals of
notifications and the removal and requeue of a thread; and to `ipc` of
layer 6, for the settlement of a call and the drains of endpoints. It
refers to no module above it, `creation` and `dispatch`, and layer 7 holds
no other module. Three reads cross layers, each downwards or as a value:

- `creation`, in layer 8, calls `is_alive` for the process of the thread
  that a new endpoint binds.
- Whether an endpoint is served is a state of this layer: `dispatch` reads
  it with `is_alive` and passes it to `ipc`, in layer 6, as a value, as the
  [IPC](../../ipc-waits/ipc/contract.md#terms) contract states.
- The revocation of the frames of a process is called by this page in the
  steps of its destruction, and `vm` reads no state of a process beyond its
  own ([VM](../../memory/vm/contract.md#extractability)).

Its items are `pub(crate)`: the architecture crate and the board crates
call no entry of this page, and the halt that a step gives reaches
`el0_dispatch` through the dispatch of the core
([provable core](../../../architecture.md#the-provable-core)). The write
entries receive the one kernel root by `&mut`
([rule 3](../../../conventions/provable-subset.md#3-flat-relations-and-one-kernel-root))
and the write-set buffer, the scheduler record and the budget ledger of the
executing CPU by explicit `&mut` arguments
([rule 8](../../../conventions/provable-subset.md#8-no-interior-mutability)).
The module touches no register and defines no callback: every change of a
table, a TLB or a frame in a destruction is a plan that the architecture
crate executes, and a step continues through `acknowledge` once its plan
has been executed. The prototype's execution manager called its backend to
retire, invalidate and scrub, and its trusted controller published exit
records into a separate join registry; its rules are sources of this page
([References](#references)). The contract is written before its code, so
this section lists no source paths; the change that adds the module writes
its `paths` block here.

## States and exit reasons

The slot of every process holds these fields of this page,
`lifecycle::Record` (planned):

| Field | Content | Written by |
| --- | --- | --- |
| `state` | Alive, Dying or Dead | `init`, the transaction that leaves Alive, the last step of the destruction |
| `reason`, `code` | The exit reason, none while alive, and the exit code, 0 unless the reason is Exited | The transaction that leaves Alive |
| `fault` | The fault record, empty unless the reason is Faulted | The transaction that leaves Alive by a fault |
| `watches` | `WATCH_SLOTS` registrations, each none or a notification reference with nonzero bits | `watch`; cleared by the transaction that leaves Alive |
| `progress` | The progress of the destruction | The steps of the destruction |
| `first_child`, `last_child` | The ends of the chain of its children, or none | `init` of a child, the reap of a child |
| `previous_sibling`, `next_sibling` | Its neighbours in the chain of the children of its owner, or none | `init` of the process or of the next child of its owner, the reap of the process or of a neighbour |

`ObjectTable::occupy` and `release` of the objects component leave these
fields as the release of the earlier occupant cleared them, and `init`
writes them for the new process.

| From | Entry or event | To | Write set |
| --- | --- | --- | --- |
| A slot that `occupy` has just allocated | `init`, in the write set of the creation of the process or of the boot of the root | Alive, without a reason, a registration or children | The process slot and, for a child, the slots of its owner and of the former last child of its owner: at most 3 |
| Alive | `exit(code)` by its thread | Dying, Exited with `code` | Phase 0, at most 5 items, and one transaction for each death notification |
| Alive | A user fault of its thread: `fault` | Dying, Faulted with the fault record | Phase 0, at most 5 items, and the death notifications |
| Alive | `kill` by a holder of CONTROL on it | Dying, Killed | Phase 0, at most 16 items, and the death notifications |
| Alive | A step of the destruction of its owner that reaches it | Dying, Killed | Phase 0, at most 16 items, and the death notifications |
| Alive, the root | Its `exit`, a user fault of its thread, or a `kill` of it | The halt of the system, without a change | None |
| Dying | A step of its destruction, which a kill makes | Dying, its progress advanced | The write set of the step, at most 54 items |
| Dying, phases 1 to 7 done | The last step of its destruction | Dead | 1: the process slot |
| Dying or Dead | A user fault, which only a host test reports for it; the destruction of its owner reaching it | No change of its reason, code or record | None |
| Dead | `kill` | No change: the kill gives its result | None |
| Dead | `reap` by its owner, or a step of the destruction of its owner | Reaped: its process slot and its thread slot are released | At most 10 items ([Reaping](#reaping)) |

- **First to arrive.** On one CPU the transitions are totally ordered
  ([internal choices](../../../security.md#internal-choices)). The first
  transaction that makes a process leave Alive writes its reason, its exit
  code and its fault record, and no later transaction changes them until
  the reap: an exit, a fault, a kill and the destruction of the owner that
  come later find the process not alive and leave its reason. The exit
  reason is the first cause that arrived, and a cause that arrives with no
  effect leaves no trace.
- **Counterexample.** A process P exits with the code 3 in one transition,
  and its owner kills P in a later one. The query of P after the kill gives
  Exited with 3, not Killed: were the kill to write its own reason, an
  observer would read a cause that did not end the process.
- **Leaving Alive is once.** A process leaves Alive in exactly one
  transaction and never returns to Alive; Dying is followed only by Dead,
  and Dead only by the reap.
- **Alive.** `is_alive(process)` gives whether `process` is the live
  reference of a process whose state is Alive, and false for every other
  reference, among them a stale one. It writes nothing and does not fail.
- **The thread.** The thread of a process runs, waits or is ready only
  while its process is alive: the transaction that leaves Alive removes it
  from scheduling, and it never runs again
  ([removal](../../scheduling/scheduler/contract.md#blocking-and-readiness)).
- **Initialization.** `init(process, owner)` writes the fields of the table
  above for a new process: the state Alive, no reason, the code 0, an empty
  fault record, no registration, an empty progress and no children; and,
  when `owner` is a process, links the process at the end of the chain of
  its owner ([Children](#children)). The boot of the root passes the kernel
  domain as the owner, so the root is in no chain. It checks nothing, since
  its caller has just occupied the slot, and does not fail.

## Exit

- **The call.** `exit(code)` ends the caller's own process with the reason
  Exited and the exit code `code`. It checks the form of `code`: an exit
  code is 32 bits wide, so its register holds at most $2^{32} - 1$
  (`InvalidExitCode`). For the root, it then gives the halt of the system
  ([The root](#the-root)).
- **Phase 0.** Otherwise it makes phase 0 of the destruction of the
  process ([Destruction](#destruction)): the state Dying, the reason, the
  code, the removal of the thread, which is the current thread, with the
  charge of its dispatch, and the clearing of the registrations; then the
  death notifications, each in a transaction of its own in the same
  transition.
- **No return.** The thread does not return to EL0 and gets no result: the
  dispatch of the core composes the return with another thread.
- **The rest.** An exit makes only phase 0. The other phases are advanced
  only by kills of the process, which its owner makes once its death
  notification has arrived ([Destruction](#destruction),
  [Reaping](#reaping)).

## Faults

- **The call.** `fault(process, record)` ends the process of the current
  thread with the reason Faulted and its fault record. The dispatch of the
  core calls it at a user fault, every class of the
  [exception classes](../../memory/address-space/contract.md#exception-classes)
  but `Svc` and `Irq`, and at a saved context that `validate` refuses at a
  return to EL0, with the record that the
  [address-space](../../memory/address-space/contract.md#user-faults)
  component gives. For the root, it gives the halt of the system; for any
  other process, it makes phase 0, as `exit` does, with the record in
  place of the code; the thread does not return to EL0.
- **The fault record.** `lifecycle::FaultRecord` (planned) holds the cause
  class, by its value in the table of user faults of the address-space
  component, 1 to 9; for an exception, the bits of `EC` of `ESR_EL1`; and,
  for the causes `DataTranslation`, `DataPermission`,
  `InstructionTranslation`, `InstructionPermission` and for `Alignment`
  from `EC` `0x24` or `0x22`, the user virtual address of `FAR_EL1`. A
  refused context has the cause `Other`, no bits of `EC` and no address.
  The record keeps nothing else; the whole syndrome, with `ELR_EL1`, is at
  most a part of the serial diagnostics, which are not an output
  ([observable outputs](../../../security.md#observable-outputs)).
- **A late fault.** A user fault of a process that has left Alive does not
  arise, since its thread no longer runs; `fault` of such a process, which
  only a host test makes, changes nothing.
- **No handler.** Release 0.1 has no fault handler of a thread, so every
  user fault ends its process, and a user fault never ends another process.
- **An abort.** An aborted program ends by a user fault of the cause
  `Breakpoint`, as faulted, while the abort path of its runtime executes
  `BRK`, as that of the Rust standard library does on AArch64; the contract
  of the runtime of EL0 fixes the instruction (planned).
- **The cases.** The QEMU tests of [Testing obligations](#testing-obligations)
  end a process by each of these eleven faults, and each ends only that
  process, with this record, while the kernel sentinel stays unchanged and
  another process runs on:

| Case | Class | Cause | `EC` | Address |
| --- | --- | --- | --- | --- |
| A read of the guard of a stack | `DataAbort` | `DataTranslation` | `0x24` | The address read |
| A write of a kernel sentinel through the kernel's mapping | `DataAbort` | `DataPermission` | `0x24` | The address written |
| A branch to a page of the EL0 window that is not mapped | `InstructionAbort` | `InstructionTranslation` | `0x20` | The target of the branch |
| An execution of a data page | `InstructionAbort` | `InstructionPermission` | `0x20` | The address of the instruction |
| A branch to an address that is not a multiple of 4 | `PcAlignment` | `Alignment` | `0x22` | The target of the branch |
| `UDF` | `Unknown` | `Undefined` | `0x00` | None |
| A read of `PMCCNTR_EL0` | `TrappedAccess` | `TrappedAccess` | `0x18` | None |
| `BRK #0x76` | `Breakpoint` | `Breakpoint` | `0x3c` | None |
| An FP/SIMD instruction after a test image has cleared `CPACR_EL1.FPEN` for the thread, which only a test image can cause | `Other` | `Other` | `0x07` | None |
| A load through a stack pointer that is not a multiple of 16 | `SpAlignment` | `Alignment` | `0x26` | None |
| `HVC` at EL0, which the processor treats as undefined there | `Unknown` | `Undefined` | `0x00` | None |

## Kill

**The call.** `kill(process)` looks up `process` for the kind process with
CONTROL, and then, by the state of the target:

1. the root: the halt of the system ([The root](#the-root));
2. Alive: phase 0 of its destruction with the reason Killed, then its
   death notifications; the call ends with `Again`, or, when the target is
   the caller's own process, without a result, since the caller's thread
   has been removed;
3. Dying: `destroy_step(target)`, one step of its destruction, after which
   the call ends with `Again`, or with its result when the step made the
   target dead;
4. Dead: the result at once, without a write, so a kill of a dead process
   succeeds and changes nothing.

- **Execution again.** A call that ends with `Again` stops at a preemption
  point and writes no result. The dispatch of the core executes it again
  from the saved user registers, at once or, when an interrupt is pending,
  once the thread runs again
  ([execution again](../../memory/address-space/contract.md#kernel-stacks-and-blocking)).
  The call repeats its checks and continues from the progress of the
  target, so a kill runs from its first call until the target is dead,
  one step for each execution. A kill whose target another caller has made
  dead and its owner has reaped in between fails its lookup with
  `StaleReference`, as every later call does.
- **The thread of the target.** Phase 0 takes the thread of the target out
  of its wait and out of scheduling, by its state; the five states of a
  target that another process kills, and the end of the current thread:

| State of the thread | Part of phase 0 |
| --- | --- |
| Ready, among them a thread in a busy loop, which the kill caller preempted | `scheduler::remove` of a ready thread, out of its run queue |
| Blocked in a `receive` | `ipc::settle` with `Cancelled`, then `scheduler::remove` of the blocked thread |
| Blocked in a `call`, queued or delivered with its context lent | `ipc::settle` with `Cancelled`, which withdraws the loans of the chain of the call, at most 11 items, so that the context returns whole to its owner, then `scheduler::remove` |
| Blocked on a notification, in a wait set or in a sleep with a deadline, or paused by a revocation | `waits::cancel`, which also clears a pause, then `scheduler::remove` |
| The current thread: its own exit or fault, or a kill of the caller's own process | `scheduler::remove` of the current thread, which charges its dispatch |

- **The outcome of the wait.** A wait that the kill ends has the outcome
  `Cancelled`, which no thread observes: the killed thread never runs
  again, and a later reply of the server of its call fails with
  `ReplyGone`, as the
  [settlement of a call](../../ipc-waits/ipc/contract.md#settlement-of-a-call)
  states. A signal of the notification on which it waited finds no waiter
  and leaves its bits in the word; a wait that a completion ended before
  the kill keeps its result; and a wait whose deadline passes in the
  transition of the kill has settled with `Timeout` before the kill, which
  then finds its thread ready
  ([cancellation](../../ipc-waits/waits/contract.md#cancellation)).
- **The server of the killed caller.** When the thread of the target is
  the caller of a call that the kill caller serves on its context, the
  settlement withdraws the loan that the current dispatch uses, and the
  requeue of the kill caller charges that dispatch up to the time of the
  transition, within the 11 items of the withdrawal
  ([lending](../../scheduling/budget-ledger/contract.md#lending)).
- **No CONTROL.** A capability without CONTROL fails the lookup with
  `PermissionDenied` of the capabilities component, and the kill changes
  nothing; OBSERVE alone queries the process but does not kill it.
- **The caller's own process.** A kill of the caller's own process, and a
  step of a kill that reaches the caller's own process as a descendant of
  the target ([Children](#children)), make phase 0 of that process with
  the reason Killed: the caller's thread is removed, and the call ends
  after that transaction, as an exit does. Later kills advance the rest. So
  the working process of a step of phases 1 to 8 is never the caller's own
  process, and the address space whose ASID phase 6 releases is never the
  one that the executing CPU runs.
- **Counterexample.** Were a kill of the caller's own process to continue
  past phase 0, its phase 6 would release the ASID and reset the tables of
  the address space in `TTBR0_EL1` of the executing CPU, which the
  [release of an ASID](../../memory/address-space/contract.md#address-spaces-and-asids)
  forbids.

## Destruction

A destruction starts with phase 0, in the transaction that leaves Alive,
and goes on through phases 1 to 8 in this order, each phase in steps.
Phase 0 is made by the exit, the fault, the kill or the step of the
destruction of the owner that ends the alive process; phases 1 to 8 are
advanced only by kills, one step for each execution of a call of `kill`,
and their work is charged to the thread that calls `kill`. The kernel does
no work in the background.

| Phase | What a step does | Write set of a transaction | Steps |
| ---: | --- | --- | --- |
| 0 | Leaves Alive: writes the state Dying, the reason, the code or the fault record, clears the registrations and sets the progress to phase 1; takes the thread out of its wait and out of scheduling as [Kill](#kill) states. Then, in the same transition, the death notifications ([Death notifications](#death-notifications)) | At most 16: the process slot, and at most 15 for the thread, the most being `ipc::settle` of a delivered call, without `scheduler::enqueue`, with `scheduler::remove`, whose thread slot is among them; at most 4 for the current thread. Each death notification at most 13 | One transaction, and at most `WATCH_SLOTS` death notifications |
| 1 | The device grants: the steps that the device-authority rules of the devices and DMA domain give for the device grants that the process uses, its MMIO windows, the interrupts bound to its notifications and the DMA that it may start, which those rules drain (planned). A process that uses no device grant passes the phase in one step | At most $W$, as those rules count; 1, the process slot, for the step that ends the phase | As those rules give, at least 1 |
| 2 | The endpoints that the process owns. From the cursor, the step examines at most `SCAN_BATCH` slots of the endpoint pool in ascending order. At the first endpoint that the process owns, it makes one `ipc::drain_step`; when that gives `drained`, the step calls `waits::drain` with the endpoint and its bound thread until it gives none and then releases the endpoint, in the same transition and without a preemption point between them. A step that finds no such endpoint moves the cursor | At most 18 for a drain step: the settlement, at most 17, and the process slot with the cursor; at most 13 for each `waits::drain` with `scheduler::enqueue`; 3 for the release: the endpoint slot, the counts of its pool and the process slot, with the credit of one endpoint and the cursor | $\lceil e / \mathtt{SCAN\_BATCH} \rceil$ for the scan, $e$ being the capacity of the endpoint pool, and, for each endpoint that it owns, at most the thread capacity drain steps and one step of its release |
| 3 | The endpoints that other processes own and whose bound thread is the thread of the process: the same scan, and for each, `ipc::drain_step` until it gives `drained`, one for each step, without `waits::drain` and without a release, since the bound thread is the removed thread and the endpoint stays its owner's | At most 18: the settlement and the process slot | $\lceil e / \mathtt{SCAN\_BATCH} \rceil$, and at most the thread capacity drain steps for each such endpoint |
| 4 | The notifications that the process owns: the same scan of the notification pool. At the first that the process owns, the step calls `waits::drain` until it gives none and releases the notification, in the same transition and without a preemption point between them | At most 13 for each `waits::drain` with `scheduler::enqueue`; 3 for the release; 1 for a step that only moves the cursor | $\lceil n / \mathtt{SCAN\_BATCH} \rceil$, $n$ being the capacity of the notification pool, and one for each notification that it owns |
| 5 | The capability table: one `Tables::teardown_step` from the progress `next`, with `ipc::reply_deleted` for the live reply capability that it deletes; or, when the step meets the target of a pending revocation, one step of that revocation with `waits::unpause` and `scheduler::enqueue` for the pauses that it ends ([teardown](../capabilities/contract.md#teardown-of-a-table)) | At most 54: 37 of the teardown, with the process slot and its progress, and 17 of one `reply_deleted`; or at most 46: 37 of a step of a revocation and 9 for the end of its pauses | $\lceil \mathtt{capability\_slots} / 4 \rceil$, and one more for each step of a pending revocation that the teardown meets |
| 6a | The ASID: the step finds the address space of the process loaded on no CPU, takes the release plan with `Asids::release_plan` and gives it; at its `acknowledge`, the step ends | 1: the process slot, with the sub-step and the plan given | 1 |
| 6b | The lower tables: `Tables::reset` of the table set of the segment of the process, whose plan holds one `Zero` for each table in use, at most 32; at its `acknowledge`, the step ends | 1: the process slot | 1 |
| 6c | The frames: one `vm::revoke_step` of the process, which gives at most `RELEASE_BATCH` zero plans of frames of its committed chain, each acknowledged by `vm::acknowledge` | 1 for the step, the VM head of the process; 2 for each `acknowledge` of a zero plan, the process slot and the VM head; 2 for the step that completes the revocation, the VM head and the process slot with the next sub-step | $\lceil m / 64 \rceil + 1$, $m$ being the frames that the process holds, committed and loaded |
| 6d | The release: `Asids::release` with the release plan, which `release_plan` gives again, and the record `Space` of the process cleared; the segment of the table pool then serves the next process of the slot | 1: the process slot | 1 |
| 7 | The children: one step of the destruction of the working process below the process, or the reap of a dead child ([Children](#children)) | That of the step of the working process; at most 7 for the reap of a dead child by its dying owner | The steps of the destructions of all descendants, and one reap for each of them |
| 8 | Dead: the step that finds the chain of children empty writes the state Dead | 1: the process slot | 1 |

- **Order.** The objects of the process other than processes go first, by
  kind and then in ascending order of their slots, and its children after
  them, as the
  [process lifetime](../../../architecture.md#kernel-objects-and-capabilities)
  states. Phase 0 kills the thread before the teardown of the table, as
  the waits and IPC components require of the composition
  ([revocation and release](../../ipc-waits/waits/contract.md#revocation-and-release)).
  The device grants have a phase of their own before the teardown: a step
  of the teardown with a reply uses 54 items of $W$ = 64, so their drains
  are not bounded by the 10 that remain. The drains that a step of a
  revocation carries for a device grant stay within the 18 items that the
  [waits](../../ipc-waits/waits/contract.md#revocation-and-release)
  contract leaves for them. The reclamation of the address space comes
  after the removal of the thread, and its four sub-steps are in the order
  of the address-space and VM components: the invalidation of the ASID, the
  reset of the tables, the revocation of the frames, and the release of
  the ASID and of the segment
  ([revocation at process destruction](../../memory/vm/contract.md#revocation-at-process-destruction)).
  The release of a region and the destruction of a process share the two
  phases of the VM component: from phase 0 no operation of the process
  reaches its regions, and the invalidation of its ASID acknowledges every
  one of its pages at once, so the revocation unmaps no page and reads no
  table. A frame returns to the pool only after the reset that removed the
  entry that mapped it, so a frame has at most one mapping and every page
  one holder during the destruction as well.
- **Progress.** The progress of a process, `lifecycle::Progress`
  (planned), holds its phase; for phases 2, 3 and 4, the cursor, the next
  slot of the pool to examine, which starts at 0 in each of them; for phase
  5, `next`, the next slot of its table, which starts at 0; and for phase
  6, the sub-step, 6a to 6d, with whether its plan has been given. Phase 7
  needs no field of its own: the child that it works on is the first child
  of the chain.
- **Loaded on no CPU.** The step of 6a finds the address space of the
  working process loaded on no CPU: its thread was removed at phase 0, a
  CPU holds the address space of the process of its current thread, and
  the working process is never the caller's own process ([Kill](#kill)).
  With one CPU, the CPU record of the address space holds at most the
  executing CPU, whose `TTBR0_EL1` holds the address space of the caller.
- **Preemption points.** A step, with its plans and the transactions of its
  drains and death notifications, runs in one transition. Between two
  steps is a preemption point, and only there: the progress is in the
  process slot of the working process, and in the objects that the
  components of the step keep, the queue and the receiver of an endpoint,
  the table and the committed chain.
- **Plans.** A step fixes in its checks the plan that it gives and gives it
  after its write-back: the release plan of 6a, which
  `krepi_arch::el0::invalidate_asid` executes; the write plan of the reset
  of 6b, which `krepi_arch::mmu::apply` executes; and the zero plans of 6c.
  No plan fails
  ([write plans](../../memory/page-tables/contract.md#write-plans-and-publication)),
  so a step has no error after its first plan. One plan is executed before
  the next is given, and no other entry runs on the tables, the VM head or
  the ASID of the working process in between.
- **Acknowledgement.** `acknowledge(target)` records that the plan in
  flight of the working process below `target`, which it finds as the
  descent of [Children](#children) does, has been executed, and gives the
  next step: after the release plan of 6a and after the reset plan of 6b,
  the end of the step, `Again`, with the next sub-step in the progress;
  after a zero plan of 6c, what `vm::acknowledge` of the working process
  gives, its next zero plan or the end of the step. The step of 6c that
  finds the committed chain empty completes the revocation, and the
  progress becomes 6d in its write set. With no plan in flight,
  `acknowledge` is `InvalidState`, a call that no composer makes, which
  changes nothing.
- **Within W.** Every transaction of a destruction stays within $W$ = 64
  items of the objects contract; the largest, 54, is a step of the teardown
  that deletes the live reply capability.

**While a process is dying.** Phases 1 to 7 advance only by kills, so until
its owner or another holder of CONTROL kills a process that exited or
faulted:

- a new call to an endpoint that it owns, or whose bound thread is its
  thread, ends at once with `PeerClosed`, since the endpoint is not served
  ([bound thread](../../ipc-waits/ipc/contract.md#bound-thread)); but the
  calls queued on those endpoints and the call that its thread served stay
  until phases 2, 3 and 5, with the contexts that their callers lent, and
  a caller without a deadline waits until then;
- the waits of threads of other processes on its notifications end, with
  `PeerClosed` or a removed source, only at phase 4;
- the device grants that it uses, its MMIO windows, interrupts and DMA,
  are drained only at phase 1;
- its pages, objects, capability slots and limits return only through its
  phases and its reap;
- its children keep running until phase 7 reaches them.

## Children

- **The chain.** `init` links a new child at the end of the chain of its
  owner: the child's `previous_sibling` is the former `last_child` of the
  owner, whose `next_sibling` and the owner's `last_child` become the
  child, and the owner's `first_child` too when the chain was empty. Slots
  are chosen lowest free first, so the order of the slots is not the order
  of creation, and the chain keeps the latter. The reap of a child unlinks
  it, in its write set. The fields are this page's; the creation component
  calls `init` in its write set, and the reap of this page writes the rest.
- **Phase 7.** A step of phase 7 of a process P descends from P: while the
  process reached is dying in phase 7 and has a child, the step takes its
  first child, which is the earliest of its children that is not reaped.
  At the process C where the descent stops:
  - C alive: phase 0 of C, with the reason Killed, and its death
    notifications;
  - C dying in a phase from 1 to 6: the next step of the destruction of C,
    C being the working process;
  - C dying in phase 7 without a child, P itself among them: the step of
    phase 8, which makes C dead;
  - C dead: the reap of C by its owner, the process before C on the path,
    as `reap` does without its lookup and without the check of the owner.
- **Bound.** The descent reads at most one process slot for each level of
  the process tree, at most the process capacity, and writes nothing; it
  ends since a chain holds only processes that are not reaped and every
  process has a finite set of descendants.
- **Order.** So the descendants of a process are destroyed children before
  their parents and siblings in the order of their creation, the order of
  cascading revocation
  ([internal choices](../../../security.md#internal-choices)), and each
  dying process reaps its own children.
- **The reason.** A process that the destruction of its owner reaches is
  killed, with the reason Killed. One that had left Alive before, by its
  own exit or fault, keeps that reason: the first to arrive decides.
- **The caller.** When the descent of a step of a kill reaches the caller's
  own process, the step is its phase 0, and the call ends there
  ([Kill](#kill)).
- **Other kills.** A holder of CONTROL on a descendant may kill it while an
  ancestor is in phase 7: its steps advance the same progress, which the
  next step of the ancestor finds advanced.
- **Limits.** The reap of a child by its dying owner merges the limits of
  the child into the owner, as every reap does, and the reap of the owner
  merges them further into its own owner
  ([returning limits](../objects/contract.md#metadata-quotas)).

## Reaping

**The call.** `reap(process)` looks up `process` for the kind process with
CONTROL, and then checks, in this order: the caller's process is the owner
of the target (`NotOwner`); the target is dead (`InvalidState`). A
non-owner gets `NotOwner` whatever the state of the target, so the reap
tells a holder of CONTROL without OBSERVE nothing about the state of a
process that it does not own.

- **The gate.** The reap succeeds only for a dead process: its thread has
  been removed and is the current thread of no CPU; its ASID has been
  released in its three steps and its segment of the table pool reset;
  the endpoints and notifications that it owned have been released and the
  endpoints bound to its thread drained; its capability table is torn
  down; the device grants that it used are drained; its children are
  reaped; its thread holds no borrowed context; and its usages of the five
  split items, child processes, endpoints, notifications, committed VM pages
  and private pages of loaded images, are 0, with its capability slots.
  Dead is the gate: no count of capabilities, no thread reference and no
  binding holds back the reap
  ([capability counts](../capabilities/contract.md#capability-counts),
  [binding](../../ipc-waits/ipc/contract.md#release-and-peer-closure)).
- **The effect.** In one write set: `ObjectTable::release` of the process
  slot and of the thread slot; `QuotaRecord::merge` of the limits of the
  five split items into the owner and `credit` of one child process to the
  owner; `ledger::release` of the holdings of the thread to the thread of
  the owner, after `scheduler::requeue` of the current thread when the
  record of the owner is the owner of the context of the current dispatch
  ([admission and release](../../scheduling/budget-ledger/contract.md#admission-and-release));
  and the unlinking from the chain of the owner.
- **Write set.** At most 10 items: the process slot and the thread slot of
  the target and the counts of their two pools; the process slot of the
  owner, with its quota record and the ends of its chain; the thread slot
  of the owner; the scheduler record and the class ledger of the requeue;
  and the process slots of the previous and the next sibling. The reap of a
  dead child by its dying owner in phase 7 has no requeue, since the thread
  of the owner has been removed, and the child is the first of the chain:
  at most 7.
- **The owner's thread.** The owner of a process is its creator and never
  changes, and a process has one thread, so the thread of the owner is the
  thread that created the process, as `ledger::release` requires; the
  creation component states this as an invariant
  ([quotas and admission](../creation/contract.md#quotas-and-admission)).
- **After the reap.** The references to the process and to its thread are
  stale. The capabilities to them stay in their slots and fail every
  lookup with `StaleReference` until their holders close them, and the slot
  serves a new process at the next generation, which no old capability
  names.
- **The duties of the owner.** The owner of a child gets no registration
  at the creation: slot 0 of the registrations is kept for it, and it
  watches the child itself ([Death notifications](#death-notifications)).
  It holds a capability with CONTROL to the child until it reaps it: the
  kill needs CONTROL, and the reap needs CONTROL in the hands of the owner.
  On a death notification, the owner, such as the root, a job service or
  the process service of a POSIX environment, kills the child until it is
  dead and then reaps it; a process service does so within its own wait for
  a POSIX process, before it reports the exit status to the parent.
- **Neglect.** When the owner closes its last capability with CONTROL to a
  child, the capabilities derived from it stay in place
  ([close](../capabilities/contract.md#close)), and another holder of
  CONTROL may kill the child, but none may reap it: until a capability with
  CONTROL reaches the owner again, the child is reclaimed only when the
  destruction of the owner reaches it in phase 7. The root is never
  destroyed ([The root](#the-root)), so a child of the root whose CONTROL
  the root no longer holds is never reclaimed.

## Queries and CPU time

**The call.** `query(process, selector)` checks the form of `selector`, 0
or 1 (`InvalidSelector`), and then looks up `process` for the kind process
with OBSERVE; a capability to a thread fails with `WrongType`, since no
operation of release 0.1 queries a thread. It writes nothing, and its
results are values of `lifecycle::Status` (planned):

| Selector | Result | Value |
| ---: | --- | --- |
| 0 | `state` | 0 Alive, 1 Dying, 2 Dead |
| 0 | `reason` | 0 none, 1 Exited, 2 Killed, 3 Faulted |
| 0 | `code` | The exit code for Exited, otherwise 0 |
| 0 | `cpu` | The CPU time of the thread of the process, in ticks of the virtual counter |
| 1 | `cause` | The value of the cause class of the fault record, 1 to 9, or 0 |
| 1 | `flags` | Bit 0 set when the record holds the bits of `EC`, bit 1 set when it holds an address; the other bits 0 |
| 1 | `ec` | The bits of `EC` of the record, or 0 |
| 1 | `address` | The user virtual address of the record, or 0 |

- **No fault.** For a process whose reason is not Faulted, the selector 1
  gives the fixed empty record: all four results 0.
- **CPU time.** `cpu` is `ledger::cpu_time` of the thread of the process:
  every interval that the scheduler has charged for it, on its own context
  and on borrowed ones
  ([CPU time](../../scheduling/budget-ledger/contract.md#cpu-time)). It
  stops growing when the thread is removed. Scheduling decides it, and the
  security model leaves it out of the output sources
  ([observable outputs](../../../security.md#observable-outputs)).
- **Until the reap.** The state, the reason, the code and the fault record
  stay readable from the transaction that leaves Alive until the reap;
  after it, the query fails its lookup with `StaleReference`. The record
  of the exit of a reaped process belongs to the service that reaped it,
  such as the process service of a POSIX environment
  ([orphans, zombies and waits](../../../architecture.md#processes-posix-and-linux-compatibility)).
- **Rights.** Both selectors need OBSERVE, and only OBSERVE: CONTROL alone
  kills a process but does not query it.

## Death notifications

**The call.** `watch(process, notification, bits)` checks the form of
`bits`, not 0 (`InvalidBits` of the
[waits](../../ipc-waits/waits/contract.md#notifications) component), and
then looks up `process` for the kind process with OBSERVE and
`notification` for the kind notification with SIGNAL; when both lookups
fail, the error of the earlier place in the order of errors decides, and
at the same place that of `process`. Then:

- when the target has left Alive, the call signals the notification with
  `bits` at once, as a death notification, and registers nothing;
- when a registration of the target already holds the notification, the
  call ORs `bits` into it and takes no other slot;
- otherwise it writes the registration into a free slot: slot 0 when the
  caller's process is the owner of the target and slot 0 is free; else the
  lowest free slot of slots 1 to `WATCH_SLOTS` - 1; with no such slot, the
  call fails with `WatchCapacity`.

A slot is free when it holds no registration or when the reference of its
notification is no longer live. `WATCH_SLOTS` is 4,
`lifecycle::WATCH_SLOTS` (planned). Slot 0 is kept for the owner: other
observers share slots 1 to 3, so observers that fill them cannot keep the
owner from its death notification. No operation removes a registration:
it ends with the death of its target, or lapses when its notification is
released.

- **Rights.** The kernel signals the notification for the observer, so
  `watch` needs SIGNAL on it: a holder of WAIT alone cannot make the kernel
  signal a notification, as no holder of WAIT alone can signal it
  ([notifications](../../ipc-waits/waits/contract.md#notifications)). It
  needs OBSERVE on the process, which authorizes the subscription to the
  death notification ([rights](../capabilities/contract.md#rights)).
- **The signals.** The death notifications of a process are signals of the
  waits component with the reference of the notification
  (`waits::signal`), each followed by `scheduler::enqueue` for the thread
  that it completes, in a transaction of its own: at most 11 items of the
  signal and 2 more of the enqueue. They have no fault-injection point and
  no failure that a contract allows, like the settlements of the IPC
  component, so none is lost after the transaction that cleared the
  registrations.

The death notification follows five rules, one for each case of the tests
of [Testing obligations](#testing-obligations):

1. **Once.** In the transition that makes a process leave Alive, after the
   transaction of phase 0, which clears the registrations, each
   registration whose notification is live is signalled once, in the order
   of the slots, and none again, since none remains; a later kill, step or
   reap signals nothing. The notification is an ordinary notification, so
   it may also be registered as a source of a wait set, which reports it
   ready ([wait sets](../../ipc-waits/waits/contract.md#wait-sets)).
2. **Late watch.** A watch of a process that has left Alive, dying or
   dead, signals the notification at once.
3. **The observer first.** A registration holds the reference of its
   notification with its generation. When the notification is released
   before the death, with the destruction of its owner or at its last
   capability, the reference goes stale and the registration lapses: the
   death signals nothing to a notification that took its slot, and leaves
   no record behind.
4. **One winner.** When an exit and a kill compete, the first transaction
   that leaves Alive writes the reason and makes the only death
   notification; the later one finds the process not alive
   ([States and exit reasons](#states-and-exit-reasons)).
5. **Kept until the reap.** The reason, the code and the fault record stay
   readable by `query` until the reap
   ([Queries and CPU time](#queries-and-cpu-time)).

- **Capacity.** `WatchCapacity` depends on the registrations of other
  observers, so it is an error of shared capacity, which the security
  model leaves out of the output sources, and not one of object state or of
  the caller's quota
  ([information-flow boundary](../../../security.md#information-flow-boundary)).
- **The root.** A registration on the root is never signalled: the end of
  the root halts the system ([The root](#the-root)).

## The root

- **Halt.** The root leaving Alive in any way, its exit, a user fault of
  its thread, a kill by its own thread or a kill by another process that
  holds CONTROL on it, halts the system. The entry checks what precedes the
  state in its order of errors, makes no write and gives `Halt`; the
  dispatch of the core returns the halt as the result of the transition,
  and `el0_dispatch` takes the fatal path of the
  [boot](../../boot-platform/boot/contract.md#records) component, as for an
  exception at EL1: it writes the record of the end of the root to the
  serial console with `CASXI_HALTED`, and halts with
  `krepi_arch::cpu::halt`. The record of the end of the root belongs to the
  boot component (planned), and the serial diagnostics are not an output.
- **No destruction.** The root is not destroyed and never reaped, so its
  private allocation of the page ownership table, `OWNER_ROOT_PAGES`, is
  never released, and its own death notification is never signalled.
- **The power to halt.** Whoever holds a capability with CONTROL on the
  root's process holds the power to halt the system. The root may derive
  that capability for another process; whether it does is a choice of its
  service topology.

## Errors

| Error | Rule broken | Entries | Place in the order of errors |
| --- | --- | --- | --- |
| `InvalidExitCode` | An exit code above $2^{32} - 1$ | `exit` | The form of the register arguments |
| `InvalidSelector` | A selector other than 0 and 1 | `query` | The form of the register arguments |
| `InvalidBits` of the waits component | Bits of 0 | `watch` | The form of the register arguments |
| `InvalidHandle`, `NoCapability`, `StaleHandle` and `WrongType` of the capabilities component | A handle that does not name a usable capability of the kind in the caller's table: a process for `kill`, `query`, `reap` and the first handle of `watch`, a notification for its second | `kill`, `query`, `reap`, `watch` | Handle resolution: the range, the empty slot, the generation, the type |
| `StaleReference` of the objects component | A capability whose process has been reaped, or whose notification has been released; a reference that a composer passes and that is not live, a call that no composer makes | `kill`, `query`, `reap`, `watch`; `destroy_step`, `acknowledge` | Handle resolution: the liveness of the object |
| `WrongPool` of the objects component | A reference of another pool than the process pool, a call that no composer makes | `destroy_step`, `acknowledge` | Handle resolution: the type |
| `PermissionDenied` of the capabilities component | A capability to a process without CONTROL for `kill` and `reap`, or without OBSERVE for `query` and `watch`; a capability to a notification without SIGNAL for `watch` | `kill`, `query`, `reap`, `watch` | Rights |
| `RevocationPending` and `TransferPending` of the capabilities component | A capability of the subtree of a pending revocation or its target, or the source of a pending move | `kill`, `query`, `reap`, `watch` | Object state: the state of the entry |
| `NotOwner` | A reap by a process that is not the owner of its target | `reap` | Object state, after those of the lookup |
| `InvalidState` | A reap of a process that is not dead; a call that no composer makes: `destroy_step` of a process that is not dying or whose step has a plan in flight, and `acknowledge` with no plan in flight | `reap`, `destroy_step`, `acknowledge` | Object state, after `NotOwner` |
| `WatchCapacity` | A registration for which the target has no free slot | `watch` | Shared capacity |

- **Order.** Each entry checks in the order of its rule section and returns
  the first error. The places of the last column are those of the order of
  errors of the [security model](../../../security.md#internal-choices),
  after the operation number and version and the reserved and unused
  registers, which the dispatch of the ABI checks: the form of the register
  arguments; handle resolution; rights; object state; shared capacity. The
  operations take all their arguments in registers, so the form of the exit
  code, of the selector and of the bits precedes handle resolution. No error
  of this page is one of the caller's quota.
- **No change on failure.** No error changes state: an entry that returns
  an error leaves every field of the kernel state as it was, the copies in
  its write set included, gives no plan, signals nothing and writes no
  counter; a composing operation that meets an error discards its buffer,
  so the kernel state after any failed operation equals the state before
  it. There is no exception. The settlements before the operation in its
  transition are transactions of their own and stay. The result registers
  of a failed system call follow the
  [observable outputs](../../../security.md#observable-outputs) of the
  security model.
- **Outcomes and states are not errors.** The states, the exit reasons and
  the fault record are results of `query`; the outcome `Cancelled` of a
  killed wait, the outcome `PeerClosed` of the calls and waits that a drain
  ends, and the halt of the system are results of their operations, not
  errors. A kill of a dead process and a watch of a process that has left
  Alive succeed.
- **Totality.** `init`, `is_alive` and `fault` have no error: `is_alive`
  gives false for every reference that does not name an alive process,
  and `fault` of a process that is not alive changes nothing. The errors of
  references of `destroy_step` and `acknowledge`, and their `InvalidState`,
  answer calls that no composer makes; the answer changes nothing.
- **Names.** The names are those of this contract; the numeric values of
  the errors that reach EL0 belong to the ABI inventory. `NotOwner` is the
  refusal of an owner, not of a right: the entry holds CONTROL, so it is
  not `PermissionDenied` of the capabilities component, which names a right
  that an entry lacks; the ABI inventory maps it, with `InvalidExitCode`,
  `InvalidSelector` and `WatchCapacity`.

The prototype's join registry had seventeen errors; three errors of its
execution manager and two that the objects contract moved here concern
this page. The prototype's exit reasons, its states of processes and
threads, the outcomes of its joins and of its waits are states and
outcomes, not errors: `Terminated` is Killed here and `Fault` is Faulted,
and the `Terminated` outcome of a wait is `Cancelled`. Here:

| Prototype error | Here |
| --- | --- |
| `joins::InvalidConfiguration` | Not applicable: there is no registry to configure; the registrations are `WATCH_SLOTS` positions of each process slot |
| `joins::Object(_)` | Not kept as a wrapper: the errors of the objects and capabilities components that this page meets are returned as they are |
| `joins::WrongRegistry` | Not applicable: the kernel has one table of processes, and the registrations of a process are in its slot |
| `joins::StaleRecord` | Rewritten: `StaleReference` of the objects component, for a process that has been reaped; the record of its exit lives in its slot until the reap |
| `joins::StaleWait` | Not applicable: there is no join ticket; a death notification is a signal, and the waits on a notification are the waits component's |
| `joins::PermissionDenied` | Moved to the capabilities component: CONTROL, OBSERVE and SIGNAL are rights of entries, which the lookups check |
| `joins::RecordCapacity` | Rewritten: `WatchCapacity`, a registration for which the target has no free slot, an error of shared capacity |
| `joins::WaitCapacity` | Not applicable: a wait for a death is a wait on a notification, which takes no capacity of its own |
| `joins::GenerationExhausted` | Not applicable: a registration has no generation of its own, and process slots retire as the objects component states |
| `joins::DuplicateTarget` | Rewritten as a rule, not an error: a watch of a notification that a registration of the target holds ORs its bits into that registration |
| `joins::InvalidState` | Kept, for a reap of a process that is not dead and for the calls that no composer makes |
| `joins::AlreadyPublished` | Not applicable: the transaction that leaves Alive writes the reason, and nothing publishes it again |
| `joins::WaitInProgress` | Not applicable: a thread waits only by its own call while it runs |
| `joins::AlreadyCompleted` | Not applicable: a later completion of a wait has no effect, a rule of the waits component |
| `joins::SelfJoin` | Not applicable: joins belong to a later release |
| `joins::Cycle` | Not applicable: joins belong to a later release; a cycle of calls is refused by the IPC component |
| `joins::ClockReversed` | Not applicable: the time does not decrease within a boot, a premise that no entry checks |
| `execution::Stale` | Rewritten: `StaleReference` of the objects component |
| `execution::ReferencesOutstanding` | Not kept: Dead gates the reap, and no reference or resource count holds it back |
| `execution::InvalidState` | Merged into `InvalidState` above |
| `Busy` of the object pool, moved by the objects contract | Not kept: an entry runs to its end, the thread of a dying process is removed at phase 0, and no running execution holds back a reap |
| `ReferencesOutstanding` of the object pool, moved by the objects contract | Not kept, as `execution::ReferencesOutstanding` |

## Check and execute

Every write entry of this page makes all its checks before its first
write, then changes only the copies in the write set of its caller
([write-set transactions](../objects/contract.md#write-set-transactions)).
The items of this page are process slots, which hold the fields of
[States and exit reasons](#states-and-exit-reasons); the entries that it
composes add theirs, as their contracts list them. The ASID allocator, the
tables and the table pool, the metadata of the page pool and the bytes of
frames are no items of a write set: their writes are fixed by the checks
of a step and executed after its write-back, in a fixed order, as plans or
as writes that cannot fail
([check and execute](../../memory/vm/contract.md#check-and-execute)). The
write phase of an entry allows only `WriteSetFull` of `stage`, which the
write sets below never reach, and the fault-injection points of test
builds (`InjectedFault`), each of which discards the buffer and leaves the
state from before the transaction, with no plan given. The death
notifications, the transactions of `waits::drain`, the release of an
endpoint or a notification in a step of phase 2 or 4, and `acknowledge`
have no fault-injection point: the death notifications follow the
committed phase 0; the transactions of `waits::drain` are settlements of
a release, which have none in the
[waits](../../ipc-waits/waits/contract.md#check-and-execute) contract;
the release follows the drains of its step, which have committed; and
`acknowledge` follows a plan that has been executed.

| Entry | Checks before the first write | Write set | Writes after the write-back |
| --- | --- | --- | --- |
| `init` | None: its caller has just occupied the slot | At most 3: the process slot, the process slot of the owner and that of the former last child of the owner | Nothing |
| `is_alive`, `query` | `query`: the selector and the lookup | Nothing: read entries | Nothing |
| `exit` | The code; the root; the state | At most 5: the process slot; `scheduler::remove` of the current thread, its slot and the scheduler record, with the slot of the owner of its context and the class ledger of `ledger::charge` | The death notifications, each a transaction of at most 13 items |
| `fault` | The root; the state | At most 5, as `exit` | As `exit` |
| `kill`, phase 0 | The lookup; the root; the state; the state of the thread of the target | At most 16: the process slot, and at most 15 for the thread | As `exit` |
| `kill`, a later call | The lookup; the state | That of `destroy_step`, or nothing for a dead target | Those of `destroy_step` |
| `destroy_step` | The state and the progress of the target; the descent to the working process; the checks of the entries of the phase | That of the phase, at most 54 ([Destruction](#destruction)) | The plan of the step, if there is one; the transactions of `waits::drain` and the release of phase 2 or 4; the death notifications of a phase 0 in phase 7 |
| `acknowledge` | The descent; a plan in flight | At most 2: the process slot, and for a zero plan the VM head of the working process, the write set of `vm::acknowledge` | The next plan, if there is one |
| `reap` | The lookup; the owner; the state | At most 10 ([Reaping](#reaping)) | Nothing |
| `watch` | The bits; the two lookups; the state of the target; a free slot or the registration of the notification | 1: the process slot of the target; for a target that has left Alive, at most 13: the signal and its enqueue | Nothing |

- **Reads that decide the effect.** The state of the target, the state of
  its thread, the progress and the descent decide what an entry does, not
  whether it fails after its checks, and cannot fail.
- **Several transactions in a transition.** Phase 0 and each of its death
  notifications, each call of `waits::drain` and the release of a step of
  phase 2 or 4, and each step with the acknowledgements of its plans are
  transactions of their own. Of the transactions of a call, at most the
  first has a fault-injection point, and a failure there rolls it back to
  the state before it; the transactions after a committed phase 0, and the
  drains and the release of a step of phase 2 or 4, have none. So phase 0
  is never left without its death notifications, and a failed call leaves
  the state from before it.
- **Within W.** Every write set of this page, with those of the entries
  that it composes, is within $W$ = 64 of the objects contract; the largest
  is the 54 items of a step of phase 5.

## Work bounds

- `init` and `is_alive` take a fixed number of steps; `init` writes three
  slots at most, and `is_alive` resolves one reference.
- `exit` and `fault` check a fixed number of fields and make phase 0, a
  fixed number of writes with `scheduler::remove` and `ledger::charge` of
  the current thread, and then at most `WATCH_SLOTS` signals, each within
  the [work bounds](../../ipc-waits/waits/contract.md#work-bounds) of the
  waits component.
- `kill` makes one lookup, of at most 17 entries and one slot of the object
  table. Its phase 0 makes, by the state of the thread, one `waits::cancel`,
  one `ipc::settle` with at most `MAX_LOAN_DEPTH` = 8 withdrawals, or none,
  and one `scheduler::remove`, which walks at most one run queue, at most
  the thread capacity; then at most `WATCH_SLOTS` signals. A later call
  makes one `destroy_step`.
- `destroy_step` descends at most the depth of the process tree, at most
  the process capacity, and then makes one step: in phases 2 to 4, the
  examination of at most `SCAN_BATCH` slots and one drain step, or at most
  the thread capacity calls of `waits::drain` and one release; in phase 5,
  one step of the teardown, of at most `REVOKE_BATCH` = 4 slots, or of a
  revocation, within the bounds of the
  [capabilities](../capabilities/contract.md#work-bounds) component; in 6a,
  one `release_plan`; in 6b, one `reset`, whose plan zeroes at most 32
  tables; in 6c, one `revoke_step` of at most `RELEASE_BATCH` = 64 frames;
  in 6d, one `release`; in phase 7, the step of the working process or one
  reap; and the steps of phase 1 within the bounds of the device-authority
  rules.
- `acknowledge` descends at most the process capacity and makes one
  `vm::acknowledge` or a fixed number of writes, and gives at most one plan.
- `reap` makes one lookup and a fixed number of writes, with
  `ledger::release` and at most one `scheduler::requeue`.
- `query` makes one lookup and reads a fixed number of fields, with one
  `ledger::cpu_time`.
- `watch` makes two lookups, compares the notification with at most
  `WATCH_SLOTS` registrations and writes one, or makes one signal.
- **The long operation.** The destruction of a process is the only long
  operation of this page, and `kill` the only entry that advances it after
  phase 0. Its preemption points are between two steps, and its progress
  is in the process slot of the working process
  ([Destruction](#destruction)). A destruction of a process without
  descendants takes at most

  ```math
  s_1 + 2 \lceil e / S \rceil + (o_e + b)(t + 1)
  + \lceil n / S \rceil + o_n + \lceil c / 4 \rceil + r
  + \lceil m / 64 \rceil + 5
  ```

  steps after phase 0, $S$ being `SCAN_BATCH`, $s_1$ the steps of phase 1,
  $e$ and $n$ the capacities of the endpoint and notification pools, $o_e$
  and $o_n$ the endpoints and notifications that it owns, $b$ the
  endpoints that others own and whose bound thread is its thread, $t$ the
  thread capacity, $c$ = `capability_slots`, $r$ the steps of pending
  revocations that its teardown meets and $m$ the frames that it holds;
  the 5 are the steps of 6a, 6b and 6d, the last of 6c and that of phase
  8. Phase 7 adds the destructions of its descendants and one reap for
  each. The number of steps grows with what the process holds, while every
  step stays within its bound.
- **Without a preemption point.** Phase 0 with its death notifications,
  the release of one endpoint with at most the thread capacity calls of
  `waits::drain`, and the release of one notification in the same way, run
  in one transition each; their time grows with the thread capacity, as
  the drains of the waits component do.
- The constants are `WATCH_SLOTS` = 4; `SCAN_BATCH` = 64, which bounds the
  slots of a pool that a step examines; `RELEASE_BATCH` = 64 of the VM
  component; `REVOKE_BATCH` = 4 of the capabilities component;
  `MAX_LOAN_DEPTH` = 8 of the budget-ledger component; and $W$ = 64 of the
  objects contract.

## Determinism

- **Requests.** Requests that contend for a process slot take effect in the
  order in which they enter the kernel.
- **Exit reasons.** The first transaction that makes a process leave Alive
  decides its reason, its code and its fault record, the rule that the
  first cause to arrive decides why a process exits
  ([internal choices](../../../security.md#internal-choices)).
- **Order of destruction.** The objects of a process other than processes
  are destroyed by kind, in the order of the phases, and within a kind in
  ascending order of their slots; the children after them, each before its
  parent and siblings in the order of their creation, the order of the
  chain, the same shape as cascading revocation. The release of a pool
  slot, the chain and the generations follow from the slots and the history
  of the objects component.
- **Death notifications.** The registrations of a process are signalled in
  the order of their slots, once, in the transition that makes it leave
  Alive; a second watch with the same notification ORs its bits into the
  same registration. A new registration takes slot 0 for the owner when it
  is free, and otherwise the lowest free of slots 1 to 3; the slot of a
  registration is an internal identifier that no output carries.
- **Order of wake-ups.** A death notification completes the first waiter
  of its notification, as the waits component chooses, and the death
  notifications of one transition complete their waiters in the order of
  the slots; the composer calls `scheduler::enqueue` in that order.
- **Preemption.** Where a destruction stops at a preemption point depends
  on when an interrupt is pending, which the arrival of the timer
  interrupt, [ND-01](../../../security.md#nd-01), and of device interrupts,
  [ND-02](../../../security.md#nd-02), of the register of
  [permitted nondeterminism](../../../security.md#permitted-nondeterminism)
  decide; for each, the rules of this page fix the result, and the result
  of a kill does not depend on it.
- **Time.** The CPU time that `query` gives is the time that ND-01 allows,
  and the time of each transition is read once on entry.
- **Several CPUs.** With more than one CPU, the order in which CPUs take
  the token of the same process slot is the multicore interleaving of
  [ND-03](../../../security.md#nd-03); for each such order, the rules of
  this page fix the result.

The component leaves no other choice open.

## State fields

| Field | Class | Lock or owner | Linearization point | Publication |
| --- | --- | --- | --- | --- |
| The `state`, `reason`, `code` and `fault` of each process, in its process slot | Shared | The token of the process slot; with one CPU, the executing CPU | The write-back of the transaction that leaves Alive, of the step that makes the process dead, and of the reap that releases the slot | Under the token, by the release of the lock that provides it once CPUs share it |
| The `watches` of each process | Shared | The token of the process slot | The write-back of the `watch` that writes a registration, and of the transaction that leaves Alive, which clears them | Under the token |
| The `progress` of each process: its phase, cursor, `next` and sub-step with whether its plan has been given | Shared | The token of the process slot; a kill of the process or of an ancestor takes it for its step | The write-back of each step of the destruction | Under the token |

The chain of children, `first_child`, `last_child`, `previous_sibling`
and `next_sibling`, which `init` links in the write set of a creation and
the reap of this page unlinks, is classified with the staging record of a
creation in the [State fields](../creation/contract.md#state-fields) of the
creation contract; this page does not read the staging record. The process
slot, its owner and its quota record are fields of the
[objects](../objects/contract.md#state-fields) component; and the record
`Space`, the ASID allocator and the lower tables of a process those of the
[address-space](../../memory/address-space/contract.md#state-fields)
component.

## Testing obligations

- The host tests of the module `lifecycle` (planned) replay every vector of
  [Legacy test vectors](#legacy-test-vectors) whose entry is on this page,
  with its expected output, and the cases of the vectors of other pages
  that this page names, and write their results for the comparison with
  the specification
  ([host results](../../../formal-verification.md#host-results)).
- States and reasons: for each pair of causes among an exit, a fault, a
  kill and the destruction of the owner, in both orders, the first decides
  the reason, the code and the record, and the second changes nothing; a
  process leaves Alive once.
- Destruction: a property test with fixed seeds builds trees of processes
  that own endpoints, notifications, capabilities, committed and loaded
  frames and children, with calls queued on their endpoints and waits on
  their notifications, kills them in random orders with preemption points
  at random steps, and checks after every step, against an independent
  model of the phases: that the phases come in their order; that every
  write set is within $W$, with the counts of [Destruction](#destruction);
  that no frame returns before the reset and the invalidation, and no ASID
  before the revocation; that the working process is never the caller's
  own process; and that, at Dead, the gate of [Reaping](#reaping) holds,
  among them the usages of 0.
- Children: a tree of depth 3, killed from its root and from a middle
  process, destroys children before parents and siblings in the order of
  their creation, with slots out of that order; a child that exited before
  keeps Exited; a child that holds CONTROL on its owner and kills it ends
  its own call at its phase 0.
- Reaping: the counterexamples of the domain page, a reap by a holder
  without CONTROL (`PermissionDenied`), a reap by a holder of CONTROL that
  is not the owner (`NotOwner`), a reap of a process that is alive or dying
  (`InvalidState`), and an exit that competes with the destruction of the
  owner; conservation of the quota records after every reap, with the limits
  back in the owner; and an owner that closed its last capability with
  CONTROL, whose child another holder kills but cannot reap.
- Kill: one case for each of the five states of the target, a busy loop,
  a receive, a call with its context lent, a wait on a notification or a
  wait set, and a sleep with a deadline. Each checks with a sentinel page
  that EL0 no longer runs in the target, that the lent context returns
  whole, and that the wait ends with `Cancelled`. A kill of a dead process
  succeeds and changes nothing; a kill without CONTROL is
  `PermissionDenied` and changes nothing.
- Faults: the eleven cases of [Faults](#faults) on QEMU virt, each ending
  only its process, with the reason Faulted and the fault record that the
  table gives, while the kernel sentinel stays unchanged and another
  process runs on; and the host test of each cause through `fault`.
- Death notifications: one case for each of the five rules of
  [Death notifications](#death-notifications), the fourth a deterministic
  case of an exit and a kill in the same order every run; a full set of
  slots 1 to 3 with `WatchCapacity` for a fourth observer and the owner's
  registration in slot 0; and a registration whose notification is
  released before the death.
- Exit codes: the codes 0, 1, 2 and 255 reach an observer through `query`
  unchanged, and $2^{32}$ is `InvalidExitCode`.
- Peers: the calls queued on the endpoints of a process that exited end
  with `PeerClosed` once its owner kills it, and a new call ends at once
  with `PeerClosed` before that.
- Baseline: three rounds of creation, watch, exit, kill and reap, and of
  creation, kill and reap, return the counts of pages, endpoints,
  notifications, capabilities and ASIDs to their values before each round.
- The root: a QEMU test whose root exits, and one in which another process
  kills the root through a derived capability with CONTROL, each ending in
  the fatal path of the boot component with `CASXI_HALTED`.
- Each error of [Errors](#errors) through a call that gives it, compared
  field by field before and after; for each pair of consecutive checks of
  an operation whose errors differ, a call that breaks both and gets the
  error of the earlier; for each fault-injection point of the
  implementation, an operation that fails there leaves every field as
  before.
- The tests take their expected values from this page, from the vectors
  and from independent models, never from an earlier run of the code under
  test ([testing](../../../conventions/testing.md#independent-evidence)).

## Open obligations

The module `lifecycle` has no `unsafe` code, no assembly and no MMIO, and
its entries are to be covered by its targets. What each of the entries
below changes in the state of other components, through the entries of
those components that it composes, is an effect across components: the
forced kill of a process across its objects and its reclamation, with the
revocation of the frames of the VM component, the release of the ASID and
the reset of the tables. Each composed entry is covered by the targets of
its own component, and the composition by none; the rows below record it,
carried by the proof of object lifetimes, waits and sequential
composition, by release 0.2. The plans that the steps give are executed by
`krepi_arch::el0::invalidate_asid`, `krepi_arch::mmu::apply` and
`krepi_arch::frames::apply`, rows of the open obligations of the
[address-space](../../memory/address-space/contract.md#open-obligations),
[page-tables](../../memory/page-tables/contract.md#open-obligations) and
[VM](../../memory/vm/contract.md#open-obligations) contracts, and the
halt by the fatal path of the boot contract.

| Obligation | Kind | Verified state | Carrier | Stage |
| --- | --- | --- | --- | --- |
| `kernel/src/lifecycle.rs#exit` (planned) | `code` | Reads and writes (composes phase 0 of the caller's process with `scheduler::remove` and `ledger::charge`, and its death notifications with `waits::signal` and `scheduler::enqueue`) | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/src/lifecycle.rs#fault` (planned) | `code` | Reads and writes (composes phase 0 of the faulting process, as `exit`) | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/src/lifecycle.rs#kill` (planned) | `code` | Reads and writes (composes phase 0 of the target with `waits::cancel`, `ipc::settle`, `scheduler::remove`, `scheduler::requeue` and the death notifications, and the steps of `destroy_step`) | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/src/lifecycle.rs#destroy_step` (planned) | `code` | Reads and writes (composes the drains of `ipc::drain_step` and `waits::drain`, the releases of `ObjectTable::release`, `Tables::teardown_step` with `ipc::reply_deleted` and `waits::unpause`, `Asids::release_plan`, `Tables::reset`, `vm::revoke_step` and `Asids::release`, and the reap of a dead child, in the order of the phases) | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/src/lifecycle.rs#acknowledge` (planned) | `code` | Reads and writes (composes `vm::acknowledge` of the working process with the sub-steps of the reclamation of its address space) | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/src/lifecycle.rs#reap` (planned) | `code` | Reads and writes (composes `ObjectTable::release`, `QuotaRecord::merge` and `credit`, `ledger::release` and `scheduler::requeue`) | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/src/lifecycle.rs#watch` (planned) | `code` | Reads and writes (composes, for a target that has left Alive, `waits::signal` and `scheduler::enqueue`) | The proof of object lifetimes, waits and sequential composition | `0.2` |

## Legacy test vectors

The vectors are host tests of the prototype tree at
`prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`, 47 in all. Their
expected outputs are those that the test bodies assert, written in the
rules of this page. In the table of each file, the column Prototype gives
what the test body asserts of the prototype, and the column Expected output
gives the cases here, through the entries that its calls name in the
notation below. The vectors are not yet in a file of the repository, so
the section holds no `vectors` block.

| File | Vectors |
| --- | ---: |
| `src/execution/tests/lifecycle.rs` | 11 |
| `src/objects/joins/tests.rs` | 16 |
| `src/objects/joins/tests/failures.rs` | 13 |
| `src/objects/tests.rs` | 7 |

- These are all the tests of the first three files, and the seven tests
  of `src/objects/tests.rs` that the
  [objects](../objects/contract.md#legacy-test-vectors) contract leaves to
  this component: those of the lifetimes of processes and threads, exit,
  termination, quiescence and the gates of reclamation. Its other thirteen
  are frozen there.
- The id of a vector is the path of its file below `src/`, without the
  directory `objects` where another directory follows it, without the
  directories and files named `tests` and without `.rs`, with a hyphen
  between the parts and in place of each underscore, and the position of
  the test among the tests of its file, from 1. The objects contract gives
  the ids `objects-1` to `objects-13` to the other thirteen tests of
  `src/objects/tests.rs`; the seven of this page are `objects-lifecycle-1`
  to `objects-lifecycle-7`, in the order of the file.

A vector of this page is one test function. The vector file is to hold one
line for each case of a vector through an entry of this page, with the id
`<vector>.<n>`, `n` counting those cases from 1 in the order of the test; a
case that its row marks not applicable has no line, and a vector whose
Expected output has no case through an entry of this page has no line.

**The prototype.** The execution manager of
`src/execution/tests/lifecycle.rs` keeps one to three domains over a page
allocator of 64 pages from `0x1000`, each domain charging 6 pages for its
layout, two of tables, one of data, one of user stack and two of kernel
stack, and an object pool of 4 processes and 4 threads; its backend
records the events `zero`, `prepare`, `cancel`, `retire`, `invalidate` and
`scrub`, and can be made to fail. A domain is a process with one thread;
`begin` activates its thread, `finish` ends it by an exit or a fault,
`destroy` reclaims it. The join fixture of `src/objects/joins/tests.rs`
and its file `failures.rs` keeps an object pool of 2 processes and 8
threads with one process of three threads, the target, the waiter and a
third, and a registry of R records and W waits: `register` makes the exit
record of a live target, `begin` a join wait of a waiter on a record with
an optional deadline, `publish` copies the reason of the dead target into
its record, `release` ends a record, and `take`, `cancel` and `abandon`
take or end a wait; every timed call takes the time as an argument. The
tests of `src/objects/tests.rs` use object pools of one or two processes
with their threads.

**Correspondence.** A domain, and a target of the join fixture, is a child
P of the root R, with its thread; R holds a capability to P with every
right of a process, which its creation gave it, and is its owner. Another
process of a case, Q, is a child of R as well, and holds what the row
gives it. `finish` with an exit is the `exit` of P, and with a fault a user
fault of P's thread, of the cause `DataTranslation` unless the row says
otherwise, which the dispatch of the core reports with `fault`; `destroy`
is the kill of P by R, called again until its result, and the reap of P by
R; a termination of a process or of a thread is a kill. A record of a
target and a join wait of a waiter are R's `watch` of P with a
notification N that R owns, with the bits 1 unless the row says
otherwise, and R's `wait` on N, an operation of the
[waits](../../ipc-waits/waits/contract.md#notifications) component; the
publication of an exit is the death notification of P.

**Notation.** Times are decimal ticks of the virtual counter. "P exits with
c" is `exit(c)` by the thread of P; "R kills P" is `kill` by R through its
capability to P, called again until it gives its result; "R reaps P" is
`reap`. The output of a call is `ok`, followed by its results, or
`err=<error>`, with the errors of this page and of the components whose
entries the row names. "The query" of a process is `query` with the
selector 0 through R's capability to it, and its results are written
`state=<s> reason=<r> code=<c>` with the names of
[Queries and CPU time](#queries-and-cpu-time), its CPU time left out.
"Changes nothing" means that every field of the kernel state is as before.

**Behaviour changes.** The rules of
[Current deviations](#current-deviations) change these vectors:

- An exit or a fault makes the process dying, and a kill takes it to dead;
  the prototype's `finish` made it dead at once.
- No reference, count or resource obligation holds back a reap, and Dead
  is its gate: the prototype's refusals with `ReferencesOutstanding`,
  `Busy` and `CounterUnderflow` of its references do not apply.
- The record of an exit lives in the process until its reap: the
  prototype's join registry, its records, receipts, tickets and
  generations, the publication, the release of a record and the take of a
  join result do not exist, and a death notification is a signal of a
  notification, whose waits are the waits component's.
- A watch needs OBSERVE alone, and a watch of a dying process is delivered
  at once, where the prototype refused it.
- A killed wait ends with `Cancelled`, which its thread does not observe,
  where the prototype reported `Terminated`.
- The prototype's activation, quiescence, execution manager and backend,
  its several threads of a process, its joins with their cycles, and its
  time arguments, which could go backwards, have no counterpart: their
  cases have no line, and several threads of a process and joins come in
  release 0.2.

### `src/execution/tests/lifecycle.rs`

| Vector | Line | Test | Prototype | Expected output |
| --- | ---: | --- | --- | --- |
| `execution-lifecycle-1` | 4 | `exit_and_fault_are_terminal_and_reclaim_owned_resources` | For an exit with 17 and for a fault: after `begin`, 1 domain is active, the thread is Running and the process holds 1 CPU obligation; after `finish`, 0 domains are active, the process is Dead with 0 CPU obligations and the reason `Exited(17)` or `Fault`, and the thread is Dead; a further `begin` and `finish` are each `err=InvalidState`; after `destroy`, the usage of the manager is that of the start, with 0 processes and 0 threads | For P exits with 17 and for a user fault of P: query of P with the selector 0 gives `ok state=Dying reason=Exited code=17`, or `ok state=Dying reason=Faulted code=0`, and P's thread is removed and runs no more; R kills P, `ok`, after which the query gives `state=Dead` with the same reason and code; R reaps P, `ok`; the usages of R's quota record, the counts of the pools, the free frames of the page pool and the free ASIDs are then those before the creation of P. The further `begin` and `finish` have no case: a removed thread makes no call |
| `execution-lifecycle-2` | 55 | `active_domain_and_external_references_block_retirement_without_side_effects` | While the domain runs, `destroy` is `err=Busy`, with no change and no backend event; after `finish` with 0, `destroy` succeeds. With an external reference to the thread of a new domain, `destroy` is `err=ReferencesOutstanding`, with no change, the process Alive and no event; after the release of the reference, `destroy` succeeds | With a capability to P's thread in the table of Q, derived from R's: R kills P, `ok`, and R reaps P, `ok`; Q's capability then fails its lookups with `StaleReference`. The refusal of a running domain has no case: on one CPU the kill caller runs, so the thread of another process does not run during the kill, and a reference holds back no reap |
| `execution-lifecycle-3` | 90 | `every_external_resource_obligation_blocks_destroy_before_termination` | For each of a mapping, a CPU and a DMA obligation that an alive process retains, `destroy` is `err=ReferencesOutstanding`, with no change, the process Alive and no event; after the release of the obligation, `destroy` succeeds | P with 2 committed VM pages and its loaded private pages: R kills P, `ok`, its steps returning the frames in phase 6, and at Dead P's usages of committed VM pages and of private pages of loaded images are 0; R reaps P, `ok`. The obligation of a CPU is the thread, which phase 0 removes; that of DMA is a use of a device grant, drained in phase 1 by the device-authority rules, and has no case |
| `execution-lifecycle-4` | 113 | `failed_tlbi_retains_every_charge_and_retry_does_not_repeat_retirement` | With a failing invalidation, `destroy` is `err=Asid(InvalidationFailed)`, with no change of the snapshot, and the events are `retire` and `invalidate(1)`; the process is Dead with 1 mapping obligation; `begin` and the information of the domain are `err=InvalidState`, and a creation is `err=Capacity`; with a working invalidation, `destroy` succeeds, with the events `invalidate(1)` and four `scrub`; 0 allocations, 0 ASIDs and 0 processes remain | R kills P, and the release plan of P's ASID in 6a is held by the host test before its execution: P stays dying in 6a, its ASID held, its frames off the pool and its usages unchanged; after the execution of the plan and its `acknowledge`, the kill continues through the reset, the zero plans of P's frames and the release of the ASID, `ok`; R reaps P, `ok`, and the ASID is free. The failed invalidation has no case: the invalidation is a plan that does not fail, and the ASID is released only after it ([release of an ASID](../../memory/address-space/contract.md#address-spaces-and-asids)) |
| `execution-lifecycle-5` | 153 | `reuse_scrubs_all_regions_and_rejects_old_generation` | With the tables, the data, the user stack and the kernel stack of a domain filled with `0xdb`, after `destroy` they read 0; a new domain gets the same backing and ASID and another handle, with 5 backend events; the information, `begin` and `destroy` of the old handle are each `err=Stale`, with no event | P with its committed pages filled with `0xdb`: R kills and reaps P; R's next child P2 takes P's process slot, P's ASID and P's segment of the table pool, and its committed pages read 0; R's capability to P then gives `err=StaleReference` for `query`, `kill` and `reap`, each changing nothing. The kernel stack and the events of the backend have no case: a kernel stack belongs to a CPU, and the frames come zero from the page pool |
| `execution-lifecycle-6` | 188 | `wrong_pool_foreign_manager_and_attenuated_handles_cannot_reach_backend` | `destroy` through another object pool is `err=Object(WrongPool)`; with the process or the thread handle restricted to observation, `destroy` is `err=Stale`; `destroy` by a foreign manager is `err=Stale`; no backend event | Q, holding a capability to P derived from R's with OBSERVE alone: Q's kill of P is `err=PermissionDenied` and changes nothing. Another pool and a foreign manager have no case: a handle names only the caller's own table, and the kernel has one table of objects |
| `execution-lifecycle-7` | 223 | `occupied_cpu_rolls_back_new_cpu_reference_and_finish_checks_exact_active_handle` | With another thread active, `begin` of the first domain is `err=Object(Busy)`, its CPU obligation stays 0 and no domain is active; after the quiescence of the other thread `begin` succeeds; `begin` of the second domain is `err=Busy`, and its `finish` with a fault `err=InvalidState`; the first thread is Running and the second Ready | No case: there is no activation and no `finish`; the scheduler chooses the thread that runs, and a process ends by the exit or a fault of its own thread, the current thread |
| `execution-lifecycle-8` | 263 | `active_execution_blocks_other_domain_mutations_without_backend_calls` | While the first of two domains runs, a creation and the `destroy` of the second are each `err=Busy`, with no change of the snapshot or of the usage, the threads Running and Ready, the second process Alive and no event; after `finish` of the first, both are destroyed and the usage is that of the start | No case: an entry runs to its end, and no state of a running execution holds back another operation |
| `execution-lifecycle-9` | 304 | `a_fault_remains_distinct_from_later_termination_and_exit_requests` | After a fault, a termination of the process and an exit of its thread with 99, the reasons of the thread and of the process are `Fault`; `destroy` succeeds, and no domain remains | After a user fault of P, R kills P, `ok`, and the query gives `state=Dead reason=Faulted code=0`. The later exit has no case: P's thread was removed at the fault and makes no call |
| `execution-lifecycle-10` | 326 | `late_faults_preserve_prior_requested_termination_or_normal_exit` | After an exit with 42 and after a termination, a fault of the process leaves the reasons of the thread and of the process as before | After P exits with 42, and after the phase 0 of R's kill of P: `fault` of P, which only a host test calls for a process that is not alive, changes nothing, and the query gives `reason=Exited code=42` and `reason=Killed code=0` |
| `execution-lifecycle-11` | 349 | `process_fault_keeps_prior_thread_exit_and_waits_for_active_stack_quiescence` | In a process of three threads, of which the first has exited with 3, the second runs and the third waits: after a fault of the process, its reason is `Fault` and its state Dying; the first thread keeps `Exited(3)`; the second is Dying with `Fault`; the third has `Fault`, its wait is completed as `Terminated` and a later completion is `err=AlreadyCompleted`; after the quiescence of the second, the process is Dead | No case: a process has one thread in release 0.1, and several threads of a process come in release 0.2; for its one thread, the end of a wait by its kill is the waits component's cancellation |

### `src/objects/joins/tests.rs`

| Vector | Line | Test | Prototype | Expected output |
| --- | ---: | --- | --- | --- |
| `joins-1` | 14 | `publication_reads_the_actual_first_exit_after_quiescence` | With a record of the target and a wait of the waiter: the observation is none; `publish` at 1 is `err=InvalidState`; after the target is activated, exits with 37 and is terminated, `publish` at 1 is `err=InvalidState` and the time of the registry is 0; after its quiescence, `publish` at 1 gives `Exited(37)`, a second `publish` at 2 is `err=AlreadyPublished`, and the take of the wait gives `Exited(Exited(37))` | R watches P with N, `ok`, and waits on N, which blocks; P exits with 37: R's wait ends with the bits 1; R kills P, `ok`, and the query gives `state=Dead reason=Exited code=37`; R's next wait on N, with a deadline later than the kill, times out at that deadline, since the death notification is made once |
| `joins-2` | 42 | `exit_observation_and_late_join_survive_target_reap` | After the target exits with -9, the record is published at 2 and the target reaped: its handle is `err=StaleHandle`, the observation gives `Exited(-9)`, and a wait begun at 3 with the deadline 0 takes `Exited(Exited(-9))` at once; after the release of the record at 4, 0 records and 0 waits remain | P exits with `0xfffffff7`, the 32 bits of -9: the query gives `state=Dying reason=Exited code=0xfffffff7`; R kills and reaps P; then R's query and watch of P are each `err=StaleReference`. The record of an exit does not outlive the reap: the service that reaps a process reads it before |
| `joins-3` | 65 | `terminated_target_reports_its_stored_reason` | With a wait on the record of the target, a termination and then an exit with 8: `publish` gives `Terminated`, and the take of the wait `Exited(Terminated)` | R watches P with N and waits on N; R kills P: R's wait ends with the bits 1, and the query gives `reason=Killed code=0`. The later exit has no case: P's thread was removed at the kill |
| `joins-4` | 83 | `pending_wait_does_not_change_execution_metadata` | A wait with the deadline 10 begun at 0: its result is none, its take is `err=WaitInProgress`, the waiter is Ready, and the snapshot of the object pool is unchanged | R's watch of P, alive, writes only the registration in P's process slot: the query of P and the states of P's and R's threads are as before. The join wait and its take have no case |
| `joins-5` | 99 | `timeout_at_equality_wins_pending_exit_publication` | A wait with the deadline 10; the target exits with 3; `publish` at 10 gives `Exited(3)`; the take gives `TimedOut`; the observation gives `Exited(3)` | R watches P with N and waits on N with the deadline 10; P exits with 3 in a transition at 10: the expiry settles R's wait with `Timeout` first, and the bit of the death notification stays in N's word for R's next wait; the query gives `reason=Exited code=3` |
| `joins-6` | 114 | `publication_before_deadline_survives_later_timeout_and_close` | A wait with the deadline 10; the target exits with 3 and is published at 9; the advance to 10 completes 0 waits; the cancellation at 11 is `err=AlreadyCompleted`; the release at 11; the take gives `Exited(Exited(3))` | R watches P with N and waits on N with the deadline 10; P exits with 3 at 9: R's wait ends with the bits 1 at 9; the expiry at 10 and R's kill and reap of P at 11 leave that result as it is |
| `joins-7` | 131 | `cancellation_wins_before_exit_and_timeout` | A wait cancelled at 2 gives `Cancelled`; a later exit with 3 and a publication at 10 leave the take at `Cancelled` | No case: no operation cancels the wait of another thread in release 0.1 |
| `joins-8` | 143 | `timeout_wins_cancellation_and_release_at_equality` | Two waits with the deadline 10: the cancellation of the first at 10 gives `TimedOut`, the release of the record at 10 follows, and both takes give `TimedOut` | No case: no operation cancels the wait of another thread, and no operation releases a record |
| `joins-9` | 156 | `target_release_completes_all_waiters_without_losing_receipts` | Two waits, one with the deadline 10; the release of the record at 2: its observation is `err=StaleRecord`, 0 records and 2 completed waits remain, the cancellation of the first is `err=AlreadyCompleted`, and both takes give `PeerClosed` | No case: there is no record to release; the release of a notification is the waits component's |
| `joins-10` | 172 | `release_and_record_slot_reuse_do_not_alias_retained_waits` | A wait on the old record; the release of the old record at 1; a new record for another thread differs from the old; a release of the old record is `err=StaleRecord`; the observation of the new is none; the take of the wait gives `PeerClosed` | R watches P with N; P exits, and R's wait on N ends with the bits 1; R kills and reaps P, and creates P2, which takes P's process slot: P2 has no registration, R's capability to P gives `err=StaleReference` for `watch`, and the exit of P2 signals nothing to N |
| `joins-11` | 186 | `stale_wait_ticket_cannot_cancel_or_consume_a_later_join` | A wait with the deadline 1, expired and taken; a new wait differs from the old; the cancellation and the take of the old are each `err=StaleWait`; the result of the new is none | No case: there is no join ticket |
| `joins-12` | 201 | `waiter_death_abandonment_releases_completed_or_pending_receipts` | For a pending and for a cancelled wait, after the termination and the reap of the waiter: `abandon` gives true and then false; the result is `err=StaleWait`; 0 waits remain; the observation is none | Q, holding a capability to P with OBSERVE that R derived, watches P with its own notification M, `ok`; R kills and reaps Q, which releases M in phase 4 of Q; P then exits, and its death signals nothing, since the registration has lapsed, and leaves no record; the slot of that registration is free for a later watch |
| `joins-13` | 221 | `waiter_object_reuse_never_abandons_an_older_identity` | The waiter is terminated and reaped, and a replacement takes its thread slot; a wait of the replacement; the abandon of the old waiter; the result of the old wait is `err=StaleWait`, that of the new none | Q watches P with M; Q closes its last capability to M, which releases M, and a new notification M2 takes M's slot at the next generation; P exits, and its death signals nothing to M2 |
| `joins-14` | 238 | `bounded_cleanup_reuses_slots_without_retaining_any_waits` | 64 rounds, each a registration, a wait, a release and a take that gives `PeerClosed`; after each, 0 records and 0 waits | 64 rounds, each: R creates P, watches P with N, P exits, R's wait on N ends with the bits 1, R kills and reaps P; after each round the usages of R, the counts of the pools, the free frames and the free ASIDs are those before the first |
| `joins-15` | 252 | `earliest_deadline_tracks_only_pending_waits` | Two waits with the deadlines 20 and 10: the earliest deadline is 10; the advance to 10 completes 1; then 20; the second wait is `TimedOut`; after the cancellation of the first, there is no deadline | No case: the deadline table is the waits component's |
| `joins-16` | 267 | `immediate_deadline_does_not_install_a_dependency_edge` | A join with an expired deadline is `TimedOut` at once; a join in the other direction then stays pending | No case: joins and their edges come in release 0.2 |

### `src/objects/joins/tests/failures.rs`

| Vector | Line | Test | Prototype | Expected output |
| --- | ---: | --- | --- | --- |
| `joins-failures-1` | 4 | `configuration_rejects_zero_identity_or_capacity` | A registry with the identity 0, with no record and with no wait is each `err=InvalidConfiguration` | No case: there is no registry to configure |
| `joins-failures-2` | 20 | `registration_validates_actual_object_authority_and_liveness` | The registration of the target restricted to observation and to control is each `err=Object(PermissionDenied)`; through another pool `err=Object(WrongPool)`; after the termination of the target `err=InvalidState`; after its reap `err=Object(StaleHandle)`; 0 records | Q, holding capabilities to P derived from R's: Q's watch of P with CONTROL alone is `err=PermissionDenied`, and with OBSERVE alone `ok`, where the prototype required every right; Q's watch with a capability to N with WAIT alone is `err=PermissionDenied`; after the phase 0 of R's kill of P, Q's watch signals N at once, `ok`, where the prototype refused it; after R reaps P, `err=StaleReference`. The refusals change nothing. Another pool has no case |
| `joins-failures-3` | 45 | `observer_rights_allow_join_and_read_but_never_publication_or_release` | An observer record widened to every right is `err=PermissionDenied`; its `publish` and `release` are `err=PermissionDenied`; the observation of a controller record is `err=PermissionDenied`, and so is a wait on it; a wait on the observer record by a waiter with control succeeds | Q, holding a capability to P with OBSERVE alone and another with CONTROL alone, derived from R's: with OBSERVE, `query` and `watch` are `ok`, and `kill` and `reap` `err=PermissionDenied`; with CONTROL, `query` and `watch` are `err=PermissionDenied`, `reap` is `err=NotOwner`, and `kill` is `ok`; a derivation of every right from the capability with OBSERVE is `err=PermissionDenied` of the capabilities component |
| `joins-failures-4` | 75 | `waiter_registration_and_abandon_require_control` | A wait of a waiter restricted to observation is `err=Object(PermissionDenied)`, and its `abandon` `err=PermissionDenied`; a wait of an active, a waiting or a terminated waiter is `err=InvalidState` | No case: the waiter of a wait is the calling thread itself |
| `joins-failures-5` | 108 | `records_and_waits_reject_different_registry_identifiers` | On a second registry, the observation, release, cancellation and take of a record and wait of the first are each `err=WrongRegistry`; on the first, the result is none | No case: there is one table of processes |
| `joins-failures-6` | 123 | `duplicate_target_and_waiter_rights_aliases_do_not_bypass_identity_checks` | A second registration of the target is `err=DuplicateTarget`; a wait through an alias of the waiter while its wait is pending, and after its cancellation before its take, is `err=WaitInProgress`; after the take, a wait succeeds | R watches P with N and the bits 1, and again with N and the bits 2: both `ok`, and the second takes no slot; P exits, and its death signals N once with the bits 3. The waits through aliases have no case |
| `joins-failures-7` | 152 | `self_join_and_three_thread_cycles_are_rejected_atomically` | A self-join is `err=SelfJoin`; a cycle of three threads is `err=Cycle`, with no change | No case: joins come in release 0.2 |
| `joins-failures-8` | 170 | `expired_and_completed_edges_do_not_form_cycles` | An edge that timed out or was cancelled closes no cycle: the join in the other direction succeeds, and the first result is `TimedOut` or `Cancelled` | No case: joins come in release 0.2 |
| `joins-failures-9` | 193 | `capacities_fail_without_advancing_clock_or_consuming_generations` | In a registry of 1 record and 1 wait: a second registration is `err=RecordCapacity`; a second wait is `err=WaitCapacity`, with the snapshot and the next generation of waits unchanged; the first wait stays pending | Three children of R other than P, each holding a capability to P with OBSERVE and owning a notification, watch P, filling slots 1 to 3: a fourth's watch is `err=WatchCapacity` and changes nothing; R, the owner, watches P in slot 0, `ok`. The capacity of waits has no case |
| `joins-failures-10` | 211 | `clock_reversal_is_atomic_for_all_timed_mutations` | At the time 9 after 10, `publish`, `release`, `cancel`, `advance` and `begin` are each `err=ClockReversed`, with no change | No case: the time does not decrease within a boot, a premise |
| `joins-failures-11` | 235 | `maximum_generation_is_used_once_and_never_wraps_to_old_receipts` | With the next record and wait generations at $2^{64} - 1$: one record and one wait take them; a further wait is `err=GenerationExhausted`; after the release, a further registration is `err=GenerationExhausted`; the old record is `err=StaleRecord` and the old ticket `err=StaleWait` | No case: registrations have no generation, and the generations of process slots are the objects component's |
| `joins-failures-12` | 260 | `maximum_absolute_deadline_requires_no_overflowing_time_arithmetic` | A wait with the deadline $2^{64} - 1$ at $2^{64} - 2$: the advance to $2^{64} - 2$ completes 0, to $2^{64} - 1$ completes 1; the take gives `TimedOut`; the advance to 0 is `err=ClockReversed` | No case: deadlines are the waits component's |
| `joins-failures-13` | 274 | `premature_object_reap_does_not_fabricate_an_exit_result` | After the target exits with 4 and its object is reaped, `publish` is `err=Object(StaleHandle)`; the observation and the result are none; after the release, the take gives `PeerClosed` | After P exits with 4, R's reap of P is `err=InvalidState` and changes nothing, and the query still gives `state=Dying reason=Exited code=4`; R's reap of an alive child is `err=InvalidState`; after R kills P, R's reap of P is `ok`. No result is made up for a process that has not reached Dead |

### `src/objects/tests.rs`

| Vector | Line | Test | Prototype | Expected output |
| --- | ---: | --- | --- | --- |
| `objects-lifecycle-1` | 175 | `retained_dead_threads_still_count_against_process_quota` | In a process with a limit of 2 threads and two threads, after the first exits with 0, the process is Alive, a new thread is `err=QuotaExceeded`; after the reap of the first, a replacement takes its slot at a larger generation, the first's handle is `err=StaleHandle`, 2 threads are live, and the second is Ready | For processes: R, with a limit of 1 child process, creates P; P exits; R's creation of another child is `err=QuotaExceeded` of the objects component while P is dying or dead; R kills and reaps P; R's next child P2 takes P's process slot at a larger generation, and R's capability to P gives `err=StaleReference` for `query` |
| `objects-lifecycle-2` | 195 | `last_active_thread_exit_closes_admission_before_stack_is_quiescent` | After the active thread exits with 23, it is Dying and the process Dying; a new thread, a resource and a thread reference are each `err=InvalidState`; the reaps of the thread and of the process are `err=Busy`; after the quiescence the thread is Dead and the reason `Exited(23)`, which a termination keeps; both are reaped and the usage is empty | P exits with 23: the query gives `state=Dying reason=Exited code=23`; R's reap of P is `err=InvalidState`; R kills P, `ok`, and the query gives `state=Dead reason=Exited code=23`; R reaps P, `ok`, and R's usages are those before the creation of P. The quiescence of a stack has no case: an entry runs to its end on the stack of its CPU |
| `objects-lifecycle-3` | 230 | `terminating_a_process_stops_all_threads_but_defers_active_stack` | In a process of three threads, one waiting and one active: after the termination, the active one is Dying and the others Dead; a completion of the wait is `err=AlreadyCompleted`, and its result `Terminated`; 1 thread is live; after a second termination and the quiescence, all are reaped and the usage is empty | P's thread blocked on N with the deadline 100: R kills P at 10, `ok`; P's wait ends with `Cancelled`, which no result records; a signal of N at 20 finds no waiter and leaves its bits in N's word; R reaps P. Several threads have no case |
| `objects-lifecycle-4` | 292 | `termination_does_not_overwrite_an_already_completed_wait` | A wait completed with `PeerClosed`; after the termination, its result is still `PeerClosed`, the thread is Dead and 1 completion is counted | P's wait on a notification M of Q ends with `PeerClosed` when Q is destroyed, and P is ready; R kills P, `ok`: the result written in P's saved context is not changed, and no second completion takes place |
| `objects-lifecycle-5` | 304 | `resource_and_thread_references_independently_gate_reclaim` | With a mapping, a CPU, a DMA and a wait obligation and a thread reference, after the termination: the reap of the thread is `err=ReferencesOutstanding`; a second release of the reference is `err=CounterUnderflow`; for each obligation the reap of the process is `err=ReferencesOutstanding` until it is released, and a second release is `err=CounterUnderflow`; then the reap succeeds and the usage is empty | P with committed VM pages, with a capability to P in Q's table and one to P's thread in R's: R kills P, `ok`, and R reaps P, `ok`, at once, since no count gates the reap. The counts and their underflow have no case |
| `objects-lifecycle-6` | 433 | `terminated_wait_cannot_wake_thread_before_or_after_result_consumption` | After the termination of a waiting thread, it is Dead; a completion of its wait is `err=AlreadyCompleted`, its result `Terminated`, a later completion `err=StaleWait`; 1 completion is counted | P's thread blocked on N: R kills P; a later signal of N finds no waiter and leaves its bits in N's word, and P's thread never runs again |
| `objects-lifecycle-7` | 453 | `running_thread_retains_completed_wait_through_exit_and_quiescence` | A wait completed with `PeerClosed`; the thread runs and exits with 7 and is Dying; a completion is `err=AlreadyCompleted`; after a termination, the result is `PeerClosed`, the thread Dying with the reason `Exited(7)`; after the quiescence it is Dead, with 1 completion counted | P's wait on M ends with `PeerClosed`; P runs and exits with 7; R kills P, `ok`, and the query gives `state=Dead reason=Exited code=7`. The take of the result of a wait has no case: a completion writes the result into the saved context |

### Vectors of other pages

These vectors are frozen on other pages, or are not frozen, and are
replayed here; the count of 47 leaves them out.

| Vector | Page and file | Line | Test | Here | Entry |
| --- | --- | ---: | --- | --- | --- |
| `cx-18` | The [context contract](../../boot-platform/context/contract.md#legacy-test-vectors), `src/execution/tests/context.rs` | 267 | `terminal_thread_cannot_resume_reconfigure_or_accept_saved_state` | After an exit and after a fault of P, its thread is removed and never chosen again, so it does not run, and no entry writes its saved context; the prototype's reads, runs, suspensions and configurations of a domain have no counterpart | `exit`, `fault` |
| `cx-29` | The context contract, `src/execution/tests/returns.rs` | 250 | `six_register_publication_cannot_modify_terminal_retired_or_reused_domains` | A wait of P that R's kill ends has the outcome `Cancelled`, which writes no result into P's saved context; after R reaps P and creates P2 in its slot, R's capability to P gives `err=StaleReference`, and P2's thread starts from its initial context | `kill`, `reap` |
| `dying_owner`, in the modules `legacy` and `parallel` | The prototype's `src/objects/tests/activations.rs`, not frozen | 341 | `dying_owner` | The thread of a process that has left Alive was removed in its phase 0 and is in no run queue, so it is never chosen and no entry activates it ([removal](../../scheduling/scheduler/contract.md#blocking-and-readiness)) | `kill`, `exit`, `fault` |
| `dead_owner`, in the modules `legacy` and `parallel` | The prototype's `src/objects/tests/activations.rs`, not frozen | 345 | `dead_owner` | As `dying_owner`, for a dead process | `kill` |
| `terminal_owner_precedes_exhaustion`, in the modules `legacy` and `parallel` | The prototype's `src/objects/tests/activations.rs`, not frozen | 424 | `terminal_owner_precedes_exhaustion` | As `dying_owner` and `dead_owner`; the serial of an activation that the test exhausts has no counterpart | `kill` |
| `abi-lifecycle-1` | The [dispatch contract](../../runtime-sdk/dispatch/contract.md#legacy-test-vectors), `src/abi/tests/lifecycle.rs` | 5 | `query_reports_actual_object_states_and_preserves_a_retained_exit` | The query of P with the selector 0 gives `state=Alive` while its thread is ready, blocked or running, and after P exits with 31, `state=Dying reason=Exited code=31` and then, after R's kill, `state=Dead` with the same reason and code, until R reaps P, after which it is `err=StaleReference`; the states of a thread and the take of the result of a wait have no counterpart | `query`, `exit`, `kill`, `reap` |
| `abi-lifecycle-3` | The dispatch contract, `src/abi/tests/lifecycle.rs` | 99 | `control_without_observation_can_stop_but_not_inspect_a_peer` | Q, holding a capability to P with CONTROL alone: Q's query of P is `err=PermissionDenied`, and Q's kill of P is `ok`; R's query then gives `state=Dead reason=Killed code=0` | `query`, `kill` |

Not replayed here, with their reasons:

- `cx-16`, `cx-20`, `cx-22`, `cx-24` and `cx-26` of the
  [context contract](../../boot-platform/context/contract.md#legacy-test-vectors),
  which has no case for them: their assertions are the suspensions, the
  reads of a context and the writes of return values of the prototype's
  execution manager, refused for a domain that runs, that is not
  configured, that is blocked, or that a failed invalidation retired. Here
  only the CPU that owns a saved context writes it, the scheduler chooses
  the thread that runs, a removed thread is never chosen, and an
  invalidation does not fail, so no rule of this page decides them.
- `matching_zero_generation_keys_allow_success_with_exact_frame`, line
  372, and `nonready_precedes_missing_owner_and_exhaustion`, line 402, of
  the prototype's `src/objects/tests/activations.rs`: the success of an
  activation and its refusal of a thread that is not ready are decided by
  other checks of the activation, not by the state of the owner, as the
  [objects](../objects/contract.md#legacy-test-vectors) contract divides
  that file; there is no activation here.

## Current deviations

The rules of this page differ from those of the prototype's object pool,
execution manager and join registry, which [References](#references)
lists:

- **Reclamation gated by Dead.** The prototype's capabilities held strong
  references to their objects, its threads and processes counted external
  references and the obligations of mappings, CPUs, DMA and waits, and its
  reaping and destruction refused while any was outstanding
  (`ReferencesOutstanding`, `Busy`), so that a capability could keep a
  terminal process and its pages alive. Here no count of capabilities, no
  thread reference and no binding gates the reap: a reference goes stale
  lazily, and Dead, which the steps of the destruction reach by draining
  what the process holds, is the gate. The vectors whose cases change with
  this rule are `execution-lifecycle-1`, `execution-lifecycle-2`,
  `execution-lifecycle-3`, `joins-2`, `joins-failures-2` and
  `objects-lifecycle-5`.
- **Destruction by kill.** The prototype's `finish` made a process dead and
  its `destroy` reclaimed it at once, behind a trusted controller. Here an
  exit or a fault makes a process dying, and the holders of CONTROL, its
  owner in the first place, advance its destruction by kills, one bounded
  step at a time, before its owner reaps it.
- **No join registry.** The prototype copied the first terminal reason of a
  target into a bounded record of a separate registry, which outlived the
  target and its slot, with join waits that a controller registered,
  completed, abandoned and took. Here the reason, the code and the fault
  record live in the process slot until the reap, and the death
  notification is a signal of a notification that the observer names; the
  record of a reaped process belongs to the service that reaped it.
- **Rights of a watch.** A registration needs OBSERVE on the process and
  SIGNAL on the notification, where the prototype required every right of
  the target; a watch of a process that has left Alive is delivered at once,
  where the prototype refused a dying or dead target.
- **Duplicates.** A second watch with the same notification merges its
  bits, where the prototype refused a second record of the target.
- **The outcome of a kill.** A wait that a kill ends has the outcome
  `Cancelled`, where the prototype's waits ended as `Terminated`; the names
  of the reasons are Killed and Faulted, for the prototype's `Terminated`
  and `Fault`.
- **One thread.** A process has one thread, created with it: the
  prototype's several threads of a process, the exit of one thread and the
  quiescence of a running stack do not exist.
- **Exit codes.** An exit code is 32 bits wide, unsigned in its register,
  where the prototype kept a signed 32-bit value.
- **The root.** The end of the root halts the system, where the
  prototype's root could not end.

## References

- Arm Limited, *Arm Architecture Reference Manual for A-profile
  architecture*, DDI 0487, version M.d, 2026,
  <https://documentation-service.arm.com/static/6abbec2a6db85c5e6614a4a1>:
  the exception syndrome of `ESR_EL1` with its exception class, the fault
  address of `FAR_EL1`, and `TLBI ASIDE1` with the completion of TLB
  maintenance by `DSB`.
- The kernel's own rules, which this page instantiates:
  [Kernel objects and capabilities](../../../architecture.md#kernel-objects-and-capabilities)
  for the process lifetime, its states, exit reasons and cascade, the
  owner that reaps, the quotas that return and the dangling references;
  [System calls and the ABI](../../../architecture.md#system-calls-and-the-abi)
  for entries that run to completion and long operations that store their
  progress; and
  [Processes, POSIX and Linux compatibility](../../../architecture.md#processes-posix-and-linux-compatibility)
  for the process services that own and reap processes; the
  [internal choices](../../../security.md#internal-choices),
  [observable outputs](../../../security.md#observable-outputs) and
  [information-flow boundary](../../../security.md#information-flow-boundary)
  of the security model.
- The rules of this page take, as clauses of their own, the rules of the
  prototype tree at `prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`:
  - `docs/features/kernel/foundations.md`, lines 113 to 131: the exit of
    the last thread, the termination that completes pending waits and keeps
    completed ones, the reclamation after quiescence and its reference
    gates, which are not carried ([Current deviations](#current-deviations)),
    and the lifecycle alive, dying, dead and reaped with the first terminal
    reason kept by later operations;
  - `docs/features/kernel/foundations.md`, lines 202 to 224: the
    reclamation of the execution manager, its rejection of external
    references, retirement, ASID invalidation, scrubbing and freeing before
    the reap, with the retention for a retry after a failed invalidation,
    which a plan that cannot fail replaces;
  - `docs/features/kernel/user-execution.md`, lines 275 to 282: the
    termination of a domain that does not run, which drains its pending
    wait and prevents its resumption, and the gates of its destruction;
  - `docs/features/kernel/user-execution.md`, lines 299 to 344: the
    ownership and lifetimes of the resources of a domain, the publication
    of the first terminal reason before its destruction, and the order of
    retirement, completed TLB invalidation, scrubbing and the reap;
  - `docs/features/kernel/capabilities.md`, lines 163 to 170: the strong
    references of capabilities that kept a terminal target alive, the
    source of the change to lazy staleness;
  - `docs/features/kernel/capabilities.md`, lines 197 to 210: a dying or
    dead caller that loses its access before the teardown of its table,
    the teardown on exit, fault or termination that keeps outward
    descendants, and the hardware steps that it does not replace;
  - `docs/features/kernel/joins.md`, lines 80 to 139: independent exit
    records, their rights, the first reason, the outcomes and their order
    with a single winner, and the abandonment of the receipts of an
    observer, which the death notification and the waits component take
    over;
  - `docs/features/kernel/joins.md`, lines 196 to 204: the design that
    decouples exit records from objects and delivers results through the
    saved return registers.
