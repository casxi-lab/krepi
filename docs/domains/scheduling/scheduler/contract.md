# Scheduler contract

This page governs the code of the `scheduler` component of the
[scheduling and budgets](../README.md) domain: the three priority classes,
the run queues of each CPU, the selection of the thread that runs with the
deadline of its dispatch, time slices, preemption, the stops of a dispatch,
blocking, readiness and removal, the reserved control capacity, the checks
of admission, the operation `yield`, the time slice among the platform
parameters, and the time of a transition as an input. The budget records,
the class ledgers, charging, replenishment, the holdings that admission
carves and the loans of budgets belong to the
[budget-ledger](../budget-ledger/contract.md) component, whose entries this
page calls; when a loan is made and withdrawn, and when a wait completes,
belong to the IPC and waits components of the IPC and waits domain
(planned), which compose the entries of this page. The observable behaviour
that these rules serve, with its evidence, is in the
[requirements](requirements.md), the other document of the component.

## Terms

- **Class.** One of the three priority classes, from the highest: control,
  interactive and background ([Priority classes](#priority-classes)). The
  class of a thread is a field of its budget record, which the
  [budget-ledger](../budget-ledger/contract.md#budget-records) component
  keeps.
- **Effective class.** The class whose run queue a ready thread joins: its
  own class, or, while it runs on a borrowed context, the effective class
  that the [lending](../budget-ledger/contract.md#lending) rules of the
  budget-ledger component give it.
- **Context.** The budget that a thread runs on: its own budget record, or
  the context that it borrows; every interval that it runs is charged to
  the owner of its context
  ([charging](../budget-ledger/contract.md#charging-and-debt)).
- **Credit.** The dispatch credit that `ledger::available` (planned) of the
  budget-ledger component gives for a thread at a time, with the owner of
  its context, the end of the current period and its effective class: the
  part of the budget of its context, and of the cap of the class of that
  context, that a dispatch may still use in the current period. A ready
  thread whose credit is 0 is **throttled**.
- **Scheduler record.** `scheduler::RunQueues` (planned): the record of one
  CPU that this page keeps: the time slice in ticks, the run queue of each
  class, the current thread with its dispatch, the timer deadline and the
  reschedule flag. It lives in the per-CPU record of the architecture crate
  (planned).
- **Run queue.** The FIFO of the ready threads of one class on one CPU
  ([Run queues](#run-queues)).
- **Scheduling state.** The fields of this page in the slot of a thread:
  its state, new, running, ready, blocked or removed; the class of the run
  queue that holds it while it is ready; its link in that queue; and its
  time slice left ([Blocking and readiness](#blocking-and-readiness)).
- **Dispatch.** The interval in which a CPU runs one thread at EL0 and in
  the entries that it makes, from the `choose` that selects the thread to
  the stop of the dispatch: `preempt`, `yield_now`, `block` or `remove`. A
  dispatch has its **start**, its **deadline** and the context that it is
  charged to.
- **Current thread.** The thread of the dispatch of a CPU, if any; with
  none, the CPU is **idle**.
- **Time slice.** `TIME_SLICE` of the
  [platform parameters](#platform-parameters-and-time), in ticks; the
  **time slice left** of a thread is the part of it that its dispatches
  have not used.
- **External deadline.** The earliest deadline of the waits of the CPU that
  have not settled, which the composer takes from the waits component
  (planned) and passes to `choose`; none when no such wait has a deadline.
- **Reschedule flag.** A field of the scheduler record that asks the
  composer of the return to stop the current dispatch
  ([Preemption](#preemption)).
- **Tick.** One count of the virtual counter `CNTVCT_EL0`.
- **Transition time.** `now`: the tick count that the architecture crate
  reads once at the entry of a transition and passes to every entry of
  this page that needs time
  ([Platform parameters and time](#platform-parameters-and-time)).
- **Composer.** The module of the core above this one that composes an
  entry of this page into an operation: `dispatch`, `ipc`, `lifecycle` or
  `creation` (planned).
- **Token.** What an access to state that is not per-CPU holds, as the
  [SMP design rules](../../../conventions/smp.md#s1-state-classes) state;
  with one CPU, the executing CPU holds every token.
- **Boot wiring.** The code of a board crate that runs on the boot CPU before
  any entry from EL0, as in the
  [objects](../../objects-capabilities/objects/contract.md#terms) contract.

## Entry points

The entries of the core are in the module `scheduler` of `krepi-kernel`
(planned). One of them is an operation of the ABI inventory, in its
production range: `yield` (planned), which takes no argument and returns
success. Its operation number and the registers of its result belong to the
inventory. The other entries are called by the boot wiring and by the
composers.

| Entry point | Kind | Called by | ABI operation | Rules |
| --- | --- | --- | --- | --- |
| `scheduler::validate_parameters` (planned), with the value type `scheduler::Parameters` | Function that writes nothing, host-testable | The boot wiring of each board, once, after `Ledger::new` of the budget-ledger component has accepted the period and the counter frequency, before the first entry from EL0 | None | [Platform parameters and time](#platform-parameters-and-time) |
| `RunQueues::new` (planned), with the value type `scheduler::RunQueues` | Function that writes nothing, host-testable | The boot wiring, once for each CPU, with the time slice that `validate_parameters` gives, which stores the record in the per-CPU record of the CPU (planned) | None | [Run queues](#run-queues), [Platform parameters and time](#platform-parameters-and-time) |
| `scheduler::admit` (planned) | Write entry on the copies of a write set, host-testable | `creation`, for the thread of a new process; the boot of the root by the kernel root (planned), for the root's thread | None | [Admission](#admission), [Reserved control capacity](#reserved-control-capacity), [Run queues](#run-queues) |
| `scheduler::enqueue` (planned) | Write entry on the copies of a write set, host-testable | The composers that complete a wait or end the pause of a thread: `ipc`, `lifecycle` and `dispatch` (planned) | None | [Blocking and readiness](#blocking-and-readiness), [Run queues](#run-queues), [Preemption](#preemption) |
| `scheduler::choose` (planned) | Write entry on the copies of a write set, host-testable | `dispatch` (planned), as the composer of the return to EL0 and of the wait of an idle CPU | None | [Selection and time slices](#selection-and-time-slices) |
| `scheduler::preempt` (planned) | Write entry on the copies of a write set, host-testable | `dispatch` (planned), at the return of an entry whose dispatch has reached its deadline or whose reschedule flag is set | None | [Preemption](#preemption), [Run queues](#run-queues) |
| `scheduler::yield_now` (planned) | Write entry on the copies of a write set, host-testable | `dispatch` (planned), for the operation `yield` | `yield` | [Run queues](#run-queues), [Selection and time slices](#selection-and-time-slices) |
| `scheduler::block` (planned) | Write entry on the copies of a write set, host-testable | The composers of the calls that block their caller: `ipc` for `call` and `receive`, and `dispatch` for the waits on notifications and wait sets and for sleeps (planned) | None | [Blocking and readiness](#blocking-and-readiness) |
| `scheduler::remove` (planned) | Write entry on the copies of a write set, host-testable | `lifecycle` (planned), in the steps of the destruction of a process | None | [Blocking and readiness](#blocking-and-readiness) |
| `scheduler::requeue` (planned) | Write entry on the copies of a write set, host-testable | `ipc` (planned), after `ledger::lend` or `ledger::withdraw` of the budget-ledger component has changed the context of a thread that is ready or running; `creation` and `lifecycle` (planned), for the current thread, before `ledger::admit` or `ledger::release` changes the record of the owner of the context of its dispatch | None | [Priority classes](#priority-classes), [Run queues](#run-queues) |

`yield_now` is the entry of the operation `yield`, a reserved word of Rust.

## Extractability

The module `scheduler` of the core (planned), in `kernel/src/scheduler.rs`
(planned), follows the
[provable Rust subset](../../../conventions/provable-subset.md): the run
queues, the selection by class with the deadline of a dispatch, the stops
of a dispatch, readiness and removal, the checks of admission and the check
of the time slice. It is not among the roles of the subset's scope, which
lists the modules for which a specification is planned; no specification
of it is planned in release 0.1, and its entries are
[open obligations](#open-obligations).

It takes layer 5 by the rules of the
[module order](../../../architecture.md#module-order-in-the-core), whose
table lists only the modules of the subset's roles: it refers to the
modules `objects` and `ledger` and to the kernel root, and to no module of
its own layer, `vm` and `waits`, or above; the module `waits` does not
refer to it either. So the operations that make a thread ready are
composed above both, each by a module that refers to `waits` and to this
module: the events of IPC by `ipc` (layer 6); the signals, sleeps,
expiries, revocations and their pauses by `dispatch` (layer 9); the forced
kill and the destruction of a process by `lifecycle` (layer 7). The waits
component gives the threads that a completion makes ready, in the order of
[Determinism](#determinism), and the composer calls `enqueue` for each in
the same transaction. The external deadline, state of the module `waits` of
the same layer, comes in as a value: `dispatch` reads it and passes it to
`choose`.

Its items are `pub(crate)` except the rows of the entry table that the
board crates call, `validate_parameters` and `RunQueues::new`, with the value
types that those rows take and return
([provable core](../../../architecture.md#the-provable-core)). Its other
entries receive the one kernel root, by `&mut` for the write entries
([rule 3](../../../conventions/provable-subset.md#3-flat-relations-and-one-kernel-root)),
and the scheduler record, the budget ledger and the write-set buffer of the
executing CPU by explicit `&mut` arguments
([rule 8](../../../conventions/provable-subset.md#8-no-interior-mutability)).
The module touches no register and defines no callback: it gives the timer
deadline as a value, with which the architecture crate arms the timer, and
it takes the time as an argument.

The scheduler record of each CPU is in the per-CPU record of the
architecture crate (planned). Finding the record of the executing CPU and
masking its interrupts is the adapter that the objects contract lists among
its
[open obligations](../../objects-capabilities/objects/contract.md#open-obligations);
lending the scheduler record by `&mut` for no longer than the token of the
CPU lives is an adapter of the architecture crate, outside the proof
target, which [Open obligations](#open-obligations) lists, as the
budget-ledger component lists the one that lends the ledger of the CPU in
its own
[open obligations](../budget-ledger/contract.md#open-obligations). The
contract is written before its code, so this section lists no source paths;
the change that adds the module writes its `paths` block here.

## Priority classes

- **Three classes.** `scheduler::PRIORITIES` (planned) = 3: control,
  interactive and background, in this order. Every thread has one class,
  fixed when it is admitted ([Admission](#admission)). The classes and
  their order are those of `ledger::Class` (planned), which the
  [budget-ledger](../budget-ledger/contract.md#terms) component defines,
  since its loans compare classes and its module is below this one;
  selection takes the classes in that order.
- **Strict priority.** Selection takes a thread of a higher effective class
  before any thread of a lower one, as long as the higher one has credit
  ([Selection and time slices](#selection-and-time-slices)); within a
  class, the run queue decides.
- **Effective class.** A ready thread waits in the run queue of its
  effective class; the budget that it uses is charged to the owner of its
  context and to that owner's class, never to the class of its queue
  ([lending](../budget-ledger/contract.md#lending)). When a loan changes
  the context of a thread that is ready or running, the composer calls
  `requeue` ([Run queues](#run-queues)).
- **Encoding.** The values of the classes that reach EL0, through the
  arguments of a creation, belong to the ABI inventory.

## Run queues

- **One queue for each class and CPU.** The scheduler record of a CPU holds
  a FIFO run queue for each class: its first and its last thread, with a
  link from each thread to the next in the scheduling state of its slot. A
  ready thread is in exactly one run queue, that of its effective class on
  the CPU that holds it; a new, running, blocked or removed thread is in
  none. A thread joins the run queue of the CPU that runs the entry; with
  more than one CPU, the choice of the CPU and the pending queues of the
  CPUs belong to the multicore components (planned).
- **Tail.** A thread that becomes ready joins the tail of its queue with a
  whole time slice: a thread that `admit` makes ready, that `enqueue`
  wakes, whose dispatch stops with no time slice left, whose dispatch stops
  without credit, and one that yields with `yield_now`. A thread that
  `requeue` moves joins the tail of its new queue and keeps its time slice
  left.
- **Head.** A thread whose dispatch `preempt` stops while it has time slice
  left and credit returns to the head of its queue and keeps the rest of
  its slice.
- **Throttled threads.** A thread whose dispatch stops without credit takes
  the tail and keeps that place while it is throttled; selection passes
  over it until the replenishment of its context gives it credit, and it
  resumes from that place. A thread that `enqueue` wakes without credit
  joins the tail in the same way, and so does a thread that `preempt` stops
  with time slice left but without credit.
- **Reading of the rule for queues.** The
  [internal choices](../../../security.md#internal-choices) of the security
  model put a thread that resumes after replenishment at the tail, and a
  thread preempted with time slice left at the head. This page reads the
  first as the tail that the thread takes when it stops, or is woken,
  without credit, and keeps while it is throttled; and it reads the second
  for a thread that has credit, so a thread without credit joins the tail
  also with time slice left. Replenishment is computed when a record is
  read ([replenishment](../budget-ledger/contract.md#replenishment)), so
  moving every thread that a boundary resumes to the tail would need a
  loop over the throttled threads at each boundary and a write set with no
  bound within $W$. The same rule has dispatch take "the first thread with
  budget at the highest non-empty priority": this page reads the highest
  non-empty priority as the highest class whose run queue holds a thread
  with credit, so a class whose ready threads are all throttled is passed
  over, as step 1 of
  [Selection and time slices](#selection-and-time-slices) states.
- **Several in one transition.** When one transition makes several threads
  ready, the composer calls `enqueue` in the order of
  [Determinism](#determinism), and each joins the tail in the order of the
  calls.
- **`yield`.** `yield_now` stops the dispatch of the current thread, charges
  it and puts the thread at the tail of its queue with a whole slice. When
  no other thread of its class or above has credit, the next `choose`
  selects it again.
- **Requeue.** `requeue(thread, now)` takes a ready thread out of the queue
  of its old effective class and puts it at the tail of the queue of its
  new one. For the current thread it charges the dispatch up to `now` to
  the context that the dispatch had, takes that interval from its time
  slice left, continues the dispatch from `now` on the new context and sets
  the reschedule flag, so that the return chooses again with a deadline for
  the new context. The composers of creation and reaping call it for the
  current thread with its context unchanged, before an admission or a
  release changes the record of the owner of that context
  ([admission and release](../budget-ledger/contract.md#admission-and-release)),
  so that the charge up to `now` uses the budget from before the change.

## Selection and time slices

`choose(now, external)` runs on a CPU with no dispatch, after the composer
has settled every wait whose deadline is not later than `now`:

1. For each class from control to background, it walks the run queue from
   its first thread and takes the first thread whose credit at `now` is
   above 0. A thread without credit is passed over and stays where it is; a
   class whose queue holds no thread with credit is passed over.
2. With a thread taken, the thread leaves its queue and becomes running and
   the current thread of the CPU; its dispatch starts at `now` on the
   context whose owner `ledger::available` gives, and its deadline is

   ```math
   d = \min(\mathit{now} + s,\ \mathit{now} + a,\ p,\ e)
   ```

   where $s$ is the time slice left of the thread, $a$ its credit and $p$
   the end of the current period, both as `ledger::available` gives them
   ([replenishment](../budget-ledger/contract.md#replenishment)), and $e$
   the external deadline, left out when there is none. The output is the
   thread and $d$, which is also the timer deadline.
3. With no thread taken, the CPU is idle, and the output is its wake time:
   the earlier of $p$, when a ready thread of the CPU is throttled, and
   $e$; or none, when neither applies. The timer deadline is the wake time.
   The CPU then waits for an interrupt, and the next transition chooses
   again.

- **The dispatch keeps its deadline.** A system call of the current thread
  that returns to it, without a stop, continues its dispatch: the composer
  calls no `choose`, and the start, the deadline and the context of the
  dispatch stay. A `choose` while a dispatch runs is `InvalidState` and
  changes nothing.
- **Stops.** A dispatch ends only with `preempt`, `yield_now`, `block` or
  `remove`. Each charges the interval from the start of the dispatch, or
  from its last charge by `requeue`, to `now` to the context of the
  dispatch, with `ledger::charge` of the budget-ledger component, and takes
  it from the time slice left of the thread; an interval longer than the
  slice left leaves no slice. Every stop charges, whatever its reason and
  however short the interval: a preemption, a yield, a block for a wait or
  a sleep, an exit, a fault or a kill.
- **Bounds of the arithmetic.** $s$ and $a$ are below $2^{62}$, and $p$ is
  at most $\mathit{now}$ plus the period, which is below $2^{62}$
  ([Platform parameters and time](#platform-parameters-and-time)); with
  $\mathit{now} < 2^{63}$, no sum of the deadline overflows 64 bits.
  The external deadline is only compared.

## Preemption

- **At the deadline.** The architecture crate arms the timer for the timer
  deadline. When the timer interrupt arrives at or after the deadline of
  the dispatch, the composer of its return calls `preempt` and then
  `choose`. So a dispatch ends when its time slice ends, when its credit
  ends, at the end of a period and at the external deadline, whichever comes
  first.
- **A higher class made ready.** While a dispatch runs, `enqueue`, `admit`
  and `requeue` of a ready thread set the reschedule flag when the thread
  that they make ready, or move, has credit and an effective class above
  that of the current thread; `requeue` of the current thread sets it
  always ([Run queues](#run-queues)). On an idle CPU they leave the flag
  clear, since the composer of the return calls `choose` in any case.
- **The life of the flag.** The flag is set only while a dispatch runs, and
  every stop of a dispatch, `preempt`, `yield_now`, `block` and `remove` of
  the current thread, clears it, so a flag that an entry sets for a
  dispatch that then stops in the same operation does not reach the next
  dispatch.
- **Where it acts.** The execution model schedules only before a return to
  EL0 and at the explicit preemption points of long operations
  ([execution model](../../../architecture.md#system-calls-and-the-abi)),
  so:
  - a thread made ready by the entry itself, by a system call of the
    current thread or by the interrupt of a device that signals a
    notification, runs at the return of that entry: the composer finds the
    reschedule flag set, calls `preempt` and then `choose`;
  - a thread made ready by time, by the expiry of a sleep or of the
    deadline of a wait, or by the replenishment of its context at the end
    of a period, runs at the timer interrupt: that time is the external
    deadline or the end of the period, so the deadline of the current
    dispatch is not later, and the composer of the interrupt completes the
    wait, calls `enqueue`, `preempt` and `choose`.
- **The checks of `preempt`.** `preempt(now)` needs a dispatch whose
  deadline is not later than `now`, or the reschedule flag set; otherwise it
  is `InvalidState` and changes nothing. An interrupt before the deadline,
  without the flag, leaves the dispatch with its start, its deadline and
  its context, and the composer returns to the current thread.
- **Placement.** `preempt` charges the dispatch and makes its thread ready:
  at the tail with a whole slice when the thread has no credit at `now`; at
  the head with the rest of its slice when it has time slice left; at the
  tail with a whole slice otherwise. Like every stop, it clears the
  reschedule flag.

## Blocking and readiness

The scheduling state of a thread starts as new when its slot is occupied,
and these entries and events change it:

| From | Entry or event | To |
| --- | --- | --- |
| New | `admit` | Ready, at the tail of the queue of its class |
| Ready | `choose` | Running, the current thread |
| Running | `preempt` | Ready, at the head or the tail ([Preemption](#preemption)) |
| Running | `yield_now` | Ready, at the tail |
| Running | `block` | Blocked |
| Blocked | `enqueue` | Ready, at the tail of the queue of its effective class |
| Ready | `requeue` | Ready, at the tail of the queue of its new effective class |
| Running | `requeue` | Running, its dispatch continued from `now` on the new context |
| Ready, running or blocked | `remove` | Removed |

- **Blocking.** A call that blocks writes, after its checks, the wait
  record of its thread, which the waits component defines, and its composer
  calls `block(now)`, which stops the dispatch of the current thread,
  charges it and makes the thread blocked. A thread blocks only by a call
  of its own, while it runs. A sleep is a wait of the waits component
  without an object, and its deadline is an external deadline: this page
  does not tell a sleep from another wait, and the prototype's sleeping and
  waiting states are both blocked here.
- **Readiness.** A blocked thread becomes ready only by `enqueue`, which the
  composer calls once the waits or IPC component has completed its wait,
  and never by itself: this page holds no deadline of a thread. A sleep
  whose deadline is not later than `now` returns at once without blocking,
  as the waits component states, so the thread keeps its dispatch.
- **Pause by revocation.** A thread whose wait settles as revoked while its
  thread is paused stays blocked; the composer of the step of the
  revocation that removes the entry through which it waited makes it ready
  with `enqueue`.
- **Removal.** `remove(thread, now)` takes a thread out of scheduling: the
  current thread with a stop of its dispatch, which charges it; a ready one
  out of its run queue; a blocked one, whose wait the destruction completes
  in the waits component, as it is. The lifecycle component holds the
  terminal states of processes and threads and calls `remove` in the
  destruction of a process; a removed thread is never chosen and never
  admitted again, and its state stays removed until its slot is released.
  A new thread, not yet admitted, is in no run queue either; a thread is
  admitted once, in the write set that creates it.
- **One CPU at a time.** A thread is the current thread of at most one CPU,
  and only a ready thread is chosen, so no new, blocked or removed thread
  runs, and a running thread is not chosen a second time.

## Reserved control capacity

- **Caps set aside.** Each class has its cap for each period, and the caps
  and the kernel margin add up to at most the period, a check of
  `Ledger::new` of the budget-ledger component at boot
  ([Platform parameters and time](#platform-parameters-and-time)). The
  caps are disjoint: admission carves each holding from a holding of the
  same class and gives a thread nothing of a class above its own, so an
  admission of an interactive or a background thread never takes from the
  control cap, and the control cap is set aside before any admission of
  the other classes
  ([admission and release](../budget-ledger/contract.md#admission-and-release)).
- **Kernel margin.** `KERNEL_MARGIN` of each period is admitted to no class:
  it is the time of the kernel and of interrupts, so the budgets that
  admission guarantees never exceed the CPU.
- **Control under load.** A control thread with credit is taken before every
  thread of the other classes, and the reschedule flag or the timer stops a
  dispatch of a lower class when it becomes ready
  ([Preemption](#preemption)). So under full load, with ready threads of
  every class, a control thread runs on its credit within each period, up
  to its budget and the control cap.
- **The other classes.** No class runs beyond its cap in a period without
  debt, which the following periods repay
  ([charging](../budget-ledger/contract.md#charging-and-debt)). So in a
  period in which the control and interactive classes start without debt,
  at least the background cap is left of the period for the background
  class, less the overrun of the dispatches that stop late.

## Admission

- **Inputs.** The creator of a new thread gives, through the arguments of
  the creation call, its class; one amount for each class, of which the
  amount of its class is its budget and those of the classes below it are
  the holdings from which its process can admit threads of those classes;
  and its service ceiling, the highest class that a loan can lend it. The
  creation component composes `admit` of this page with `ledger::admit` of
  the budget-ledger component in the write set that creates the thread;
  the ABI form of the arguments belongs to the ABI inventory.
- **Checks.** `admit(creator, thread, class, ceiling, now)` checks, in this
  order and before the first write of the composition:
  1. the references of the creator and of the new thread
     (`WrongPool` and `StaleReference` of `ObjectTable::resolve` of the
     [objects](../../objects-capabilities/objects/contract.md#identities-and-generations)
     component);
  2. the scheduling state of the new thread is new (`InvalidState`);
  3. its class is not above the class of the creator, and its ceiling is
     not above the class of the creator (`AdmissionRejected`).

  A ceiling at or below the class of the thread lends it no higher class,
  since its effective class is the higher of its own class and the class
  that a loan gives it within the ceiling
  ([lending](../budget-ledger/contract.md#lending)). The amounts are
  checked by `ledger::admit`
  ([admission and release](../budget-ledger/contract.md#admission-and-release)),
  with its errors: a budget of 0, an amount above 0 for a class above the
  class of the thread, and an amount beyond the creator's holding of the
  same class. The composer makes the checks of both entries before its
  first write, in the order of errors of [Errors](#errors).
- **Effect.** `admit` makes the thread ready at the tail of the queue of its
  class with a whole slice, and sets the reschedule flag as
  [Preemption](#preemption) states. The creation component decides when, in
  the creation, the thread is admitted.
- **The root.** The boot of the root admits the root's thread in the class
  control, with the holdings that the budget-ledger component gives the
  root; its creator is the kernel domain, whose class this page takes as
  control.
- **Release.** The removal of a thread is `remove`; the return of its
  holdings at its reaping is `ledger::release` of the budget-ledger
  component.

## Platform parameters and time

**Platform parameters.** Each board gives these values in microseconds, in
its board crate. The boot wiring reads `CNTFRQ_EL0` once and passes the
values with the frequency to `Ledger::new` of the budget-ledger component,
which converts and checks the period, the caps and the margin, and then
`TIME_SLICE` and `REPLENISH_PERIOD` with the frequency to
`validate_parameters`, which converts the time slice and the period by the
same rule, $\lfloor u \cdot f / 10^6 \rfloor$ ticks for $u$ microseconds at
the frequency $f$, checks the time slice and gives it in ticks;
`RunQueues::new` keeps that time slice in the scheduler record of each CPU.
The values are read-only after boot.

| Parameter | Meaning | Constraint, and the entry that checks it | QEMU virt | Raspberry Pi 5 |
| --- | --- | --- | --- | --- |
| `TIME_SLICE` | The time slice of a dispatch | At least 1 tick and fewer ticks than `REPLENISH_PERIOD`: `validate_parameters` | Set by the board (planned) | Set by the board (planned) |
| `REPLENISH_PERIOD` | The period of replenishment, one for every class and record of a CPU | At least 1 tick and fewer than $2^{62}$: `Ledger::new` | Set by the board (planned) | Set by the board (planned) |
| `CONTROL_CAP`, `INTERACTIVE_CAP` and `BACKGROUND_CAP` | The cap of each class for each period | With `KERNEL_MARGIN`, at most `REPLENISH_PERIOD` in ticks: `Ledger::new`. For a board, `CONTROL_CAP` is at least 1 tick, since the root's thread runs on it; no entry checks this ([classes](../budget-ledger/contract.md#classes)) | Set by the board (planned) | Set by the board (planned) |
| `KERNEL_MARGIN` | The part of each period set aside for the kernel and interrupts | As the caps: `Ledger::new` | Set by the board (planned) | Set by the board (planned) |

- **Counter frequency.** `CNTFRQ_EL0` is not 0, and each converted value
  fits 64 bits: checks of `Ledger::new`. A time slice that fits fewer ticks
  than the period fits 64 bits as well.
- **Failure.** A value that breaks a constraint of this page is
  `InvalidConfiguration` of `validate_parameters`, and the boot stops before
  any entry from EL0; those of `Ledger::new` are the budget-ledger
  component's [errors](../budget-ledger/contract.md#errors). There is no
  fallback value.
- **Range.** After the checks, the time slice, the period, the caps and the
  margin are each below $2^{62}$ ticks.
- **Separate from the boot test timer.** These parameters are separate from
  the `TIMER_RATE` of the
  [boot](../../boot-platform/boot/contract.md#platform-parameters)
  component, which sets the period of the timer interrupt of its own test
  path.

**Time.**

- **One count.** Time is the count of the virtual counter `CNTVCT_EL0`,
  which EL0 reads as well
  ([EL0 controls](../../memory/address-space/contract.md#el0-controls)), so
  a deadline that EL0 builds from it and `CNTFRQ_EL0` and the time of a
  transition are in the same count.
- **Read once, passed in.** The architecture crate reads the counter once at
  the entry of every transition and passes it as `now` to every entry of
  this page that needs time; this page reads no counter. A host test passes
  `now` itself, so the time source is injected.
- **Premises.** Within one boot, `now` never decreases and stays below
  $2^{63}$. They are premises of the architecture crate, which reads the
  counter, and no entry checks them, so time that goes backwards and times
  near $2^{64}$ have no error here.
- **Deadlines from EL0.** A deadline that EL0 gives may be any 64-bit value;
  the waits component only compares it, and this page only compares the
  external deadline that results.
- **The timer of the board.** The timer whose interrupt preempts is the
  board's: the virtual timer on QEMU virt and the physical timer on the
  Pi 5. Where it is not the virtual timer, the architecture crate and the
  board support convert the timer deadline, which is in the virtual count,
  into the compare value of that timer (planned).

## Errors

| Error | Rule broken | Entries | Place in the order of errors |
| --- | --- | --- | --- |
| `InvalidConfiguration` | A `TIME_SLICE` of fewer than 1 tick, or of no fewer ticks than `REPLENISH_PERIOD` | `validate_parameters` | At boot |
| `WrongPool` of the objects component | A reference of another pool than the thread pool | `admit`, `enqueue`, `remove`, `requeue` | Handle resolution: the type |
| `StaleReference` of the objects component | A reference to a thread that is not live | `admit`, `enqueue`, `remove`, `requeue` | Handle resolution: the liveness of the object |
| `InvalidState` | A thread or a dispatch in a state other than the one that the entry needs: `admit` of a thread that is not new; `enqueue` of one that is not blocked; `requeue` of one that is neither ready nor running; `remove` of one that is new or removed; `choose` while a dispatch runs; `preempt`, `yield_now` and `block` without a dispatch; `preempt` before the deadline of the dispatch without the reschedule flag | `admit`, `enqueue`, `requeue`, `remove`, `choose`, `preempt`, `yield_now`, `block` | Object state |
| `AdmissionRejected` | A class, or a service ceiling, above the class of the creator | `admit` | The caller's quota |

- **Order.** Each entry checks in the order of its rule section and
  returns the first error. A composing operation applies the order of
  errors of the [security model](../../../security.md#internal-choices):
  handle resolution, then object state, then the caller's quota, where the
  class and the ceiling of this page come before the holdings that
  `ledger::admit` checks. The form of its arguments, among them a budget
  of 0 and an amount above 0 for a class above the thread's, which
  `ledger::admit` refuses, comes before handle resolution when the ABI
  inventory passes them in registers, and after the rights and the user
  buffers, before object state, when it copies them in an argument
  structure.
- **No change on failure.** No error changes state: an entry of this page
  that returns an error leaves every field of the kernel state as it was,
  the copies in the write set included, and writes no counter; a composing
  operation that meets an error discards its buffer, so the kernel state
  after any failed operation equals the state before it. There is no
  exception. The result registers of a failed system call follow the
  [observable outputs](../../../security.md#observable-outputs) of the
  security model; this component writes no register. An error of the boot
  stops the boot before any entry from EL0.
- **Totality.** `InvalidState` and the errors of references answer calls
  that no composer makes, since a composer calls each entry in the state
  that its rules give; the answer changes nothing.
- **Names.** The names are those of this contract; the numeric values of
  the errors that reach EL0 through a composing operation belong to the ABI
  inventory.

The prototype's scheduler had 23 errors, which this page and the
[budget-ledger](../budget-ledger/contract.md#errors) component divide; this
page also maps the activation part of the prototype's `Busy` of its object
pool, which the objects contract moved to the scheduler. Here:

| Prototype error | Here |
| --- | --- |
| `InvalidConfiguration` | Kept, for the check of the time slice; the prototype's capacity of 0 does not apply, since the run queues take the threads of the thread pool and have no capacity of their own. The checks of the period, the caps, the margin and the amounts of an admission are the budget-ledger component's, with its own row |
| `AdmissionRejected` | Kept, for a class or a ceiling above the creator's class; an amount beyond the creator's holding of the same class is the budget-ledger component's |
| `Duplicate` | Not applicable: a thread is admitted once, in the write set that creates it, and a second `admit` of it, which no composer makes, is `InvalidState` |
| `Capacity` | Not applicable: a run queue holds threads of the thread pool and has no capacity of its own |
| `UnknownThread` | Not applicable: the entries take thread references, and a reference that is not live is `StaleReference` of the objects component |
| `Busy` | Not applicable: every operation runs within the dispatch of its caller or on an idle CPU, and no entry needs the dispatch to have stopped; a thread can be made ready, admitted or removed while another runs, and a `choose` while a dispatch runs is `InvalidState` |
| `InvalidState` | Kept, for a thread or a dispatch in a state other than the one that the entry needs |
| `ClockWentBackwards` | Not applicable: `now` never decreases within a boot, a premise of [Platform parameters and time](#platform-parameters-and-time); the budget-ledger component has its own row |
| `InvalidDeadline` | Not applicable: this page computes the deadline of a dispatch, and the composer settles every wait whose deadline has passed before `choose`; an early `preempt` is `InvalidState` |
| `Object(_)` | Not kept as a wrapper: the errors of the objects component that this page meets, `WrongPool` and `StaleReference`, are returned as they are; the budget-ledger component has its own row |
| `WrongRegistry` | Not applicable: each CPU has one scheduler record, which its adapter lends, and no record carries a registry number |
| `StaleScope` | Not applicable: there are no scopes; the budget of a child is carved from its creator's holding when the child is created |
| `PermissionDenied` | Moved to the [capabilities](../../objects-capabilities/capabilities/contract.md#rights) component: CONTROL on a thread and CREATE on a process are rights of capability entries, which the composers look up; the budget-ledger component has its own row |
| `DuplicateOwner` | Not applicable: there are no scopes; the budget of a process is the record of its one thread |
| `ScopeCapacity` | Not applicable: there are no scopes |
| `GenerationExhausted` | Not applicable: the prototype used it for the generations of its scopes; the activation serials of the prototype's object pool do not exist either |
| `OwnerMismatch` | Not applicable: admission is composed into the creation of a process with its thread, so the thread always belongs to the process that the creation names |
| The activation part of the prototype's `Busy` of its object pool | Not applicable: there is no activation; the current thread of a CPU is the one that `choose` takes from the run queues, so a second activation of a thread does not exist. Its part for the reaping of a running thread belongs to the lifecycle component |

## Check and execute

Every write entry of this page checks, before its first write, everything
that its effect needs, as [Errors](#errors) lists, then changes only the
copies in the write set of its caller
([write sets](../../objects-capabilities/objects/contract.md#write-set-transactions)).
The items of this page are thread slots, keyed by their pool and slot, and
the scheduler record of the CPU, one item keyed by its CPU. That kind of
key is this component's, as the objects component leaves the items of the
composing components to their contracts, like the queue links of other
components; with more than one CPU, an entry stages only the scheduler
record of the executing CPU. The composer completes the checks of every
entry that it composes before its first write; afterwards only
`WriteSetFull` of `stage`, which a write set within $W$ = 64 items never
meets, and the fault-injection points of test builds can stop it, and
either discards the buffer and leaves the state from before the operation.

| Entry | Checks before the first write | Write set of this page |
| --- | --- | --- |
| `validate_parameters` | The constraints of the time slice | Nothing: a function of values |
| `RunQueues::new` | None | Nothing: it gives the empty record with the time slice, which the boot wiring stores before any token exists |
| `admit` | The references, the state new, the class and the ceiling; the composer adds those of `ledger::admit` | At most 3: the slot of the new thread, the slot of the last thread of its queue, the scheduler record; with the items of `ledger::admit` |
| `enqueue` | The reference, the state blocked | At most 3: the slot of the thread, the slot of the last thread of its queue, the scheduler record |
| `choose` | No dispatch | At most 3: the slot of the chosen thread, the slot of the thread before it in its queue when it is not the first, the scheduler record; 1, the scheduler record, when the CPU is idle |
| `preempt` | A dispatch at or after its deadline, or the reschedule flag | At most 3: the slot of the thread, the slot of the last thread of its queue when it joins the tail, the scheduler record; with the items of `ledger::charge` |
| `yield_now` | A dispatch | At most 3, as `preempt`; with the items of `ledger::charge` |
| `block` | A dispatch | 2: the slot of the thread and the scheduler record; with the items of `ledger::charge` |
| `remove` | The reference, a state other than new and removed | The current thread: 2, its slot and the scheduler record, with the items of `ledger::charge`; a ready thread: at most 3, its slot, the slot of the thread before it in its queue and the scheduler record; a blocked thread: 1, its slot |
| `requeue` | The reference, the state ready or running | A ready thread: at most 4, its slot, the slot of the thread before it in its old queue, the slot of the last thread of its new queue and the scheduler record; the current thread: 2, its slot and the scheduler record, with the items of `ledger::charge` |

- `validate_parameters` and `RunQueues::new` run once at boot and cannot
  fail after their checks; the other entries cannot fail after theirs.
- Reads that decide the effect of an entry, not whether it fails, cannot
  fail: the credit of each thread that `choose` walks past; the credit
  after the charge, on the copies that `ledger::charge` has changed, which
  decides where `preempt` puts its thread; the credit that decides the
  reschedule flag; and the walk of a run queue to the thread before
  another.
- An operation that composes several entries of this page with those of
  other components, such as the return of a timer interrupt with
  `enqueue`, `preempt` and `choose`, keeps its whole write set within $W$;
  each settlement of a wait before it is a transaction of its own, as the
  waits component states.

## Work bounds

- `validate_parameters` converts two values, the time slice and the
  period, and makes two comparisons; `RunQueues::new` sets `PRIORITIES`
  queues empty and stores the time slice.
- `admit` resolves two references, reads the classes of the creator and of
  the thread and writes 3 items.
- `enqueue` resolves one reference, reads the credit of the thread once and
  writes 3 items.
- `choose` walks at most `PRIORITIES` = 3 run queues, and within them reads
  the credit of at most the threads that the run queues of the CPU hold,
  at most the thread capacity of the capacity record of the objects
  component; it reads the end of the period once and writes at most 3
  items. The walk is the only loop of the entry that the thread capacity
  bounds.
- `preempt` and `yield_now` make one charge and write at most 3 items;
  `block` one charge and 2 items.
- `remove` and `requeue` of a ready thread walk one run queue to the thread
  before it, at most the thread capacity, and write at most 3 and 4 items;
  of the current thread they make one charge and write 2 items.
- Each `ledger::charge` and `ledger::available` that these entries make is
  bounded by the [work bounds](../budget-ledger/contract.md#work-bounds) of
  the budget-ledger component, in a fixed number of steps.
- The component has no long operation: every entry runs to its end, and no
  progress is stored between two calls. The constants are `PRIORITIES` = 3
  and $W$ = 64 of the objects contract.

## Determinism

- **Requests.** Requests that contend for the scheduler record of a CPU take
  effect in the order in which they enter the kernel.
- **Run queues.** Each class has one FIFO run queue on each CPU. A thread
  that becomes ready, being woken, created, out of time slice or out of
  credit, or that yields, joins the tail; a thread preempted with time
  slice left and with credit returns to the head; selection takes the first
  thread with credit of the highest class that has one. This is the rule
  for queues of the
  [internal choices](../../../security.md#internal-choices) as
  [Run queues](#run-queues) reads it: a thread that resumes after
  replenishment does so from the place at the tail that it took when it
  stopped or was woken without credit, and a thread without credit joins
  the tail also with time slice left.
- **Several wake-ups.** When one transition makes several threads ready,
  the composer calls `enqueue` in the order of the internal choices: the
  threads woken by timeouts first, earliest deadline first with ties in
  registration order, then those woken by events in registration order; the
  run queues keep the order of the calls.
- **Expiry first.** The composer settles every wait whose deadline is not
  later than `now`, all deadlines that expire together included, before it
  calls `choose`, so the threads that they make ready take part in the
  selection of that transition.
- **Deadline and placement.** The deadline of a dispatch, the wake time of
  an idle CPU, the placement after a stop and the reschedule flag follow
  from the rules of [Selection and time slices](#selection-and-time-slices)
  and [Preemption](#preemption) and from the credit that the budget-ledger
  component gives.
- **Outputs.** Which thread runs, the order in which threads are woken and
  the CPU time that they use are outputs that scheduling decides, which the
  output sources of the
  [observable outputs](../../../security.md#observable-outputs) leave out.
- **Time.** The time of each transition, the arrival of the timer interrupt
  and so where a dispatch is preempted and how much it is charged are the
  time that [ND-01](../../../security.md#nd-01) of the register of
  [permitted nondeterminism](../../../security.md#permitted-nondeterminism)
  allows; for each value of it, the rules of this page fix the result.
- **Interrupts.** The transition in which the interrupt of a device makes a
  thread ready, through a notification, is the arrival of device interrupts
  that [ND-02](../../../security.md#nd-02) allows; for each, the rules of
  this page fix the result.
- **Several CPUs.** With more than one CPU, the order in which CPUs take the
  token of a thread that one of them makes ready on another, through the
  pending queue of that CPU, is the multicore interleaving of
  [ND-03](../../../security.md#nd-03); for each such order, the rules of
  this page fix the result.

The component leaves no other choice open.

## State fields

| Field | Class | Lock or owner | Linearization point | Publication |
| --- | --- | --- | --- | --- |
| The run queues of the scheduler record of each CPU: for each class its first and its last thread | Per-CPU | Its CPU, which lends the record by `&mut` to the entry that runs; another CPU asks for a change through the pending queue of the CPU, which that CPU applies | The write-back of the write set that changes it, on its CPU | `none`: its single owner never changes |
| The current thread of each CPU, with the start, the deadline and the context of its dispatch, and the timer deadline | Per-CPU | Its CPU, as above | The write-back of the write set that changes it, on its CPU | `none`: its single owner never changes |
| The reschedule flag of each CPU | Per-CPU | Its CPU, as above; another CPU sets it through the pending queue of the CPU | The write-back of the write set that changes it, on its CPU | `none`: its single owner never changes |
| The scheduling state of each thread, in its thread slot: its state, the class of the queue that holds it, its link in that queue and its time slice left | Per-thread | The CPU that runs the thread, the CPU whose run queue holds it while it is ready, or the object that it waits on while it is blocked | The write-back of the write set that changes it, under the token of its owner | At a handover: by the release of the token of the object whose completion makes it ready, or through the pending queue of the CPU that it goes to |
| The time slice in ticks of the scheduler record of each CPU | Per-CPU, read-only after boot | Its CPU, which `RunQueues::new` builds the record for before any entry from EL0 | The return of `RunQueues::new` | `none`: its single owner never changes |

The scheduler record is a compound record whose fields are classified one by
one; it lives in the per-CPU record of the architecture crate, so this page
adds no allocation to the storage carved at boot. The budget ledger of each
CPU is per-CPU as well, except its lending and cross-CPU settlement fields,
which are shared; its fields, the budget records in the thread slots with
the class and the effective class of each thread among them, are in the
[State fields](../budget-ledger/contract.md#state-fields) of the
budget-ledger contract. The slots of the thread pool and their counts are
fields of the
[objects](../../objects-capabilities/objects/contract.md#state-fields)
component. With one CPU, the executing CPU holds every token and the
pending queues are empty; no lock order is stated here.

## Testing obligations

- The host tests of the module `scheduler` (planned) replay every vector of
  [Legacy test vectors](#legacy-test-vectors) whose entry is on this page,
  with its expected output, and the vector `objects-13` of the
  [objects contract](../../objects-capabilities/objects/contract.md#legacy-test-vectors),
  whose rule is on this page, and write their results
  ([host results](../../../formal-verification.md#host-results)); the cases
  whose entry belongs to the budget-ledger component are replayed with its
  entries.
- Time and parameters: the host tests pass `now` and the platform parameters
  themselves, and the QEMU tests take their periods from the platform
  parameters of the board; no test depends on the speed of a CPU or on a
  fixed instruction count
  ([determinism and time](../../../conventions/testing.md#determinism-and-time)).
- The check of the time slice: a slice of 1 tick and one of 1 tick fewer
  than the period are accepted, and a slice of 0 microseconds and one of as
  many ticks as the period are `InvalidConfiguration`, for the frequencies
  of both boards and for 1 Hz. Once the values of each board are in the
  table, the values of the board pass `Ledger::new` and
  `validate_parameters`.
- Run queues: a property test drives admissions, enqueues, choices,
  preemptions with and without time slice left and with and without
  credit, yields, blocks, removals and requeues over the three classes, and
  checks after every write-back, against an independent model of one FIFO
  for each class, that the queues hold exactly the ready threads in the
  model's order and that `choose` takes the model's thread.
- Deadlines: each of the four limits of the deadline decides it in one case;
  an idle CPU gives the end of the period when a thread is throttled, the
  external deadline, the earlier of the two, and no wake time.
- Preemption: a thread of a higher class that a system call of the current
  thread makes ready runs at the return of that call; one that the expiry
  of a sleep makes ready, and one whose context a replenishment gives
  credit, run at the timer interrupt; an interrupt before the deadline
  without the reschedule flag leaves the dispatch as it was. A thread of a
  higher class made ready by a call whose caller then blocks leaves no
  reschedule flag for the next dispatch, and an entry on an idle CPU sets
  none.
- States: a second `admit` of a thread, also after its `remove` and before
  its slot is released, is `InvalidState`, and a new thread is in no run
  queue and is never chosen.
- Order of the composition: with `ledger::admit` composed in the order of
  [Errors](#errors), an admission of a thread that is not new is
  `InvalidConfiguration` with a budget of 0 and `InvalidState` with a
  class above the creator's.
- For each error of [Errors](#errors), a call that gives it leaves every
  field of the scheduler record and of the thread slots as before, compared
  field by field.
- Write sets: the largest write set of each entry of
  [Check and execute](#check-and-execute) is reached and stays within its
  count.
- QEMU tests, from EL0 on QEMU virt: a thread whose budget is exhausted does
  not run before its replenishment; a thread of a higher class that the
  timer makes ready preempts a thread of a lower class at the timer
  interrupt; and under full load, with ready threads of every class, a
  control thread runs on its credit in every period.
- The tests take their expected values from this page, from the vectors and
  from independent models, never from an earlier run of the code under test
  ([testing](../../../conventions/testing.md#independent-evidence)).

## Open obligations

The module `scheduler` has no `unsafe` code, no assembly and no MMIO. No
specification of it is planned in release 0.1, so each of its entries has
a row here, carried by the proof of object lifetimes, waits and sequential
composition, by release 0.2; a function of the module that is not an entry
of this page is covered by a row that the change that adds it writes. The
fairness of selection and the time bounds of scheduling are progress
obligations, which the change that adds the code records; the proof gate
is to register them as its progress obligations by release 0.2, and the
proof of SMP composition and progress is to prove them by release 0.3.
They are not rows of this table. The adapter that lends the scheduler
record of the executing CPU has a row as well
([rule 8](../../../conventions/provable-subset.md#8-no-interior-mutability));
finding the per-CPU record and masking interrupts is the row of the
[objects contract](../../objects-capabilities/objects/contract.md#open-obligations)
for that record.

| Obligation | Kind | Verified state | Carrier | Stage |
| --- | --- | --- | --- | --- |
| `kernel/src/scheduler.rs#validate_parameters` (planned) | `code` | - | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/src/scheduler.rs#RunQueues::new` (planned) | `code` | - | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/src/scheduler.rs#admit` (planned) | `code` | - | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/src/scheduler.rs#enqueue` (planned) | `code` | - | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/src/scheduler.rs#choose` (planned) | `code` | - | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/src/scheduler.rs#preempt` (planned) | `code` | - | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/src/scheduler.rs#yield_now` (planned) | `code` | - | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/src/scheduler.rs#block` (planned) | `code` | - | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/src/scheduler.rs#remove` (planned) | `code` | - | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/src/scheduler.rs#requeue` (planned) | `code` | - | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/arch/src/percpu.rs#Cpu::run_queues_mut` (planned) | `code` | - | The proof of the SMP primitives and of the concurrency backend | `0.2` |

## Legacy test vectors

The vectors are host tests of the prototype tree at
`prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`, 86 in all. Their
expected outputs are those that the test bodies assert, written in the
rules of this page. The vectors are not yet in a file of the repository, so
the section holds no `vectors` block.

| File | Vectors |
| --- | ---: |
| `src/scheduler/tests.rs` | 14 |
| `src/scheduler/tests/failures.rs` | 11 |
| `src/scheduler/tests/waits.rs` | 5 |
| `src/scheduler/budget/tests.rs` | 5 |
| `src/scheduler/budget/tests/failures.rs` | 8 |
| `src/scheduler/budget/tests/lifecycle.rs` | 6 |
| `src/scheduler/budget/tests/waits.rs` | 6 |
| `src/scheduler/budget/scopes/tests.rs` | 2 |
| `src/scheduler/budget/scopes/tests/admission.rs` | 8 |
| `src/scheduler/budget/scopes/tests/lifecycle.rs` | 4 |
| `src/objects/tests/activations.rs` | 7 |
| `src/abi/clock/tests.rs` | 10 |

- `src/scheduler` holds 114 tests. Each is a vector of exactly one of this
  page and the [budget-ledger](../budget-ledger/contract.md#legacy-test-vectors)
  component: a test whose assertions are mostly about charges,
  replenishment, debt, loans and their withdrawal is the budget-ledger
  component's, and one whose assertions are mostly about selection, time
  slices, preemption, blocking and readiness, classes and admission, or
  removal is this page's. The 69 here are the three files of the
  prototype's round robin and 39 tests of its budget scheduler; the other
  45, among them every test of `budget/credit.rs`,
  `budget/tests/accounting.rs`, `budget/tests/loans.rs`,
  `budget/tests/loan_scopes.rs` and `budget/scopes/tests/accounting.rs`, are
  the budget-ledger component's.
- `src/objects/tests/activations.rs` holds 42 test functions, 25 in its
  source, of which the macro `owner_regressions!` expands 17 twice, in its
  modules `legacy` and `parallel`. The
  [objects contract](../../objects-capabilities/objects/contract.md#legacy-test-vectors)
  freezes 20 of them. The 7 here test the activation serial and the claims,
  stops and receipts of activation: the 4 tests at the start of the file,
  the two functions of the serial in the expansion of `legacy` and the test
  `legacy_identity_precedes_every_active_receipt`. The other 15 test
  activation on several CPUs, the owners that are dying or dead, and
  rejections that another check of activation or a success decides, and are
  not vectors of this page.
- `src/abi/clock/tests.rs` holds the 10 tests of the prototype's query of
  the clock. Its module `src/abi/clock.rs` holds none.

A vector of this page is one test function. Its id is formed from the path
of its file below `src/`, without the directories and files named `tests`
and without `.rs`, with a hyphen between the parts and in place of each
underscore, and the position of the test among the tests of its file, from
1, also where the other tests of the file are the budget-ledger component's,
so that no id repeats between the two pages. The tests of `activations.rs`
keep the names of the objects contract: the tests outside the macro are
`activation-<n>`, from 1 in the order of the file, and the functions of the
expansion of `legacy` continue the numbers of `activation-legacy-<n>` of
that contract. The vector file is to hold one line for each case of a vector
through an entry, with the id `<vector>.<n>`, `n` counting those cases from
1 in the order of the test; a case that its row marks not applicable has no
line.

**Notation.** Times, budgets, slices, credits and deadlines are in ticks,
decimal. Threads are named by the letters of their tests, classes by their
names. The cases call `admit(t, class, budget)`, which the creator of the
row makes, R unless the row names another, with `ledger::admit`, the
amount `budget` of `class` and 0 of every other class, and the ceiling
equal to the class; `enqueue(t, now)`, `requeue(t, now)` and
`remove(t, now)`; `choose(now)`, or `choose(now, e)` with the external
deadline $e$; and `preempt(now)`, `yield_now(now)` and `block(now)` of the
current dispatch. The output of `choose` is `ok <thread> deadline=<d>`, or
`ok idle wake=<w>`, or `ok idle` without a wake time; the output of another
call is `ok` or `err=<error>`, with the error by its name on this page, on
the budget-ledger contract or on the objects contract. "t blocks at n in a
sleep until d" is a sleep of the waits component that blocks t, followed by
`block(n)`, after which $d$ is an external deadline of the CPU until the
sleep completes; "at d the sleep completes" is the composer's completion of
the sleep and `enqueue(t, d)`, before its `preempt` and `choose`. A wait
without a deadline is written the same way without "until". The CPU time of
a thread is `ledger::cpu_time` of the budget-ledger component.

**Fixtures.**

- **Budget fixture**, for the files below `src/scheduler/budget/`: the
  counter frequency 1,000,000 Hz, so a microsecond is a tick;
  `TIME_SLICE` 10, `REPLENISH_PERIOD` 100, `CONTROL_CAP` 20,
  `INTERACTIVE_CAP` 50, `BACKGROUND_CAP` 20 and `KERNEL_MARGIN` 10, the
  prototype's configuration with its 10 ticks of slack as the margin; the
  epoch of the ledger is 0. R is the root's thread, admitted at the epoch
  with every cap as its holdings by `ledger::admit` alone, as the
  budget-ledger component's vectors have it: no case calls `admit` of this
  page for R, so its scheduling state stays new, it is in no run queue and
  no case makes it ready. R admits every thread of the case, in the order
  of the test, and its holdings fall by what it admits. Where a row names
  other creators, each holds what the row states.
- **Round-robin fixture**, for `src/scheduler/tests.rs` and its `tests/`
  files: the prototype's round robin had no budgets, so the threads are in
  one class, interactive, and no budget, cap or end of a period limits a
  dispatch of the case: the frequency 1,000,000 Hz, `TIME_SLICE` as the
  test sets it, 5, 7 or 10, `REPLENISH_PERIOD` 1,000,000, `CONTROL_CAP`
  100,000, `INTERACTIVE_CAP` 800,000, `BACKGROUND_CAP` 50,000 and
  `KERNEL_MARGIN` 50,000, and R, as in the budget fixture, admits every
  thread with the class interactive and a budget of 100,000. The
  prototype's capacity of its queue does not apply.
- **Activation fixture**: as the row of each test states, with the tables of
  the objects contract.
- **Clock fixture**: the prototype's clock of the frequency 25 with its last
  sample 10; this page has no clock.

**Behaviour changes.** These rules differ from the prototype:

- The prototype had two schedulers, a round robin without budgets and a
  budget scheduler; here one scheduler does both, and the vectors of the
  round robin run in one class with budgets that do not limit them.
- A thread stopped with time slice left and with credit keeps the rest of
  its slice and returns to the head of its queue, where the prototype gave
  every dispatch a whole quantum and moved its round robin past the stopped
  thread: the outputs of `scheduler-3` and `scheduler-budget-waits-4`
  change.
- The stops of a dispatch act on the current dispatch, and a preemption
  needs the deadline or the reschedule flag; the prototype's stop of a
  named thread with a reason, its refusal of an early preemption
  (`InvalidDeadline`) and its stops of threads that do not run do not apply.
- This page has no terminal state: `remove` takes a thread out in any state,
  and the terminal states with their retention until reaping are the
  lifecycle component's.
- This page holds no sleep and no deadline of a thread: sleeps are waits of
  the waits component, the earliest deadline is the external deadline of
  `choose`, and a blocked thread becomes ready only by `enqueue`, whatever
  it waits for.
- A thread can be made ready, admitted or removed while another runs, where
  the prototype refused it (`Busy`).
- The scheduler keeps no counts of dispatches, preemptions, yields, sleeps,
  waits, wake-ups, throttles or overruns, and its read entries are no
  snapshots: the assertions on these counts are dropped, and the vectors of
  their overflow do not apply. The CPU time is the budget-ledger
  component's, which keeps no count of replenishments either.
- Time is an input that never decreases and stays below $2^{63}$ within a
  boot; the vectors of time that goes backwards and of times near $2^{64}$
  do not apply.
- The scheduler has no capacity and no registry, and takes references, not
  handles: the prototype's duplicate admission, capacity, unknown thread,
  restricted handles and threads of other pools do not apply as written.
- Admission is part of the creation of a thread and takes its budget, and
  its holdings of the classes below its own, from the holdings of its
  creator, whose class may be above its own, where the prototype's child
  scopes took the class of their parent; there are no scopes, so the
  vectors of scopes keep only their cases of admission, and a budget
  beyond a holding is refused without the prototype's sums and their
  `Overflow`.
- The platform parameters are given in microseconds and converted at boot;
  the prototype's quantum is the time slice of this page, its epoch the
  start of the periods of the budget-ledger component, the time of the
  boot, and its capacity no parameter at all.
- `yield` is an operation of the production range of the ABI inventory,
  not the prototype's diagnostic encoding by `SVC` immediates.
- There is no activation and no activation serial: the current thread of a
  CPU is the one that `choose` takes.
- There is no query of the clock: EL0 reads `CNTVCT_EL0` and `CNTFRQ_EL0`.

### `src/scheduler/tests.rs`

14 vectors, with the round-robin fixture.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `scheduler-1` | 28 | `two_noncooperative_peers_rotate_on_each_expired_quantum` | `TIME_SLICE` 5; a and b admitted. At 0, 5, 10, 15, 20 and 25, `choose` gives a, b, a, b, a and b in turn, each with the deadline 5 later, and `preempt` at that deadline, with no time slice left, puts the thread at the tail. The CPU time of each is 15. The prototype's counts of 3 dispatches and 3 preemptions of each are not kept | `admit`, `choose`, `preempt` |
| `scheduler-2` | 59 | `three_peers_rotate_after_short_and_zero_duration_yields` | `TIME_SLICE` 10; a, b and c admitted. `choose(0)` gives a; `yield_now(1)`; `choose(1)` gives b; `yield_now(1)`, after no tick; `choose(1)` gives c; `yield_now(4)`; `choose(4)` gives a. The CPU times of a, b and c are 1, 0 and 3 | `admit`, `choose`, `yield_now` |
| `scheduler-3` | 78 | `a_ready_thread_prevents_idle_even_while_another_thread_sleeps` | `TIME_SLICE` 10; a and b admitted. `choose(0)` gives a with the deadline 10; a blocks at 1 in a sleep until 7; `choose(1, 7)` gives b with the deadline 7. At 7 the sleep completes and a joins the tail; `preempt(7)` puts b, with 4 ticks of its slice left, at the head; `choose(7)` gives b with the deadline 11; `preempt(11)` puts b at the tail; `choose(11)` gives a with the deadline 21. The CPU time of b is 10. The prototype ran a at 7, with the deadline 17, and charged b 6; its count of the wake-ups of a is not kept | `admit`, `choose`, `block`, `enqueue`, `preempt` |
| `scheduler-4` | 106 | `all_sleepers_idle_until_earliest_deadline_and_wake_once` | `TIME_SLICE` 10; a and b admitted. `choose(0)` gives a; a blocks at 2 in a sleep until 20; `choose(2, 20)` gives b with the deadline 12; b blocks at 3 in a sleep until 10; `choose(3, 10)` and `choose(9, 10)` give `ok idle wake=10`, with both threads blocked. At 10 the sleep of b completes, and `choose(10, 20)` gives b with the deadline 20; b exits at 11, `remove(b, 11)`; `choose(11, 20)` gives `ok idle wake=20`; at 20 the sleep of a completes, and `choose(20)` gives a. The prototype's counts of one sleep and one wake-up of each are not kept | `admit`, `choose`, `block`, `enqueue`, `remove` |
| `scheduler-5` | 131 | `simultaneous_expiration_wakes_every_peer_before_cyclic_selection` | `TIME_SLICE` 10; a, b and c admitted. `choose(0)` gives a; a blocks at 1 in a sleep until 10; `choose(1, 10)` gives b with the deadline 10; b blocks at 2 in a sleep until 10; `choose(2, 10)` gives c; c blocks at 3 in a sleep until 20; `choose(9, 10)` gives `ok idle wake=10`. At 10 both sleeps until 10 complete, before `choose`, a first by the order of registration: a and then b join the tail; `choose(10, 20)` gives a, and b is ready; `yield_now(11)`; `choose(11, 20)` gives b with the deadline 20 | `admit`, `choose`, `block`, `enqueue`, `yield_now` |
| `scheduler-6` | 162 | `past_and_immediate_sleep_requests_do_not_block_or_create_phantom_wakes` | `TIME_SLICE` 10; a admitted; `choose(10)` gives a with the deadline 20. A sleep of a until 0 at 10, and one until 11 at 11, each return at once without blocking, as the waits component's `sleep` states: there is no `block`, a keeps its dispatch from 10 with the deadline 20, and no external deadline arises. The prototype's counts of 2 sleeps and 0 wake-ups are not kept | `choose`; the waits component, for the sleep |
| `scheduler-7` | 177 | `ready_and_sleeping_termination_remove_waits_and_keep_accounting` | `TIME_SLICE` 10; a, b and c admitted. `remove(c, 0)` of the ready c: ok, it leaves its queue. `choose(0)` gives a; a blocks at 3 in a sleep until 30; `choose(3, 30)` gives b with the deadline 13; `remove(a, 3)` of the blocked a: ok, its sleep completed by the destruction in the waits component, which leaves no external deadline. b runs, with the start 3 and the deadline 13. The CPU times of a and c are 3 and 0. The prototype's terminal state between termination and removal is the lifecycle component's | `admit`, `remove`, `choose`, `block` |
| `scheduler-8` | 207 | `terminal_outcomes_are_retained_until_explicit_removal` | Three cases, an exit, a fault and a kill of a: a admitted; `choose(0)` gives a; at 4 the destruction of its process removes it, `remove(a, 4)`: ok, with 4 ticks charged, so its CPU time is 4; `choose(5)` gives `ok idle`; a second `remove(a, 5)` is `err=InvalidState`. The terminal states, the exit code and their retention until reaping are the lifecycle component's | `admit`, `choose`, `remove` |
| `scheduler-9` | 229 | `elapsed_accounting_includes_overrun_but_excludes_time_between_dispatches` | `TIME_SLICE` 7; a admitted. `choose(100)` gives a with the deadline 107; `preempt(115)`, a late stop, charges 15 ticks and puts a at the tail; `choose(215)` gives a with the deadline 222; `yield_now(216)` charges 1 tick. The CPU time of a is 15 after the first stop and 16 after the second | `admit`, `choose`, `preempt`, `yield_now` |
| `scheduler-10` | 252 | `direct_syscall_time_cannot_reset_the_active_quantum` | `TIME_SLICE` 10; a and b admitted. `choose(100)` gives a with the deadline 110. The system calls of a at 101, 104 and 109 return to a without `choose`, and its dispatch keeps the start 100 and the deadline 110; `choose` while it runs, at 101, 104, 109 and 112, is each `err=InvalidState` and changes nothing; `preempt(112)` charges 12 ticks; `choose(112)` gives b with the deadline 122 | `admit`, `choose`, `preempt` |
| `scheduler-11` | 280 | `duplicate_identity_is_rejected_even_with_restricted_rights` | a admitted: a second `admit(a, interactive, 1)` is `err=InvalidState` and changes nothing. The prototype's handle of a with restricted rights does not apply, since a reference carries no rights, and its capacity of two entries (`Capacity`) does not apply | `admit` |
| `scheduler-12` | 297 | `reused_object_and_policy_slots_do_not_match_old_generations` | The thread old is admitted and removed, and its slot is released; fresh occupies the slot at the next generation and is admitted. `remove` and `enqueue` of the reference of old are each `err=StaleReference` and change nothing; `choose(0)` gives fresh. The prototype's stop of old by its handle does not apply: `preempt` acts on the current dispatch, that of fresh | `admit`, `remove`, `enqueue`, `choose`; `ObjectTable::resolve` of the objects component |
| `scheduler-13` | 326 | `different_pools_with_matching_slots_and_generations_remain_distinct` | Not applicable: a kernel has one thread pool, so the threads that the run queues hold never share a slot, and a reference of another pool is `err=WrongPool` of `ObjectTable::resolve`, which the vectors of the objects contract test | The objects component |
| `scheduler-14` | 343 | `snapshot_partitions_all_admitted_slots_without_counting_removed_entries` | `TIME_SLICE` 10; a, b, c and d admitted; `remove(d, 0)`; `choose(0)` gives a; a blocks at 1 in a sleep until 50; `choose(1, 50)` gives b. Then a is blocked, b running, c ready and d removed, and the run queue holds c alone. The prototype's snapshot, its count of terminal entries until their removal and its capacity do not apply | `admit`, `remove`, `choose`, `block` |

### `src/scheduler/tests/failures.rs`

11 vectors, with the round-robin fixture.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `scheduler-failures-1` | 4 | `empty_capacity_and_zero_quantum_are_rejected` | `validate_parameters` with a `TIME_SLICE` of 0: `err=InvalidConfiguration`. The prototype's capacity of 0 does not apply | `validate_parameters` |
| `scheduler-failures-2` | 16 | `backwards_clock_is_rejected_even_when_idle_without_any_state_change` | Not applicable: `now` never decreases within a boot, a premise of [Platform parameters and time](#platform-parameters-and-time), so a `choose` or a stop at an earlier time than the last does not occur | None: a premise |
| `scheduler-failures-3` | 36 | `a_wrong_or_repeated_stop_cannot_advance_clock_or_charge_another_thread` | `TIME_SLICE` 10; a and b admitted. `choose(10)` gives a; `yield_now(11)`: ok; a second `yield_now(12)`, with no dispatch, is `err=InvalidState` and changes nothing; `choose(12)` gives b. The prototype's stops of b, which did not run (`InvalidState`), and of a thread unknown to it (`UnknownThread`) do not apply: the stops act on the current dispatch | `admit`, `choose`, `yield_now` |
| `scheduler-failures-4` | 63 | `running_removal_and_termination_are_rejected_without_losing_ownership` | Three cases, each with a admitted: `remove(a, 0)` of the ready a; `remove(a, 1)` with a running from 0, which charges 1 tick; and `remove(a, 2)` of a, which blocked at 1 in a sleep until 20: each ok, and a second `remove` of a is each `err=InvalidState` and changes nothing. The prototype's refusals of the removal of a ready or sleeping thread (`InvalidState`) and of the removal and termination of a running one (`Busy`) do not apply | `admit`, `choose`, `block`, `remove` |
| `scheduler-failures-5` | 84 | `an_early_preemption_does_not_mutate_the_running_quantum` | `TIME_SLICE` 10; a admitted. `choose(10)` gives a with the deadline 20; `preempt(19)`, before the deadline and without the reschedule flag, is `err=InvalidState` and changes nothing, where the prototype gave `InvalidDeadline`; `preempt(20)` charges 10 ticks | `admit`, `choose`, `preempt` |
| `scheduler-failures-6` | 105 | `deadline_overflow_does_not_wake_sleepers_or_advance_clock` | Not applicable: `now` stays below $2^{63}$ within a boot, so a `choose` at $2^{64} - 6$ does not occur; a sleep until $2^{64} - 7$ is a deadline that the waits component only compares | None: a premise |
| `scheduler-failures-7` | 122 | `dispatch_count_overflow_is_atomic` | Not applicable: the scheduler keeps no count of dispatches | None |
| `scheduler-failures-8` | 133 | `waking_any_sleeper_overflow_rejects_the_entire_dispatch` | Not applicable: the scheduler keeps no count of wake-ups | None |
| `scheduler-failures-9` | 151 | `elapsed_tick_overflow_keeps_thread_running_without_partial_charge` | Not applicable: the scheduler keeps no count of ticks; the CPU time of the budget-ledger component counts ticks of one boot, below $2^{63}$ | None |
| `scheduler-failures-10` | 163 | `stop_counter_overflow_does_not_commit_elapsed_ticks_or_clock` | Not applicable: the scheduler keeps no counts of preemptions, yields or sleeps | None |
| `scheduler-failures-11` | 183 | `idle_at_maximum_tick_does_not_wrap_or_require_a_quantum` | Not applicable: `now` stays below $2^{63}$ and never decreases within a boot, so neither a `choose` at $2^{64} - 1$ nor one at 0 after it occurs | None: a premise |

### `src/scheduler/tests/waits.rs`

5 vectors, with the round-robin fixture.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `scheduler-waits-1` | 4 | `external_wait_never_auto_wakes_and_retains_charged_service` | `TIME_SLICE` 10; a and b admitted. `choose(0)` gives a; a blocks at 3 in a wait; `choose(1000)` gives b; b blocks at 1001 in a wait; `choose(2000)` gives `ok idle`, with no wake time: this page never makes a blocked thread ready by itself. `enqueue(a, 2000)`; `choose(2000)` gives a, whose CPU time is 3. The prototype's counts of waits, sleeps and wake-ups are not kept | `admit`, `choose`, `block`, `enqueue` |
| `scheduler-waits-2` | 27 | `repeated_wake_and_sleep_wake_are_rejected_without_mutation` | `TIME_SLICE` 10; a admitted. `enqueue(a, 1)` of the ready a is `err=InvalidState` and changes nothing. `choose(1)` gives a; a blocks at 2 in a sleep until 20; at 20 the sleep completes, `enqueue(a, 20)`: ok; `choose(20)` gives a; a blocks at 21 in a wait; `enqueue(a, 22)`: ok; a second `enqueue(a, 23)` is `err=InvalidState` and changes nothing. This page does not tell a sleep from another wait, and its composer calls `enqueue` only once the waits component has completed the sleep, so the prototype's refusal of a wake during a sleep (`InvalidState`) is no rule of this page; its time that goes backwards does not apply | `admit`, `choose`, `block`, `enqueue` |
| `scheduler-waits-3` | 51 | `active_peer_prevents_external_wake_but_waiting_termination_is_allowed` | `TIME_SLICE` 10; a and b admitted; `choose(0)` gives a; a blocks at 1 in a wait; `choose(1)` gives b. Two cases: `enqueue(a, 1)` while b runs, ok, a joins the tail, where the prototype refused it (`Busy`); or `remove(a, 1)` of the blocked a, ok, its wait completed by the destruction in the waits component, and then `enqueue(a, 2)` is `err=InvalidState`. The prototype's count of waits is not kept | `admit`, `choose`, `block`, `enqueue`, `remove` |
| `scheduler-waits-4` | 69 | `wait_and_wake_counter_overflow_are_transactional` | Not applicable: the scheduler keeps no counts of waits and wake-ups | None |
| `scheduler-waits-5` | 87 | `removed_generation_cannot_complete_a_new_external_wait` | `TIME_SLICE` 10; old admitted; `choose(0)` gives old; old blocks at 1 in a wait; `remove(old, 1)`; its slot is released, and fresh occupies it at the next generation and is admitted; `choose(1)` gives fresh; fresh blocks at 2 in a wait. `enqueue` of the reference of old at 3 is `err=StaleReference` and changes nothing; `enqueue(fresh, 3)`: ok | `admit`, `choose`, `block`, `remove`, `enqueue`; `ObjectTable::resolve` of the objects component |

### `src/scheduler/budget/tests.rs`

5 vectors, with the budget fixture; the other three tests of the file are
the budget-ledger component's.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `scheduler-budget-1` | 32 | `strict_classes_preserve_background_capacity_and_nominal_kernel_slack` | b (background, 20), i (interactive, 50) and c (control, 20) admitted in this order. At 0, 10, ..., 80, `choose` gives c twice, i five times and b twice, each with the deadline 10 later, and `preempt` at each deadline; a thread whose credit the stop ends joins the tail. `choose(90)` gives `ok idle wake=100`, the end of the period, every thread being throttled; the CPU times of c, i and b are 20, 50 and 20; `choose(100)`, after the replenishment, gives c. The prototype's count of 3 throttled threads is the three throttled threads here, and its counts of replenishments are not kept | `admit`, `choose`, `preempt`; `ledger::available` and `ledger::charge` of the budget-ledger component |
| `scheduler-budget-2` | 79 | `peers_rotate_independently_of_lower_class_cursor` | low (background, 20), a and b (interactive, 25 each) admitted. From 0, each `choose` gives a thread and each `preempt` comes at its deadline: a until 10, b until 20, a until 30, b until 40, a until 45, its credit then 0, b until 50, and low until 60 | `admit`, `choose`, `preempt` |
| `scheduler-budget-3` | 104 | `sleeping_control_thread_preempts_lower_class_at_its_wake_deadline` | high (control, 20) and low (background, 20) admitted. `choose(0)` gives high; high blocks at 2 in a sleep until 7; `choose(2, 7)` gives low with the deadline 7. At 7 the sleep completes, and `enqueue` of high sets the reschedule flag; `preempt(7)` puts low, with 5 ticks of its slice left, at the head of its queue; `choose(7)` gives high, whose credit is 18. The prototype's count of the wake-ups of high is not kept | `admit`, `choose`, `block`, `enqueue`, `preempt` |
| `scheduler-budget-5` | 140 | `quantum_budget_and_period_boundaries_independently_limit_dispatch` | a (control, 13) admitted. `choose(0)` gives the deadline 10, the slice; `preempt(10)`; `choose(10)` gives 13, the credit; `preempt(13)`; `choose(197)` gives 200, the end of the period; `preempt(200)` leaves a with 7 ticks of its slice at the head. At 200 the remaining budget of a is 13 and its period starts at 200, as the budget-ledger component gives them | `admit`, `choose`, `preempt`; the budget-ledger component, for the budget |
| `scheduler-budget-7` | 168 | `zero_class_caps_disable_admission_without_disabling_other_classes` | The budget fixture with `CONTROL_CAP` 0, so R holds nothing of control: `admit(a, control, 1)` is `err=AdmissionRejected` of `ledger::admit`, the holding being 0, and changes nothing; `admit(a, background, 1)`: ok; `choose(0)` gives a with the deadline 1, its credit | `admit`, `choose`; `ledger::admit` of the budget-ledger component |

### `src/scheduler/budget/tests/failures.rs`

8 vectors, with the budget fixture; the other two tests of the file are the
budget-ledger component's.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `scheduler-budget-failures-1` | 4 | `invalid_configuration_and_sum_overflow_are_rejected` | The parameters of the fixture with one change each: `REPLENISH_PERIOD` 0, `err=InvalidConfiguration` of `Ledger::new`; `TIME_SLICE` 0, `err=InvalidConfiguration` of `validate_parameters`; `CONTROL_CAP` 30 or `BACKGROUND_CAP` 31, whose caps and margin add up to 110 or 111 against the period of 100, each `err=InvalidConfiguration` of `Ledger::new`. A `CONTROL_CAP` of $2^{64} - 1$, whose ticks fit 64 bits at this frequency, gives caps and a margin beyond the period: `err=InvalidConfiguration` of `Ledger::new`, where the prototype's sum overflowed (`Overflow`). The prototype's capacity of 0 does not apply, and neither does its epoch of $2^{64} - 1$: the epoch is the time of the boot, `now` of `Ledger::new`, below $2^{63}$ by the premises | `validate_parameters`; `Ledger::new` of the budget-ledger component |
| `scheduler-budget-failures-2` | 49 | `zero_budget_capacity_and_admission_overflow_leave_no_reservation` | `admit(a, control, 0)` is `err=InvalidConfiguration` of `ledger::admit` and changes nothing; `admit(a, control, 10)`: ok; `admit(b, control, 18446744073709551615)`, beyond the 10 left of R's holding of control, is `err=AdmissionRejected` of `ledger::admit`, where the prototype's sum overflowed (`Overflow`), and changes nothing. The prototype's capacity of one entry (`Capacity`) does not apply | `admit`; `ledger::admit` of the budget-ledger component |
| `scheduler-budget-failures-3` | 69 | `backward_time_is_rejected_during_idle_and_execution` | Not applicable: `now` never decreases within a boot, a premise | None: a premise |
| `scheduler-budget-failures-4` | 90 | `direct_syscalls_cannot_refresh_an_active_quantum_or_period` | a (control, 20) admitted; `choose(0)` gives a with the deadline 10. `choose` while its dispatch runs, at 1, 9, 10, 100 and 10,000, is each `err=InvalidState` and changes nothing: a system call that returns to a calls no `choose` and keeps the start, the deadline and the context of the dispatch | `admit`, `choose` |
| `scheduler-budget-failures-5` | 103 | `early_wrong_and_repeated_stops_cannot_charge_any_account` | a (control, 20) and b (background, 20) admitted; `choose(0)` gives a with the deadline 10. `preempt(9)`, before the deadline and without the reschedule flag, is `err=InvalidState`, where the prototype gave `InvalidDeadline`; `preempt(10)`: ok; a second `preempt(100)`, with no dispatch, is `err=InvalidState`; each refusal changes nothing. The prototype's stops of b, which did not run, and of an unknown thread do not apply: the stops act on the current dispatch | `admit`, `choose`, `preempt` |
| `scheduler-budget-failures-6` | 130 | `active_removal_and_termination_preserve_ownership_and_reservations` | a (control, 20) admitted; `choose(0)` gives a; its kill at 3 is `remove(a, 3)`: ok, with 3 ticks charged; a second `remove(a, 3)` is `err=InvalidState` and changes nothing. The removal of a ready thread is ok as well, where the prototype refused it (`InvalidState`), and the removal of a running one stops its dispatch, where the prototype refused it (`Busy`) | `admit`, `choose`, `remove` |
| `scheduler-budget-failures-9` | 181 | `counter_overflow_cannot_partially_wake_or_replenish_peers` | Not applicable: the scheduler keeps no counts of wake-ups and dispatches, and the budget-ledger component none of replenishments | None |
| `scheduler-budget-failures-10` | 207 | `reason_counter_overflow_cannot_commit_sleep_or_yield_charges` | Not applicable: the scheduler keeps no counts of yields and sleeps | None |

### `src/scheduler/budget/tests/lifecycle.rs`

6 vectors, with the budget fixture; the other two tests of the file are the
budget-ledger component's.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `scheduler-budget-lifecycle-1` | 4 | `admission_sums_class_reservations_and_failure_keeps_all_state` | `admit(a, control, 15)`: ok; `admit(b, control, 6)`, with 5 left of R's holding of control, is `err=AdmissionRejected` of `ledger::admit` and changes nothing; `admit(b, control, 5)`: ok, which leaves R no control; `admit(c, control, 1)` is `err=AdmissionRejected`; `admit(c, background, 20)`: ok | `admit`; `ledger::admit` of the budget-ledger component |
| `scheduler-budget-lifecycle-2` | 24 | `rights_aliases_cannot_duplicate_an_admission_or_change_its_class` | a (control, 20) admitted: a second `admit(a, interactive, 1)` is `err=InvalidState` and changes nothing, and the class of a stays control. The prototype's handle of a with only the right to observe does not apply: a reference carries no rights | `admit` |
| `scheduler-budget-lifecycle-5` | 80 | `ready_and_sleeping_termination_remove_waits_without_spending_changes` | a and b (interactive, 25 each) admitted; `choose(0)` gives a; a blocks at 3 in a sleep until 50; `remove(a, 3)` of the blocked a, whose sleep the destruction completes, and `remove(b, 3)` of the ready b: ok, after which no thread is in a run queue and no external deadline remains. The CPU times of a and b are 3 and 0, and the interactive class keeps its spending, 47 left of its cap, as the budget-ledger component gives it. The prototype's terminal states until removal and its snapshot do not apply | `admit`, `choose`, `block`, `remove`; the budget-ledger component, for the class |
| `scheduler-budget-lifecycle-6` | 101 | `stale_generation_cannot_change_reused_policy_slot` | old (control, 20) admitted and removed, and its slot released; fresh occupies the slot at the next generation and is admitted with control 20. `remove` of the reference of old is `err=StaleReference` and changes nothing; `choose(0)` gives fresh. The prototype's query, termination and stop of old by its handle do not apply | `admit`, `remove`, `choose`; `ObjectTable::resolve` of the objects component |
| `scheduler-budget-lifecycle-7` | 128 | `matching_slots_in_different_pools_are_distinct` | Not applicable: a kernel has one thread pool, so the threads that the run queues hold never share a slot, and a reference of another pool is `err=WrongPool` of `ObjectTable::resolve`, which the vectors of the objects contract test | The objects component |
| `scheduler-budget-lifecycle-8` | 141 | `all_sleepers_are_woken_before_throttle_and_priority_selection` | a (control, 20) and b (background, 20) admitted. `choose(0)` gives a with the deadline 10; a blocks at 20, a late stop, in a sleep until 50, with 20 ticks charged, which leaves it no credit; `choose(20, 50)` gives b with the deadline 30; b blocks at 25 in a sleep until 50; `choose(25, 50)` gives `ok idle wake=50`. At 50 both sleeps complete before `choose`, a first by the order of registration; `choose(50)` passes over a, throttled until 100, and gives b. The prototype's counts of throttles and wake-ups are not kept | `admit`, `choose`, `block`, `enqueue` |

### `src/scheduler/budget/tests/waits.rs`

6 vectors, with the budget fixture; the first three tests of the file are
the budget-ledger component's.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `scheduler-budget-waits-4` | 65 | `external_event_clamps_running_deadline_and_allows_preemption_at_event` | a (control, 20) admitted. `choose(0, 3)` gives a with the deadline 3, its dispatch starting at 0; `preempt(2)` is `err=InvalidState` and changes nothing, where the prototype gave `InvalidDeadline`; `preempt(3)`: ok, with 3 ticks charged, so the credit of a is 17, and a, with 7 ticks of its slice left, returns to the head; `choose(3, 99)` gives a with the deadline 10, where the prototype gave a new quantum and the deadline 13. The prototype's count of overruns is not kept | `admit`, `choose`, `preempt` |
| `scheduler-budget-waits-5` | 94 | `external_deadline_and_sleep_period_and_credit_use_the_earliest_limit` | a (control, 20) and b (background, 5) admitted. `choose(0)` gives a; a blocks at 1 in a sleep until 8; `choose(1, 4)` gives b with the deadline 4, the external deadline; `preempt(4)` leaves b at the head; `choose(4, 7)` gives b with the deadline 6, its credit; `preempt(6)` leaves b throttled at the tail; `choose(6, 7)` gives `ok idle wake=7`; at 8 the sleep completes, and `choose(8, 200)` gives a with the deadline 18, its slice; a blocks at 18 in a wait; `choose(199, 205)` gives b with the deadline 200, the end of the period | `admit`, `choose`, `block`, `enqueue`, `preempt` |
| `scheduler-budget-waits-6` | 132 | `invalid_external_deadline_never_advances_period_wakes_sleepers_or_moves_cursor` | a (control, 20) admitted; `choose(0)` gives a; a blocks at 1 in a sleep until 100. At 100 the composer completes the sleep before `choose`, so the external deadlines 0, 99 and 100, not later than `now`, which the prototype refused (`InvalidDeadline`), are never passed; `choose(100, 101)` gives a with the deadline 101; `choose(100, 102)` while its dispatch runs is `err=InvalidState` and changes nothing | `admit`, `choose`, `block`, `enqueue` |
| `scheduler-budget-waits-7` | 160 | `failed_external_wakes_are_atomic_including_overflow_after_period_advancement` | a (control, 20) and b (background, 20) admitted. `enqueue(a, 0)` of the ready a, and `enqueue(u, 0)` of a thread u that is not admitted, are each `err=InvalidState` and change nothing. `choose(0)` gives a; a blocks at 1 in a wait; `choose(1)` gives b; `enqueue(a, 1)` while b runs: ok, a joins the tail of control and the reschedule flag is set, where the prototype refused the wake (`Busy`); a second `enqueue(a, 2)` is `err=InvalidState` and changes nothing. The prototype's time that goes backwards and its count of wake-ups do not apply | `admit`, `choose`, `block`, `enqueue` |
| `scheduler-budget-waits-8` | 191 | `waiting_termination_releases_reservation_only_on_remove_without_erasing_debt` | a (control, 20) admitted; `choose(0)` gives a; a blocks at 45 in a wait, a late stop, with 45 ticks charged, which leaves a debt of 25 in its record and in the control class. `remove(a, 45)` of the blocked a: ok; `enqueue(a, 100)` afterwards is `err=InvalidState`. The class keeps the debt of 25, and the holding of a returns to R at its reaping, as the budget-ledger component gives them. The prototype's terminal state before removal and its count of waits do not apply | `admit`, `choose`, `block`, `remove`, `enqueue`; `ledger::release` of the budget-ledger component |
| `scheduler-budget-waits-9` | 209 | `waiting_stop_counter_overflow_does_not_charge_or_advance_periods` | Not applicable: the scheduler keeps no count of waits | None |

### `src/scheduler/budget/scopes/tests.rs`

2 vectors, with the budget fixture.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `scheduler-budget-scopes-1` | 36 | `zero_registry_and_missing_scope_capacity_are_rejected` | Not applicable: there are no scopes; the budget of a child is carved from its creator's holding when it is created. The prototype's registry identity of 0 and scope capacity below the thread capacity (`InvalidConfiguration`) and its refusal of an admission without a scope (`InvalidState`) do not exist | None |
| `scheduler-budget-scopes-2` | 53 | `scope_and_object_inspection_never_amplify_authority` | Not applicable here: that observation never gains control is a rule of the rights of the [capabilities](../../objects-capabilities/capabilities/contract.md#rights) component, whose vectors test it; the scopes and their receipts do not exist | The capabilities component |

### `src/scheduler/budget/scopes/tests/admission.rs`

8 vectors, with the budget fixture. The processes of a row are each created
with their thread, which the creator of the process admits; the
prototype's scope of a process is the holding of its thread.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `scheduler-budget-scopes-admission-1` | 4 | `nested_reservations_charge_the_class_once_and_inherit_priority` | R admits a with interactive 30; a admits b with interactive 20, and b admits c with interactive 10, each the thread of a new process: each ok, each new thread interactive, not above the class of its creator, and the interactive class has 30 admitted in all, since each nested admission carves its budget from its creator's holding, as the budget-ledger component gives it. The prototype's tree of scopes, with its reservations by scope and its count of scopes, does not apply | `admit`; `ledger::admit` of the budget-ledger component |
| `scheduler-budget-scopes-admission-2` | 27 | `actual_owner_rights_state_and_pool_are_checked_before_scope_creation` | Not applicable here: the right CREATE of the creator is a rule of the capabilities component, which the creation component checks; a reference of another pool is `err=WrongPool` of `ObjectTable::resolve`; and a terminated creator runs no thread, so it makes no creation, a state of the lifecycle component | The capabilities, creation and lifecycle components |
| `scheduler-budget-scopes-admission-3` | 56 | `a_process_can_own_only_one_scope_even_with_another_class_or_parent` | Not applicable: there are no scopes, and the budget of a process is the record of its one thread | None |
| `scheduler-budget-scopes-admission-4` | 76 | `admission_requires_ready_controlled_thread_from_the_exact_owner` | Admission is part of the creation of a thread, before it has run, so the new thread belongs to the process that the creation names, is neither running nor waiting, and is admitted once: a second `admit` of it is `err=InvalidState` and changes nothing. The prototype's thread of another owner (`OwnerMismatch`), handles with restricted rights (`PermissionDenied`) and admissions of a running or waiting thread (`InvalidState`) do not apply | `admit` |
| `scheduler-budget-scopes-admission-5` | 115 | `observer_and_control_receipts_enforce_separate_operations` | Not applicable: there are no scopes and no receipts of scopes | None |
| `scheduler-budget-scopes-admission-6` | 139 | `parent_and_class_excesses_do_not_consume_capacity_or_generations` | A creator P whose holding of control is 20 admits a thread with control 15: ok; then one with control 6, 5 being left: `err=AdmissionRejected`; one with control 18446744073709551615: `err=AdmissionRejected`, where the prototype's sums overflowed (`Overflow`); R, whose holding of control is 0 after P's 20, admits one with control 1: `err=AdmissionRejected`; each refusal, of `ledger::admit`, changes nothing | `admit`; `ledger::admit` of the budget-ledger component |
| `scheduler-budget-scopes-admission-7` | 172 | `zero_capacity_and_generation_errors_leave_all_reservations_unchanged` | An admission with the budget 0 is `err=InvalidConfiguration` of `ledger::admit` and changes nothing. The prototype's capacity of scopes (`ScopeCapacity`), its scope generations (`GenerationExhausted`) and its stale scope receipts (`StaleScope`) do not apply | `admit`; `ledger::admit` of the budget-ledger component |
| `scheduler-budget-scopes-admission-8` | 204 | `a_running_dispatch_prevents_every_tree_mutation_and_entry_removal` | Not applicable: every operation runs within the dispatch of its caller, whose interval the stop of the dispatch charges, so no admission or removal discards a charge, and the prototype's refusals during a dispatch (`Busy`) do not exist; `remove` of a ready thread while another runs is ok | `remove` |

### `src/scheduler/budget/scopes/tests/lifecycle.rs`

4 vectors, with the budget fixture and the processes of the previous
section; the other three tests of the file are the budget-ledger
component's.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `scheduler-budget-scopes-lifecycle-2` | 24 | `release_requires_no_children_no_bindings_and_no_spending` | One case: a and b (control, 10 each) admitted; `remove(a, 0)` and `remove(b, 0)` of the ready a and b: each ok, after which neither is in a run queue. The budget-ledger component returns their holdings to R when they are reaped. The prototype's release of scopes and its refusals while a scope has children, threads or spending (`InvalidState`) are not applicable, since there are no scopes, and have no line | `admit`, `remove`; `ledger::release` of the budget-ledger component |
| `scheduler-budget-scopes-lifecycle-4` | 73 | `foreign_scheduler_and_stale_scope_receipts_cannot_mutate_live_scopes` | Not applicable: each CPU has one scheduler record, and there are no scopes and no receipts (`WrongRegistry`, `StaleScope`) | None |
| `scheduler-budget-scopes-lifecycle-5` | 104 | `dead_and_reaped_owners_keep_accounting_but_cannot_admit_or_delegate` | t (control, 20) admitted; `choose(0)` gives t; t faults at 3, `remove(t, 3)`: ok, with 3 ticks charged, which leaves 17 of its budget. Its process, dying, runs no thread and makes no further creation, where the prototype refused one (`InvalidState`). The return of its holding at its reaping and the spending that its class keeps are the budget-ledger component's, where the prototype kept the scope until the period repaid it (`OutstandingBudget`) | `admit`, `choose`, `remove`; `ledger::release` of the budget-ledger component |
| `scheduler-budget-scopes-lifecycle-6` | 133 | `process_slot_reuse_does_not_rebind_old_scope_or_erase_debt` | P (control, 20) admitted by R and reaped, its holding of 20 returned to R; a new process in its slot, at the next generation, is created with its thread, and `admit` of that thread with control 20: ok, where the prototype's old scope still held the reservation (`AdmissionRejected`); an `admit` of the reference of P's old thread is `err=StaleReference` | `admit`; `ledger::release` of the budget-ledger component; `ObjectTable::resolve` of the objects component |

### `src/objects/tests/activations.rs`

7 vectors. The first four use tables of the objects contract with four or
two processes, each with its thread; the last three the fixture of the
module `activation_migration` of the file, two processes each with its
thread in a table of two processes and three threads.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `activation-1` | 4 | `simultaneous_claims_preserve_unique_thread_and_cpu_ownership` | One case, on one CPU with the round-robin fixture: a admitted; `choose(0)` gives a; `choose(0)` while a runs is `err=InvalidState` and changes nothing, so a running thread, which is in no run queue, is not taken a second time ([Blocking and readiness](#blocking-and-readiness)). The claims of four threads on four CPUs belong to the multicore components (planned), and the states dying and dead of a process to the lifecycle component; they are not applicable here and have no line | `admit`, `choose`; the multicore and lifecycle components |
| `activation-2` | 44 | `a_stale_stop_cannot_release_a_migrated_or_restarted_dispatch` | Not applicable: migration between CPUs belongs to the multicore components; on one CPU a dispatch is that of the current thread, and the stops act on the current dispatch, so a stop with a stale receipt does not exist | None |
| `activation-3` | 58 | `serialized_and_parallel_claims_cannot_bypass_each_other` | a and b admitted with the round-robin fixture. `choose(0)` gives a; `choose(0)` while a runs is `err=InvalidState`; `yield_now(1)`; `choose(1)` gives b; `choose(1)` while b runs is `err=InvalidState`; `yield_now(2)`; `choose(2)` gives a; `yield_now(3)`. So no thread runs beside the current one; the activation on other CPUs belongs to the multicore components | `admit`, `choose`, `yield_now` |
| `activation-4` | 72 | `activation_generation_exhaustion_and_foreign_receipts_are_retained` | Not applicable: there is no activation serial and no receipt of an activation | None |
| `activation-legacy-11` | 349 | `zero_serial_is_exhausted` | Not applicable: there is no activation serial | None |
| `activation-legacy-12` | 357 | `maximum_serial_is_used_once_then_retained_as_exhausted` | Not applicable: there is no activation serial | None |
| `activation-5` | 492 | `legacy_identity_precedes_every_active_receipt` | Not applicable here: the order of the lookup of a thread capability and of its rights (`PermissionDenied`, `WrongPool`, `StaleHandle`) is the capabilities and objects components', whose vectors test it, and there is no activation, so the dispatch of another thread does not make an entry refuse with `Busy`, whose activation part [Errors](#errors) maps | The capabilities and objects components |

### `src/abi/clock/tests.rs`

10 vectors, with the clock fixture. This page has no query of the clock:
EL0 reads `CNTVCT_EL0` and `CNTFRQ_EL0`, and `now` is an input with its
premises ([Platform parameters and time](#platform-parameters-and-time)).

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `abi-clock-1` | 24 | `frequency_is_nonzero_bounded_and_fixed_for_the_boot` | The parameters of the budget fixture taken as seconds: `TIME_SLICE` 10,000,000, `REPLENISH_PERIOD` 100,000,000, the caps 20,000,000, 50,000,000 and 20,000,000 and `KERNEL_MARGIN` 10,000,000 microseconds. The counter frequency 0 is `err=InvalidConfiguration` of `Ledger::new`; $2^{64} - 1$ is `err=Overflow` of `Ledger::new`, since the period does not fit 64 bits in ticks; 1, 25, 54,000,000, $2^{32} - 1$ and $2^{32}$ pass `Ledger::new` and `validate_parameters`, the time slice taking ten times as many ticks as the frequency and the period a hundred times as many. The prototype's bound of $2^{32}$ on the frequency does not apply, and its query, which returned the frequency, does not exist | `validate_parameters`; `Ledger::new` of the budget-ledger component |
| `abi-clock-2` | 42 | `repeated_samples_preserve_all_tick_bits_without_rebasing` | Not applicable: there is no query of the clock; that `now` stays below $2^{63}$ and never decreases is a premise | None |
| `abi-clock-3` | 58 | `regression_fails_without_clamping_or_changing_the_last_sample` | Not applicable: there is no query of the clock, and time that goes backwards does not occur, a premise | None |
| `abi-clock-4` | 74 | `every_unused_register_is_checked_at_full_width` | Not applicable: there is no such operation; the form of the arguments of an operation belongs to the ABI dispatch | None |
| `abi-clock-5` | 96 | `versions_and_operations_are_validated_before_observation` | Not applicable: there is no such operation; versions and operation numbers belong to the ABI dispatch | None |
| `abi-clock-6` | 122 | `observation_handle_cannot_impersonate_the_captured_caller` | Not applicable: there is no such operation, and the caller of an operation is the running thread, not a handle | None |
| `abi-clock-7` | 133 | `foreign_and_reused_thread_handles_are_rejected` | Not applicable: there is no such operation | None |
| `abi-clock-8` | 159 | `running_blocked_and_terminal_callers_cannot_query` | Not applicable: there is no such operation, and EL0 reads the counter without a call | None |
| `abi-clock-9` | 184 | `callers_share_one_guard_without_needing_capability_or_resource_slots` | Not applicable: there is no query and no guard of the last sample; that `now` never decreases within a boot is a premise of the architecture crate, which reads the counter | None |
| `abi-clock-10` | 206 | `queried_ticks_and_frequency_construct_an_exact_notification_deadline` | EL0 reads the count 100 and the frequency 25, and builds the deadline $100 + \lceil 25/25 \rceil = 101$ in the count of `now`. A wait on a notification with that deadline at 100 does not expire at 100 and times out at 101, and a wait at 101 with the deadline 101 times out at once, as the waits component's expiry states; between 100 and 101 the composer passes 101 as the external deadline, so `choose(100, 101)` with a ready thread gives a deadline of at most 101 | `choose`; the waits component, for the wait |

### Vectors of other pages

`objects-13` of the
[objects contract](../../objects-capabilities/objects/contract.md#legacy-test-vectors),
`src/objects/tests.rs`, line 412,
`activation_is_single_owner_and_never_schedules_a_blocked_or_dead_thread`,
is frozen there and replayed here, and the count of 86 leaves it out. Its
rule is that of [Blocking and readiness](#blocking-and-readiness): with a
thread running, `choose` is `err=InvalidState`, so a second thread does not
run beside it; a blocked thread and a removed one are in no run queue and
are never chosen. A wait begins only by a call of the running thread itself,
which then blocks with `block`, so the prototype's refusal to begin a wait
of a running thread (`InvalidState`) is the converse of the rule here; its
activation and quiescence (`Busy`, `InvalidState`) do not apply. The entry
is `choose`, with `block` and `remove`.

## References

- The kernel's own rules, which this page instantiates:
  [Scheduling and budgets](../../../architecture.md#scheduling-and-budgets)
  for the priority queues with round robin, the budgets with replenishment,
  preemption by the timer, the control capacity and the margin set aside at
  admission and the per-CPU run queues; the execution model under
  [System calls and the ABI](../../../architecture.md#system-calls-and-the-abi)
  for scheduling only before a return to EL0 and at preemption points, and
  for blocking and its completion; the budget lending of
  [IPC, notifications and waits](../../../architecture.md#ipc-notifications-and-waits);
  and [Multicore by design](../../../architecture.md#multicore-by-design)
  for the classes of state and the pending queues.
- The [security model](../../../security.md): its
  [internal choices](../../../security.md#internal-choices) for queues,
  deadlines and the order of errors, its
  [observable outputs](../../../security.md#observable-outputs), and the
  register of
  [permitted nondeterminism](../../../security.md#permitted-nondeterminism).
- The rules of this page take, as clauses of their own, the rules of the
  prototype tree at `prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`:
  - `docs/features/kernel/scheduling.md`, lines 69 to 85: the quantum of a
    dispatch, preemption by the timer, a deadline that system calls do not
    restart, sleep and idle;
  - `docs/features/kernel/scheduling.md`, lines 86 to 116: the classes with
    their caps and one period, the slack for the kernel and interrupts,
    admission within the caps, and the charge of every stop; its debt and
    replenishment belong to the budget-ledger component;
  - `docs/features/kernel/scheduling.md`, lines 117 to 147: the deadline as
    the earliest of its limits, throttled threads that stay ready, waiting
    and waking, and failures that change nothing;
  - `docs/features/kernel/quotas.md`, lines 55 to 134: of its scopes, only
    that the budget of a child is cut from its parent's, with a class not
    above the parent's;
  - `docs/kernel-state.md`, lines 43 to 76: the division into per-CPU,
    per-thread, per-process and shared state, with the run queue of each
    CPU.
