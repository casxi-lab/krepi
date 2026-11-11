---
features: none
---

# Scheduler requirements

The observable behaviour of the `scheduler` component of the
[scheduling and budgets](../README.md) domain: the priority classes, the
run queues of each CPU, the selection of the thread that runs with the
deadline of its dispatch, preemption, blocking, readiness and removal, the
reserved control capacity, the checks of admission, the time slice among
the platform parameters, and the time of a transition as an input. The
rules that its code and tests follow are in the [contract](contract.md). No
feature document covers the component, so the metadata lists none.

## Sources

- The three classes in strict order, the round robin within a class, the
  deadline of a dispatch as the earliest of its limits, preemption by the
  timer, system calls that keep the deadline, the charge of every stop,
  throttled threads that stay ready, the caps with the slack for the kernel
  and interrupts, and the admission of a child within its parent's budget
  take the rules of the prototype's round robin and budget scheduler, which
  the [references](contract.md#references) of the contract list, with their
  host tests as the frozen [vectors](contract.md#legacy-test-vectors).
- One scheduler for both, the placement at the head of a thread preempted
  with time slice left, the external deadline that the waits component
  gives, the reschedule flag at the return to EL0, admission as a part of
  the creation of a thread without scopes, the time slice in microseconds
  converted at boot, and the time of a transition as an input with its
  premises are new, from the kernel's
  [scheduling and budgets](../../../architecture.md#scheduling-and-budgets)
  and its
  [execution model](../../../architecture.md#system-calls-and-the-abi); the
  [behaviour changes](contract.md#legacy-test-vectors) of the contract list
  where they differ from the prototype.
- The order of the run queues, of several wake-ups and of errors follows the
  [security model](../../../security.md#internal-choices), and the time of a
  transition its entry [ND-01](../../../security.md#nd-01); the classes of
  state follow the
  [SMP design rules](../../../conventions/smp.md#s5-state-field-tables).
- The budgets, the credit of a thread, the charges, the replenishment, the
  holdings of admission, the loans and the checks of the period, the caps
  and the margin are those of the
  [budget-ledger](../budget-ledger/requirements.md) component; the thread
  references, the write sets and the errors of references are those of the
  [objects](../../objects-capabilities/objects/requirements.md) component.

## Configurations

- **QEMU virt.** The machine `virt-8.2` without EL2 and EL3, with GICv2, one
  Cortex-A76 and 128 MiB of RAM at `0x4000_0000`: the machine of
  `cargo xtask qemu`, with the QEMU version that `toolchains.toml` pins for
  the host, with the platform parameters of the board and its virtual
  timer.
- **Raspberry Pi 5.** Only the 8 GB model is run on a board in release 0.1,
  with one of its four Cortex-A76 cores running, the platform parameters of
  the board and its physical timer for preemption.
- **Host.** The host tests of the module `scheduler` of the core (planned)
  run on the development host and in CI, with the frozen vectors and the
  tests that the [contract](contract.md#testing-obligations) adds, each with
  the time and the platform parameters that it passes.
- One CPU. The run queues and the scheduler record are per-CPU data
  structures, one for each CPU, also while one CPU runs; no requirement here
  covers secondary CPUs, the pending queues between CPUs, the migration of a
  thread or the locks that provide the tokens.

## Requirements

### SCHED-R01

**Priority classes.** There are three classes, control, interactive and
background, in strict order: a thread of a higher class that has credit is
selected before every thread of a lower one, and a class whose ready
threads have no credit gives way to the next. A ready thread waits in the
queue of its effective class. The criterion: a control, an interactive and
a background thread are selected in this order until each has used its
budget, a control thread that wakes runs before a background one, and a
control thread without credit lets a background one run.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `scheduler::choose`, `scheduler::admit` and
  `scheduler::requeue` (planned).
- **Contract.** [Priority classes](contract.md#priority-classes) and
  [Selection and time slices](contract.md#selection-and-time-slices).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `scheduler-budget-1`,
  `scheduler-budget-3` and `scheduler-budget-lifecycle-8` as host tests,
  and the property test of the run queues of the
  [contract](contract.md#testing-obligations).

### SCHED-R02

**Run queues.** Each class has one FIFO run queue on each CPU. A thread that
is admitted, woken, out of time slice, out of credit or that yields joins
the tail; a thread preempted with time slice left and with credit returns
to the head and keeps the rest of its slice. Threads that one transition
makes ready join in the order of the internal choices. `yield` puts the
caller at the tail of its queue. The criterion: two and three threads of one
class rotate on expired slices and on yields of 0 and more ticks, a thread
stopped at the deadline of another's wait keeps its place and its slice, and
two threads whose sleeps expire together are queued in the order of their
registration.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `scheduler::admit`, `scheduler::enqueue`,
  `scheduler::preempt`, `scheduler::yield_now` and `scheduler::requeue`
  (planned).
- **Contract.** [Run queues](contract.md#run-queues) and
  [Determinism](contract.md#determinism).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `scheduler-1`, `scheduler-2`,
  `scheduler-3`, `scheduler-5`, `scheduler-budget-2` and
  `scheduler-budget-waits-4` as host tests, and the property test of the run
  queues of the [contract](contract.md#testing-obligations), against an
  independent model of one FIFO for each class. The operation `yield` from
  EL0 is shown once the ABI inventory holds it.

### SCHED-R03

**Deadline of a dispatch.** A dispatch ends at the earliest of the end of
the time slice left of its thread, the end of its credit, the end of the
current period and the earliest deadline of the waits of the CPU. An idle
CPU wakes at the earlier of the end of the period, when a ready thread is
throttled, and that deadline, or not by time. The criterion: each of the
four limits decides the deadline in a case of its own, and an idle CPU
wakes at the end of the period, at the deadline of a wait or not at all.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `scheduler::choose` (planned).
- **Contract.** [Selection and time slices](contract.md#selection-and-time-slices).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `scheduler-4`, `scheduler-budget-1`,
  `scheduler-budget-5`, `scheduler-budget-waits-5`,
  `scheduler-budget-waits-6` and `scheduler-waits-1` as host tests, and the
  host tests of the deadlines of the
  [contract](contract.md#testing-obligations).

### SCHED-R04

**Stops of a dispatch.** A system call that returns to the running thread
keeps its dispatch with its start and its deadline. A dispatch ends only by
a preemption, a yield, a block or a removal, and each of them charges the
whole interval of the dispatch, also a late stop beyond the deadline and a
stop after no tick. The criterion: choices while a dispatch runs are
refused and change nothing, and the CPU time of a thread after late stops
and yields is the sum of the intervals of its dispatches.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `scheduler::choose`, `scheduler::preempt`,
  `scheduler::yield_now`, `scheduler::block` and `scheduler::remove`
  (planned).
- **Contract.** [Selection and time slices](contract.md#selection-and-time-slices)
  and [Blocking and readiness](contract.md#blocking-and-readiness).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `scheduler-2`, `scheduler-9`,
  `scheduler-10` and `scheduler-budget-failures-4` as host tests. The
  charges themselves are shown by the tests of the budget-ledger
  component.

### SCHED-R05

**Preemption.** The timer interrupt at the deadline of a dispatch stops it;
an interrupt before the deadline leaves it as it was. A thread of a higher
class that a system call or a device interrupt makes ready runs at the
return of that entry, and one that the expiry of a wait or the
replenishment of its budget makes ready runs at the timer interrupt. The
criterion: an early preemption is refused and changes nothing, a sleeping
control thread preempts a background one at the end of its sleep, and on
QEMU virt a thread of a higher class that the timer makes ready preempts a
thread of a lower class that loops at EL0.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `scheduler::preempt`, `scheduler::enqueue` and
  `scheduler::choose` (planned).
- **Contract.** [Preemption](contract.md#preemption).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `scheduler-budget-3`,
  `scheduler-failures-5`, `scheduler-budget-failures-5` and
  `scheduler-budget-waits-4` as host tests, the host tests of preemption of
  the [contract](contract.md#testing-obligations), and its QEMU test of a
  higher class made ready by the timer. They show preemption on one CPU.

### SCHED-R06

**Blocking, readiness and removal.** A thread blocks only by a call of its
own while it runs, and a blocked thread becomes ready only when its wait
completes; this component never wakes one by itself. A removed thread is
never chosen again, whatever state it was removed in, and only a ready
thread is chosen, so a thread runs on at most one CPU at a time. Each
transition from a state other than the one that its entry needs is refused
and changes nothing. The criterion: a waiting thread without a deadline
stays blocked until it is made ready, a ready, a running and a blocked
thread can each be removed, a second wake and a wake of a removed or stale
thread are refused, and a thread can be made ready while another runs.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `scheduler::block`, `scheduler::enqueue` and
  `scheduler::remove` (planned).
- **Contract.** [Blocking and readiness](contract.md#blocking-and-readiness).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `scheduler-7`, `scheduler-8`,
  `scheduler-12`, `scheduler-failures-4`, `scheduler-waits-1` to
  `scheduler-waits-3`, `scheduler-waits-5`, `scheduler-budget-waits-7`,
  `scheduler-budget-waits-8` and `activation-3` as host tests, and the
  vector `objects-13` of the objects contract, which this component
  replays. When a wait completes is shown by the tests of the waits and IPC
  components, which compose these entries.

### SCHED-R07

**Reserved control capacity.** The caps of the three classes and the kernel
margin fit the period, and admission never gives the control cap to
another class, so a control thread with credit runs under full load in
every period, up to its budget and the cap of its class. The criterion: the
boot refuses caps and a margin beyond the period, the classes run in their
order up to their caps with the margin left idle, and on QEMU virt a
control thread under full load from the other classes runs on its credit in
every period.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `scheduler::choose` and `scheduler::admit`, with
  `Ledger::new` of the budget-ledger component (planned).
- **Contract.** [Reserved control capacity](contract.md#reserved-control-capacity).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `scheduler-budget-1` and
  `scheduler-budget-failures-1` as host tests, and the QEMU test of full
  load of the [contract](contract.md#testing-obligations). The holdings by
  class are shown by the tests of the budget-ledger component.

### SCHED-R08

**Admission.** A new thread is admitted once, when it is created, with the
class, the budget and the service ceiling that its creator gives: a class or
a ceiling above the creator's class is refused with `AdmissionRejected`,
the budget comes from the creator's holding of the class, and a refused
admission changes nothing. The admitted thread is ready at the tail of the
queue of its class. The criterion: the frozen vectors of admission hold,
among them admissions within and beyond a holding of 20, a class whose cap
is 0, nested admissions that take their budgets from their creators, and a
second admission of a thread.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `scheduler::admit`, with `ledger::admit` of the
  budget-ledger component (planned).
- **Contract.** [Admission](contract.md#admission).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `scheduler-11`, `scheduler-budget-7`,
  `scheduler-budget-failures-2`, `scheduler-budget-lifecycle-1`,
  `scheduler-budget-lifecycle-2`, `scheduler-budget-scopes-admission-1`,
  `scheduler-budget-scopes-admission-4` and
  `scheduler-budget-scopes-admission-6` as host tests. The creation call
  from EL0, which composes admission, is shown by the tests of the creation
  component.

### SCHED-R09

**Platform parameters.** The time slice, the period, the three caps and the
kernel margin are platform parameters of each board, in microseconds,
converted into ticks at boot with the counter frequency. A time slice of
fewer than 1 tick, or of no fewer ticks than the period, stops the boot
with `InvalidConfiguration`, and so do the checks of the budget-ledger
component for the other values; there is no fallback. The values of QEMU
virt and of the Pi 5 are those of the
[contract](contract.md#platform-parameters-and-time), which the change that
adds the scheduling of each board writes there. The criterion: each check
accepts its limit and refuses one beyond it, the frequencies of both boards
and of 1 Hz to $2^{32}$ Hz are accepted with values that fit, and the values
of each board pass.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `scheduler::validate_parameters` and `RunQueues::new`,
  with `Ledger::new` of the budget-ledger component (planned).
- **Contract.** [Platform parameters and time](contract.md#platform-parameters-and-time).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `scheduler-failures-1`,
  `scheduler-budget-failures-1` and `abi-clock-1` as host tests, the host
  tests of the check of the time slice of the
  [contract](contract.md#testing-obligations), and the QEMU and Pi 5 boots
  with the values of their boards.

### SCHED-R10

**Time as an input.** Every entry that depends on time takes the time of its
transition as an argument, in ticks of the virtual counter that EL0 reads as
well, so a deadline that EL0 builds from `CNTVCT_EL0` and `CNTFRQ_EL0` and
the time of the kernel are in one count. The component reads no counter, and
within a boot the time never decreases and stays below $2^{63}$. The
criterion: every host test passes its times and parameters, the results do
not depend on the speed of the host or on a fixed instruction count, and a
deadline that EL0 builds expires at the time of the count that it names.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `scheduler::choose`, `scheduler::preempt`,
  `scheduler::yield_now`, `scheduler::block`, `scheduler::remove`,
  `scheduler::enqueue`, `scheduler::requeue` and `scheduler::admit`
  (planned).
- **Contract.** [Platform parameters and time](contract.md#platform-parameters-and-time)
  and [Determinism](contract.md#determinism).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** Every frozen vector as a host test, with the times of the
  test, among them `abi-clock-10`, and the host and QEMU tests of the
  [contract](contract.md#testing-obligations), which take their periods
  from the platform parameters. The reading of the counter on entry is the
  architecture crate's and is shown by its QEMU tests.

### SCHED-R11

**No change on failure.** Every error of the component leaves every field
of the scheduler record and of the thread slots as it was, and no failure is
counted. The criterion: for each error of the contract, a call that gives it
leaves every field compared before and after unchanged, and the frozen
vectors of refusals hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** Every row of the
  [entry table](contract.md#entry-points).
- **Contract.** [Errors](contract.md#errors) and
  [Check and execute](contract.md#check-and-execute).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `scheduler-10`, `scheduler-12`,
  `scheduler-failures-3`, `scheduler-failures-5`, `scheduler-waits-2`,
  `scheduler-budget-failures-5` and `scheduler-budget-waits-7` as host
  tests, and the host test of each error of the
  [contract](contract.md#testing-obligations).

## Liveness, time and performance

- Every entry of the component runs to its end within the bounds of the
  [contract](contract.md#work-bounds); none waits, retries or takes a lock
  of its own, and the component has no long operation.
- Selection walks at most the three run queues of its CPU, and within them
  passes over at most the threads that the CPU holds; the removal or the
  move of a ready thread walks at most one run queue.
- Within one class and while no thread of a higher class with credit is
  ready, a ready thread with credit waits at most for the time slices of
  the threads ahead of it in its queue, each of which a late stop can
  exceed by the latency of the timer interrupt. That selection is fair and
  that scheduling meets time bounds are progress obligations, which no
  requirement here proves
  ([open obligations](contract.md#open-obligations)).
- No requirement bounds the time that a step takes.

## Scope

- One CPU. The pending queues of the CPUs, the choice of a CPU for a thread,
  migration, the tokens and their locks are not covered.
- The budget records, the class ledgers, the charges, the replenishment, the
  holdings and the loans of budgets are not covered; they are the
  [budget-ledger requirements](../budget-ledger/requirements.md).
- When a wait completes, the deadlines of waits and sleeps, when a loan is
  made and withdrawn, the creation call that composes admission and the
  destruction that composes removal are not covered; the waits, IPC,
  creation and lifecycle components compose the entries of this component
  and have their own requirements.
- Scheduling on several CPUs, migration between them, and the proofs of
  fairness and of time bounds belong to later releases.
- A process has one thread; further threads of a process are not covered.
- The operation numbers and numeric error codes of the ABI inventory are
  not covered.

## Contract sections without a requirement

- [Terms](contract.md#terms): definitions only.
- [Extractability](contract.md#extractability) states the module, its layer
  and its adapter, which no requirement observes.
- [State fields](contract.md#state-fields) binds the code without an
  observable behaviour of its own.
- [Work bounds](contract.md#work-bounds) states the bounds that
  [Liveness, time and performance](#liveness-time-and-performance) relies
  on.
- [Open obligations](contract.md#open-obligations) lists the entries of the
  module and the adapter that lends the scheduler record of the executing
  CPU, which no requirement observes.
