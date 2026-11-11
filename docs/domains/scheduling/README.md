# Scheduling and budgets

## Overview

The scheduling and budgets domain decides which thread runs on a CPU and
for how long, how the time of a CPU is divided among the processes in fixed
periods and charged to them, how the budget of a caller pays for the
service of its call, and how much of the CPU a new process may receive. It
covers the three priority classes with the run queues of each CPU, the
budget of each thread with the caps of the classes and their
replenishment, preemption by the timer and at the return to EL0, the
lending of a caller's budget to the service of a synchronous call, the
control capacity and the kernel margin that every period sets aside, and
the admission of a new thread with its class, budget and ceiling.

Three limits bound the domain. Time is the count of the virtual counter of
the board, read once on entry to each transition; within a boot it does
not decrease and stays below $2^{63}$, and every time slice, period, cap
and budget is below $2^{62}$ ticks, so the arithmetic of deadlines and
charges fits 64 bits without a check. The kernel schedules only before a
return to EL0 and at the preemption points of long operations, so a
dispatch can run past its deadline by the time to the next such point, and
that overrun is charged as debt. Every class and every thread of a CPU
shares one period, a chain of loans has at most eight loans, and the run
queues and budget ledgers are structures of one CPU each: a result on one
CPU does not show the choice of a CPU for a thread, migration or the
charge of a dispatch to the ledger of another CPU.

The domain builds on others, listed in the
[subject-domain index](../README.md). The boot and platform domain gives
the counter frequency, the timers and the interrupt controllers of each
board and the board crate that holds the platform parameters; the memory
and address-spaces domain gives the EL0 policy that lets EL0 read the
virtual counter and the return to EL0 that runs the thread chosen here; the
kernel objects and capabilities domain holds the thread slots in which the
budget records and the scheduling state live, the write-set transactions,
the rights that creation and control need, and the creation and lifecycle
of processes, which compose admission, removal and release; the IPC and
waits domain decides when a call lends and withdraws a budget and
completes the waits that make threads ready; the multicore domain moves
threads and charges between CPUs. The
[budget-ledger](budget-ledger/requirements.md) component holds the ledger
of each CPU with its period and the caps of its classes, the budget record
of each thread, the charge of a dispatch with its debt, replenishment, the
holdings that admission carves and release returns, the loans and the CPU
time. The [scheduler](scheduler/requirements.md) component holds the
classes, the run queues, the selection of a thread with the deadline of its
dispatch, preemption, blocking, readiness and removal, the reserved control
capacity, the checks of admission, the operation `yield` and the time
slice.

## Conventions

- **Time as an argument.** Every entry that depends on time takes the time
  of its transition as an argument, read once from the virtual counter on
  entry; no entry reads a clock, and a deadline that EL0 builds from the
  counter is in the same count.
- **One period.** Every class and every thread of a CPU counts its periods
  from one epoch with one period, so all of them replenish at the same
  boundaries.
- **The whole interval is charged.** Every stop of a dispatch, whatever its
  reason, charges its whole interval to the owner of the context that it
  ran on and to that owner's class; an overrun is debt, which later
  periods repay and which is never forgiven or moved to another record.
- **No banked credit.** Credit that a period leaves unused is lost at its
  end, and a positive credit never exceeds one budget.
- **Strict classes, FIFO within a class.** A higher class with credit
  always runs before a lower one, and within a class the run queue
  decides, by the rules of the
  [internal choices](../../security.md#internal-choices).
- **Checks first.** An entry makes all its checks before its first write;
  when several fail, the first in the order of errors of the
  [security model](../../security.md#internal-choices) decides, and a
  failure changes no state and counts nothing.
- **Bounded entries.** No entry loops over periods; a walk of the run
  queues is bounded by the thread capacity, and no entry of the domain is a
  long operation.

## Feature index

| Feature | Scope | Feature documents | Components |
| --- | --- | --- | --- |
| [Priority classes](#priority-classes) | The three classes in strict order, the FIFO run queues of each CPU, selection, blocking, readiness and removal, and `yield` | - | [scheduler](scheduler/requirements.md) |
| [Budgets and replenishment](#budgets-and-replenishment) | The budget records and class ledgers, the charge of every dispatch, debt, replenishment at period boundaries, CPU time and the platform parameters of the ledger | - | [budget-ledger](budget-ledger/requirements.md) |
| [Preemption](#preemption) | Time slices, the deadline of a dispatch, preemption by the timer and at the return of an entry, and the time of a transition | - | [scheduler](scheduler/requirements.md) |
| [Synchronous budget lending](#synchronous-budget-lending) | The loan of a caller's context to the service of its call, nested loans, the effective class within a ceiling and the withdrawal of loans | - | [budget-ledger](budget-ledger/requirements.md); the IPC component of the IPC and waits domain, for when a loan is made and withdrawn |
| [Reserved control capacity](#reserved-control-capacity) | The caps of the classes and the kernel margin within the period, and the share that the control class keeps under load | - | [scheduler](scheduler/requirements.md) |
| [Admission](#admission) | The class, budget and ceiling of a new thread, their checks, and the holdings carved from its creator and returned at its reap | - | [scheduler](scheduler/requirements.md); [budget-ledger](budget-ledger/requirements.md), for the holdings |

## Priority classes

**Description.** Every thread has one of three priority classes, control,
interactive and background, from the highest, fixed when it is admitted.
Each CPU keeps one FIFO run queue for each class, and a ready thread waits
in the queue of its effective class: its own class, or a higher one while
it runs on a borrowed budget. Selection takes, from the highest class, the
first thread of the queue whose budget has credit; a thread without credit
keeps its place and is passed over, and a class whose ready threads have
no credit gives way to the next. A thread that becomes ready by its
admission or by the completion of its wait, whose dispatch ends with its
time slice or its credit, or that yields joins the tail of its queue; a
thread preempted with time slice left and with credit returns to the head
with the rest of its slice. An admitted thread is running, ready, blocked
or removed: it blocks only by a call of its own while it runs, becomes
ready only when its wait completes, and is never chosen again once
removed, so it runs on at most one CPU at a time. `yield` ends the
dispatch of its caller and puts it at the tail of its queue. The classes
order selection and do not divide the CPU, which the caps of the classes
do.

**Design background.** Strict priorities with round robin within a
priority are the round-robin policy of POSIX real-time scheduling
(IEEE Std 1003.1-2024), restricted to three levels so that selection is a
walk of three queues. A FIFO for each class makes the order in which ready
threads run a fixed rule, as the security model requires of every internal
choice, and a throttled thread that keeps its place resumes, after the
replenishment of its budget, in the order in which it stopped.

**Consumers.** The root and the paths that keep the system in control, such
as supervisors, the stopping of processes and the report of faults, in the
control class; interactive services and applications; batch and
background jobs; the IPC and waits domain, whose completions make threads
ready; the lifecycle of processes, which removes their threads.

**Interface.** The operation `yield`, which takes no argument and returns
success; the class of a thread is an argument of the creation of its
process. Inside the kernel, the scheduler admits, enqueues, chooses,
preempts, blocks, removes and requeues threads
([entry points](scheduler/contract.md#entry-points)); an entry called in a
state that it does not accept is an error that changes nothing. Which
thread runs and the order in which threads are woken are outputs that
scheduling decides
([observable outputs](../../security.md#observable-outputs)).

**Prerequisites.** [Budgets and replenishment](#budgets-and-replenishment),
for the credit; [Synchronous budget lending](#synchronous-budget-lending),
for the effective class; the
[scheduler contract](scheduler/contract.md#run-queues); the thread slots of
the [objects](../objects-capabilities/objects/requirements.md) component;
the waits of the IPC and waits domain.

**Engineering notes.** Selection walks at most the three queues of its CPU
and passes over at most the threads that the CPU holds, which the thread
capacity of the capacity record bounds; the removal of a ready thread walks
one queue to the thread before it. A process has one thread, created with
it. The run queues and the current thread are per-CPU state, and the
scheduling state of a thread is per-thread state, classified in the
[State fields](scheduler/contract.md#state-fields) of the scheduler
contract.

**Verification.** Invariants: a ready thread is in exactly one run queue,
that of its effective class on its CPU; a new, running, blocked or removed
thread is in none; selection takes the first thread with credit of the
highest class that has one. Required counterexamples: a control thread
without credit beside a background thread with credit, two threads whose
waits complete in one transition, a second wake of a ready thread, a wake
of a removed or stale thread. Environments: host tests with the frozen
vectors of the prototype's round robin and budget scheduler, and a property
test against an independent model of one FIFO for each class; QEMU runs of
threads of several classes from EL0.

## Budgets and replenishment

**Description.** Each CPU has one replenishment period, and every class and
every thread of the CPU counts its periods from one epoch, the time of the
boot. Each class has a cap per period and each thread a budget per period,
which its budget record holds in its thread slot. When a dispatch stops, at
the end of its time slice or its credit, by a yield, a block, a sleep, an
exit, a fault or a kill, its whole interval, the work of the kernel in it
included, is charged to the record of the owner of its context and to the
ledger of that owner's class. The part beyond the remaining credit becomes
debt in full: it is not reduced, forgiven or charged to another record. At
each period boundary the credit of a record becomes the smaller of its
credit plus its budget and its budget, and that of a class the same with
its cap: debt is repaid first, and unused credit never accumulates. A
thread runs only while both its context and the class of that context have
credit, and a record with a budget of 0 never runs. Waiting and sleeping
neither add nor remove credit. The CPU time of a thread is the sum of the
intervals that it ran, on its own budget or a borrowed one. There is no
scheduling-context object, no replenishment list, no sporadic server and no
timeout handler, and no charge reaches an ancestor of a process.

**Design background.** A budget that is a field of a record, charged when a
dispatch stops and replenished at boundaries that every record shares,
keeps each charge and each replenishment a fixed number of steps, and a
closed form over the number of boundaries crossed charges an interval of
any length without a loop over periods. Charging the whole interval and
keeping an overrun as debt bound what a thread obtains over several periods
by its budget, also when a timer interrupt comes late, and a credit capped
at one budget keeps a thread that has slept from running in a burst. The
model leaves out the scheduling contexts, replenishment lists and timeout
handlers of the mixed-criticality scheduling of seL4 (Lyons et al. 2018),
and with them the finer sporadic budgets that they give.

**Consumers.** Every process, whose thread runs within its budget; the root
and the process manager, which give each service and worker its budget at
its creation; the process service of each POSIX environment, which reports
the CPU time of its processes; the selection of the scheduler, which reads
the credit and the end of the period.

**Interface.** No operation of its own: the budget of a thread is an
argument of the creation of its process, and its CPU time a result of the
query of the CPU time of a process with the observation right. Inside the
kernel, the budget ledger charges, replenishes, gives the credit of a
thread and reads its CPU time
([entry points](budget-ledger/contract.md#entry-points)). Platform
parameters that fail their checks stop the boot with a fixed error.

**Prerequisites.** [Admission](#admission), for the budgets;
[Synchronous budget lending](#synchronous-budget-lending), for the context
that pays; the
[budget-ledger contract](budget-ledger/contract.md#charging-and-debt); the
[board support](../boot-platform/README.md#qemu-virt-and-pi-5-board-support)
of the boot and platform domain, for the counter frequency and the
platform parameters; the thread slots of the
[objects](../objects-capabilities/objects/requirements.md) component.

**Engineering notes.** Each charge and each replenishment is a fixed
number of 64-bit operations. A record with a debt $d$ and a budget $b > 0$
regains credit within $\lceil d/b \rceil$ boundaries, its debt falling at
each of them. Each board gives the period, the caps and the kernel margin
in microseconds, which the boot converts into ticks with the counter
frequency, rounding the caps down and the margin up. The ledgers and the
budget records are per-CPU state; the lending fields and the pending ticks
of a charge from another CPU are shared state, all classified in the
[State fields](budget-ledger/contract.md#state-fields) of the budget-ledger
contract.

**Verification.** Invariants: the spending of a record and of a class
equals that of a model that charges one tick at a time and replenishes at
each boundary; a debt falls at each boundary until it is 0; no credit
exceeds one budget. Required counterexamples: an overrun within one period,
a stop exactly at a boundary, a stop across many boundaries, a gap of
$10^{12}$ periods, a record with a budget of 0, and each platform parameter
at the limit of its check and one beyond. Environments: host tests with the
frozen vectors of the prototype's budget scheduler and a property test
against an independent tick model; QEMU runs in which a thread that loops
at EL0 runs no further once its budget is spent until the next period.

## Preemption

**Description.** A dispatch starts when its thread is chosen, and its
deadline is the earliest of the end of the time slice left of the thread,
the end of its credit, the end of the current period and the earliest
deadline of the waits of the CPU. The kernel arms the timer for that
deadline. The timer interrupt at or after it ends the dispatch, and an
interrupt before it leaves the dispatch as it was, unless a thread of a
higher class has become ready. A system call that returns to its caller
keeps the dispatch with its start and its deadline, so no system call
restarts a time slice. The kernel schedules only before a return to EL0 and
at the preemption points of long operations: a thread of a higher class
that a system call or the interrupt of a device makes ready runs at the
return of that entry, and one that the expiry of a wait or the
replenishment of its budget makes ready runs at the timer interrupt that
its time sets. An idle CPU wakes at the earliest deadline of its waits and,
while a ready thread waits for credit, at the end of the period; with
neither, time does not wake it. The time of a transition is read once on
entry, and every deadline of the transition is judged by it.

**Design background.** A deadline that is the earliest of every limit of a
dispatch needs one setting of the timer for each dispatch instead of a
periodic tick, and a time slice that system calls keep stops a thread from
lengthening its slice by entering the kernel. Scheduling only at the return
to EL0 and at preemption points keeps every entry a step that runs to
completion, which the sequential proofs assume
([execution model](../../architecture.md#system-calls-and-the-abi)); the
price is a latency of preemption of up to the longest step between two
such points. A thread preempted with its slice left keeps its place at the
head, so a higher class that preempts it takes from it only the time that
the higher class uses.

**Consumers.** Interactive services and applications, whose latency depends
on preemption; the control paths, which preempt the lower classes when
they become ready; the waits and sleeps of the IPC and waits domain, whose
deadlines end a dispatch; the clocks of the runtimes of EL0, which read the
same counter.

**Interface.** No operation of its own. `TIME_SLICE` is a platform
parameter of each board, and a deadline that EL0 builds from `CNTVCT_EL0`
and `CNTFRQ_EL0` is in the count of the time of the kernel. Inside the
kernel, the choice of a thread gives its deadline, which is also the
deadline of the timer, and preemption ends a dispatch at its deadline or
when a thread of a higher class is ready
([preemption](scheduler/contract.md#preemption)); an early preemption is an
error that changes nothing.

**Prerequisites.** [Priority classes](#priority-classes),
[Budgets and replenishment](#budgets-and-replenishment); the
[scheduler contract](scheduler/contract.md#selection-and-time-slices); the
[interrupt controllers](../boot-platform/README.md#interrupt-controllers)
and timers of the boot and platform domain; the
[EL0 controls](../memory/address-space/contract.md#el0-controls) of the
address-space component, which let EL0 read the virtual counter; the
deadlines of the waits of the IPC and waits domain.

**Engineering notes.** The timer whose interrupt preempts is the virtual
timer on QEMU virt and the physical timer on the Pi 5, whose compare value
the board support computes from the deadline in the virtual count. A late
interrupt lengthens a dispatch, and the overrun is charged as debt. Under
the premises of time no sum of a deadline overflows 64 bits, and a deadline
that EL0 gives is only compared. The current thread with the start, the
deadline and the context of its dispatch, the timer deadline and the
reschedule flag are per-CPU state, classified in the
[State fields](scheduler/contract.md#state-fields) of the scheduler
contract.

**Verification.** Invariants: no dispatch has a deadline later than the end
of its time slice left, of its credit or of its period; a system call that
returns to its caller changes neither the start nor the deadline of its
dispatch. Required counterexamples: each of the four limits deciding the
deadline in turn, an interrupt before the deadline, a thread of a higher
class made ready by a system call and by the expiry of a sleep, a late
stop. Environments: host tests with the frozen vectors of the prototype's
round robin and budget scheduler, each with the times that it passes; QEMU
runs in which a thread of a higher class that the timer makes ready
preempts a thread that loops at EL0.

## Synchronous budget lending

**Description.** When a call is delivered, its caller lends its context,
its own budget record or the context that it borrows, to the receiver: the
receiver then runs on that context, and every interval that it runs is
charged to the owner of the context and to the owner's class, never to the
receiver. A receiver that calls in turn lends the same context one level
deeper, so a chain of calls runs on the budget of its first caller, up to
`MAX_LOAN_DEPTH` = 8 loans; a ninth is refused. The receiver runs at the
higher of its own class and the effective class of its lender bounded by
the ceiling that its creator gave it. A loan moves no credit: a context has
one active holder, the last thread of its chain, while the others wait in
their calls, and its budget is never duplicated. A receiver whose borrowed
context has no credit waits for the replenishment of that context and does
not fall back on its own budget. When a call ends, by a reply, a timeout, a
kill, a revocation or the closure of its peer, the loans of its receiver
and of every thread downstream of it are withdrawn in the same transition,
before the caller is made ready; the loans upstream stay, and what the
context has paid is not refunded.

**Design background.** Lending the caller's budget makes a client pay for
the service that it asks for, so a server needs no budget sized for its
busiest client and a client cannot run beyond its own budget through a
server; the donation of scheduling contexts to passive servers of seL4
(Lyons et al. 2018) works the same way, through a scheduling-context object
that this model does not have. The ceiling keeps a client of a high class
from raising every service that it calls to that class. Withdrawing the
downstream loans before the caller wakes keeps one holder for each context
and settles a loan as a whole within one transition, as the
[internal choices](../../security.md#internal-choices) require.

**Consumers.** The services that answer calls, such as the file, block and
process services, which run on the budgets of their clients; their
clients, whose calls draw on no budget but their own; the IPC of the IPC
and waits domain, which makes and withdraws the loans.

**Interface.** No operation of its own: a loan is a part of a call, and the
ceiling of a thread is an argument of the creation of its process. Inside
the kernel, the budget ledger lends a context and withdraws a loan
([lending](budget-ledger/contract.md#lending)). A loan beyond the depth is
an error of shared capacity. A loan back to the owner of a context is an
error, which the IPC component avoids by refusing a call to oneself and a
cycle of calls before delivery; a second loan to a borrower that already
borrows is an error as well, which the rules of the IPC component for the
delivery of a call to a receiver avoid.

**Prerequisites.** [Budgets and replenishment](#budgets-and-replenishment),
[Priority classes](#priority-classes), and [Admission](#admission) for the
ceiling; the calls of the IPC and waits domain and their settlement; the
[budget-ledger contract](budget-ledger/contract.md#lending).

**Engineering notes.** A loan and a withdrawal each write one budget
record; the withdrawal of a chain is at most eight withdrawals, with the
move of the last thread of the chain to the run queue of its own class,
within the write set of the settlement of the call. A loan or a withdrawal
during a dispatch leaves the interval up to it charged to the context that
the dispatch had. The source and the effective class of a record are
shared state, under the token of the slot of the borrower, classified in
the [State fields](budget-ledger/contract.md#state-fields) of the
budget-ledger contract.

**Verification.** Invariants: every interval is charged to the owner of
exactly one context; a context has at most one holder that runs; the sum of
the credits of all records is the same with and without loans; after a call
ends, no thread downstream of its receiver has a borrowed context. Required
counterexamples: a ninth loan, a second lender of one borrower, a loan back
to the owner, a borrowed context without credit beside the credit of the
receiver's own budget, the end of a call in the middle of a chain.
Environments: host tests with the frozen vectors of the prototype's
synchronous budgets, among them the nine pairs of classes of a caller and a
service; host tests of the IPC component that compose the loans with calls.

## Reserved control capacity

**Description.** The caps of the three classes and the kernel margin,
`KERNEL_MARGIN`, together fit within the period, which the boot checks:
the budgets that admission guarantees never exceed the CPU, and the margin
is left to the kernel and to the handling of interrupts. The caps are
disjoint, and the control cap is set aside before any other admission,
since the admission of an interactive or background thread takes only from
its own class. A control thread with credit is chosen before every thread
of a lower class and preempts one at the return of the entry or at the
timer interrupt that makes it ready, so under full load from the other
classes it runs within each period up to its budget and the control cap.
The background class keeps at least its cap in a period that the higher
classes start without debt, less the overrun of dispatches that stop late.

**Design background.** Setting aside the control capacity and the overhead
of the kernel and of interrupts at admission keeps the paths that stop
processes, report faults and recover services able to run whatever the
ordinary load, as the control reserve of the object pools keeps slots for
them
([boot-time capacities](../objects-capabilities/README.md#boot-time-capacities)).
A cap for each class gives the background class a minimum share as well,
so that no class can starve another by its load alone.

**Consumers.** The root and the control paths: supervisors, the stopping of
processes, the report of faults and the recovery of services; background
jobs, which keep their share under interactive load.

**Interface.** The caps and the margin are platform parameters of each
board; no operation. Caps and a margin that exceed the period stop the boot
with a fixed error.

**Prerequisites.** [Admission](#admission),
[Budgets and replenishment](#budgets-and-replenishment),
[Preemption](#preemption); the
[scheduler contract](scheduler/contract.md#reserved-control-capacity) with
its [platform parameters](scheduler/contract.md#platform-parameters-and-time).

**Engineering notes.** The conversion into ticks rounds the caps down and
the margin up, so that it neither enlarges a cap nor shrinks the margin. An
overrun of a dispatch can use the margin, and is debt that the following
periods repay. The caps and the margin are per-CPU state, read-only after
boot, classified in the
[State fields](budget-ledger/contract.md#state-fields) of the budget-ledger
contract.

**Verification.** Invariants: the caps and the margin add up to at most the
period; for each class, the budgets of its threads add up to at most its
cap. Required counterexamples: caps and a margin one tick beyond the
period, a class whose cap is 0, full load from the interactive and
background classes beside a control thread. Environments: host tests of the
checks of the boot and the frozen vectors; QEMU runs in which a control
thread under full load runs on its credit in every period.

## Admission

**Description.** A new thread is admitted once, in the creation of its
process, with the class, the budget and the ceiling that its creator gives.
Neither the class nor the ceiling may be above the class of the creator,
and the budget, of at least 1 tick, is carved from the creator's holding of
that class, so a creator that admits a thread of its own class lowers its
own budget. The reap of the thread returns its holdings to its owner, while
the spending of its class stays with the class. The root starts with a
holding of each class equal to its cap, so through any tree of processes
the budgets of each class add up to at most its cap. A refused admission
changes nothing, and an admitted thread joins the tail of the run queue of
its class. A budget is carved from the creator alone, and a charge changes
only the record that pays and its class, never an ancestor.

**Design background.** Carving the budget of a child from its parent's, as
the [metadata quotas](../objects-capabilities/README.md#metadata-quotas)
carve their limits, bounds what a subtree of processes can take by what its
root was given, without a global allocator; charging the record that pays
alone, and not each ancestor, keeps a charge a fixed number of steps.

**Consumers.** The root and the process manager, which give services and
workers their class, budget and ceiling; the process service of each POSIX
environment, which gives its processes budgets from its own; the creation
and the lifecycle of processes, which compose admission and release.

**Interface.** The class, the budget and the ceiling are arguments of the
creation of a process, whose form belongs to the operation inventory. A
class or a ceiling above the creator's class and a budget beyond the
creator's holding are refused with one error of the caller's quota, and a
budget of 0 is an error of the form of the arguments
([admission](scheduler/contract.md#admission)).

**Prerequisites.** [Priority classes](#priority-classes),
[Budgets and replenishment](#budgets-and-replenishment),
[Reserved control capacity](#reserved-control-capacity); the
[scheduler contract](scheduler/contract.md#admission) and the
[budget-ledger contract](budget-ledger/contract.md#admission-and-release);
the
[process and thread lifetimes](../objects-capabilities/README.md#process-and-thread-lifetimes)
of the kernel objects and capabilities domain.

**Engineering notes.** An admission writes the thread slots of the
creator, of the new thread and of the last thread of its run queue, and the
scheduler record of the CPU, within the write set of the creation. A
process is reaped after its children, so holdings return up the tree in
order. The holdings are fields of the budget records,
per-CPU state classified in the
[State fields](budget-ledger/contract.md#state-fields) of the budget-ledger
contract, and the scheduling state of a thread is classified in the
[State fields](scheduler/contract.md#state-fields) of the scheduler
contract.

**Verification.** Invariants: for each class, the holdings of all live
records and the part of the cap that the root has not taken add up to the
cap. Required counterexamples: a class above the creator's, a ceiling above
it, a budget of 0, a budget one tick beyond the holding, a class whose cap
is 0, a second admission of one thread, a chain of processes each of which
gives its whole holding to the next. Environments: host tests with the
frozen vectors of the prototype's admission and a property test of the
conservation of holdings over trees of processes; QEMU runs that create
processes with budgets from EL0.

## Dependencies

| Feature | Depends on | Reason |
| --- | --- | --- |
| Priority classes | Budgets and replenishment, Synchronous budget lending | Selection reads the credit of the context of a thread and queues it by its effective class |
| Budgets and replenishment | QEMU virt and Pi 5 board support, Process and thread lifetimes | The period, the caps and the margin are platform parameters converted with the counter frequency; the records live in the thread slots |
| Preemption | Priority classes, Budgets and replenishment, Interrupt controllers | The deadline of a dispatch comes from its slice, its credit and its period; the timer interrupt ends it |
| Synchronous budget lending | Budgets and replenishment, Admission, Calls | A loan charges the budget of its owner within the ceiling that admission sets; a call lends and withdraws |
| Reserved control capacity | Budgets and replenishment, Priority classes, Preemption | The caps bound each class; the control class is chosen first and preempts |
| Admission | Budgets and replenishment, Reserved control capacity, Process and thread lifetimes | Admission carves holdings within the caps, in the creation of a process |

## Exclusions

- Scheduling on several CPUs, the choice of a CPU for a thread, migration,
  the pending queues between CPUs, the charge of a dispatch to the ledger
  of another CPU and the locks that provide the tokens belong to the
  multicore domain.
- When a call lends and withdraws a budget, the completion of the waits that
  make threads ready, and the deadlines of waits and sleeps belong to the
  IPC and waits domain; this domain gives the loans and the readiness.
- The creation and reaping of processes, their lifecycle states, the query
  of their CPU time and the rights that creation and control need belong to
  the kernel objects and capabilities domain; this domain gives admission,
  release, removal and the CPU time of a thread.
- The timers and interrupt controllers of each board, the counter frequency
  and the board constants belong to the
  [boot and platform](../boot-platform/README.md) domain, and the EL0
  policy of the timers to the
  [memory and address spaces](../memory/README.md) domain.
- The operation numbers and the encoding of `yield` and of the class,
  budget and ceiling of a creation belong to the operation inventory of the
  runtime ABI and SDK domain.
- The POSIX interfaces of scheduling built on the classes belong to the
  compatibility personalities.

## References

- Arm Limited, *Arm Architecture Reference Manual for A-profile
  architecture*, DDI 0487, version M.d, 2026,
  <https://documentation-service.arm.com/static/6abbec2a6db85c5e6614a4a1>.
- IEEE and The Open Group, *The Open Group Base Specifications Issue 8*,
  IEEE Std 1003.1-2024, <https://pubs.opengroup.org/onlinepubs/9799919799/>.
- A. Lyons, K. McLeod, H. Almatary, G. Heiser, "Scheduling-context
  capabilities: a principled, light-weight operating-system mechanism for
  managing time", EuroSys 2018,
  <https://trustworthy.systems/publications/full_text/Lyons_MAH_18.pdf>.
