# Budget-ledger contract

This page governs the code of the `budget-ledger` component of the
[scheduling and budgets](../README.md) domain: the ledger of each CPU with
its period, its class caps and the ledger of each class; the budget record
of each thread with its holdings, its credit and its CPU time; the charge
of a stopped dispatch, with the debt of an overrun; the replenishment at
period boundaries; the admission that carves the budget of a new thread
from its creator and the release that returns it at the reap; and the loan
of a caller's context to the service of its call and its withdrawal. The
priority classes, the run queues, the selection of the thread that runs,
its time slice, preemption and the admission checks of the class and the
ceiling belong to the [scheduler](../scheduler/contract.md) component, the
module `scheduler` of the core (planned), which reads the dispatch credit
that this page gives; when a loan is made and withdrawn belongs to the
module `ipc` (planned); the creation and the reap of the thread of a
process belong to the modules `creation` and `lifecycle` (planned), which
compose the admission and the release of this page. The observable
behaviour that these rules serve, with its evidence, is in the
[requirements](requirements.md), the other document of the component.

## Terms

- **Tick.** One count of the virtual counter `CNTVCT_EL0`, which EL0 also
  reads ([EL0 controls](../../memory/address-space/contract.md#el0-controls)).
  Every time and every amount of this page is in ticks.
- **Time.** The value of the virtual counter that the adapter reads once
  on entry to a transition and passes to the entries of this page as their
  argument `now` ([ND-01](../../../security.md#nd-01)). The **premises of
  time** are that the time does not decrease within a boot and stays below
  $2^{63}$; no entry checks them.
- **Ledger.** `ledger::Ledger` (planned): the ledger of one CPU, with the
  epoch $E$, the period $P$, the cap $C_k$ of each class $k$, the kernel
  margin $M$, the class ledger of each class and the unallocated holdings
  ([Classes](#classes)).
- **Class.** One of the three priority classes, control, interactive and
  background, from the highest to the lowest, as the scheduler's
  [priority classes](../scheduler/contract.md#priority-classes) define
  them. The record stores a class as `ledger::Class` (planned), since this
  module is below the scheduler's.
- **Period index.** $\pi(t) = \lfloor (t - E) / P \rfloor$ for a time
  $t \ge E$. The **boundaries** are the times $E + nP$ for $n \ge 1$, and
  the **current period** at $t$ runs from $E + \pi(t) P$ to its **end**,
  $E + (\pi(t) + 1) P$.
- **Budget record.** `ledger::Record` (planned): the fields of
  [Budget records](#budget-records) in the slot of a thread.
- **Holding.** The amount per period that a record holds of one class.
  The **budget** $b$ of a record is its holding of its own class; its
  holdings of the other classes are what it can give to the threads that
  it admits.
- **Spent.** The amount $s$ that a record or a class ledger has used, net
  of the replenishments it has received, as of its **stamp**, the period
  index at which it was last brought up to date. The **remaining credit**
  is $\max(b - s, 0)$ and the **debt** $\max(s - b, 0)$, with the cap in
  place of $b$ for a class ledger.
- **Context.** The record that pays for a dispatch: the record of the
  thread that runs, or the record that it borrows. The thread of that
  record is the **owner** of the context.
- **Source.** The context that a record borrows, written as its owner and
  the **depth**, the number of loans from the owner to the borrower, from 1
  to `MAX_LOAN_DEPTH`; or none.
- **Lender and borrower.** The two threads of a loan: the caller of a call
  and the receiver to which it is delivered.
- **Effective class.** The class at which the scheduler runs a thread: its
  own class without a source, and with one the class that
  [Lending](#lending) gives.
- **Ceiling.** The highest class at which a thread may run on a borrowed
  context, which its creator sets at its admission, not above the creator's
  class; a ceiling at or below the thread's own class lends it no higher
  class.
- **Dispatch credit.** What `available` gives for a thread at a time: the
  smaller of the remaining credit of its context and of the class ledger
  of the owner's class, both brought up to date at that time.
- **Kernel domain.** The calling domain of the kernel itself
  ([objects](../../objects-capabilities/objects/contract.md#terms)), which
  admits the root's thread at boot from the unallocated holdings.

## Entry points

The entries of the core are in the module `ledger` of `krepi-kernel`
(planned). No entry of this page is an operation of the ABI inventory: the
class, budget and ceiling of a thread are arguments of the creation of its
process, and its CPU time is a result of the query of the lifecycle
component.

| Entry point | Kind | Called by | ABI operation | Rules |
| --- | --- | --- | --- | --- |
| `Ledger::new` (planned), with the value types `ledger::Parameters` and `ledger::Error` | Function that writes nothing but the ledger it returns, host-testable | The boot wiring of each board crate, once for each CPU that it starts, with the platform parameters of the board and the value of `CNTFRQ_EL0`, before any entry from EL0 | None | [Classes](#classes), [Replenishment](#replenishment) |
| `ledger::admit` (planned) | Write entry on the copies of a write set, host-testable | The module `creation` (planned), in the write set that occupies the thread slot of a new process, after the [admission](../scheduler/contract.md#admission) checks of the scheduler; the boot of the root by the kernel root (planned), once, for the root's thread | None | [Admission and release](#admission-and-release), [Budget records](#budget-records) |
| `ledger::release` (planned) | Write entry on the copies of a write set, host-testable | The module `lifecycle` (planned), in the write set that reaps a process and releases its thread slot | None | [Admission and release](#admission-and-release) |
| `ledger::charge` (planned) | Write entry on the copies of a write set, host-testable | The [scheduler](../scheduler/contract.md#entry-points), when the dispatch of the current thread stops, by its preemption, yield, block or removal, and when `requeue` moves the current thread to another context, with the start of the dispatch and the owner of its context | None | [Charging and debt](#charging-and-debt), [CPU time](#cpu-time) |
| `ledger::replenish` (planned) | Write entry on the copies of a write set, host-testable | The write entries of this page, for each record and class ledger that they change, before they change it; and the tests. The scheduler needs no call of its own, since `available` gives the credit as brought up to date | None | [Replenishment](#replenishment) |
| `ledger::lend` (planned) | Write entry on the copies of a write set, host-testable | The module `ipc` (planned), when a call is delivered to its receiver | None | [Lending](#lending) |
| `ledger::withdraw` (planned) | Write entry on the copies of a write set, host-testable | The module `ipc` (planned), when a call ends for any reason, for its receiver and each thread downstream of it, at most `MAX_LOAN_DEPTH` in one transition | None | [Lending](#lending) |
| `ledger::available` (planned) | Read entry, host-testable | The [scheduler](../scheduler/contract.md#selection-and-time-slices), in its selection, for the deadline of a dispatch, and for the place and the reschedule flag of a thread that it makes ready or moves | None | [Charging and debt](#charging-and-debt), [Replenishment](#replenishment), [Lending](#lending) |
| `ledger::cpu_time` (planned) | Read entry, host-testable | The module `lifecycle` (planned), for the query of the CPU time of a process, and the tests | None | [CPU time](#cpu-time) |

## Extractability

The module `ledger` of the core (planned), below `kernel/src/` (planned),
follows the [provable Rust subset](../../../conventions/provable-subset.md):
the ledgers and their class ledgers, the budget records, the charge, the
replenishment, the admission and release, the loans and the CPU time. Its
items are `pub(crate)` except `Ledger::new`, the row of the entry table
that the boot wiring calls, with the value types that it takes and returns,
`ledger::Parameters`, `ledger::Ledger` and `ledger::Error`
([provable core](../../../architecture.md#the-provable-core)). The module is
in layer 4 of the
[module order](../../../architecture.md#module-order-in-the-core): it
refers to the module `objects`, for the references, the resolution of
thread slots and the write sets, and to the kernel root, which holds the
thread slots, and to no module of its own layer, such as `capabilities`,
or above, such as `scheduler`, `waits`, `ipc`, `lifecycle` and `creation`.
Its write entries receive the one kernel root by `&mut`
([rule 3](../../../conventions/provable-subset.md#3-flat-relations-and-one-kernel-root)),
and every entry other than `Ledger::new` receives the ledger of the
executing CPU and, for the write entries, the write-set buffer of that CPU
by explicit `&mut` arguments
([rule 8](../../../conventions/provable-subset.md#8-no-interior-mutability)).
The module defines no callback: the stop of a dispatch, the delivery and
end of a call, the creation and the reap of a process are composed by the
scheduler and by `ipc`, `creation` and `lifecycle`, and each entry of this
page gives only the checks and the writes of its own part.

The ledger of each CPU is in the per-CPU record of the architecture crate
(planned). Finding the record of the executing CPU and masking its
interrupts is the adapter that the objects contract lists among its
[open obligations](../../objects-capabilities/objects/contract.md#open-obligations);
lending the ledger by `&mut` for no longer than the token of the CPU lives
is an adapter of the architecture crate, outside the proof target, which
[Open obligations](#open-obligations) lists. The contract is written
before its code, so this section lists no source paths; the change that
adds the module writes its `paths` block here.

## Budget records

Every thread slot that holds a thread holds its budget record; with one
thread to a process, it is also the record of the process. A record has
these fields:

| Field | Content | Written by |
| --- | --- | --- |
| `class` | The class of the thread | `admit` |
| `ceiling` | The class of its ceiling | `admit` |
| `holdings` | One amount for each class; the one of `class` is the budget $b$ | `admit`, `release` |
| `spent` and `stamp` | The spent $s$ and the period index at which it is up to date | `admit`, `charge`, `replenish`, `release` |
| `cpu` | The CPU time | `admit`, `charge` |
| `source` | None, or the owner of the borrowed context and the depth | `admit`, `lend`, `withdraw` |
| `effective` | The effective class | `admit`, `lend`, `withdraw` |
| `pending` | The pending ticks: charges from another CPU that its own ledger has not yet added to `spent` | `admit`; a `charge` on another CPU, and the write entries that add it to `spent` |

- **One model.** The record and the class ledgers are the whole budget
  model: each thread has one budget per period, each class one cap per
  period, and every record and class of a CPU shares one epoch and one
  period.
- **Bounds.** Every holding, every budget and every cap is at most $P$,
  and $P < 2^{62}$; the `spent` of a record or a class ledger and the `cpu`
  of a record are at most the time less $E$, so below $2^{63}$, since the
  intervals of the dispatches of one CPU do not overlap and every charge
  adds one of them.
- **References.** A record names other threads only by thread references
  of the objects component: the owner in its `source`. No record holds a
  copy of the credit of another.
- **Released threads.** No `source` names a thread whose slot has been
  released: the IPC component withdraws every loan downstream of a thread
  when it settles the calls of that thread, before the reap of the
  thread's process ([Lending](#lending)). No dispatch outlives the record
  of the owner of its context either: a withdrawal during a dispatch is
  followed by the scheduler's `requeue`, which charges the dispatch up to
  that time.

## Classes

The ledger of a CPU has the class ledger of each class: its cap $C_k$,
its `spent` $S_k$ and its `stamp`. The class ledger counts every interval
that a context of a record of its class pays for, whichever thread runs
on it, and its remaining credit bounds the dispatch credit of every thread
whose context is of that class.

- **No borrowing between classes.** A class never uses the cap of
  another. The cap of a class that its threads leave unused in a period is
  lost at the next boundary, as unused credit always is
  ([Replenishment](#replenishment)).
- **One period.** Every class ledger and every record of the ledger counts
  its periods from the epoch $E$ with the period $P$, so all of them
  replenish at the same boundaries.
- **Platform parameters.** `Ledger::new(parameters, frequency, now)` takes
  the replenishment period `REPLENISH_PERIOD`, the caps `CONTROL_CAP`,
  `INTERACTIVE_CAP` and `BACKGROUND_CAP` and the kernel margin
  `KERNEL_MARGIN` of the board in microseconds, which the table of the
  scheduler's
  [platform parameters](../scheduler/contract.md#platform-parameters-and-time)
  lists, and the frequency of the counter in hertz, the value of
  `CNTFRQ_EL0`. It converts each value $u$ into
  $\lfloor u \cdot f / 10^6 \rfloor$ ticks, and the margin into
  $\lceil u \cdot f / 10^6 \rceil$ ticks, so that no conversion enlarges a
  cap or shrinks the margin. It makes these checks in this order and
  returns the first error:
  1. the frequency is not 0 (`InvalidConfiguration`);
  2. each converted value, computed without overflow, fits 64 bits
     (`Overflow`);
  3. the period is at least 1 tick and below $2^{62}$ ticks
     (`InvalidConfiguration`);
  4. the caps and the margin, summed without overflow, do not exceed the
     period (`InvalidConfiguration`).
- **Starting state.** A ledger that passes the checks has the epoch $E$
  equal to `now`, every class ledger with `spent` 0 and `stamp` 0, and an
  unallocated holding of each class equal to its cap. The values are read
  only after boot.
- **Margin.** The part of the period above the caps is the margin of the
  kernel and of interrupt handling; no class and no record holds it. Since
  the caps and the margin do not exceed the period, the dispatch credit
  that the classes give in a period leaves at least the margin to the
  kernel, the bound that the scheduler's
  [reserved control capacity](../scheduler/contract.md#reserved-control-capacity)
  relies on. An overrun of a dispatch can use the margin; it is debt of its
  record and its class, repaid by later periods.

## Charging and debt

`charge(thread, owner, since, now)` charges the interval from `since`, the
time at which the scheduler started the dispatch of `thread` or last
charged it, to `now`, the time at which that dispatch stops or moves to
another context. `owner` is the owner $O$ of the context that the dispatch
has, which `available` gave when the dispatch started and which the
scheduler keeps with the dispatch. `since` is not later than `now`, a
premise of the scheduler.

- **Context.** The interval is charged to the record of $O$: `thread`
  itself when it had no source at the start of the dispatch, and the owner
  of its source when it had one. A loan or a withdrawal during a dispatch
  does not change the record that the dispatch is charged to: the
  scheduler's `requeue` charges the dispatch up to that time to $O$ and
  continues it on the new context. The charge writes nothing in the credit
  of a borrower; the class ledger charged is that of the class of $O$,
  never that of the borrower or of the borrower's effective class.
- **Whole interval.** Every stop charges its whole interval, whatever its
  reason: the end of a time slice or of the dispatch credit, a yield, a
  block, a sleep, an exit, a fault or a kill. The interval includes the
  work of the kernel between the start of the dispatch and its stop.
- **Debt.** The part of a charge beyond the remaining credit becomes debt
  of the record, and the part beyond the remaining credit of the class
  debt of the class ledger, in full: it is not reduced, not forgiven and
  not charged to any other record.
- **Closed form.** The charge first brings the record of $O$ up to date at
  `since` ([Replenishment](#replenishment)), and then sets its `spent`
  $s$ and its `stamp` from the budget $b$ of $O$:

  ```math
  s' =
  \begin{cases}
  s + (\mathit{now} - \mathit{since})
    & \text{if } \pi(\mathit{now}) = \pi(\mathit{since}), \\
  \max\bigl(s + (e - \mathit{since}) - b,\ 0\bigr)
    + (n - 1)(P - b) + (\mathit{now} - E - \pi(\mathit{now}) P)
    & \text{otherwise},
  \end{cases}
  ```

  where $e = E + (\pi(\mathit{since}) + 1) P$ is the end of the period of
  `since` and $n = \pi(\mathit{now}) - \pi(\mathit{since})$ the number of
  boundaries that the interval crosses; the new `stamp` is
  $\pi(\mathit{now})$. The class ledger of the class of $O$ is charged by
  the same rule with its cap in place of $b$. The value equals that of a
  model that charges one tick at a time and, at each boundary, sets the
  credit to the smaller of the credit plus $b$ and $b$; a stop exactly at a
  boundary charges the old period and then replenishes.
- **CPU time.** The charge adds $\mathit{now} - \mathit{since}$ to the
  `cpu` of `thread` ([CPU time](#cpu-time)).
- **Dispatch credit.** `available(thread, now)` writes nothing and gives
  four values: the owner $O$ of the context of `thread`, `thread` itself
  without a source and the owner of its source with one; the dispatch
  credit, the smaller of the remaining credit of the record of $O$ and of
  the class ledger of its class, both as brought up to date at `now`; the
  end of the current period at `now`; and the effective class of `thread`.
  A thread whose context has a budget of 0, or
  whose context or class has debt, has the dispatch credit 0, and the
  scheduler starts no dispatch on it.
- **Other CPUs.** A charge to an owner whose record belongs to the ledger
  of another CPU adds the interval to the `pending` of that record, which
  the next write entry of this page on the owner's own CPU adds to its
  `spent` first. With one CPU every record belongs to the ledger of that
  CPU, and `pending` stays 0.
- **No other mechanism.** The model has no scheduling-context object, no
  replenishment list, no sporadic server, no timeout handler and no charge
  to an ancestor of a process: a budget is a field of a record, and a
  charge changes one record and one class ledger.

## Replenishment

Bringing a record up to date at a time $t$ applies the boundaries since
its `stamp` $q$: with $k = \pi(t) - q$ boundaries and the budget $b$, its
`spent` becomes $\max(s - k b, 0)$ and its `stamp` $\pi(t)$. A class
ledger is brought up to date by the same rule with its cap.
`replenish(target, now)` writes the result: for a thread, of its record and
of the class ledger of its class; for a class, of its class ledger. Every
write entry of this page brings the records and class ledgers that it
changes up to date at its time before it changes them, so a budget that an
admission or a release changes applies only from the time of that change.

- **One boundary.** At each boundary, the credit $r - d$ of a record becomes
  the smaller of $r - d + b$ and $b$: a debt is repaid first, and a
  positive credit never exceeds one budget. The cap of a class ledger
  replenishes it the same way. The rule above applies $k$ boundaries at
  once and equals $k$ applications of this one.
- **First termination.** Each access makes a fixed number of steps: one
  division of 64-bit values for $\pi(t)$, one multiplication and one
  subtraction, whatever the number of boundaries since the stamp. No entry
  loops over periods.
- **Second termination.** A record with debt $d$ and budget $b > 0$ has
  the dispatch credit 0, so no dispatch on its context starts and no charge
  reaches it; at each boundary its debt falls by $b$ or to 0, a measure
  that decreases strictly while it is positive, and it is 0 within
  $\lceil d / b \rceil$ boundaries. A class ledger with debt $d$ and cap
  $c > 0$ is 0 within $\lceil d / c \rceil$ boundaries by the same
  argument. A dispatch that runs at a boundary is charged by the closed
  form of [Charging and debt](#charging-and-debt), which applies the same
  rule to each boundary it crosses.
- **Budget 0.** A record with budget 0 is never replenished and has the
  dispatch credit 0; a record has budget 0 when it has given its whole
  holding of its own class to the threads that it admitted.
- **Waits and sleeps.** A record changes only by the entries of this page:
  blocking, waking and sleeping add and remove nothing, and a record that
  was blocked across boundaries has, when it is next brought up to date,
  the credit that the same boundaries give a record that was ready.
- **No overflow.** By the premises of time and the bounds of
  [Budget records](#budget-records), $k b \le \pi(t) P \le t - E < 2^{63}$
  and the end of a period is below $2^{64}$, so no step of a replenishment
  or of a charge overflows 64 bits.

## Admission and release

- **The root.** `admit(kernel, root, now)`, which the boot of the root
  makes once, gives the root's thread the class control, the ceiling
  control and every unallocated holding of the ledger as its holdings, and
  sets the unallocated holdings to 0. It refuses with `AdmissionRejected`
  when an unallocated holding is not its cap, since the root has been
  admitted already.
- **A thread.** `admit(creator, child, class, budget, ceiling, now)` admits
  the thread of a new process for the thread `creator` of the process that
  creates it. It makes these checks in this order and returns the first
  error: `budget` is not 0 (`InvalidConfiguration`); `creator` and `child`
  resolve as the objects component states; `budget` does not exceed the
  holding of `creator` of `class` (`AdmissionRejected`). The scheduler has
  checked before that `class` and `ceiling` are not above the class of
  `creator` ([admission](../scheduler/contract.md#admission)). It then
  brings the record of `creator` up to date at `now`, lowers its holding of
  `class` by `budget`, and writes the record of `child`: the `class`, the
  `ceiling`, a holding of `budget` of `class` and of 0 of the other
  classes, `spent` 0 at the stamp $\pi(\mathit{now})$, `cpu` 0, no source,
  the effective class `class` and `pending` 0.
- **The creator's budget.** An admission of a thread of the creator's own
  class lowers the creator's budget; its `spent` is kept, so the admission
  can leave the creator with less remaining credit or with debt in the
  current period. The admission of a thread of another class leaves the
  creator's budget as it was.
- **Release.** `release(owner, child, now)` releases the record of the
  thread `child` of a process that its owner reaps, with `owner` the thread
  of the owner's process. It checks that both resolve and that `child` has
  no source (`OutstandingLoan`), brings the record of `owner` up to date at
  `now`, adds each holding of `child` to the holding of `owner` of the same
  class and clears the record of `child`. The `spent` of `child`, its debt
  among it, leaves with the record; the class ledger keeps every charge
  that it has counted, so the spending of the class in its period and its
  debt are not erased by a release or a new admission.
- **Order.** A process is reaped after its children, so the holdings that
  a release returns are those that its admission gave: what its children
  took has returned to it before.
- **Conservation.** From the return of `Ledger::new` on, for each class
  $k$, the holdings of class $k$ of the records of all live threads and the
  unallocated holding of $k$ add up to $C_k$: `Ledger::new` sets the
  unallocated holding to $C_k$, and each admission and each release moves
  an amount between two of these terms. So the budgets of all threads of a
  class never add up to more than its cap.

## Lending

`lend(lender, borrower)` lends the context of `lender`: the record of
`lender` at depth 1 when it has no source, and otherwise its source, the
owner $O$ with depth $d$, at depth $d + 1$. It makes these checks in this
order and returns the first error: both resolve as the objects component
states; `borrower` has no source, and is neither `lender` nor $O$
(`OutstandingLoan`); the new depth does not exceed `MAX_LOAN_DEPTH` = 8
(`LoanDepth`). It then writes the record of `borrower` alone: its source
becomes $O$ with the new depth, and its effective class the higher of its
own class and the lower of the effective class of `lender` and the
ceiling of `borrower`.

- **Nested loans.** A borrower that calls lends the same context on, one
  level deeper, so every thread of a chain from $O$ runs on the context of
  $O$, and the effective class is bounded again by the ceiling at each
  level.
- **One holder.** The IPC component lends at the delivery of a call from
  its caller, which blocks until the call ends and withdraws the loans
  before it makes the caller ready. So the threads that use a context form
  one chain from its owner, each blocked in a call but the last, and only
  the last runs; the checks above refuse a second lender of one borrower
  and a loan back to the lender or to the owner, which a call to oneself
  and a cycle of calls would need and which the IPC component refuses
  before delivery.
- **No duplication.** A loan moves no credit and writes no `spent`; every
  charge goes to the owner of the context, so a loan neither adds credit
  nor charges any record twice, and the sum of the credits of the records
  is the same with and without it.
- **No fallback.** The dispatch credit of a borrower is that of the
  borrowed context; a borrower whose borrowed context has no credit does not
  run on its own credit until the context is replenished or the loan is
  withdrawn.
- **Withdrawal.** `withdraw(borrower)` clears the source of `borrower` and
  sets its effective class to its own class, and gives `withdrawn`; for a
  record without a source it writes nothing and gives `none`. When a call
  ends, for any reason, the IPC component withdraws its receiver and each
  thread downstream of it, at most `MAX_LOAN_DEPTH` withdrawals, and leaves
  the loans upstream as they are; a downstream thread stays blocked in its
  own call, with no context lent to it, until that call ends. For a thread
  that is ready or running when a loan or a withdrawal changes its
  context, the IPC component calls `requeue` of the scheduler, which
  charges a running dispatch up to that time and moves the thread to the
  run queue of its effective class
  ([run queues](../scheduler/contract.md#run-queues)).
- **Full return.** Every end of a call, by reply, timeout, kill, revocation
  or peer closure, withdraws in the same way: the owner's context returns
  whole, less what has been charged to it, and nothing is refunded.

## CPU time

- **Rule.** The `cpu` of a record is the sum of the intervals that
  `charge` has charged for its thread as `thread`, on its own context and
  on borrowed ones; a charge to the owner of a borrowed context adds to the
  `cpu` of the borrower that ran, not to the owner's.
- **Reading.** `cpu_time(thread)` gives the `cpu` of its record: every
  interval that `charge` has charged for it. The part of a dispatch that is
  running, from its start or its last charge, is added when the dispatch
  stops; with one CPU, a thread that is not the current thread has no such
  part.
- **Output.** The CPU time of a process is an observable output for an
  observer with OBSERVE on the process; scheduling decides it, which the
  [observable outputs](../../../security.md#observable-outputs) of the
  security model exempt from the output sources.

## Errors

| Error | Rule broken | Entries | Place in the order of errors |
| --- | --- | --- | --- |
| `InvalidConfiguration` | A counter frequency of 0, a period of 0 ticks or of $2^{62}$ ticks or more, or caps and a margin whose sum exceeds the period; a budget of 0 | `Ledger::new`; `admit` | At boot; for `admit`, the form of the register arguments |
| `Overflow` | A platform parameter whose ticks do not fit 64 bits | `Ledger::new` | At boot |
| `WrongPool` of the objects component | A reference of another pool than the thread pool | Every entry that takes a thread | Handle resolution: the type |
| `StaleReference` of the objects component | A thread reference that is not live | Every entry that takes a thread | Handle resolution: the liveness of the object |
| `OutstandingLoan` | For `lend`, a borrower that has a source, or that is the lender or the owner of the lender's context; for `release`, a record that has a source | `lend`, `release` | Object state |
| `AdmissionRejected` | A budget beyond the creator's holding of the class; the admission of the root when an unallocated holding is not its cap | `admit` | The caller's quota |
| `LoanDepth` | A loan whose depth would exceed `MAX_LOAN_DEPTH` | `lend` | Shared capacity |

- **Order.** Each entry checks in the order that its rule section states
  and returns the first error. The places of the last column are those of
  the order of errors of the
  [security model](../../../security.md#internal-choices). `LoanDepth`
  depends on the calls of other threads, so it is an error of shared
  capacity, one of the declared global flows of the
  [information-flow boundary](../../../security.md#information-flow-boundary).
- **No change on failure.** No error changes state: an entry of this page
  that returns an error leaves every record, class ledger and holding as it
  was, the copies in the write set included, and writes no counter; a
  composing operation that meets an error discards its buffer, so the
  kernel state after any failed operation equals the state before it. There
  is no exception. An error of `Ledger::new` stops the boot before any
  entry from EL0.
- **Results.** `withdraw` has no error: a record without a source is its
  result `none`. `charge`, `replenish`, `available` and `cpu_time` have no
  error of their own beyond those of the resolution of their thread, which
  their callers never meet.
- **Names.** The names are those of this contract; the numeric values of
  the errors that reach EL0 through a composing operation belong to the ABI
  inventory.

The prototype's scheduler had 23 errors. The ten below are those whose
rules are on this page; four of them, `InvalidConfiguration`,
`ClockWentBackwards`, `Object(_)` and `PermissionDenied`, are also in the
errors of the [scheduler contract](../scheduler/contract.md#errors), which
gives the place of the other thirteen and of the activation part of `Busy`
of the objects component, among them `AdmissionRejected`, which `admit`
reports here for the holdings. Here:

| Prototype error | Here |
| --- | --- |
| `InvalidConfiguration` | Kept, for the platform parameters of `Ledger::new` and a budget of 0; the form of the prototype's loan identities does not apply, since a loan has no identity |
| `ClockWentBackwards` | Not applicable: the time is an argument that does not decrease within a boot, a premise of time that no entry checks |
| `Overflow` | Kept, for the conversion of a platform parameter at boot; the overflow of a charge, of a period boundary, of an admission sum and of a count does not apply, since the bounds of [Budget records](#budget-records) and the premises of time exclude it and the counts of the prototype are not kept |
| `Object(_)` | Not kept as a wrapper: the errors of the objects component that this page meets, `WrongPool` and `StaleReference`, are returned as they are |
| `PermissionDenied` | Moved to the capabilities component: the rights of the operations that create and reap a process, CREATE and CONTROL, are checked by their lookups; a loan needs no right of its own, since it is a part of a call, and every record has a ceiling |
| `OutstandingBudget` | Not applicable: a record is released at the reap of its thread at once, its holdings return to the owner, and the spending of its class stays in the class ledger |
| `OutstandingLoan` | Kept, for a borrower that has a source or would close a cycle, and for the release of a record that has a source |
| `StaleLoan` | Not applicable: a loan has no identity; the call that made it identifies it, and the withdrawal of a record without a source is `none` |
| `LoanCycle` | Not applicable: the IPC component refuses a call to oneself and a call that closes a cycle before delivery, so no loan closes a cycle; `lend` refuses such a borrower with `OutstandingLoan` |
| `LoanDepth` | Kept, for a ninth level of depth |

## Check and execute

- `available` and `cpu_time` write nothing.
- `Ledger::new` makes the checks of [Classes](#classes) before it builds
  the ledger that it returns; it runs once for each CPU at boot and cannot
  fail after its checks.
- `admit`, `release`, `charge`, `replenish`, `lend` and `withdraw` make all
  their checks, the resolution of their threads, of the `owner` of
  `charge` and of the owner of a source among them, before their first
  write, and then change only the
  copies in the write set of their caller. The composing entry has made
  the same checks before its first write, so its write phase meets none of
  them.
- The class ledgers and the unallocated holdings are per-CPU state that
  the write entries stage in the write set with the thread slots, each
  class ledger keyed by its CPU and its class and the unallocated holdings
  by their CPU, so that the write-back of the composing operation changes
  them together with the records.
- The write phase of every entry of this page allows only `WriteSetFull`
  of `stage`, which the write sets below never reach, and the
  fault-injection points of test builds (`InjectedFault`), each of which
  discards the buffer and leaves the state from before the entry
  ([write-set transactions](../../objects-capabilities/objects/contract.md#write-set-transactions)).

The write set of each write entry of this page, by its items: the thread
slot of a thread, which holds its record, a class ledger and the
unallocated holdings:

| Entry | Write set | Items |
| --- | --- | ---: |
| `Ledger::new` | The ledger that it returns, before any token exists | - |
| `admit` | The thread slots of the creator and of the child; for the root, the thread slot of the root and the unallocated holdings | 2 |
| `release` | The thread slots of the owner and of the child | 2 |
| `charge` | The thread slot of the owner of the context; the class ledger of its class; the thread slot of the thread that ran, when it is not that owner | 3 |
| `replenish` | The thread slot; the class ledger of its class | 2 |
| `lend` | The thread slot of the borrower | 1 |
| `withdraw` | The thread slot of the borrower, when it has a source | 1 |

The withdrawal of a chain when a call ends writes at most `MAX_LOAN_DEPTH`
= 8 items of this page, and `requeue` of the scheduler, for the last thread
of the chain, adds the items that its
[check and execute](../scheduler/contract.md#check-and-execute) gives to
the same write set; the IPC component counts them with the settlement of
the call.

## Work bounds

- `Ledger::new` makes five conversions, one sum and four checks, and
  writes the ledger once, at boot.
- `admit` and `release` resolve two thread references, bring one record up
  to date and write two items; for the root, `admit` resolves one
  reference, compares three holdings with their caps and writes two items.
- `charge` resolves its thread and its `owner`, brings one record and one
  class ledger up to date at `since` and charges each with
  the closed form, and writes at most three items.
- `replenish` resolves its thread, brings one record and one class ledger
  up to date, and writes at most two items; `available` makes the same
  steps and writes nothing.
- `lend` resolves two thread references and the owner of the lender's
  source, and writes one item; `withdraw` resolves one reference and
  writes at most one item.
- `cpu_time` reads one record.
- Each bringing up to date is one 64-bit division, one multiplication and
  one subtraction; each closed-form charge is a fixed number of 64-bit
  operations ([Replenishment](#replenishment)). No entry has a loop: none
  iterates over periods, records, classes beyond three or loans.
- The component has no long operation: every entry runs to its end, and no
  progress is stored between two calls. The withdrawal of a chain is at
  most `MAX_LOAN_DEPTH` calls of `withdraw` by the IPC component in one
  transition.
- The constant is `MAX_LOAN_DEPTH` = 8, the bound of the prototype's
  synchronous budgets, which the frozen vectors test.

## Determinism

- **Time.** Every entry takes its times as arguments: `now`, and `since`
  for `charge`, which the scheduler recorded when it started or last
  charged the dispatch.
  The time of each transition is the entry
  [ND-01](../../../security.md#nd-01) of the register of
  [permitted nondeterminism](../../../security.md#permitted-nondeterminism);
  for each value of it, the rules of this page fix the result.
- **Arithmetic.** Charges, replenishments, admissions and releases are
  fixed arithmetic on the fields of the records and class ledgers and on
  the arguments; the conversion of the platform parameters rounds down,
  and up for the margin.
- **Boundaries.** A stop exactly at a boundary charges the old period and
  then replenishes; a charge across boundaries charges the old period's
  part before the first replenishment, by the closed form.
- **Context.** The record charged is the owner of the context that the
  dispatch had at its start, which `available` gives from the loans of the
  IPC component; the class charged is the owner's.
- **Effective class.** The effective class of a borrower is the rule of
  [Lending](#lending), from its own class, its ceiling and its lender's
  effective class.
- **Admission.** The class, budget and ceiling of a thread are its
  creator's arguments; the holdings that move are fixed by them.
- **Requests.** The dispatches of one CPU stop one at a time, and requests
  that change the same records take effect in the order in which they
  enter the kernel, as the
  [internal choices](../../../security.md#internal-choices) state. With
  more than one CPU, the order in which CPUs take the tokens of the
  lending fields and the pending ticks of the same records is the
  multicore interleaving that [ND-03](../../../security.md#nd-03) allows;
  for each such order, the rules of this page fix the result.

The component leaves no other choice open.

## State fields

| Field | Class | Lock or owner | Linearization point | Publication |
| --- | --- | --- | --- | --- |
| The epoch, the period, the caps and the margin of the ledger of each CPU | Per-CPU, read-only after boot | Its CPU, which `Ledger::new` builds the ledger for before any entry from EL0 | The return of `Ledger::new` | `none`: its single owner never changes |
| The `spent` and `stamp` of each class ledger, and the unallocated holdings, of the ledger of each CPU | Per-CPU | Its CPU, with its interrupts masked, which the adapter lends the ledger to by `&mut` for one entry | The write-back of the write set that changes them | `none`: its single owner never changes |
| The `class`, `ceiling`, `holdings`, `spent`, `stamp` and `cpu` of the budget record of each thread, in its thread slot | Per-CPU, with the ledger of the CPU that the record belongs to | That CPU, with its interrupts masked; a charge from another CPU goes to `pending` instead | The write-back of the write set that changes them | `none` while the record belongs to one CPU; the move of a record to the ledger of another CPU is a handover that the cross-CPU budgets of the multicore domain define |
| The `source` and `effective` of the budget record of each thread | Shared | The token of the thread slot of the borrower, which `lend`, `withdraw`, `charge`, `available` and `release` hold; with one CPU, the executing CPU | The release of the token after the write-back of the `lend` or `withdraw` that changes them | Under the token, by the release of the lock that provides it once CPUs share it |
| The `pending` of the budget record of each thread | Shared | The token of the thread slot of the owner, which a charge from another CPU and the write entries of this page on the owner's CPU hold; with one CPU it stays 0 | The release of the token after the write-back of the charge that adds to it, or of the entry that adds it to `spent` and clears it | Under the token |

The thread slots that hold the records are slots of the objects component,
whose state, generation and owner the
[objects contract](../../objects-capabilities/objects/contract.md#state-fields)
classifies. The run queues of each CPU, per-CPU like the ledger, and the
current thread with the start, the deadline and the context of its
dispatch are fields of the
[scheduler](../scheduler/contract.md#state-fields); the wait records that
tie the threads of a chain of loans are fields of the waits component. No
lock order is stated here.

## Testing obligations

- The host tests of the module `ledger` (planned) replay every vector of
  [Legacy test vectors](#legacy-test-vectors) whose entry is on this page,
  with its expected output, and write their results for the comparison
  with the specification
  ([host results](../../../formal-verification.md#host-results)); the parts
  of a vector whose entry belongs to the scheduler or the IPC component are
  driven through the entries of this page in the order that the row gives.
- Time and parameters: every test passes its times and its platform
  parameters, among them a frequency of 1,000,000 Hz, at which a
  microsecond is a tick, and the frequencies of the counters of QEMU virt
  and of the Pi 5; no test reads a counter, depends on the speed of the
  host or uses a fixed instruction count
  ([testing](../../../conventions/testing.md#determinism-and-time)).
- Boot checks: a frequency of 0; a parameter whose ticks are
  $2^{64} - 1$ and one whose ticks are $2^{64}$; periods of 1 tick and of
  $2^{62} - 1$ ticks accepted and of 0 and $2^{62}$ ticks refused; caps and
  a margin that add up to the period accepted and to one tick more refused;
  a margin that rounds up and caps that round down at a frequency that
  does not divide $10^6$. For each pair of consecutive checks whose errors
  differ, parameters that break both give the error of the earlier.
- Closed form: a property test with fixed seeds compares `charge` with an
  independent model that charges one tick at a time, for periods from 1 to
  1,000, budgets from 0 to the period, `spent` from 0 to three periods and
  intervals that start in any period and cross up to five boundaries, for
  a record and for a class ledger.
- Terminations: replenishments across $0$, $1$ and $10^{12}$ boundaries
  make the same number of steps; a record with debt $d$ and budget $b$
  that is not charged has, at each boundary, a smaller debt or 0, and 0
  after $\lceil d / b \rceil$ boundaries, for $d$ from 1 to $5b$; a record
  with budget 0 is never replenished.
- Conservation: a property test admits and releases threads in a tree of
  processes of every class, among them creators that give their whole own
  budget away, and checks after every write-back that the holdings of each
  class and its unallocated holding add up to its cap.
- Loans: chains of every depth from 1 to 8 and a ninth loan refused; the
  withdrawal of the receiver of a call in the middle of a chain, which
  leaves the upstream loans; the effective class for each of the 27
  combinations of own class, ceiling and lender's effective class; and
  intervals on a borrowed context, which change the `spent` of the owner
  and of the owner's class only; and a loan and a withdrawal during a
  dispatch, after which the interval up to the change stays charged to the
  owner of the context that the dispatch had.
- For each error of [Errors](#errors), a call that gives it leaves every
  record, class ledger and holding as before, compared field by field.
- Write sets: for each fault-injection point, an operation that fails there
  leaves the records and ledgers as before; the largest write set of each
  entry is reached and stays within the item counts of
  [Check and execute](#check-and-execute).
- QEMU tests: the boot of QEMU virt with its platform parameters passes
  `Ledger::new`, and a thread that spins from EL0 is charged by the
  scheduler's preemption, once the scheduler and the creation operations
  exist.
- The tests take their expected values from this page, from the vectors and
  from independent models, never from an earlier run of the code under test
  ([testing](../../../conventions/testing.md#independent-evidence)).

## Open obligations

The module `ledger` has no `unsafe` code, no assembly and no MMIO, and its
entries are to be covered by its targets. An entry that a later contract
adds to the ledger beyond the entries of this page is an open obligation of
the contract that adds it, carried by the proof of object lifetimes, waits
and sequential composition, by release 0.2. The entries receive the ledger
of the executing CPU from an adapter of the architecture crate
([rule 8](../../../conventions/provable-subset.md#8-no-interior-mutability));
finding the per-CPU record and masking interrupts is the row of the
[objects contract](../../objects-capabilities/objects/contract.md#open-obligations)
for that record, and the lending of the ledger is the row below.

| Obligation | Kind | Verified state | Carrier | Stage |
| --- | --- | --- | --- | --- |
| `kernel/arch/src/percpu.rs#Cpu::ledger_mut` (planned) | `code` | - | The proof of the SMP primitives and of the concurrency backend | `0.2` |

## Legacy test vectors

The vectors are host tests of the prototype tree at
`prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`, 45 in all. Their
expected outputs are those that the test bodies assert, written in the
rules of this page. The vectors are not yet in a file of the repository,
so the section holds no `vectors` block.

| File | Vectors |
| --- | ---: |
| `src/scheduler/budget/credit.rs` | 2 |
| `src/scheduler/budget/scopes/tests/accounting.rs` | 8 |
| `src/scheduler/budget/scopes/tests/lifecycle.rs` | 3 |
| `src/scheduler/budget/tests.rs` | 3 |
| `src/scheduler/budget/tests/accounting.rs` | 9 |
| `src/scheduler/budget/tests/failures.rs` | 2 |
| `src/scheduler/budget/tests/lifecycle.rs` | 2 |
| `src/scheduler/budget/tests/loan_scopes.rs` | 2 |
| `src/scheduler/budget/tests/loans.rs` | 11 |
| `src/scheduler/budget/tests/waits.rs` | 3 |

- `src/scheduler` holds 114 tests. The 45 above assert chiefly charges,
  replenishment, debt, loans and their withdrawal, and are frozen here; the
  other 69, which assert chiefly selection, time slices, preemption,
  blocking and readiness, classes and admission, and removal, are vectors
  of the [scheduler contract](../scheduler/contract.md#legacy-test-vectors):
  2 of `budget/scopes/tests.rs`, 8 of `budget/scopes/tests/admission.rs`,
  4 of `budget/scopes/tests/lifecycle.rs`, 5 of `budget/tests.rs`, 8 of
  `budget/tests/failures.rs`, 6 of `budget/tests/lifecycle.rs`, 6 of
  `budget/tests/waits.rs`, and the 14, 11 and 5 of `tests.rs`,
  `tests/failures.rs` and `tests/waits.rs`.
- The id of a vector is the path of its file below `src/`, without every
  path component `tests` and the suffix `.rs`, with `/` and `_` written as
  `-`,
  followed by the position of its test among all the tests of that file,
  counted from 1. The positions that this page skips are the vectors of the
  scheduler contract.

A vector of this page is one test function. The vector file is to hold one
line for each case of it through an entry of this page, with the id
`<vector>.<n>`, `n` counting those cases from 1 in the order of the test; a
case that its row marks not applicable has no line, and a vector whose
Entry column names no entry of this page has none.

**Notation.** Times, amounts and counts are decimal ticks and counts. A
ledger is written `period=<P> caps=<c>/<i>/<b> margin=<M> epoch=<E>`, with
the caps of control, interactive and background, as `Ledger::new` gives it
for parameters in microseconds at a frequency of 1,000,000 Hz. A process
and its thread
have one name. "X admits T in class k with b" is
`admit(X, T, k, b, k, now)`, with the ceiling the class itself unless the
row gives another; R is the root's thread, admitted at the epoch, which
holds every cap and which no vector makes ready, and its holdings fall by
what it admits. "T runs from s to t" is a dispatch of T that the scheduler
starts at s and stops at t, which `charge(T, O, s, t)` accounts, with O the
owner of the context that `available` gives for T at s; a deadline,
where the row gives one, is that of the scheduler's selection, from
`available`. "Nothing is selectable at t" is the scheduler's selection at t
finding no ready thread whose dispatch credit is above 0. A record is
written by its remaining credit and its debt, `remaining` and `debt`, as
brought up to date at the time of the row, and `cpu` for its CPU time; a
class by those of its class ledger. "A loan A to B" is `lend(A, B)`, which
the IPC component makes when it delivers the call of A to B; "a
withdrawal of B" is `withdraw(B)`. Blocking, waking and sleeping are the
waits component's and the scheduler's, and change no record. The output
of a call is `ok`, followed by its fields, or `err=<error>`.

**Fixtures.**

- `budget/tests.rs`, `budget/tests/` and `budget/scopes/tests/`:
  `period=100 caps=20/50/20 margin=10 epoch=0`, with the time slice of the
  scheduler 10. The prototype's sum of caps had to be below the period,
  and its 10 ticks of slack are the margin.
- `budget/tests/loans.rs` also starts from its `blocked_caller`: R admits A
  in control with 20; A runs from 0 to 2 and calls; R admits B and C in
  background with 10 each, with the ceiling control. A row that admits D
  admits it in interactive with 50.
- `budget/credit.rs` tests the arithmetic of a record alone, with the
  epoch 0.

**Vectors of a property.** `scheduler-budget-credit-1` and
`scheduler-budget-credit-2` assert a property over a generated family of
inputs; their rows state the property and the generation rule.

**Behaviour changes.** These rules differ from the prototype:

- An admission carves a thread's budget from its creator's holding, and
  the reap returns it; a charge changes the record of the context and its
  class only. The prototype's CPU scopes, with their roots, delegation,
  scoped admission, receipts, generations, the charge of every ancestor
  and the refusal to release a scope with spending (`OutstandingBudget`,
  `DuplicateOwner`, `StaleScope`), do not apply; where a vector asserts the
  spending of a scope, its row gives that of the record or of the class.
- A process has one thread, so the prototype's replacement threads within
  one process or scope do not apply; a thread admitted after a reap is the
  thread of a new process, with a record of its own.
- The time is an argument that does not decrease within a boot and stays
  below $2^{63}$: the prototype's refusals of a time before the last
  (`ClockWentBackwards`) and its overflows at times near $2^{64}$ do not
  apply.
- A record keeps its `spent`, `stamp` and CPU time, and a class ledger its
  `spent` and `stamp`: the prototype's counts of replenishments, of late
  stops and of charged ticks are not kept, and where a vector asserts one,
  its row gives the credit or the number of boundaries that it stands for;
  its counts of dispatches, preemptions, yields, sleeps, waits and wake-ups
  are not on this page; the overflow of any count does not apply.
- A loan has no identity: the prototype's loan identities with their
  registry, their staleness (`StaleLoan`), duplicates (`Duplicate`) and form
  (`InvalidConfiguration`) do not apply, and a withdrawal without a source
  is `none`.
- No loan closes a cycle, since the IPC component refuses a call to oneself
  and a cycle of calls: the prototype's `LoanCycle` does not apply.
- Every record has the ceiling that its creator gives at its admission:
  the prototype's services without a ceiling,
  which could not borrow (`PermissionDenied`), and its later change of a
  ceiling do not apply.
- A dispatch is charged to the context that it had at its start, and a
  change of a loan during a dispatch is followed by `requeue` of the
  scheduler, which charges the dispatch up to that time: the prototype's
  refusals to change a loan during an unsettled dispatch (`Busy`) do not
  apply.
- A lender blocks in its call until the IPC component has withdrawn its
  loans, so the prototype's refusals to wake, kill, remove or lend again
  from a lender while its loan is out are rules of that composition, not
  of this page; this page refuses the release of a borrower and a second
  lender of one borrower.
- The ready, running, sleeping and waiting states and the next wake-up are
  the scheduler's; the rows give them where the test asserts them, and the
  ledger gives the end of the period for the next replenishment.
- The caps and the margin may add up to the period, where the prototype
  required the caps to be below it.
- References carry no rights: the prototype's observation-only handles of
  a budget source and its lenders with restricted rights do not apply.

### `src/scheduler/budget/credit.rs`

`src/scheduler/budget/credit.rs`, 2 vectors, on the arithmetic of a
record.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `scheduler-budget-credit-1` | 143 | `active_accounting_matches_independent_tick_oracle` | Property. For each period $P$ of 3, 7, 17 and 100, budget $b$ of 1, $\lfloor P/2 \rfloor$ and $P - 1$, `spent` $s$ of 0, $\lfloor b/2 \rfloor$, $b$, $b + 7$ and $3P$ up to date in period 0, `since` of 0, 1, $\lfloor P/2 \rfloor$ and $P - 1$, and each `now` from `since` to `since` $+ 5P - 1$: the `spent` after `charge` from `since` to `now` equals that of the tick model, which starts from the credit $b - s$, takes 1 for each tick from `since` to `now` and, at each boundary, sets the credit to the smaller of the credit plus $b$ and $b$ | `charge` |
| `scheduler-budget-credit-2` | 162 | `idle_refill_matches_repeated_capped_credit_without_banking` | Property. For each budget $b$ of 0, 1, 7 and 23, `spent` $s$ of 0, 1, 17 and 1000, and $k$ from 0 to 29 boundaries: the `spent` that `replenish` gives after $k$ boundaries equals that of $k$ applications of the rule that sets the credit $b - s$ to the smaller of the credit plus $b$ and $b$; with $b$ = 0 it never changes. The prototype's two cases with `spent`, budget and boundaries of $2^{64} - 1$ lie outside the premises of time and the bounds of a record, and have no line | `replenish` |

### `src/scheduler/budget/scopes/tests/accounting.rs`

`src/scheduler/budget/scopes/tests/accounting.rs`, 8 vectors; their
scopes are records and classes here.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `scheduler-budget-scopes-accounting-1` | 19 | `a_cross_period_stop_matches_independent_credit_at_every_ancestor` | For each $t$ of 0, 9, 10, 99, 100, 101, 267 and 999, on a fresh ledger: R admits T in interactive with 10; T runs from 0, with the deadline 10, to $t$. T then has `remaining` and `debt` 10 and 0, 1 and 0, 0 and 0, 0 and 89, 0 and 80, 0 and 81, 0 and 237, 0 and 899, the tick model with the limit 10, and the interactive class 50 and 0, 41 and 0, 40 and 0, 0 and 49, 0 and 0, 0 and 1, 0 and 117, 0 and 499, the tick model with the limit 50; T's `cpu` is $t$. The prototype's three ancestor scopes of 40, 30 and 20 above T do not apply: a charge reaches the record and its class only | `admit`, `charge`; the scheduler, for the deadline |
| `scheduler-budget-scopes-accounting-2` | 45 | `sibling_service_charges_the_shared_ancestor_once_per_elapsed_interval` | R admits A in interactive with 30 and D with 20; A admits B with 20 and B admits C with 10, so that A, B and C have the budget 10 each and D 20. A, B, C, D and D run, in this order, for 10 ticks each from 0, 10, 20, 30 and 40: A, B and C have `spent` 10 and D 20, each with `remaining` 0, and the interactive class `remaining` 0 and `debt` 0; nothing is selectable at 50, and the end of the period is 100. The prototype's ancestor totals of 30, 20 and 10 do not apply: no ancestor is charged | `admit`, `charge`, `available` |
| `scheduler-budget-scopes-accounting-3` | 73 | `sleep_wait_and_yield_cannot_refill_parent_credit` | For a yield, a sleep until 3 and a block that ends at 3 in turn: R admits T in control with 20; T runs from 0 to 3: `remaining` 17; T runs from 3, with the deadline 13, to 20: its dispatch credit is 0 and nothing is selectable at 20 | `admit`, `charge`, `available` |
| `scheduler-budget-scopes-accounting-4` | 95 | `parent_debt_throttles_replacement_threads_without_harming_other_roots` | R admits O in interactive with 20 and Q with 30; O runs from 0 to 45 and exits: O has `debt` 25 and the interactive class `remaining` 5. At the reap of O, `release` returns its 20 to R; the class keeps its spending of 45. Q, of the other root, runs from 45 to 50 with the dispatch credit 5 that the class leaves it, and is selected again at 100, where the class has `remaining` 50. The prototype's replacement thread in the scope of O, which the debt of 25 of that scope throttles until 200, does not apply: a process has one thread, the debt of O leaves with its record, and a process that R admits in its place has a record of its own, which only the class ledger limits | `admit`, `charge`, `release`, `available` |
| `scheduler-budget-scopes-accounting-5` | 124 | `ancestor_credit_clamps_a_fresh_threads_timer_deadline` | R admits P in control with 20; P runs from 0 to 17 and exits; at its reap `release` returns 20 to R, and R admits Q in control with 20: Q has `remaining` 20 and the dispatch credit 3, which the control class's `remaining` 3 bounds, and runs from 17 with the deadline 20. The prototype's ancestor scope is the class ledger here | `admit`, `charge`, `release`, `available`; the scheduler, for the deadline |
| `scheduler-budget-scopes-accounting-6` | 140 | `scope_overflow_cannot_partially_charge_other_scopes_or_advance_time` | Not applicable: the test sets the spending of a scope to $2^{64} - 1$; there is no scope, and the `spent` of a record and of a class stays below $2^{63}$, so a charge does not overflow | None |
| `scheduler-budget-scopes-accounting-7` | 160 | `huge_idle_gaps_repay_empty_scope_debt_without_banking_credit` | R admits P in control with 20; P runs from 0 to 250 and faults: the control class has `debt` 190. P's reap releases its record at once, where the prototype refused the release of its scope with `OutstandingBudget`. At $10^{12}$ nothing is selectable, and the control class has `remaining` 20 and `debt` 0, brought up to date across $10^{10} - 2$ boundaries in one step, and no credit beyond its cap | `admit`, `charge`, `release`, `replenish` |
| `scheduler-budget-scopes-accounting-8` | 179 | `clock_and_period_overflow_failures_preserve_scope_ledgers` | Not applicable: a time before the last, the prototype's `ClockWentBackwards`, and a time of $2^{64} - 1$, its `Overflow`, lie outside the premises of time, which no entry checks | None |

### `src/scheduler/budget/scopes/tests/lifecycle.rs`

`src/scheduler/budget/scopes/tests/lifecycle.rs`, 3 vectors; its tests at
positions 2, 4, 5 and 6 are vectors of the scheduler contract.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `scheduler-budget-scopes-lifecycle-1` | 4 | `removing_a_thread_preserves_its_scope_spending_and_reservation_root` | R admits P in control with 20; P runs from 0 to 20 and exits; at its reap `release` returns 20 to R at once, where the prototype kept the reservation of 20 of the scope in the class and refused the release of the scope with `OutstandingBudget`. R admits Q in control with 20: Q has `remaining` 20 and the dispatch credit 0, since the control class has `remaining` 0, and nothing is selectable at 20 | `admit`, `charge`, `release`, `available` |
| `scheduler-budget-scopes-lifecycle-3` | 46 | `partial_period_spending_prevents_scope_recreation_before_replenishment` | R admits P in control with 20, and P admits Q with 10, so that P and Q have the budget 10 each; Q runs from 0 to 3 and exits: Q has `debt` 0. At its reap `release` returns 10 to P, whose budget is 20 again; the control class keeps `remaining` 17 until 100, where it has 20. P admits a new process S with 10: S has `remaining` 10. The prototype's refusals to release and re-create a scope with spending in its period, `OutstandingBudget`, `DuplicateOwner` and `StaleScope`, do not apply: the spending stays in the class ledger | `admit`, `charge`, `release`, `replenish` |
| `scheduler-budget-scopes-lifecycle-7` | 161 | `maximum_tree_depth_has_bounded_charging_and_cleanup` | R admits N0 in control with 20, and each of N0 to N4 admits the next of N1 to N5 with 20, so that N0 to N4 have the budget 0 and N5 has 20; N5 runs from 0 to 10 and exits: N5 has `remaining` 10 and the control class `remaining` 10, one record and one class charged where the prototype charged six scopes; N0 to N4, with the budget 0, are not replenished and have the dispatch credit 0, and nothing is selectable at 100. The reaps then release N5, N4, N3, N2, N1 and N0 in this order, each returning 20 to its owner, and R holds 20 of control again | `admit`, `charge`, `release`, `available` |

### `src/scheduler/budget/tests.rs`

`src/scheduler/budget/tests.rs`, 3 vectors; its tests at positions 1, 2,
3, 5 and 7 are vectors of the scheduler contract.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `scheduler-budget-4` | 125 | `a_high_class_cannot_borrow_unused_lower_class_capacity` | R admits T in control with 20; T runs from 0 to 10 and from 10 to 20: nothing is selectable at 20, while the interactive class has `remaining` 50 and the background class 20, which no thread of control uses; the end of the period is 100 | `admit`, `charge`, `available` |
| `scheduler-budget-6` | 155 | `no_positive_credit_accumulates_after_many_idle_periods` | R admits T in control with 20; T runs from 0 to 3; selected at $10^{12}$, T has `remaining` 20 and the control class 20, brought up to date across $10^{10}$ boundaries in one step. The prototype's count of 10,000,000,000 replenishments is that number of boundaries, which `replenish` computes and does not count | `admit`, `charge`, `replenish`, `available` |
| `scheduler-budget-8` | 182 | `epoch_offsets_align_replenishment_to_one_shared_period` | The ledger `period=100 caps=20/50/20 margin=10 epoch=37`. R admits A in control with 20, and A runs from 40 to 60; R admits B in background with 20, and B runs from 135 to 137: the current period starts at 137, A and B each have `remaining` 20, and A is selected at 137 | `Ledger::new`, `admit`, `charge`, `available`; the scheduler, for the selection |

### `src/scheduler/budget/tests/accounting.rs`

`src/scheduler/budget/tests/accounting.rs`, 9 vectors. In each, R admits T
in control with 20 unless the row says otherwise.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `scheduler-budget-accounting-1` | 4 | `same_period_overrun_is_charged_and_repaid_before_full_credit_returns` | T runs from 0 to 27: the charge is the 27 ticks, all of them, and T has `debt` 7 and the control class `debt` 7; nothing is selectable at 27; at 100 T runs with the deadline 110 and `remaining` 13; it stops at 110 and runs from 110 with the deadline 113. The prototype's count of one late stop is not kept | `admit`, `charge`, `available`; the scheduler, for the deadlines |
| `scheduler-budget-accounting-2` | 27 | `stop_across_many_boundaries_matches_explicit_split_charges` | T runs from 0 to 10, and from 90 to 250: T has `remaining` 0, `debt` 110 and `cpu` 170, and the control class `debt` 110; the end of the period is 300; at 700 nothing is selectable and T has `debt` 10; at 800 T runs with the deadline 810, `debt` 0 and `remaining` 10. The prototype's count of 2 replenishments is the two boundaries 100 and 200 of the charge | `admit`, `charge`, `replenish`, `available` |
| `scheduler-budget-accounting-3` | 51 | `first_boundary_does_not_forget_service_in_the_final_period` | T runs from 90 to 110: T has `remaining` 10 and `cpu` 20, and the control class `remaining` 10 | `admit`, `charge` |
| `scheduler-budget-accounting-4` | 63 | `exact_boundary_replenishes_after_charging_the_old_period` | T runs from 90 to 100: T has `remaining` 20 and `cpu` 10, and the end of the period is 200 | `admit`, `charge`, `available` |
| `scheduler-budget-accounting-5` | 75 | `short_yields_and_immediate_sleeps_never_refresh_credit` | For a yield and for a sleep until 0 in turn: T runs from $n$ to $n + 1$ for each $n$ from 0 to 19, and after each has `remaining` $19 - n$; nothing is selectable at 20, T has `cpu` 20, and the end of the period is 100. The prototype's count of no wake-up is the waits component's: a sleep whose time has come does not block | `admit`, `charge`, `available` |
| `scheduler-budget-accounting-6` | 93 | `sleeping_preserves_spending_and_period_debt_before_waking` | T runs from 0 to 45 and sleeps until 150: `debt` 25; at 150 nothing is selectable and T has `debt` 5, and the end of the period is 200; at 200 T runs with the deadline 210 and `remaining` 15. The prototype's count of one wake-up is the waits component's | `admit`, `charge`, `replenish`, `available` |
| `scheduler-budget-accounting-7` | 109 | `every_stop_reason_charges_even_when_before_the_timer_deadline` | For a yield, a sleep until 50, an exit with the code 7, a fault and a kill in turn: T runs from 0 to 3: the charge is 3 ticks, and T has `remaining` 17 and `cpu` 3 and the control class `remaining` 17 | `admit`, `charge` |
| `scheduler-budget-accounting-8` | 129 | `another_thread_and_class_refill_as_idle_while_active_thread_carries_debt` | R admits A and B in interactive with 25 each and C in background with 20; A runs from 0 to 5, B from 5 to 15 and C from 15 to 20, each then sleeping; A runs from 90 to 250: A has `debt` 100, B `remaining` 25, C `remaining` 20, the background class `remaining` 20 and the interactive class `debt` 50 | `admit`, `charge`, `available` |
| `scheduler-budget-accounting-9` | 151 | `trillion_period_active_gap_is_accounted_without_period_iteration` | T runs from 0 to $10^{14}$: T has `cpu` 100,000,000,000,000 and `debt` 79,999,999,999,980, in one step across $10^{12}$ boundaries; nothing is selectable at $10^{14}$. The prototype's count of $10^{12}$ replenishments is that number of boundaries | `admit`, `charge`, `available` |

### `src/scheduler/budget/tests/failures.rs`

`src/scheduler/budget/tests/failures.rs`, 2 vectors; its tests at
positions 1 to 6, 9 and 10 are vectors of the scheduler contract.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `scheduler-budget-failures-7` | 147 | `unrepresentable_period_boundary_does_not_refill_wake_or_advance_time` | Not applicable: the selection at $2^{64} - 2$, the prototype's `Overflow`, lies outside the premise that a time stays below $2^{63}$, under which the end of every period is representable | None |
| `scheduler-budget-failures-8` | 159 | `stop_overflow_preserves_every_ledger_and_running_context` | Not applicable: the test sets a count to $2^{64} - 1$; the `spent` and `cpu` of a record and the `spent` of a class stay below $2^{63}$, and the prototype's counts of preemptions, late stops and replenishments are not kept | None |

### `src/scheduler/budget/tests/lifecycle.rs`

`src/scheduler/budget/tests/lifecycle.rs`, 2 vectors; its tests at
positions 1, 2 and 5 to 8 are vectors of the scheduler contract.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `scheduler-budget-lifecycle-3` | 39 | `termination_and_removal_preserve_class_spending_for_new_threads` | R admits A in control with 20, after which R holds 0 of control; A runs from 0 to 12 and exits; at its reap `cpu_time(A)` is 12 and `release` returns 20 to R, and the control class has `remaining` 8. R admits B with 20: `remaining` 20 and the dispatch credit 8; B runs from 12 with the deadline 20, and is killed at 20; after its reap R admits C with 20: nothing is selectable at 20, and the end of the period is 100. The prototype's class reservations of 20 and 0 are R's holdings of 0 and 20 of control, and its one throttled thread is C, ready with the dispatch credit 0 | `admit`, `charge`, `cpu_time`, `release`, `available` |
| `scheduler-budget-lifecycle-4` | 62 | `removed_thread_debt_remains_in_class_ledger_until_repaid` | R admits A in control with 20; A runs from 0 to 45 and faults; at its reap `release` returns 20 to R, and the control class keeps `debt` 25. R admits B with 20: at 100 nothing is selectable, B has `remaining` 20 and the dispatch credit 0, and the class `debt` 5; at 200 B runs with the deadline 210 and the dispatch credit 15 | `admit`, `charge`, `release`, `available` |

### `src/scheduler/budget/tests/loan_scopes.rs`

`src/scheduler/budget/tests/loan_scopes.rs`, 2 vectors.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `scheduler-budget-loan-scopes-1` | 5 | `borrowed_execution_debits_caller_ancestors_and_retains_debt_after_recreation` | R admits P in interactive with 40 and S in background with 20, with the ceiling control; P admits C with 20, so that P and C have the budget 20 each. C runs from 0 to 1 and calls S: a loan C to S; S runs from 1 to 65: C has `debt` 45 and `cpu` 1, S has `remaining` 20 and `cpu` 64, the interactive class has `debt` 15, and P, an ancestor, is not charged. After the withdrawal of S and the kill and reap of C, `release` returns 20 to P and C's debt leaves with its record, while the interactive class keeps `debt` 15; a loan from C is then `err=StaleReference`, the prototype's `UnknownThread`. The prototype's ancestor debt of 25, its observation-only handle of the budget source and its replacement thread of C do not apply: no ancestor is charged, references carry no rights, and a process has one thread | `admit`, `lend`, `charge`, `withdraw`, `release` |
| `scheduler-budget-loan-scopes-2` | 49 | `charged_counter_overflow_rolls_back_all_borrowed_ledgers` | Not applicable: the test sets the prototype's count of charged ticks, which no record keeps, to $2^{64} - 1$; the `spent` of a record stays below $2^{63}$ | None |

### `src/scheduler/budget/tests/loans.rs`

`src/scheduler/budget/tests/loans.rs`, 11 vectors, each from the fixture
`blocked_caller` unless the row says otherwise.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `scheduler-budget-loans-1` | 23 | `one_context_bills_caller_and_keeps_service_credit_separate` | R admits D. A loan A to B: B's effective class is control, and B, not D, is selected at 2; B runs from 2 to 9: A has `remaining` 11 and `cpu` 2, B `cpu` 7 and `remaining` 10, the control class `remaining` 11 and the background class 20. The withdrawal of B is `ok withdrawn`: B's effective class is background and its dispatch credit 10; A is made ready with `remaining` 11. The prototype's dispatch credit of 0 of A while its context is lent is A's blocking in its call, outside this page | `admit`, `lend`, `charge`, `withdraw`, `available`; the scheduler, for the selection |
| `scheduler-budget-loans-2` | 46 | `nested_priority_is_clipped_at_each_hop_but_charges_original_class` | R admits B with the ceiling interactive instead of control, the prototype's later change of the ceiling. A loan A to B: B's effective class is interactive; B runs from 2 to 5 and calls C: a loan B to C gives C the source A at depth 2 and the effective class interactive; C runs from 5 to 12: the control class has `remaining` 8, the interactive class 50 and the background class 20. The withdrawal of C leaves C without a source and B with the source A at depth 1; the withdrawal of B leaves B without a source | `admit`, `lend`, `charge`, `withdraw` |
| `scheduler-budget-loans-3` | 81 | `withdrawal_of_outer_call_detaches_downstream_without_automatic_relending` | A loan A to B; B runs from 2 to 3 and calls C: a loan B to C. A's call ends: the IPC component withdraws B and C, two withdrawals, each `ok withdrawn`; B stays blocked in its call to C, and C's effective class is background. A further withdrawal of C is `ok none`, where the prototype refused the identity of the old loan with `StaleLoan`; A is made ready with `remaining` 17 | `lend`, `charge`, `withdraw` |
| `scheduler-budget-loans-4` | 98 | `exhausted_loan_cannot_fall_back_to_own_credit_or_duplicate_refill` | The prototype first ends C, which plays no part here. A loan A to B; B runs from 2 to 20: B has `remaining` 10 and the dispatch credit 0; nothing is selectable at 20, and the end of the period is 100; at 100 B is selected, with A's `remaining` 20 after one boundary; B stops at 103; after the withdrawal of B, A has `remaining` 17, one boundary applied once | `lend`, `charge`, `available`, `withdraw` |
| `scheduler-budget-loans-5` | 119 | `late_stop_keeps_all_cross_period_debt_on_original_context` | A loan A to B; B runs from 2 to 250: A has the `debt` of the tick model over the 250 ticks from the credit 20 with the boundaries 100 and 200, 190, and so has the control class; B has `debt` 0; after the withdrawal of B, A's dispatch credit at 250 is 0. The prototype's count of 250 charged ticks is A's `spent` of 210, the 250 ticks less two replenishments of 20 | `lend`, `charge`, `withdraw`, `available` |
| `scheduler-budget-loans-6` | 142 | `unsettled_dispatch_cannot_change_any_loan_or_erase_charge` | Not applicable: a dispatch is charged to the context that it had at its start, and `requeue` of the scheduler charges it up to a change of its loan, so no change erases a charge and the prototype's refusals during an unsettled dispatch, `Busy` for a withdrawal, a reconciliation, a change of the ceiling and a loan, do not exist; the ceiling is set at admission | None |
| `scheduler-budget-loans-7` | 155 | `exact_receipts_and_attached_lifecycle_reject_without_mutation` | A loan A to B: `release` of B is `err=OutstandingLoan` and leaves every record as before; after the withdrawal of B, a loan A to C is `ok`. The prototype's refusal of a wrong loan identity (`StaleLoan`) and its refusals to wake, kill or remove A, to kill B, to change the ceiling of B and to lend from A to C while the loan is out do not apply on this page: a loan has no identity, the ceiling is set at admission, and A blocks in its call until the IPC component has withdrawn the loan | `lend`, `release`, `withdraw` |
| `scheduler-budget-loans-8` | 178 | `self_cycles_and_unauthorized_services_fail_atomically` | A loan A to A is `err=OutstandingLoan`. A loan A to B; B runs from 2 to 3 and calls A: a loan B to A, to the owner of B's context, is `err=OutstandingLoan`. Both refusals leave every record as before; the IPC component refuses the calls that would need them, a call to oneself and a call that closes a cycle, before delivery, so the prototype's `LoanCycle` does not arise. The prototype's loan to D without a ceiling (`PermissionDenied`) does not apply, since every record has a ceiling, nor does its lender with rights restricted to OBSERVE, since references carry no rights | `lend` |
| `scheduler-budget-loans-9` | 198 | `depth_is_bounded_and_all_downstream_edges_are_withdrawn` | The ledger `period=1000 caps=100/600/200 margin=100 epoch=0`. R admits T0 in control with 100, and T1 to T9 in background with 10 each, with the ceiling control. For $n$ from 0 to 7, T$n$ runs from $n$ to $n + 1$ and calls T$(n+1)$: a loan T$n$ to T$(n+1)$, at depth $n + 1$. T8 runs from 8 to 9 and calls T9: the loan T8 to T9, at depth 9, is `err=LoanDepth` and leaves every record as before. The end of the call of T0: the IPC component withdraws T1 to T8, eight withdrawals, and no record has a source | `admit`, `lend`, `charge`, `withdraw` |
| `scheduler-budget-loans-10` | 232 | `class_pairs_never_double_bill_or_move_consumption_to_inherited_priority` | Without the fixture, for each of the nine pairs of a class X and a class Y: R admits A in X with 10; A runs from 0 to 0 and calls; R admits B in Y with 5, with the ceiling control; a loan A to B; B is selected at 0 with the external deadline 4, which is its deadline, and stops at 7: the class X has `remaining` its cap less 7, and the other classes their caps; A has `remaining` 3 and B 5; the 7 ticks are charged to A, none to B | `admit`, `lend`, `charge`; the scheduler, for the external deadline |
| `scheduler-budget-loans-11` | 261 | `second_donor_cannot_reuse_an_existing_recipient_or_identity` | A loan A to B; R admits D, which a test makes block in a call: a loan D to B is `err=OutstandingLoan` and leaves every record as before. The prototype's duplicate loan identity (`Duplicate`) and its identities with a part of 0 (`InvalidConfiguration`) do not apply: a loan has no identity | `admit`, `lend` |

### `src/scheduler/budget/tests/waits.rs`

`src/scheduler/budget/tests/waits.rs`, 3 vectors, in each of which R
admits T in control with 20; its tests at positions 4 to 9 are vectors of
the scheduler contract.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `scheduler-budget-waits-1` | 4 | `external_wait_keeps_credit_and_cannot_launder_repeated_short_dispatches` | Four times, for $n$ from 0 to 3: T runs from $5n$ to $5n + 5$, blocks and is made ready at $5n + 5$, with the same `remaining` and `debt` before and after the block and no boundary between. Then T has `remaining` 0 and `cpu` 20; nothing is selectable at 20, and the end of the period is 100. The prototype's counts of waits, wake-ups and throttled threads are not on this page | `admit`, `charge`, `available` |
| `scheduler-budget-waits-2` | 31 | `waiting_spans_periods_without_auto_wake_or_accumulating_unused_credit` | T runs from 0 to 45 and blocks: `debt` 25; at 100 T has `debt` 5 and stays blocked, which no boundary changes; made ready at 1000, T has `remaining` 20 after 10 boundaries and `cpu` 45 | `admit`, `charge`, `replenish` |
| `scheduler-budget-waits-3` | 51 | `waiting_wake_after_one_period_keeps_unpaid_debt_and_reservation` | T runs from 0 to 45 and blocks; made ready at 100, T has `debt` 5, the control class `debt` 5, and R still holds 0 of control, the prototype's reservation of 20; nothing is selectable at 100 | `admit`, `charge`, `replenish`, `available` |

## References

- The kernel's own rules, which this page instantiates:
  [Scheduling and budgets](../../../architecture.md#scheduling-and-budgets)
  for the per-domain budgets with replenishment periods, the budget of a
  child cut from its parent's, the control capacity and the overhead set
  aside at admission and the per-CPU budget records;
  [IPC, notifications and waits](../../../architecture.md#ipc-notifications-and-waits)
  for budget lending within a ceiling, its one active holder and its
  withdrawal before the caller is woken; the execution model under
  [System calls and the ABI](../../../architecture.md#system-calls-and-the-abi)
  for entries that run to completion and blocking by wait records; and
  [Multicore by design](../../../architecture.md#multicore-by-design) for
  the per-CPU ledger and its shared lending and settlement fields.
- The security model's
  [internal choices](../../../security.md#internal-choices), for the order
  of errors, the run queues and the settlement of a loan as a whole, and
  its [permitted nondeterminism](../../../security.md#permitted-nondeterminism),
  for the time of a transition and the interleaving of CPUs.
- A. Lyons, K. McLeod, H. Almatary, G. Heiser, "Scheduling-context
  capabilities: a principled, light-weight operating-system mechanism for
  managing time", EuroSys 2018,
  <https://trustworthy.systems/publications/full_text/Lyons_MAH_18.pdf>:
  the scheduling contexts, passive servers,
  replenishment lists and timeout handlers that this model leaves out, and
  the donation of a client's budget to a server that its loans resemble.
- The rules of this page take, as clauses of their own, the rules of the
  prototype tree at `prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`:
  - `docs/features/kernel/synchronous-budgets.md`, lines 77 to 137:
    ownership and scheduling of a loan, nested loans of one context with
    at most eight edges, the effective priority clipped by the ceiling, no
    fallback to own credit, settlement before waking, the withdrawal of the
    downstream loans and the integrated profile; the time at which a loan
    is made and withdrawn belongs to the IPC component;
  - `docs/features/kernel/scheduling.md`, lines 86 to 116: admission and
    credit, the class caps with the kernel slack, the charge of every stop,
    debt, credit that never accumulates and the bounded arithmetic of long
    gaps;
  - `docs/features/kernel/scheduling.md`, lines 117 to 147: the deadline
    of a dispatch from the credit and the period boundary, waiting and
    waking without a change of credit, the CPU time of a dispatch and the
    atomicity of failures; the selection belongs to the scheduler;
  - `docs/features/kernel/quotas.md`, lines 55 to 134: of its CPU scopes,
    only the budget of a child carved from its parent's, which the holdings
    take;
  - `docs/kernel-state.md`, lines 43 to 76: the objects of the resource
    managers and the division into per-CPU, per-thread, per-process and
    shared state, with the aggregate parent budget that donated execution
    cannot multiply;
  - `docs/kernel-state.md`, lines 110 to 131: the owner of waits, IPC and
    loans, with the rule that no IRQ path borrows this state and that an
    owner cannot wake while its context is lent.
