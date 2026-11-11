---
features: none
---

# Waits requirements

The observable behaviour of the `waits` component of the
[IPC and waits](../README.md) domain: the wait record of each thread and
its completion, notifications, deadlines, timeouts and sleeps, wait sets,
the single winner of an event, the cancellation of a wait by the kill of its
thread, and the settlement of waits when a revocation becomes pending and
when their object is released. The rules that its code and tests follow are
in the [contract](contract.md). No feature document covers the component,
so the metadata lists none.

## Sources

- The word of pending bits that signals OR together and a wait consumes
  whole, a signal before and after the registration of a wait, results that
  never change once written, a deadline that wins against an event at the
  same time and keeps the bits, a wait whose deadline has passed when it is
  made, and the order of a timeout and a peer closure before a
  cancellation take the rules of the prototype's notifications and of its
  common wait owner, which the [references](contract.md#references) of the
  contract list, with their host tests and those of its object pool, its
  execution manager, its ABI of notifications and waits and its bounded
  model of waits as the frozen [vectors](contract.md#legacy-test-vectors).
- The wait record in the slot of each thread with a generation of its own,
  completion by continuation into the saved context, the deadline 0 as no
  deadline, wait sets of persistent registrations with level reports that
  consume nothing, the single winner with direct waiters first,
  cancellation by the kill of the thread, the settlement and pause of the
  waits through a revoked subtree, and the drain of the waiters of an
  object before its release are new, from the kernel's
  [IPC, notifications and waits](../../../architecture.md#ipc-notifications-and-waits)
  and its
  [execution model](../../../architecture.md#system-calls-and-the-abi); the
  [behaviour changes](contract.md#legacy-test-vectors) of the contract list
  where they differ from the prototype.
- The single winner, the order of several wake-ups, expiry first, the order
  of outcomes, the reports of wait sets and the order of errors follow the
  [security model](../../../security.md#internal-choices), the pause of
  affected execution its
  [effective revocation](../../../security.md#effective-revocation), and the
  time of a transition its entry [ND-01](../../../security.md#nd-01); the
  classes of state follow the
  [SMP design rules](../../../conventions/smp.md#s5-state-field-tables).
- The lookups, rights and revocation of capabilities are those of the
  [capabilities](../../objects-capabilities/capabilities/requirements.md)
  component; the references, write sets and errors of references are those
  of the [objects](../../objects-capabilities/objects/requirements.md)
  component; the calls, receives, replies and the receiver that an endpoint
  binds are those of the [IPC](../ipc/requirements.md) component; blocking
  and readiness are those of the
  [scheduler](../../scheduling/scheduler/requirements.md) component.

## Configurations

- **QEMU virt.** The machine `virt-8.2` without EL2 and EL3, with GICv2, one
  Cortex-A76 and 128 MiB of RAM at `0x4000_0000`: the machine of
  `cargo xtask qemu`, with the QEMU version that `toolchains.toml` pins for
  the host, with its virtual timer.
- **Raspberry Pi 5.** Only the 8 GB model is run on a board in release 0.1,
  with one of its four Cortex-A76 cores running and its physical timer.
- **Host.** The host tests of the module `waits` of the core (planned) run
  on the development host and in CI, with the frozen vectors and the tests
  that the [contract](contract.md#testing-obligations) adds, each with the
  times that it passes.
- One CPU. The wait records are per-thread, and the notifications and the
  deadline table are shared state under their tokens, also while one CPU
  runs; no requirement here covers waits across CPUs, the division of the
  deadlines of several CPUs among their timers or the locks that provide
  the tokens.

## Requirements

### WAIT-R01

**One wait and one result.** A thread has at most one pending wait, which
only its own call begins while it runs. The first completion of the wait
writes its outcome into the saved context of the thread and makes the
thread ready, or pauses it, in one transaction; every later completion of
that wait, and every completion of an earlier wait of the thread, has no
effect and no error, and the outcome never changes. A completion leaves
every other thread, process and field of the slot as it was. The
criterion: for each completion of a wait, by a signal, a timeout, a peer
closure and a kill, a second completion and a completion of the previous
generation change nothing, and the vectors of completion hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `waits::complete`, `waits::begin`, `waits::deliver`,
  `waits::wait`, `waits::sleep` and `waits::wait_set_wait` (planned).
- **Contract.** [Wait records](contract.md#wait-records) and
  [Single winner](contract.md#single-winner).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `waits-execution-1`,
  `waits-lifecycle-1`, `waits-reuse-1`, `notifications-2`,
  `objects-wait-contract-1`, `objects-wait-contract-2`,
  `execution-waits-1`, `execution-waits-7`, `verification-waits-3` and
  `verification-waits-6` as host tests, with `objects-8` and `objects-9` of
  the objects contract, and the host test of a completion whose saved
  context `validate` refuses of the
  [contract](contract.md#testing-obligations). They show the rule for the
  completions of the tests; that it holds for every order is a property that
  the property tests sample and do not prove.

### WAIT-R02

**Wait generations.** Each wait that blocks takes the next generation of
its thread, in 64 bits. A call that would block while the generation is
$2^{64} - 1$ is refused with `GenerationExhausted` and changes nothing; a
call that returns at once takes no generation. The criterion: a wait blocks
with the generation $2^{64} - 1$ and completes, and the next wait that
would block is refused, while one that a pending word satisfies at once
succeeds.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `waits::wait`, `waits::sleep`, `waits::wait_set_wait`
  and `waits::begin` (planned).
- **Contract.** [Wait records](contract.md#wait-records).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `waits-admission-5`, `notifications-12`
  and `notifications-cancellation-7` as host tests, with `objects-12` of the
  objects contract, and the host test of generations of the
  [contract](contract.md#testing-obligations).

### WAIT-R03

**Signal and consumption.** A signal of a nonzero set of bits, through a
capability with SIGNAL or by the kernel, ORs them into the word of the
notification; repeated signals coalesce. A wait through a capability with
WAIT returns the whole word at once when it is not 0 and clears it, and
otherwise blocks until a signal, which completes it with the whole word. A
completed wait keeps its result, and later bits stay for the next wait.
Any holder of WAIT may wait; the bits are the argument of the signal; a
signal allocates nothing. The criterion: the signals 1, 1, 4 and $2^{63}$
before a wait give it $2^{63} + 5$; a signal after a wait that blocked
completes it; a signal after a completed wait is taken by the next wait;
and the vectors of signals hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `waits::signal` and `waits::wait` (planned).
- **Contract.** [Notifications](contract.md#notifications).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `notifications-1`, `notifications-3`,
  `notifications-11`, `notifications-quotas-2`, `waits-lifecycle-3`,
  `abi-notification-2`, `abi-notification-4`, `abi-notification-8`,
  `abi-notification-quotas-2`, `abi-waits-5` and `abi-waits-7` as host
  tests, and the host tests of signals of the
  [contract](contract.md#testing-obligations).

### WAIT-R04

**Deadlines and timeouts.** A deadline is an absolute time in ticks of the
virtual counter, and 0 is no deadline. Every wait whose deadline is not
later than the time of a transition settles as a timeout before the
operation of that transition, the earliest deadline first and equal
deadlines in the order of registration, so an event at the same time finds
the wait settled; a wait whose deadline has passed when it is made times
out at once and consumes nothing. A timeout only means that the caller
stopped waiting: it consumes no bits and undoes nothing. The criterion: a
signal at the deadline of a wait leaves its bits for the next wait; a wait
with the deadline 6 at 6 times out with the word 1 kept; a kill at the
deadline finds the wait timed out; and three waits whose deadlines pass
together time out in the order of the rule.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `waits::first_deadline`, `waits::complete` and
  `waits::wait` (planned).
- **Contract.** [Deadlines and sleep](contract.md#deadlines-and-sleep) and
  [Determinism](contract.md#determinism).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `notifications-4`, `notifications-8`,
  `notifications-10`, `notifications-cancellation-5`,
  `waits-lifecycle-2`, `waits-budgets-6`, `abi-notification-7`,
  `abi-notification-cancellation-6`, `abi-waits-4` and
  `verification-waits-5` as host tests, and the host tests of deadlines of
  the [contract](contract.md#testing-obligations). The timer interrupt at a
  deadline is shown by the QEMU test of a wait that times out.

### WAIT-R05

**Sleep.** A sleep until a time not later than the time of its call, 0
among them, returns at once without blocking; a later one blocks its thread
until that time and then returns success. The criterion: sleeps until 0,
until the time of the call and until one tick later behave as the rule
states, and the vectors of sleeps of the scheduler hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `waits::sleep` and `waits::first_deadline` (planned).
- **Contract.** [Deadlines and sleep](contract.md#deadlines-and-sleep).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vector `waits-lifecycle-1` as a host test, with
  `scheduler-6` of the
  [scheduler contract](../../scheduling/scheduler/contract.md#legacy-test-vectors),
  and the host tests of sleeps of the
  [contract](contract.md#testing-obligations); the QEMU test of a sleep
  shows it from EL0.

### WAIT-R06

**Registrations of a wait set.** A thread registers at most
`WAIT_SET_SOURCES` = 4 sources, each at a position that it names: a
notification through a capability with WAIT, or an endpoint through a
capability with RECEIVE while it is the bound thread of that endpoint. A
position beyond the limit, a position that holds a registration, a source
that another position registers and the removal of an empty position are
refused, each with its error and without a change. A registration stays
across waits until it is removed or reported removed. The criterion: each
of these refusals, and a registration of each kind at each position, hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `waits::check_source`, `waits::wait_set_add` and
  `waits::wait_set_remove` (planned).
- **Contract.** [Wait sets](contract.md#wait-sets) and
  [Errors](contract.md#errors).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The host tests of wait sets of the
  [contract](contract.md#testing-obligations); the refusal of a thread that
  is not the bound thread is shown with the tests of the IPC component.
  No frozen vector covers wait sets, which the prototype did not have.

### WAIT-R07

**Waiting on a wait set.** A wait on a wait set returns at once, with
success, when a source is ready, a notification with pending bits or an
endpoint with a queued call, or when a source has been removed, its
capability closed or removed, its object released or its capability under
revocation; it reports the ready and the removed positions as two sets in
the order of the positions, consumes nothing and clears the removed
registrations. Otherwise it blocks until a source becomes ready or is
removed, or its deadline passes. A wait set without a registration is
refused. The criterion: the reports of the tests hold, among them a source
removed while the thread does not wait and while it waits, and a report
after which a wait takes the word.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `waits::sources`, `waits::wait_set_wait`,
  `waits::source_ready` and `waits::drain` (planned).
- **Contract.** [Wait sets](contract.md#wait-sets) and
  [Revocation and release](contract.md#revocation-and-release).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The host tests of wait sets of the
  [contract](contract.md#testing-obligations), and the QEMU test of a wait
  set over a notification and an endpoint once the operations exist. No
  frozen vector covers wait sets.

### WAIT-R08

**Single winner.** Each event completes at most one waiter: of the waiters
of a notification, the first that began to wait directly, and only when no
thread waits on it directly the first of its wait-set waiters; of a call
queued on an endpoint, its bound thread when that waits on its wait set.
The other waiters keep waiting, and a direct waiter never blocks while the
word is not 0. The criterion: the property test of the single winner holds
against an independent model, and so do the vectors of orders of events.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `waits::signal`, `waits::source_ready` and
  `waits::complete` (planned).
- **Contract.** [Single winner](contract.md#single-winner).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `notifications-7`,
  `notifications-cancellation-6`, `verification-waits-1` and
  `verification-waits-2` as host tests, with `objects-9` of the objects
  contract, and the property test of the single winner of the
  [contract](contract.md#testing-obligations). They show the rule for the
  orders that the tests generate; that it holds for every order is not
  proved here.

### WAIT-R09

**Cancellation.** The wait of a thread is cancelled only by its kill: the
kill takes the thread out of every queue of its wait, writes no result and
leaves no pending wait, and the thread never runs again. A timeout whose
deadline passes in the transition of the kill wins against the kill. No
operation cancels or interrupts the wait of another thread. The criterion:
the kill of a thread blocked in each kind of wait leaves no queue naming it,
and the vectors of kills hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `waits::cancel` (planned).
- **Contract.** [Cancellation](contract.md#cancellation).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `waits-lifecycle-4`, `notifications-9`,
  `execution-waits-4`, `execution-waits-5`, `waits-budgets-3` and
  `waits-budgets-4` as host tests; the kill itself is shown by the tests of
  the lifecycle component.

### WAIT-R10

**Revocation.** When a revocation becomes pending, every wait through a
capability of its subtree settles in that transition: a wait on a
notification as revoked, a wait set with the positions of the subtree
reported removed; its thread is paused, in no run queue, until the step of
the revocation that removes that capability, which makes it ready. No
paused thread remains once the revocation is complete. The criterion: for
each kind of wait, the settlement, the pause and its end at its step hold,
with at most four ends of pauses in one step, and the vectors of
revocation hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `waits::revoked`, `waits::complete` and
  `waits::unpause` (planned).
- **Contract.** [Revocation and release](contract.md#revocation-and-release).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `waits-transfers-3` and
  `waits-transfers-4` as host tests, and the host tests of revocation of
  the [contract](contract.md#testing-obligations). The revocation itself is
  shown by the tests of the capabilities component.

### WAIT-R11

**Release of a source.** When a notification or an endpoint is released by
the destruction of its owner, every wait on it completes first, in the
order of registration: a direct wait on a notification with peer closed,
a wait set with the position of the source reported removed. A
notification has no closed state: after its release a capability to it
fails its lookup, and its word is cleared. At the deletion of the last
capability no thread waits on the object. The criterion: the drain of a
notification with direct and wait-set waiters in mixed order completes them
in the order of registration, and the vectors of release hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `waits::drain` (planned).
- **Contract.** [Revocation and release](contract.md#revocation-and-release).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `notifications-6`,
  `notifications-quotas-6`, `execution-waits-1` and `abi-waits-7` as host
  tests, and the host tests of release of the
  [contract](contract.md#testing-obligations). The destruction of the
  owner is shown by the tests of the lifecycle component.

### WAIT-R12

**Time as an argument.** Every entry that depends on time takes the time of
its transition as an argument; no entry reads a counter or a clock. The
time is the virtual counter of the board in ticks, which does not decrease
within a boot and stays below $2^{63}$. The criterion: every host test
passes its times, the results do not depend on the speed of the host or on
a fixed instruction count, and the same calls with the same times give the
same results.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `waits::wait`, `waits::sleep`, `waits::wait_set_wait`
  and `waits::begin` (planned).
- **Contract.** [Deadlines and sleep](contract.md#deadlines-and-sleep) and
  [Determinism](contract.md#determinism).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** Every frozen vector as a host test, with the times of the
  test, and the host tests of the
  [contract](contract.md#testing-obligations), each run twice with the same
  inputs. The reading of the counter on entry is the architecture crate's
  and is shown by its QEMU tests.

### WAIT-R13

**No change on failure.** Every error of the component leaves the kernel
state as it was: a refused signal, wait, sleep or change of a wait set
writes nothing, consumes no bits and begins no wait, and no refusal is
counted. The errors follow the order of the security model. The criterion:
for each error of the contract, a call that gives it leaves every field
compared before and after unchanged, and the frozen vectors of refusals
hold.

- **Examples.** None: no feature document covers the component.
- **Entry points.** Every row of the
  [entry table](contract.md#entry-points).
- **Contract.** [Errors](contract.md#errors) and
  [Check and execute](contract.md#check-and-execute).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `waits-admission-3`, `notifications-10`,
  `objects-wait-contract-3`, `waits-transfers-5`, `abi-notification-1`,
  `abi-notification-3` and `abi-waits-3` as host tests, and the host test of
  each error of the [contract](contract.md#testing-obligations).

## Liveness, time and performance

- Every entry of the component runs to its end within the bounds of the
  [contract](contract.md#work-bounds); none waits, retries or takes a lock
  of its own, and the component has no long operation.
- The expiry of the deadlines that pass in one transition, the scan of a
  revocation that becomes pending and the drain of a released object each
  take at most as many settlements as the thread capacity, in one
  transition; a signal and the queueing of a call complete at most one wait
  in a fixed number of steps.
- A wait with a deadline ends no later than the first transition whose time
  is not earlier than its deadline; the scheduler arms the timer for the
  earliest deadline. A wait without a deadline ends only by an event, a
  kill, a revocation or a release; no requirement bounds when that happens.
- No requirement bounds the time that a step takes.

## Scope

- One CPU. Waits across CPUs, the division of the deadlines among the
  timers of several CPUs, the tokens and their locks are not covered.
- The calls, receives and replies, their queues, the binding of the receiver
  of an endpoint, the transfer of capabilities, the loans of budgets and the
  settlement of calls are not covered; they are the
  [IPC requirements](../ipc/requirements.md), whose waits this component
  holds.
- Joins and death notifications, the kill of a thread and the destruction
  of a process are not covered; the lifecycle component composes the entries
  of this component and has its own requirements. The binding and the
  acknowledgement of interrupts belong to the device-authority rules.
- Futex-style waits and futex keys as sources of a wait set, upcalls and the
  interrupt of a wait belong to later releases.
- A process has one thread; further threads of a process are not covered.
- The operation numbers, the registers of arguments and results and the
  numeric codes of errors and outcomes of the ABI inventory are not
  covered.

## Contract sections without a requirement

- [Terms](contract.md#terms): definitions only.
- [Extractability](contract.md#extractability) states the module, its layer
  and the modules that it does not refer to, which no requirement observes.
- [State fields](contract.md#state-fields) binds the code without an
  observable behaviour of its own.
- [Work bounds](contract.md#work-bounds) states the bounds that
  [Liveness, time and performance](#liveness-time-and-performance) relies
  on.
- [Open obligations](contract.md#open-obligations) has no row: the code of
  the component adds no obligation beyond its entries.
