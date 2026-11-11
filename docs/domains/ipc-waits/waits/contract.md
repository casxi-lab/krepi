# Waits contract

This page governs the code of the `waits` component of the
[IPC and waits](../README.md) domain: the wait record of each thread and
its completion; notifications, with their signal and their consumption;
deadlines, timeouts and sleeps, with the deadline table; the wait sets of
threads, with their registrations and reports; the single winner of an
event among the threads that wait for it; the part of this page in the kill
of a thread, which is the cancellation of its wait; and the settlement of
waits when a revocation becomes pending and when the object that they wait
on is released. Calls, receives and replies, the queues of endpoints, the
receiver that an endpoint binds, badges, capability transfer, budget
lending and the settlement of a call belong to the
[IPC](../ipc/contract.md) component, the module `ipc` of the core
(planned), which composes the entries of this page for the waits of calls
and receives; readiness and the run queues belong to the
[scheduler](../../scheduling/scheduler/contract.md) component; joins,
death notifications, the kill of a thread and the destruction of a process
belong to the lifecycle component (planned); the binding and the
acknowledgement of interrupts belong to the device-authority rules of the
devices and DMA domain. The observable behaviour that these rules serve,
with its evidence, is in the [requirements](requirements.md), the other
document of the component.

## Terms

- **Wait record.** The record of one thread, in its thread slot, that holds
  its wait while the thread is blocked
  ([Wait records](#wait-records)). It is a kernel record, not an object
  ([objects](../../objects-capabilities/objects/contract.md#object-kinds-and-pools)).
- **Kind.** The kind of a wait: none, notification, call, receive, wait set
  or sleep. A wait of the kind call or receive is a **wait of the IPC
  component**; the others are the waits of this page.
- **Source.** The reference of the object that a wait waits on: the
  notification of a wait of the kind notification, the endpoint of a call
  or of a receive; none for a wait set and a sleep.
- **Entries of a wait.** The entry references of the capabilities through
  which a wait goes: the capability of the notification or of the receive;
  for a call, its endpoint capability and the source of the capability that
  it transfers, if any; none for a sleep. A wait set goes through the
  entries of its registrations.
- **Generation.** The 64-bit wait generation of a thread, which every wait
  that blocks raises by one.
- **Tick.** One count of the virtual counter `CNTVCT_EL0`, which EL0 also
  reads ([EL0 controls](../../memory/address-space/contract.md#el0-controls)).
- **Time.** `now`: the value of the virtual counter that the architecture
  crate reads once on entry to a transition and passes to the entries of
  this page that need it ([ND-01](../../../security.md#nd-01)). The
  **premises of time** are that the time does not decrease within a boot
  and stays below $2^{63}$; no entry checks them.
- **Deadline.** A time in ticks after which a wait times out; 0 is no
  deadline. A deadline **has passed** at `now` when it is not 0 and not
  later than `now`.
- **Outcome.** The result state of a wait that has ended: success, with the
  results of its operation; `Timeout`; `PeerClosed`; `Revoked`; or
  `Cancelled`, the outcome of a kill, which no thread observes. An outcome
  is not an error ([Errors](#errors)).
- **Completion.** The transaction that ends a pending wait and writes its
  outcome into the saved context of its thread; its **completer** is the
  composer that makes it.
- **Pause.** The state of a thread whose wait the pending transition of a
  revocation has settled: blocked and in no run queue, until the step of the
  revocation that removes the entry recorded with the pause
  ([Revocation and release](#revocation-and-release)).
- **Notification.** An object of the notification pool, with its word and
  its two queues ([Notifications](#notifications)). Its **word** is the
  64-bit word of its pending bits.
- **Waiter queue.** The FIFO of the threads that wait on a notification, in
  the order in which their waits began: its **direct waiters**, which wait
  on it with `wait`, and its **wait-set waiters**, which wait on it through
  a registration of their wait set.
- **Direct queue.** The FIFO of the direct waiters of a notification alone,
  in the same order.
- **Registration.** The record of a source at one **position** of the wait
  set of a thread, from 0 to `WAIT_SET_SOURCES` - 1
  ([Wait sets](#wait-sets)).
- **Wait set.** The registrations of one thread. It is not an object: no
  wait set can be created, held or shared.
- **Report.** The result of a wait set: its **ready set** and its **removed
  set**, each a set of positions.
- **Deadline table.** The list of the pending waits that have a deadline,
  in the order of their deadlines and, for equal deadlines, of their
  registration ([Deadlines and sleep](#deadlines-and-sleep)).
- **Bound thread.** The receive thread that an endpoint binds at its
  creation, the only thread for which RECEIVE on it is valid, as the
  [IPC](../ipc/contract.md#bound-thread) component defines it.
- **Kill.** The forced kill of a process and its thread by the lifecycle
  component (planned), in the steps of the destruction of the process.
- **Thread capacity.** The capacity of the thread pool in the
  [capacity record](../../objects-capabilities/objects/contract.md#capacity-record)
  of the objects component.
- **Composer.** The module of the core above this one that composes an
  entry of this page into an operation: `ipc`, `lifecycle` or `dispatch`
  (planned).
- **Token.** What an access to state that is not per-CPU holds, as the
  [SMP design rules](../../../conventions/smp.md#s1-state-classes) state;
  with one CPU, the executing CPU holds every token.

## Entry points

The entries of the core are in the module `waits` of `krepi-kernel`
(planned). Six of them are operations of the ABI inventory, in its
production range: `signal`, `wait`, `sleep`, `wait_set_add`,
`wait_set_remove` and `wait_set_wait` (planned). Their operation numbers,
the registers of their arguments and results and the numeric values of
their errors and outcomes belong to the inventory; this page names the
arguments and the results. The other entries are called by the composers.

| Entry point | Kind | Called by | ABI operation | Rules |
| --- | --- | --- | --- | --- |
| `waits::signal` (planned) | Write entry on the copies of a write set, host-testable | `dispatch` (planned), for the operation `signal`, with a handle of the caller; the lifecycle component (planned), for the death notification of a process, and the composer of an interrupt that the device-authority rules bind to a notification (planned), each with the reference of the notification; each composer calls `scheduler::enqueue` for the thread that it gives | `signal` | [Notifications](#notifications), [Single winner](#single-winner) |
| `waits::wait` (planned) | Write entry on the copies of a write set, host-testable | `dispatch`, for the operation `wait`, which composes `scheduler::block` when the wait blocks | `wait` | [Notifications](#notifications), [Deadlines and sleep](#deadlines-and-sleep), [Wait records](#wait-records) |
| `waits::sleep` (planned) | Write entry on the copies of a write set, host-testable | `dispatch`, for the operation `sleep`, which composes `scheduler::block` when the sleep blocks | `sleep` | [Deadlines and sleep](#deadlines-and-sleep) |
| `waits::check_source` and `waits::wait_set_add` (planned) | A read entry and a write entry on the copies of a write set, host-testable | `dispatch`, for the operation `wait_set_add`: `check_source`; for an endpoint, `ipc::check_receiver` of the IPC component, whether the caller is its bound thread; then `wait_set_add` | `wait_set_add` | [Wait sets](#wait-sets) |
| `waits::wait_set_remove` (planned) | Write entry on the copies of a write set, host-testable | `dispatch`, for the operation `wait_set_remove` | `wait_set_remove` | [Wait sets](#wait-sets) |
| `waits::sources` and `waits::wait_set_wait` (planned) | A read entry and a write entry on the copies of a write set, host-testable | `dispatch`, for the operation `wait_set_wait`: `sources`; for each endpoint that it gives, `ipc::has_call` of the IPC component, whether a call is queued on it; then `wait_set_wait` with the answers, and `scheduler::block` when the wait blocks | `wait_set_wait` | [Wait sets](#wait-sets), [Single winner](#single-winner) |
| `waits::begin` and `waits::deliver` (planned) | Write entries on the copies of a write set, host-testable | `ipc` (planned): `begin` for a `call` or a `receive` that blocks its caller; `deliver` for the delivery of a queued call, after which its wait no longer goes through the source of its transfer | None | [Wait records](#wait-records), [Deadlines and sleep](#deadlines-and-sleep) |
| `waits::complete` (planned) | Write entry on the copies of a write set, host-testable | `ipc`, for the delivery of a call to a receiver that waits, for a reply, and in `ipc::settle`, `ipc::reply_deleted` and `ipc::drain_step` for the other ends of a call or a receive; `dispatch`, for the expiry of the waits of this page and for their settlement when a revocation becomes pending; each composer calls `scheduler::enqueue` for the thread that it gives | None | [Wait records](#wait-records), [Deadlines and sleep](#deadlines-and-sleep), [Revocation and release](#revocation-and-release) |
| `waits::first_deadline` (planned) | Read entry, host-testable | `dispatch`, at the entry of every transition for the expiry of waits, and for the external deadline that it passes to `scheduler::choose` | None | [Deadlines and sleep](#deadlines-and-sleep) |
| `waits::source_ready` and `waits::drain` (planned) | Write entries on the copies of a write set, host-testable | `source_ready`: `ipc`, when a call joins the call queue of an endpoint, with the bound thread of the endpoint; `drain`: the lifecycle component, in the destruction of the owner of a notification or an endpoint, in the transition of its release and before it, for an endpoint after `ipc::drain_step` has given `drained` with its bound thread; each composer calls `scheduler::enqueue` for the thread that it gives | None | [Single winner](#single-winner), [Revocation and release](#revocation-and-release) |
| `waits::revoked` and `waits::unpause` (planned) | A read entry and a write entry on the copies of a write set, host-testable | `revoked`: `dispatch`, in the transition that makes a revocation pending; `unpause`: `dispatch`, in each step of a revocation, and the lifecycle component, in each step of a teardown that makes a step of a revocation, for each capability that the step removes, with `scheduler::enqueue` for the thread that it gives | None | [Revocation and release](#revocation-and-release) |
| `waits::cancel` (planned) | Write entry on the copies of a write set, host-testable | The lifecycle component, in the destruction of a process, for its thread, in the transaction of `scheduler::remove`; for a wait of the IPC component it composes `ipc::settle` with `Cancelled` instead | None | [Cancellation](#cancellation) |

## Extractability

The module `waits` of the core (planned), below `kernel/src/` (planned),
follows the [provable Rust subset](../../../conventions/provable-subset.md):
the wait records and their completion, the notifications with their
queues, the deadline table, the registrations and reports of wait sets,
the settlements of revocation and release, and the part of a kill. Its
items are `pub(crate)`: no entry of this page is called by the architecture
crate or a board crate
([provable core](../../../architecture.md#the-provable-core)).

The module is in layer 5 of the
[module order](../../../architecture.md#module-order-in-the-core). It
refers to the modules `objects`, for references, resolution and write
sets, `context`, for the result registers, and `address_space`, for the
bounds of the EL0 window, all of layer 1; to `capabilities` of layer 4, for
lookups and the entries of tables; and to the kernel root, which holds the
deadline table and the slots. It refers to no module of its own layer,
`vm` and `scheduler`, or above it: `ipc`, `lifecycle`, `creation` and
`dispatch`. So the operations that make a thread blocked or ready are
composed above both this module and the scheduler: an entry of this page
gives the thread that a completion makes ready, in the order of
[Determinism](#determinism), or the thread that blocks, and the composer
calls `scheduler::enqueue` or `scheduler::block` for it in the same
transaction. The state of the module `ipc` comes in as values: whether a
call is queued on an endpoint source, which `dispatch` reads with
`ipc::has_call` and passes to `wait_set_wait`; the bound thread of an
endpoint, which `ipc` passes to `source_ready` and `ipc::drain_step` gives
the lifecycle component for `drain`; and the binding check of an endpoint
source,
`ipc::check_receiver`, which `dispatch` composes between `check_source`
and `wait_set_add`. The IPC component, above this module, uses the wait
records of its calls and receives through `begin`, `deliver` and
`complete`, and links its call queues through their `queue` fields.

The write entries receive the one kernel root by `&mut`
([rule 3](../../../conventions/provable-subset.md#3-flat-relations-and-one-kernel-root))
and the write-set buffer of the executing CPU by an explicit `&mut`
argument
([rule 8](../../../conventions/provable-subset.md#8-no-interior-mutability)).
The deadline table is shared state in the kernel root
([State fields](#state-fields)), so the module has no per-CPU state of its
own and no adapter; the write-set buffer is lent by the adapter that the
objects contract lists among its
[open obligations](../../objects-capabilities/objects/contract.md#open-obligations).
The module touches no register and defines no callback, and it takes the
time as an argument. The contract is written before its code, so this
section lists no source paths; the change that adds the module writes its
`paths` block here.

## Wait records

- **One record.** Each thread has one wait record, in its thread slot,
  with these fields:

  | Field | Content |
  | --- | --- |
  | `kind` | None, notification, call, receive, wait set or sleep |
  | `source` | The reference of the notification or the endpoint, or none |
  | `entries` | At most two entry references, the entries of the wait |
  | `generation` | The 64-bit generation of the last wait of the thread that blocked |
  | `deadline` | The deadline of the wait, or 0 |
  | `form` | The form of the result registers that the completion writes: two, `x0` and `x1`, or six, `x0` to `x5`, as the ABI inventory gives the operation |
  | `pause` | None, or the entry reference whose removal ends the pause of the thread |
  | `queue` | The links of the thread in the queue of its source: the waiter queue of its notification, or, for a queued call, the call queue of its endpoint, which the IPC component links |
  | `direct` | The links of the thread in the direct queue of its notification, for a wait of the kind notification |
  | `deadlines` | The links of the thread in the deadline table, for a wait with a deadline |

  The registrations of the wait set of the thread are in the same slot
  ([Wait sets](#wait-sets)). A call waits in two states, queued and then
  delivered and waiting for its reply, which the reply record of the IPC
  component tells apart, with the receiver that serves it
  ([replies](../ipc/contract.md#replies)). `begin` writes the record of a
  call or a receive: its endpoint, its entries, which for a queued call
  with a transfer include the source, its deadline and the six-register
  form of the results of the IPC component; and `deliver` removes the
  source of the transfer from the entries of a queued call when its
  delivery commits the transfer
  ([delivery](../ipc/contract.md#delivery)).
- **A new thread.** The record of a new thread has the kind none, the
  generation 0, the deadline 0 and no pause, and the thread has no
  registration; the release of its slot clears them with the other fields
  of the slot
  ([release](../../objects-capabilities/objects/contract.md#identities-and-generations)).
- **Beginning.** A wait begins only by a call of the thread itself, while
  it runs: `wait`, `sleep` and `wait_set_wait` of this page, and the `call`
  and the `receive` of the IPC component through `begin`. So a thread with a
  pending wait never begins another. A wait that blocks takes the
  generation $g + 1$, where $g$ is the generation of the record; a call that
  would block while $g = 2^{64} - 1$ is refused with `GenerationExhausted`
  before its first write, and the thread stays as it was. A call that its
  object satisfies at once, or whose deadline has passed, returns its result
  without blocking: it begins no wait and takes no generation.
- **Blocking.** The composer of a call that blocks calls `scheduler::block`
  in the same transaction, after the checks of both; the thread stays
  blocked until the completion of its wait. Every blocking call of this page
  completes by continuation: its completer writes the result into the saved
  context, and no call of this page is executed again from the saved user
  registers ([execution model](../../../architecture.md#system-calls-and-the-abi)).
- **Completion.** `complete(thread, generation, outcome)` resolves the
  thread and finds its wait pending with that generation. In one
  transaction it takes the thread out of the queues of this page and out of
  the deadline table, writes the outcome into the saved context, sets the
  kind to none and gives the thread to the composer to make ready. For
  `Revoked`, with the entry that `revoked` gives, it records that entry as
  the pause instead and gives no thread; for
  `Cancelled`, which `ipc::settle` gives for the kill of a thread that waits
  in a call or a receive, it writes no result and gives no thread, since
  the thread never runs again. The IPC component, for a wait of the IPC
  component, takes the thread out of its own queues in the same
  transaction.
- **The first only.** Only the first completion of a wait takes effect. A
  completion of a thread whose wait has ended, or whose pending wait has
  another generation, has no effect and no error: `complete` gives none. The
  outcome of a wait never changes once it is written, and the woken thread
  only collects it by its return.
- **The result registers.** The completer writes the results with
  `set_return_values` or `set_return_registers`, as the `form` gives, with
  the bounds of the EL0 window
  ([the bounds of a thread](../../memory/address-space/contract.md#el0-address-layout),
  [results of a call](../../boot-platform/context/contract.md#results-of-a-call));
  the result registers that the outcome does not use are 0. While the thread
  is blocked, only its completer writes its saved context. Its `validate`
  refuses only a context that was refused already when the thread entered
  the kernel, such as one whose `PSTATE.SSBS` EL0 left set
  ([validation](../../boot-platform/context/contract.md#validation)): then
  the completer writes no register, and the completion still takes effect
  and makes the thread ready; the composer of its return refuses the
  context, and its process ends by a user fault of the cause `Other`
  ([user faults](../../memory/address-space/contract.md#user-faults)).
- **No registry.** No pool of records, no ceiling of waits for a process and
  no reserve for a class of processes exists: every thread has its record,
  so a wait never fails for want of one. The generation of a wait is an
  internal identifier; no operation returns it, and no identity of a wait
  is an observable output.

## Notifications

- **The object.** A notification slot holds the word, initially 0, and the
  first and last threads of the waiter queue and of the direct queue,
  initially empty. The creation component creates notifications (planned);
  their release is in [Revocation and release](#revocation-and-release). A
  notification has no recipient and no closure: any thread that holds WAIT
  on it may wait on it, and any holder of SIGNAL may signal it. A
  notification capability carries no badge
  ([rights](../../objects-capabilities/capabilities/contract.md#rights)).
- **Signal.** `signal(target, bits)` takes a handle of the caller, which it
  looks up for a notification with SIGNAL, or, for the signals of the
  kernel, the reference of a notification, which it resolves. The bits
  must not be 0 (`InvalidBits`). It ORs the bits into the word and then:
  1. when the direct queue holds a thread, it completes the first, with
     success and the whole word as its bits, and sets the word to 0;
  2. otherwise, when the waiter queue holds a thread, which is then a
     wait-set waiter, it completes the first with its report
     ([Wait sets](#wait-sets)) and leaves the word as it is;
  3. otherwise it changes nothing else.

  Its result is `ok`. A signal allocates nothing and never waits, so the
  composer of an interrupt and the lifecycle component use it as it is.
- **Wait.** `wait(handle, deadline, now)` looks up the handle for a
  notification with WAIT, and then:
  1. when the deadline has passed, the result is `Timeout`, at once: the
     wait consumes nothing, leaves the word and begins no wait;
  2. otherwise, when the word is not 0, the result is success with the whole
     word as its bits, at once, and the word becomes 0;
  3. otherwise the wait blocks, unless the generation of the thread is
     exhausted (`GenerationExhausted`, [Wait records](#wait-records)): the
     record takes the kind notification, the source, the entry of the
     capability, the deadline and the next generation; the thread joins the
     tails of the waiter queue and of the direct queue, and, with a
     deadline, the deadline table.

  Its results are its outcome and its bits, 0 for every outcome but
  success.
- **Coalescing and consumption.** Signals coalesce: the word is the OR of
  the bits of every signal since the last consumption, and a wait consumes
  the whole word at once. The word is a reason to look at a queue, not a
  count of messages; the state of the queue counts them
  ([IPC, notifications and waits](../../../architecture.md#ipc-notifications-and-waits)).
- **Orders.** For a notification and one thread T that waits on it:

  | Order of the events | Result |
  | --- | --- |
  | A signal of $b$, then T's wait | The wait returns at once with success and the bits $b$, OR the bits of other signals before it; the word is 0 |
  | T's wait, which blocks, then a signal of $b$ | The signal completes the wait with success and the bits $b$; the word is 0 |
  | T's wait completed, then a signal of $c$ | The result of the wait stays; the word is $c$, which T's next wait takes at once |
  | T's wait with the deadline $d$, then a signal of $b$ at $d$ | The expiry at $d$ settles the wait as `Timeout` first; the signal finds no waiter and leaves the word $b$ for the next wait |

- **Signals of the kernel.** The interrupt paths that the device-authority
  rules bind to a notification ([ND-02](../../../security.md#nd-02)) and
  the death notification of a process, which the lifecycle component
  delivers, call `signal` with the reference of the notification, under
  the same rules; which notification and which bits they use belongs to
  those rules and to that component.

## Deadlines and sleep

- **Deadlines.** A deadline is an absolute time in ticks of the virtual
  counter, in the count of `now`, which EL0 also reads. Every 64-bit value
  is a valid deadline, and 0 is no deadline. A deadline is only compared
  with times, never added to, so no value of it overflows.
- **Expiry first.** At the entry of every transition, before its operation
  runs, the composer `dispatch` settles every wait whose deadline has passed
  at `now`: it takes the first wait of the deadline table with
  `first_deadline` and, while its deadline has passed, settles it as
  `Timeout` in a transaction of its own: a wait of this page with
  `complete`, followed by `scheduler::enqueue` for the thread that it
  gives, and a wait of the IPC component with `ipc::settle`, which makes
  its thread ready itself
  ([settlement of a call](../ipc/contract.md#settlement-of-a-call)). So the
  event of the operation finds no
  such wait: a signal leaves its bits for the next wait, and a reply to a
  call that timed out fails with `ReplyGone` of the IPC component.
- **Several deadlines.** All the waits whose deadlines have passed settle
  in that transition, the earliest deadline first and, for equal deadlines,
  in the order in which the waits joined the deadline table, which is the
  order of their registration. The loop takes at most one settlement for
  each wait of the table, so at most the thread capacity.
- **At admission.** A call that would begin a wait whose deadline has
  passed returns `Timeout` at once: it consumes no pending state, reserves
  nothing and begins no wait. For a call and a receive the IPC component
  states the same ([calls and receives](../ipc/contract.md#calls-and-receives)).
- **The deadline table.** The deadline table holds every pending wait with
  a deadline, linked through the `deadlines` field of the records, in the
  order of the deadline and then of the joining. A wait that blocks with a
  deadline joins it after every wait whose deadline is not later, by a walk
  from its first wait of at most its length; a completion or a kill takes
  the wait out of it. `first_deadline` gives the first wait of the table,
  with its thread, its deadline and its kind, or none. After the expiry,
  its deadline is the external deadline that `dispatch` passes to
  `scheduler::choose`
  ([selection](../../scheduling/scheduler/contract.md#selection-and-time-slices)).
- **Sleep.** `sleep(deadline, now)` is a wait on no object, and its
  deadline is the time to wake. When that time is not later than `now`, 0
  among them, the sleep returns `ok` at once and does not block: for a
  sleep, 0 does not mean no deadline. Otherwise it blocks with the kind
  sleep, unless the generation of the thread is exhausted
  (`GenerationExhausted`), and joins the deadline table, and the expiry of
  its deadline completes it with `ok`: the end of a sleep is its success,
  not a timeout. A sleep goes through no capability, so no revocation
  settles it.
- **A timeout.** A timeout means that the caller stopped waiting, and only
  that: it does not undo what has happened, such as a delivered message, a
  committed transfer of a capability or the work that a server has done for
  a call, and it consumes no state of the object.

## Wait sets

- **Registrations.** Each thread has `WAIT_SET_SOURCES` = 4 positions,
  `waits::WAIT_SET_SOURCES` (planned), from 0 to 3, in its thread slot;
  this is the number of sources that a wait set holds at most. A
  registration records the kind of its source, notification or endpoint,
  the reference of the object, the entry reference of the capability
  through which it was made, and the links of the thread in the waiter queue
  of a notification source while the thread waits on its wait set.
- **Add.** The operation `wait_set_add(position, handle)` checks, in this
  order: the position is below `WAIT_SET_SOURCES` (`InvalidPosition`);
  the handle names a notification with WAIT or an endpoint with RECEIVE,
  with `check_source`, whose lookup refuses a capability of another kind
  (`WrongType`); for an endpoint, the caller is its bound thread, which
  `ipc::check_receiver` of the IPC component checks, with its error
  `NotReceiver` ([bound thread](../ipc/contract.md#bound-thread)); no other
  position registers the same object (`DuplicateSource`); and the position
  holds no registration (`PositionOccupied`). `wait_set_add` then writes the
  registration. A registration is kept in the thread alone: it is not
  linked to its source while the thread does not wait on its wait set, and
  it stays across waits until it is removed or reported removed.
- **Remove.** The operation `wait_set_remove(position)` checks the position
  (`InvalidPosition`) and that it holds a registration (`PositionEmpty`),
  and clears it.
- **Wait.** The operation `wait_set_wait(deadline)` takes, from `dispatch`,
  for each endpoint that `sources` gives, whether a call is queued on it,
  which `ipc::has_call` gives, and checks that the wait set holds a
  registration (`EmptyWaitSet`). Then:
  1. when the deadline has passed, the result is `Timeout` at once, and the
     registrations stay as they are;
  2. otherwise, for each position that holds a registration, in the order
     of the positions, it looks up the capability of the registration again,
     with its kind and right. When the lookup fails, because the capability
     has been closed or removed, its object has been released or the entry
     or an ancestor is marked for revocation, the position is **removed**:
     it joins the removed set and its registration is cleared. Otherwise the
     position is **ready** when its source is: a notification whose word
     is not 0, or an endpoint on which a call is queued;
  3. when the ready set or the removed set is not empty, the result is
     success with both, at once;
  4. otherwise the wait blocks, unless the generation of the thread is
     exhausted (`GenerationExhausted`): the record takes the kind wait set,
     the deadline and the next generation; the thread joins the tail of the
     waiter queue of each notification source and, with a deadline, the
     deadline table.
- **Readiness.** Readiness is a level, not an edge: a source is ready while
  its notification has pending bits or its endpoint has a queued call,
  however often it has been reported.
- **Endpoint sources.** Only the bound thread of an endpoint may register
  it, so the bound thread is the only wait-set waiter that an endpoint can
  have, and an endpoint keeps no queue of wait-set waiters: when a call
  joins the call queue of an endpoint, the IPC component calls
  `source_ready` with the endpoint and its bound thread, which completes
  the receiver when it waits on its wait set with that endpoint registered,
  and does nothing otherwise. A call that finds the bound thread waiting
  in a `receive` is delivered to it and joins no queue
  ([endpoint queues](../ipc/contract.md#endpoint-queues)).
- **The report of a completion.** A completion of a wait-set waiter by an
  event of one of its sources reports that position as ready or, for a
  removal, as removed, with every other notification source whose word is
  not 0 as ready. An endpoint source that did not cause the completion has
  no queued call then: a call queued on it after the start of the wait would
  have completed the wait. The expiry completes a wait set with `Timeout`
  and no report.
- **No consumption.** A report consumes nothing: the bits of a notification
  stay in its word and the calls of an endpoint in its queue. The thread
  takes them with `wait` or `receive`, which may find them taken by another
  thread in the meantime and then give their usual result.
- **The fixed reason.** A source that is removed is reported in the removed
  set, with success: it is a fixed reason of the report, not an error. The
  source of a blocked wait-set waiter is removed by the release of its
  object, through `drain`, and by a pending revocation of its entry, through
  the scan of [Revocation and release](#revocation-and-release); the
  registration of a thread that does not wait is not on its source, and its
  next `wait_set_wait` finds the source removed. A futex key is no source of
  a wait set in release 0.1.
- **Results.** The results of `wait_set_wait` are its outcome, its ready set
  and its removed set, each a set of positions given in the ascending order
  of the positions, both empty for every outcome but success.

## Single winner

- **One waiter for each event.** Each event completes at most one wait:
  a signal completes at most one waiter of its notification, and a call that
  joins a call queue at most the bound thread of its endpoint. The other
  waiters keep waiting, and their waits stay as they were.
- **The first registered wins.** Of the waiters of one event, the one that
  began its wait first wins: the waiter queue and the direct queue hold
  their threads in the order in which their waits began. For a wait-set
  waiter that order is the start of the `wait_set_wait` that blocked, when
  it joined the queues of its sources, not the time of its registrations.
  The receivers of an endpoint do not compete: the bound thread is its
  only receiver.
- **Consumers first.** A direct waiter of a notification wins against its
  wait-set waiters, and a receiver in `receive` against a wait set of the
  same endpoint. The reason is that a report consumes nothing: if a signal
  completed a wait-set waiter while a direct waiter waited, the word would
  stay set while a thread blocked in `wait` for it, and a call reported to
  a wait set while the receiver blocked in `receive` would stay queued
  beside a waiting receiver. So a direct waiter never blocks while the word
  is not 0, and a receiver never blocks beside a queued call.
- **Leaving the queues.** The completed waiter leaves every queue of this
  page that it is in: both queues of its notification, or the waiter queue
  of each notification source of its wait set, and the deadline table.
- **Bounds of the scan.** A signal and `source_ready` take only the first
  thread of a queue, or the bound thread, in a fixed number of steps;
  taking a completed wait-set waiter out of its queues touches at most
  `WAIT_SET_SOURCES` queues; and the checks of `wait_set_wait` make at most
  `WAIT_SET_SOURCES` lookups.
- **One result.** The first completion of a wait decides its outcome,
  whatever comes later in the same transition or after it
  ([Wait records](#wait-records)).

## Cancellation

- **The kill.** In release 0.1 a wait is cancelled only by the kill of its
  thread, which completes its wait record: there is no operation that
  cancels the wait of another thread or interrupts it, and a blocked thread
  cannot cancel its own wait, since a process has one thread.
- **The part of this page.** `cancel(thread)`: for a wait of this page, it
  takes the thread out of the queues of this page and out of the deadline
  table and sets the kind to none; for a paused thread, it clears the pause.
  It writes no result and gives no thread to make ready: the lifecycle
  component calls `scheduler::remove` in the same transaction, and the
  thread never runs again. For a wait of the IPC component it does nothing:
  the lifecycle component ends that wait with `ipc::settle` and the outcome
  `Cancelled`, which composes `complete`
  ([settlement of a call](../ipc/contract.md#settlement-of-a-call)). For a
  thread without a pending wait or a pause, it changes nothing.
- **No interrupt.** The interrupt of the wait of a thread, and the upcalls
  that complete a wait, are not part of release 0.1, so no wait has an
  interrupted outcome.
- **Its place among the outcomes.** The outcome of a kill is `Cancelled`.
  In the order of the outcomes of one wait, timeout, cancellation,
  revocation, peer closure and then the event of the wait, a signal, a
  delivery or a reply: the expiry settles every passed deadline before the
  kill, so a wait whose deadline passes in the transition of the kill reports
  `Timeout`; a composed operation that brings a kill and another of these to
  one wait applies the kill first.
- **What it decides.** The killed thread does not observe its outcome. The
  outcome decides only the order above and, for a call, that the server's
  later reply fails with `ReplyGone` of the IPC component.

## Revocation and release

- **The scan.** When a revocation becomes pending, the composer `dispatch`,
  after the write-back of the revocation mark and without a preemption
  point, walks the slots of the thread pool in their order and, for each
  thread with a pending wait, calls `revoked(thread, target)`, which gives
  the first entry of the wait, in the order of its entries and then of the
  positions of its registrations, that lies in the subtree of the
  revocation, or none. An entry lies in the subtree when the entry reference
  of the target is among the references of its path
  ([derivation links](../../objects-capabilities/capabilities/contract.md#derivation-links)).
  For each thread that `revoked` names, `dispatch` settles its wait in a
  transaction of its own, with the outcome `Revoked` and the entry that
  `revoked` gives: a wait of this page with `complete`, and a wait of the
  IPC component with `ipc::settle`, which composes `complete` and returns
  the loans of the call
  ([settlement of a call](../ipc/contract.md#settlement-of-a-call)).
- **The settlement.** The outcome of a wait on a notification is `Revoked`.
  A wait set reports, with success, every position whose entry lies in the
  subtree as removed, and clears those registrations, with the ready
  positions of its report. The thread leaves the queues and the deadline
  table, as for every completion, and its result is written into its saved
  context.
- **The pause.** The settled thread is not made ready: its record keeps the
  entry that `revoked` named as its `pause`, and the thread stays blocked
  in no run queue. In each step of the revocation, for each capability that
  the step removes, the composer of the step calls `unpause` for the thread
  of the process whose table held it; when that thread's pause names the
  capability, `unpause` clears it and gives the thread, and the composer
  makes it ready with `scheduler::enqueue` in the write set of the step, in
  the order in which the step removes the capabilities
  ([pause by revocation](../../scheduling/scheduler/contract.md#blocking-and-readiness)).
  A process has one thread, so at most one thread waits through one entry,
  and a step that removes at most `REVOKE_BATCH` = 4 capabilities ends at
  most 4 pauses. Every entry of the subtree is removed by a step before the
  revocation is complete, so no thread is paused when it is complete, and
  no pause outlasts its revocation. The kill of a paused thread proceeds as
  for every thread, and `cancel` clears its pause; its written outcome
  stays.
- **Write sets.** Each settlement is one transaction of at most $k$ = 15
  items, within the 27 items that $W$ = 64 leaves beside the largest write
  set of the capabilities component
  ([check and execute](../../objects-capabilities/capabilities/contract.md#check-and-execute)):
  at most 11 of this page for a wait set and 7 for a wait on a
  notification ([Check and execute](#check-and-execute)); for a call or a
  receive, the write set of `ipc::settle` without `scheduler::enqueue`,
  which a paused thread does not take, at most 15 for a delivered call with
  the withdrawal of its chain of loans
  ([lending](../../scheduling/budget-ledger/contract.md#check-and-execute)),
  as the [IPC contract](../ipc/contract.md#check-and-execute) counts it,
  with the items of this page among them. The end of the pauses
  adds at most 9 items to a step of the revocation: the slots of at most 4
  threads, the last threads of their run queues and the scheduler record of
  the CPU, so the largest step writes at most 41 items.
- **Work.** The scan reads, for each thread with a pending wait, at most
  2 + `WAIT_SET_SOURCES` entries and compares each with the
  target in at most 16 references of its path; the number of threads and
  of settlements is at most the thread capacity, in one transition without
  a preemption point, like the expiry of deadlines that pass together
  ([Work bounds](#work-bounds)).
- **What is not scanned.** The registrations of a thread that does not wait
  are not on their sources: its next `wait_set_wait` reports them removed,
  since their lookups then fail (`RevocationPending`, or the removal of the
  capability). A new wait through a capability of the subtree fails at its
  lookup (`RevocationPending`).
- **Transactions in one transition.** The pending transition writes the
  mark, each settlement and each expiry before it as separate transactions,
  and the operation itself in another. The write phase of a settlement has
  no failure that this contract allows: it allocates nothing, its write set
  stays below $W$ and it has no fault-injection point, so no settlement ends
  half done. Each transaction rolls back to the state before itself when it
  fails, and an operation that fails keeps the settlements that preceded it
  in its transition, which are results of time and of revocation, not of
  the operation.
- **Several CPUs.** With more than one CPU, the transactions of one
  transition may interleave with those of other CPUs: a completer then checks
  the revocation marks of the entries of a wait before it writes its result.
  With one CPU the check always passes, since the pending transition settles
  those waits.
- **Release at the last capability.** An endpoint or a notification is
  released when its last capability of the current generation is deleted
  ([capability counts](../../objects-capabilities/capabilities/contract.md#capability-counts)),
  or by the destruction of its owner. At the last capability no thread
  waits on it: a blocked thread waits through a capability of its own
  table that the object counts; it cannot close that capability itself,
  since a process has one thread; a pending revocation settles its wait
  before a step removes the capability; and the lifecycle component kills
  a thread before it tears down its table, which is a premise of the
  composition. So the part of this page in that write set is empty. A
  registration that names the object in a thread that does not wait is
  reported removed by its next `wait_set_wait`.
- **Release by the destruction of the owner.** In the destruction of the
  owner of a notification or an endpoint, before the transaction that
  releases it, the lifecycle component calls `drain` until it gives none,
  each call a transaction of its own, in the transition of that release and
  without a preemption point between them, so no wait joins the queues of the
  object in between and the release finds them empty. For a notification,
  `drain` completes the first thread of its waiter queue: a direct waiter
  with `PeerClosed`, and a wait-set waiter with success and the report of
  that position as removed, whose registration it clears. For an endpoint,
  the calls and the receiver are ended first by the drain steps of the IPC
  component, `ipc::drain_step`, which the endpoint, no longer served, keeps
  from new calls
  ([release and peer closure](../ipc/contract.md#release-and-peer-closure));
  `drain` then completes the bound thread that `ipc::drain_step` gives
  with `drained` when it waits on its wait set with that endpoint
  registered, in the same way. Every call
  on the endpoint began before that wait, since a call queued during it
  would have completed it and one queued before it would have made it
  return at once, so this is the order of registration. The calls of
  `drain` for one object are at most the thread capacity; how many objects
  one step of the destruction releases is the lifecycle contract's
  (planned).
- **The word.** The release clears the word of a notification with its
  slot; a later lookup of a capability to it fails (`StaleReference`), so a
  released notification has no closed state.
- **The destruction of a process.** The part of this page in the
  destruction of a process is the kill of its thread, with `cancel`, and
  the drains of the notifications and endpoints that it owns; the death
  notification of the process is a signal of the lifecycle component.

## Errors

| Error | Rule broken | Entries | Place in the order of errors |
| --- | --- | --- | --- |
| `InvalidBits` | Bits of 0 | `signal` | The form of the register arguments |
| `InvalidPosition` | A position not below `WAIT_SET_SOURCES` | `check_source`, `wait_set_remove` | The form of the register arguments |
| The errors of `lookup` of the capabilities component, from `InvalidHandle` to `TransferPending` | The checks of a [lookup](../../objects-capabilities/capabilities/contract.md#lookup) of a notification with SIGNAL or WAIT, or of an endpoint with RECEIVE | `signal` with a handle, `wait`, `check_source` | The places that that contract gives: handle resolution, rights and the state of the entry |
| `WrongPool` of the objects component | A reference of another pool than its kind's | Every entry that takes a reference | Handle resolution: the type |
| `StaleReference` of the objects component | A reference that is not live | Every entry that takes a reference | Handle resolution: the liveness of the object |
| `NotReceiver` of the IPC component | A registration of an endpoint by a thread other than its bound thread, which `ipc::check_receiver` refuses | The operation `wait_set_add`, which `dispatch` composes | Object state, before `DuplicateSource` |
| `DuplicateSource` | Another position registers the same object | `wait_set_add` | Object state |
| `PositionOccupied` | The position holds a registration | `wait_set_add` | Object state |
| `PositionEmpty` | The position holds no registration | `wait_set_remove` | Object state |
| `EmptyWaitSet` | The wait set holds no registration | `wait_set_wait` | Object state |
| `GenerationExhausted` | A wait that would block while the generation of the thread is $2^{64} - 1$ | `wait`, `sleep`, `wait_set_wait`, `begin` | Object state, after the other errors of the operation |
| `InvalidState` | A call that no composer makes: `begin` of a thread with a pending wait or a pause, or with a deadline that has passed; `deliver` of a thread without a pending call | `begin`, `deliver` | Object state |

- **Order.** Each entry checks in the order that its rule section states
  and returns the first error. The places of the last column are those of
  the order of errors of the
  [security model](../../../security.md#internal-choices): the operation
  number and version, which the dispatch of the ABI checks; the form of the
  register arguments; handle resolution; rights; object state; the caller's
  quota; shared capacity. For `wait_set_add` the order is the position, the
  lookup with its rights and the state of the entry, `NotReceiver` for an
  endpoint, `DuplicateSource` and `PositionOccupied`. No error of this
  page is one of the caller's quota or of shared capacity.
- **No change on failure.** No error changes state: an entry of this page
  that returns an error leaves every field of the kernel state as it was,
  the copies in the write set included, and writes no counter; a composing
  operation that meets an error discards its buffer, so the kernel state
  after any failed operation equals the state before it. There is no
  exception. The settlements before the operation in its transition are
  transactions of their own and stay
  ([Revocation and release](#revocation-and-release)). The result registers
  of a failed system call follow the
  [observable outputs](../../../security.md#observable-outputs) of the
  security model.
- **Outcomes are not errors.** `Timeout`, `PeerClosed`, `Revoked` and
  `Cancelled` are outcomes of a wait, and a removed source is a fixed
  reason of a report: an operation that gives one has succeeded in the sense
  of this rule and writes its outcome into the result registers, also when
  it returns at once ([shared conventions](../../README.md#shared-conventions)).
- **Totality.** `InvalidState` and the errors of references answer calls
  that no composer makes: the composers pass live references and call
  `begin` and `deliver` only after their own checks. `complete`,
  `source_ready`, `drain`, `unpause` and `cancel` have no error beyond the
  resolution of their references: a wait that is not pending, a receiver
  that does not wait on its wait set, a queue that is empty and a pause that
  names another entry are their result none.
- **Names.** The names are those of this contract; the numeric values of
  the errors and outcomes that reach EL0 belong to the ABI inventory.

The prototype's notifications had 13 errors and its common wait owner 16,
and the objects contract moved three errors of the prototype's object pool
to this page. Here:

| Prototype error | Here |
| --- | --- |
| `notifications::InvalidConfiguration` | Not applicable: there is no registry of waits and no control reserve to configure; the thread pool, which the capacity record of the objects component sizes, holds the records |
| `notifications::Object(_)` | Not kept as a wrapper: the errors of the objects and capabilities components that this page meets are returned as they are |
| `notifications::InvalidState` | Rewritten: a released notification fails the lookup of a capability to it (`StaleReference`), since there is no closed state; a second wait of a thread whose wait is pending, or whose result has not been taken, does not exist, since a thread waits only by its own call while it runs and its result is written at the completion; `InvalidState` answers only the calls of `begin` and `deliver` that no composer makes |
| `notifications::InvalidDeadline` | Not applicable: every 64-bit deadline is valid, and 0 is no deadline |
| `notifications::InvalidBadge` | Renamed `InvalidBits`: a signal with the bits 0; a notification capability carries no badge, and the bits are the argument of `signal` |
| `notifications::ClockReversed` | Not applicable: the time is an argument that does not decrease within a boot, a premise of time that no entry checks |
| `notifications::Capacity` | Not applicable: every thread has its wait record, so no wait waits for a record |
| `notifications::QuotaExceeded` | Not applicable: no process has a ceiling of waits, and a process has one thread |
| `notifications::TokenExhausted` | Renamed `GenerationExhausted`: a wait that would block while the generation of the thread is $2^{64} - 1$ |
| `notifications::PermissionDenied` | Moved to the capabilities component: SIGNAL and WAIT are rights of the entry, which the lookup checks (`PermissionDenied` there); the exact recipient and the admission of a process do not exist, and the kill that cancels a wait needs CONTROL on the process, a right that the lifecycle component looks up |
| `notifications::NotFound` | Not applicable: there is no cancellation through an identity; a wait is cancelled only by the kill of its thread |
| `notifications::NotCompleted` | Not applicable: there is no take of a result |
| `notifications::TimedOut` | An outcome, `Timeout`, also for a wait whose deadline has passed when it is made; not an error |
| `waits::Object(_)` | Not kept as a wrapper, as `notifications::Object(_)` |
| `waits::Capability(_)` | Not kept as a wrapper: the errors of `lookup` are returned as they are |
| `waits::Notification(_)` | Not kept as a wrapper: the notifications are this page's |
| `waits::Ipc(_)` | Not kept as a wrapper: the errors of calls, receives and replies are the IPC component's |
| `waits::Join(_)` | Moved to the lifecycle component: joins |
| `waits::Execution(_)` | Moved: the block of a thread is `scheduler::block`, its completion is this page's, and its saved context and its return are the context and address-space components' |
| `waits::Scheduler(_)` | Moved to the scheduler: the composers return the errors of its entries as they are |
| `waits::ParallelBudget(_)` | Not applicable in release 0.1: budgets across CPUs belong to the multicore components |
| `waits::InvalidState` | As `notifications::InvalidState` |
| `waits::NotFound` | As `notifications::NotFound` |
| `waits::NotCompleted` | As `notifications::NotCompleted` |
| `waits::Capacity` | As `notifications::Capacity` |
| `waits::QuotaExceeded` | As `notifications::QuotaExceeded` |
| `waits::TokenExhausted` | As `notifications::TokenExhausted`: `GenerationExhausted` |
| `waits::ClockReversed` | As `notifications::ClockReversed` |
| `waits::Deadlock` | Moved to the IPC component for its part between calls: a call to oneself and a call that closes a cycle of calls are refused there ([calls and receives](../ipc/contract.md#calls-and-receives)); a join forms no edge of that check, and joins are the lifecycle component's |
| `WaitInProgress`, moved from the objects contract | Not applicable: a thread begins a wait only by its own call while it runs, so a blocked thread begins none, and there is no take of a result |
| `StaleWait`, moved from the objects contract | Rewritten as a rule, not an error: a completion whose generation is not that of the pending wait has no effect |
| `AlreadyCompleted`, moved from the objects contract | Rewritten as a rule, not an error: a completion of a wait that has ended has no effect; only the first completion takes effect |

## Check and execute

Every write entry of this page makes all its checks before its first write,
then changes only the copies in the write set of its caller
([write-set transactions](../../objects-capabilities/objects/contract.md#write-set-transactions)).
The items of this page are thread slots, with their wait records,
registrations and saved contexts; notification slots, with their words and
queues; and the deadline table, one item with a key of its own. That kind
of key is this component's, as the objects component leaves the items of
the composing components to their contracts, like the queue links of
other components. A composer completes the checks of every entry that it
composes before its first write; afterwards only `WriteSetFull` of
`stage`, which a write set within $W$ = 64 items never meets, and the
fault-injection points of test builds can stop it, and either discards the
buffer and leaves the state from before the transaction. The settlements of
expiry, revocation and release have no fault-injection point.

| Entry | Checks before the first write | Write set of this page |
| --- | --- | --- |
| `signal` | The bits; the lookup of the handle, or the resolution of the reference | At most 11: the notification slot; with a completion, the slot of the completed thread, its neighbours in the queues of the notification, which are the notification slot and at most 3 thread slots for a direct waiter and its successor for a wait-set waiter, at most 2 neighbours in the queue of each other notification source of a wait-set waiter, and at most 2 in the deadline table |
| `wait` | The lookup; the deadline, the word and, for a wait that blocks, the generation | 2 when it returns at once with the bits: the notification slot and the caller's slot with its result; 1 for a `Timeout` at once; at most 6 when it blocks: the caller's slot, the notification slot, the last threads of the waiter queue and of the direct queue, and the neighbours of the caller in the deadline table |
| `sleep` | The deadline and, for a sleep that blocks, the generation | 1 when it returns at once; at most 3 when it blocks: the caller's slot and its neighbours in the deadline table |
| `check_source` | The position; the lookup | Nothing: a read entry |
| `wait_set_add` | No other position with the same object; the position free | 1: the caller's slot, with its result |
| `wait_set_remove` | The position; a registration at it | 1: the caller's slot, with its result |
| `sources` | None | Nothing: a read entry |
| `wait_set_wait` | A registration; the deadline; the lookup of each registration and the readiness of its source; for a wait that blocks, the generation | 1 when it returns at once: the caller's slot, with its result and the cleared registrations; at most 11 when it blocks: the caller's slot, for each notification source its slot and the last thread of its waiter queue, and the neighbours of the caller in the deadline table |
| `begin` | The reference; no pending wait and no pause; the deadline not passed; the generation | At most 3: the slot of the thread and its neighbours in the deadline table |
| `deliver` | The reference; a pending call | 1: the slot of the caller |
| `complete` | The reference; the wait pending with the generation; for a wait set, the words of its notification sources | At most 11 for a wait set: the slot of the thread, at most 2 neighbours for each notification source and 2 in the deadline table; at most 7 for a wait on a notification: the slot, at most 4 neighbours in its two queues, the notification slot among them, and 2 in the deadline table; at most 3 for a sleep and for a wait of the IPC component |
| `first_deadline` | None | Nothing: a read entry |
| `source_ready` | The reference of the receiver; its wait set with the endpoint registered | At most 9: the slot of the receiver, at most 2 neighbours for each of its at most 3 notification sources and 2 in the deadline table |
| `drain` | The reference of the object, or of the receiver; the first thread of the waiter queue, or the wait of the receiver | At most 11, as `complete` |
| `revoked` | The reference of the thread | Nothing: a read entry |
| `unpause` | The reference; the pause naming the entry | 1: the slot of the thread |
| `cancel` | The reference | At most 11, as `complete`; 1 for a paused thread; nothing for a wait of the IPC component |

- `check_source`, `sources`, `first_deadline` and `revoked` write nothing;
  the other entries cannot fail after their checks.
- Reads that decide the effect of an entry, not whether it fails, cannot
  fail: the deadline and the word of a `wait`; the lookups of the
  registrations of `wait_set_wait`, whose failure removes a position; the
  words that a report reads; and the walk of the deadline table to the
  place of a wait.
- The composed write sets stay within $W$: a signal with its completion,
  `scheduler::enqueue`, 2 more items, and the caller's slot, at most 14; a
  wait, a sleep or a wait set that blocks with `scheduler::block` and
  `ledger::charge`, 3 more items, at most 9, 6 and 14; `source_ready` and
  `drain` with `scheduler::enqueue`, at most 11 and 13; an expiry of a wait
  of this page with `scheduler::enqueue`, at most 13. The IPC component
  counts its composed write sets with the items of `begin`, `deliver`,
  `complete` and `source_ready`.
- The settlements of a pending revocation keep within $k$ = 15 items, and
  the end of the pauses within 9 items of a step of the revocation
  ([Revocation and release](#revocation-and-release)).

## Work bounds

- `signal` makes one lookup, of at most 17 entries and one slot of the
  object table, or one resolution, one OR, and at most one completion: the
  first thread of one queue, at most `WAIT_SET_SOURCES` queues to leave and
  at most `WAIT_SET_SOURCES` words to read for its report; it writes at most
  11 items.
- `wait` makes one lookup, and, when it blocks, joins two queues at their
  tails and walks the deadline table to its place, at most the thread
  capacity of waits; it writes at most 6 items.
- `sleep` walks the deadline table, at most the thread capacity of waits,
  and writes at most 3 items.
- `check_source` makes at most two lookups; `wait_set_add` compares the
  object with at most `WAIT_SET_SOURCES` - 1 registrations and writes 1
  item; `wait_set_remove` writes 1 item; `sources` reads
  `WAIT_SET_SOURCES` registrations.
- `wait_set_wait` makes at most `WAIT_SET_SOURCES` lookups and reads at
  most `WAIT_SET_SOURCES` words, and, when it blocks, joins at most
  `WAIT_SET_SOURCES` queues and walks the deadline table, at most the
  thread capacity; it writes at most 11 items.
- `begin` walks the deadline table, at most the thread capacity, and writes
  at most 3 items; `deliver` writes 1 item.
- `complete`, `drain` and `cancel` leave at most `WAIT_SET_SOURCES` + 2
  queues, read at most `WAIT_SET_SOURCES` words and write at most 11
  items; `source_ready` reads at most `WAIT_SET_SOURCES` registrations and
  writes at most 9 items; `unpause` reads and writes one slot;
  `first_deadline` reads one item.
- `revoked` reads at most 2 + `WAIT_SET_SOURCES` entries and compares each
  with the target in at most 16 references.
- The loops of the composers in one transition, without a preemption point,
  each bounded by the thread capacity: the expiry of every passed deadline;
  the scan of a pending revocation and its settlements; and the calls of
  `drain` before the release of one object. Their time without a
  preemption point grows with the thread capacity, as the security model
  allows for deadlines that expire together
  ([internal choices](../../../security.md#internal-choices)). The walk of
  the deadline table in `wait`, `sleep`, `wait_set_wait` and `begin` is the
  only loop of an entry that the thread capacity bounds.
- The loops bounded by constants: the positions of a wait set, at most
  `WAIT_SET_SOURCES` = 4, in its checks, its joins, its leaving of queues
  and its reports; and the pauses that one step of a revocation ends, at
  most `REVOKE_BATCH` = 4 of the capabilities component.
- The component has no long operation: every entry runs to its end, and no
  progress is stored between two calls. The long operations that compose
  its entries, the revocation and the destruction of a process, store
  their progress in the capabilities and lifecycle components.
- The constants are `WAIT_SET_SOURCES` = 4, which lets one wait set hold,
  for example, two notifications and two endpoints; `REVOKE_BATCH` = 4 of
  the capabilities component; and $W$ = 64 of the objects contract. The
  deadline table and the queues hold at most the thread capacity of
  threads.

## Determinism

- **Requests.** Requests that contend for a notification, a thread slot or
  the deadline table take effect in the order in which they enter the
  kernel.
- **The single winner.** Of several waiters of one event, the first
  registered wins and the others keep waiting; a direct waiter wins against
  a wait-set waiter; for a wait set, registration is the start of the wait
  that blocked ([Single winner](#single-winner)).
- **Several wake-ups.** When one transition makes several threads ready,
  the composers call `scheduler::enqueue` in this order, which the run
  queues keep: the threads woken by the expiry first, in the order of the
  deadline table, the earliest deadline first and equal deadlines in the
  order of registration; then those woken by the event of the operation in
  the order of registration: the waiters that `drain` completes, in the
  order of the waiter queue of the notification, or for an endpoint after
  its calls, which began before the wait of its bound thread; and the
  threads whose pauses a step of a revocation ends, in the order in which
  the step removes their capabilities. A signal and `source_ready` wake at
  most one thread.
- **Expiry first.** A wait whose deadline has passed settles as `Timeout`
  before the operation of the transition, and a wait whose deadline has
  passed when it is made times out at once, consuming nothing
  ([Deadlines and sleep](#deadlines-and-sleep)).
- **Deadlines together.** Every wait whose deadline has passed settles in
  the same transition, in the loop that the thread capacity bounds.
- **The order of outcomes.** For one wait, the first transition that ends
  it decides its outcome; within one transition, timeout, cancellation,
  revocation, peer closure and the event of the wait, in this order
  ([Cancellation](#cancellation)). The IPC component states the same order
  for calls, whose event is the reply, with its rules for the order of the
  call queues, the badges of senders and the settlement of a loan as a
  whole ([calls and receives](../ipc/contract.md#calls-and-receives)).
- **Reports.** A wait set reports every source that is ready, or removed,
  in the transition that ends its wait, as one ready set and one removed
  set in the order of the positions, which are the places of the
  registrations that its thread chose.
- **Words.** The word of a notification is the OR of the bits of the
  signals since its last consumption, and a wait takes it whole.
- **Outputs.** The outcome, the bits and the report of a wait depend on the
  thread's own wait record and registrations, on the objects that it waits
  on through its capabilities, on the time and on the rules of this page;
  the order in which threads are woken is an output that scheduling
  decides, which the output sources of the
  [observable outputs](../../../security.md#observable-outputs) leave out.
  The generation of a wait is an internal identifier.
- **Time.** The time of each transition, and so which waits have expired
  and when a sleep ends, is the entry
  [ND-01](../../../security.md#nd-01) of the register of
  [permitted nondeterminism](../../../security.md#permitted-nondeterminism);
  for each value of it, the rules of this page fix the result.
- **Interrupts.** The transition in which the interrupt of a device signals
  a notification is the arrival of device interrupts that
  [ND-02](../../../security.md#nd-02) allows; for each, the rules of this
  page fix the result.
- **Several CPUs.** With more than one CPU, the order in which CPUs take
  the tokens of the same notification, thread slot or deadline table is
  the multicore interleaving of [ND-03](../../../security.md#nd-03); for
  each such order, the rules of this page fix the result.

The component leaves no other choice open.

## State fields

| Field | Class | Lock or owner | Linearization point | Publication |
| --- | --- | --- | --- | --- |
| The `kind`, `source`, `entries`, `generation`, `deadline`, `form` and `pause` of the wait record of each thread, in its thread slot | Per-thread | The CPU that runs the thread, which begins its wait; while it is blocked, the object that it waits on, whose completer writes the record, and for a wait set the sources of its registrations, for a sleep the deadline table; while it is paused, the token of the table of its process, which the steps of the revocation hold | The write-back of the write set that changes it, under the token of its owner; the write of a completion is the linearization point of the single result of the wait | At a handover: by the release of the token of the object whose completion or the end of whose pause makes the thread ready, before the thread goes to the run queue of its CPU or, on another CPU, through the pending queue of that CPU |
| The registrations of each thread, in its thread slot, without their links | Per-thread | The CPU that runs the thread, which adds, removes and checks them; while the thread waits on its wait set, the sources of its registrations, whose completer clears a removed one | The write-back of the write set that changes them | As the wait record |
| The `queue` and `direct` links of each wait record and the links of each registration in the waiter queue of its source | Shared | The token of the notification of the queue, or of the endpoint of a call queue, whose links the IPC component writes; with one CPU, the executing CPU | The release of the token after the write-back of the write set that changes them | Under the token, by the release of the lock that provides it once CPUs share it |
| The `deadlines` links of each wait record, and the first and last waits of the deadline table | Shared | The token of the deadline table; with one CPU, the executing CPU | The release of the token after the write-back | Under the token |
| The word, the waiter queue and the direct queue of each notification, in its slot | Shared | The token of the notification slot | The release of the token after the write-back | Under the token |

The deadline table is a field of the kernel root, so this page adds no
allocation to the storage carved at boot. With one CPU it holds the waits
of that CPU; how the waits of several CPUs divide among their timers, and
the tokens and locks of the shared fields, belong to the multicore
components (planned). The slots of the thread and notification pools, their
states and generations are fields of the
[objects](../../objects-capabilities/objects/contract.md#state-fields)
component; the saved context of a thread is the
[context](../../boot-platform/context/contract.md#state-fields)
component's, whose owner while the thread is blocked is the completer of its
wait; the scheduling state of a thread and the run queues are the
[scheduler](../../scheduling/scheduler/contract.md#state-fields)'s; the
endpoint queues, the bound threads and the reply records are the
[IPC](../ipc/contract.md#state-fields) component's. No lock order is stated
here.

## Testing obligations

- The host tests of the module `waits` (planned) replay every vector of
  [Legacy test vectors](#legacy-test-vectors) whose entry is on this page,
  with its expected output, and the vectors `objects-8`, for its case of a
  wait, `objects-9` and `objects-12` of the
  [objects contract](../../objects-capabilities/objects/contract.md#legacy-test-vectors),
  whose rules are on this page, and write their results for the comparison
  with the specification
  ([host results](../../../formal-verification.md#host-results)); the
  cases whose entries belong to the IPC, budget-ledger, scheduler or
  lifecycle components are replayed by the tests of those components with
  the entries of this page.
- Time: every test passes its times; no test reads a counter, depends on
  the speed of the host or uses a fixed instruction count
  ([determinism and time](../../../conventions/testing.md#determinism-and-time)).
- Signals: a signal before a wait, after a wait that blocked and after a
  completed wait, with the bits 1, $2^{63}$ and $2^{64} - 1$; coalescing of
  repeated and overlapping bits; a signal of the kernel through a reference;
  and the bits 0 refused.
- Single winner: a property test with fixed seeds drives signals, waits,
  wait sets, expiries, kills, drains and calls that join a queue on
  notifications with up to four direct and four wait-set waiters, and checks
  after every write-back, against an independent model of FIFO queues, that
  each event completes at most one waiter, that a direct waiter wins against
  a wait-set waiter, that the first registered wins, that no direct waiter is
  blocked while the word is not 0, and that no outcome changes once written.
- Deadlines: a wait whose deadline is `now` - 1, `now` and `now` + 1 when it
  is made, and 0; a signal at the deadline of a wait; three waits whose
  deadlines pass together, two of them equal, settled in the order of the
  deadline table; a deadline of $2^{64} - 1$; and a sleep until 0, `now` and
  `now` + 1.
- Wait sets: each position, `InvalidPosition`, `DuplicateSource`,
  `PositionOccupied`, `PositionEmpty` and `EmptyWaitSet`; reports of ready
  sources in the order of the positions; a source removed by the close of
  its capability before the wait, by a revocation while the thread does not
  wait and while it waits, and by the release of its object while it waits;
  a report that consumes nothing, after which a `wait` takes the word; and,
  with the IPC component, an endpoint source with a call queued before the
  wait and after it.
- Revocation: for each kind of wait, a revocation that becomes pending
  settles the waits through its subtree, pauses their threads and leaves
  the other waits; each pause ends at the step that removes its entry, at
  most four in one step, and none remains when the revocation is complete;
  a kill during a pause; and an operation that fails after the settlements
  of its transition keeps them.
- Release: the drain of a notification with direct and wait-set waiters in
  mixed order completes them in the order of the waiter queue; a release at
  the last capability finds no waiter.
- Generations: a wait that blocks with the generation $2^{64} - 1$, and the
  next wait that would block refused while one that returns at once
  succeeds.
- A completion of a thread whose saved context `validate` refuses writes no
  register, makes the thread ready, and its return ends its process with a
  user fault of the cause `Other`.
- For each error of [Errors](#errors), a call that gives it leaves every
  field of the kernel state as before, compared field by field.
- Write sets: the largest write set of each entry of
  [Check and execute](#check-and-execute) is reached and stays within its
  count, and so do the composed write sets and $k$.
- QEMU tests, from EL0 on QEMU virt, once the operations exist: a wait with a
  deadline that times out at the timer interrupt; a sleep; a signal from
  another process that wakes a waiter; and a wait set over a notification
  and an endpoint.
- The tests take their expected values from this page, from the vectors and
  from independent models, never from an earlier run of the code under test
  ([testing](../../../conventions/testing.md#independent-evidence)).

## Open obligations

The module `waits` has no `unsafe` code, no assembly and no MMIO, and its
entries are to be covered by its targets. An entry that a later contract
adds to this component beyond the entries of this page is an open
obligation of the contract that adds it, carried by the proof of object
lifetimes, waits and sequential composition, by release 0.2. The entries
use the write-set buffer that the adapter of the objects component lends,
a row of the
[open obligations of the objects contract](../../objects-capabilities/objects/contract.md#open-obligations),
and the deadline table is in the kernel root; the code of this page adds no
obligation, so the table has no row.

| Obligation | Kind | Verified state | Carrier | Stage |
| --- | --- | --- | --- | --- |

## Legacy test vectors

The vectors are host tests of the prototype tree at
`prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`, 93 in all. Their
expected outputs are those that the test bodies assert, written in the
rules of this page. The vectors are not yet in a file of the repository,
so the section holds no `vectors` block.

| File | Vectors |
| --- | ---: |
| `src/waits/tests/admission.rs` | 5 |
| `src/waits/tests/budgets.rs` | 6 |
| `src/waits/tests/execution.rs` | 1 |
| `src/waits/tests/lifecycle.rs` | 7 |
| `src/waits/tests/reuse.rs` | 1 |
| `src/waits/tests/transfers.rs` | 5 |
| `src/notifications/tests.rs` | 12 |
| `src/notifications/tests/cancellation.rs` | 7 |
| `src/notifications/tests/quotas.rs` | 8 |
| `src/objects/tests/wait_contract.rs` | 3 |
| `src/objects/tests/wait_resources.rs` | 1 |
| `src/execution/tests/waits.rs` | 7 |
| `src/execution/tests/wait_capacity.rs` | 1 |
| `src/abi/notification/tests.rs` | 8 |
| `src/abi/notification/tests/cancellation.rs` | 6 |
| `src/abi/notification/tests/quotas.rs` | 2 |
| `src/abi/waits/tests.rs` | 7 |
| `src/verification/waits/tests.rs` | 6 |

- The 25 tests of `src/waits` and the 27 of `src/notifications` are frozen
  here, among them the tests whose assertions are mostly about calls,
  transfers, loans or joins: their rows name the entries of the IPC,
  capabilities, budget-ledger and lifecycle components that replay them.
  The other files of these directories hold no test.
- The 41 tests of the other files are the tests of the prototype's wait
  records in its object pool, of the waits of its execution manager, of its
  ABI of notifications and waits and of its bounded model of waits. The
  other files of `src/abi/notification`, `src/abi/waits` and
  `src/verification/waits` hold no test.
- The id of a vector is the path of its file below `src/`, without the
  directories and files named `tests` and without `.rs`, with a hyphen
  between the parts and in place of each underscore, and the position of the
  test among the tests of its file, from 1.

A vector of this page is one test function. The vector file is to hold one
line for each case of a vector through an entry of this page, with the id
`<vector>.<n>`, `n` counting those cases from 1 in the order of the test; a
case that its row marks not applicable has no line, and a vector whose
Entry column names no entry of this page has none.

**Notation.** Times, bits and generations are decimal, or hexadecimal with
`0x`. Threads are named by letters, notifications N and endpoints E, with
the numbers of the fixtures. "N is signalled with $b$ at $t$" is `signal`
of the bits $b$ in the transition at $t$, through a capability with SIGNAL
of a thread of the row or by the kernel, through the reference of N. "T
waits on N at $t$" is T's `wait` through its capability to N with WAIT,
without a deadline unless the row gives one, and "T sleeps until $d$" is
`sleep`. "T calls E", "T receives on E" and "T replies" are the `call`,
`receive` and `reply` of the [IPC component](../ipc/contract.md), whose
errors and rules hold for them. "The expiry at $t$" is the settlement of the
waits whose deadlines have passed at the start of the transition at $t$.
"The kill of T" is the destruction of T's process by the lifecycle
component, which composes `cancel`, or `ipc::settle` with `Cancelled` for
a call or a receive. "The release of N at $t$" is its
release in the destruction of its owner, a process other than those of its
waiters, which composes `drain`. The output of a call that returns is `ok`,
`ok bits=<b>` for a wait, an outcome `timeout`, `peer-closed` or `revoked`,
or `err=<error>`, with the error by its name on this page, on the objects
or capabilities contract or on the contract that the row names; "blocks"
is a call that blocks its thread; "its wait completes with" gives the
outcome that the completion writes.

**Fixtures.**

- **Waits fixture**, for `src/waits/tests/` (`src/waits/tests.rs`, lines 8
  to 57): four processes, each with its thread T0 to T3; for each $i$, a
  notification N$i$ with a capability with SIGNAL and WAIT in the table of
  the process of T$i$, and an endpoint E$i$ that binds T$i$ as its
  receiver, with a capability with RECEIVE in that table, both owned by
  that process. T$i$ holds a capability with SEND to E$(i+1 \bmod 4)$, with
  the badge 9, so that "T$i$ calls" is a call to E$(i+1 \bmod 4)$ with the
  words 13 and 17; "T$i$ joins" is a join of T$(i+1 \bmod 4)$ of the
  lifecycle component. The prototype's registry of waits, with its
  records, its principals, its wait ceiling of 1 for each process, its
  control class of the process of T3, its control reserve and its exit
  records, does not apply.
- **Budget fixture**, for `budgets.rs`: the budget fixture of the
  [budget-ledger contract](../../scheduling/budget-ledger/contract.md#legacy-test-vectors),
  `period=100 caps=20/50/20 margin=10 epoch=0` with the time slice 10; T0
  in control with 20, T1 and T2 in background with 10 each and the ceiling
  control. "The pair" is: T0 runs from 0 and calls E1 at 1 with the
  deadline 50, which queues and charges its tick; T1 receives on E1 at 1,
  and the delivery lends T0's context to T1.
- **Transfer fixture**, for `transfers.rs`: the waits fixture with the
  capability tables of its processes; T0 holds a capability to T2 with
  every right, and T0's call to E1 that transfers a capability goes through
  a capability with SEND with the badge 17 and carries the words 19 and 23
  and the capability with OBSERVE.
- **Notification fixture**, for `src/notifications/`: a process with its
  thread T and a notification N, with a capability with SIGNAL and WAIT in
  T's table; `quotas.rs` builds such pairs of processes.
- **Object fixture**, for `src/objects/tests/`: tables of the objects
  contract with processes and their threads, and a notification N.
- **Execution fixture**, for `src/execution/tests/`: processes with their
  threads, whose saved contexts hold the fixed values of the prototype's
  fixture, and a notification N.
- **ABI fixture of notifications**, for `src/abi/notification/`: the
  process of the thread R, whose table holds a capability to N with WAIT
  and one to R with every right; the process of the thread P, whose table
  holds a capability to N with every right; the transitions at 10 unless
  the row gives another time. The prototype's sibling thread of R does not
  exist, since a process has one thread.
- **ABI fixture of waits**, for `src/abi/waits/`: three processes with
  their threads T0, T1 and T2; a notification N; endpoints E0 to E2 that
  bind T0 to T2; T0's table holds a capability to N with WAIT, one to E1
  with SEND and the badge 77 and one to E0 with RECEIVE; T2's table holds a
  capability to N with every right.
- **Model fixture**, for `src/verification/waits/`: the prototype's
  bounded serial model of one wait of each family, which its tests compare
  with the native mechanisms; here the model of the property tests, with
  the entries of this page and of the IPC component in place of the native
  mechanisms.

**Vectors of a property.** `notifications-cancellation-6`,
`verification-waits-1` and `verification-waits-2` assert a property over a
generated family of inputs; their rows state the property and the
generation rule.

**Behaviour changes.** These rules differ from the prototype:

- Every thread has its wait record in its thread slot, with a generation of
  its own: the prototype's common registry of waits, its global sequence of
  identities, its records, principals, ceilings, control reserve, admission
  of processes and exit records do not apply, and neither do its
  `Registry` configurations and their counts.
- The completion writes the result into the saved context and makes the
  thread ready in one transaction: the prototype's take, abandon and
  completed records that held their capacity until taken do not apply.
- A wait begins and blocks in one call of its own thread: the prototype's
  steps between registration, block and resumption by its execution
  manager, with their refusals, do not apply.
- A wait is cancelled only by the kill of its thread: the prototype's query
  of a wait identity and its cancellation through it, by EL0 or a trusted
  controller, with `Cancelled` for a thread that kept running, do not
  apply.
- A notification has no recipient, no badge and no closure: any holder of
  WAIT may wait on it, the bits are the argument of `signal`, and it is
  released with its last capability or its owner, after which its
  capabilities fail their lookups.
- References go stale lazily and hold back no reclamation: the prototype's
  references that pinned threads, notifications and processes until an
  abandon or a release do not apply.
- A deadline of 0 is no deadline, and every other value is valid; the time
  does not decrease within a boot and stays below $2^{63}$, so the
  prototype's refusals of a time before the last do not apply.
- A wait that returns at once begins no wait and takes no generation.
- The delivery of a call commits the transfer of its capability, so the
  prototype's commit after the delivery, and the events that ended a call
  before that commit, do not apply as written.
- A pending revocation settles the waits through its subtree as revoked and
  pauses their threads, where the prototype cancelled them.
- A process has one thread, so the prototype's sibling threads do not
  exist; joins and exits belong to the lifecycle component, and only calls
  form the cycles that the IPC component refuses.
- No counter of completions, wake-ups or references is kept.
- The receiver that an endpoint binds and the refusal of a call to oneself
  and of a cycle of calls are rules of the IPC component that keep the
  prototype's; they are no change.

### `src/waits/tests/admission.rs`

5 vectors, with the waits fixture.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `waits-admission-1` | 3 | `sibling_quota_covers_all_wait_families_and_retained_completions` | Not applicable: the test asserts the prototype's wait ceiling, which the threads of one process shared and which completed waits held until their results were taken (`QuotaExceeded`), and its refused release of the admission of a process (`InvalidState`); a process has one thread, every thread has its wait record, no ceiling or admission exists and a result is written at the completion. Its joins, closures and reaps are the lifecycle component's | None |
| `waits-admission-2` | 54 | `mixed_ordinary_saturation_preserves_every_control_wait_family` | T0 waits on N0 at 1 and T1 calls at 2, and both block. T2 then waits on N2 at 3 and blocks, where the prototype's two ordinary records were taken (`Capacity`); so do T2's call and its receive on E2 in their own cases, and every wait of T3. No class of waits exists: the prototype's control record of the process of T3 and its counts of records do not apply | `wait`; the IPC component's `call` and `receive` |
| `waits-admission-3` | 87 | `native_rejection_rolls_back_the_extra_reference_and_identity` | N1 is signalled with 4 at 1: `ok`, and its word is 4. A wait of T0 at 2 through a handle of T0's table that holds no capability is `err=NoCapability`, and through a capability of T0 to N1 without WAIT `err=PermissionDenied`; each changes nothing: the word of N1 stays 4, and T0's record keeps the kind none and its generation. The prototype's refusal of a thread that was not the recipient of N1 is the lookup of the handle here | `signal`, `wait` |
| `waits-admission-4` | 126 | `cross_family_dependencies_reject_cycles_but_ignore_completed_edges` | Its call: T0 joins T1, and T1 calls E0, whose bound thread is T0, through a capability with SEND to E0: the call is `ok`, it queues and T1 blocks, both while T0 waits in its join and after the join has ended. A join is no edge of the check of cycles of the IPC component, which only calls form ([calls and receives](../ipc/contract.md#calls-and-receives)), so the prototype's `Deadlock` across a join and a call does not apply; the join is the lifecycle component's | The IPC component's `call`; the lifecycle component, for the join |
| `waits-admission-5` | 145 | `registry_identity_exhaustion_and_foreign_cancellation_are_atomic` | T0, whose next wait generation is $2^{64} - 1$, waits on N0 at 1 and blocks with that generation; N0 is signalled with 1 at 2, and the wait completes with `ok bits=1`. T0's next wait on N0 at 3, with the word 0, would block and is `err=GenerationExhausted`, and changes nothing. The prototype's cancellation through the identity of another registry (`NotFound`) does not apply: a wait has no identity | `wait`, `signal` |

### `src/waits/tests/budgets.rs`

6 vectors, with the budget fixture.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `waits-budgets-1` | 67 | `only_authenticated_delivered_calls_can_lend_and_only_once` | T0 runs from 0 and calls E1 at 1 with the deadline 50: the call queues and lends nothing. T1 receives on E1 at 1: the delivery lends T0's context to T1 in the same transaction, so T1 has the source T0 at depth 1 and the effective class control, the lower of T0's class and T1's ceiling, above its own background, and T0 has no source. No other step lends: the prototype's explicit loan through a reply, before the delivery (`InvalidReply`), by another thread (`PermissionDenied`) and a second time (`InvalidState`), does not apply | The IPC component's `call` and `receive`; `ledger::lend` |
| `waits-budgets-2` | 92 | `active_service_cannot_accept_a_second_clients_request_under_first_budget` | After the pair, T2 calls E1 at 2 through a capability with SEND to E1 and the badge 22, with the words 2 and 2, and queues. T1, which runs on T0's context and has not replied, receives on E1 at 2: the IPC component refuses that receive with `err=ReplyPending` and changes nothing ([budget lending](../ipc/contract.md#budget-lending)), so no call is delivered to T1 under T0's context and T2 lends nothing. T1 replies with 7 and 8 at 3: T0's call ends with the reply, the loan of T1 is withdrawn in that transaction, and T0 is made ready. T2's call stays queued until T1's next receive at 3, which delivers it with a reply capability other than the first | The IPC component's `call`, `receive` and `reply`; `ledger::lend`, `ledger::withdraw` |
| `waits-budgets-3` | 127 | `every_terminal_call_event_withdraws_before_wake_and_keeps_spending` | After the pair, T1 runs from 1 to 7 on T0's context. Then, in turn: T1 replies with 1 and 2 at 7; T0 is killed at 7, which stands for both the prototype's cancellation and the termination of T0's process; T1's process, which owns E1, is destroyed at 7, which kills T1 and releases E1, for both the death of the server and the closure of E1; or the expiry at 50. In each case the call ends in one transaction that withdraws the loan of T1 before T0 is made ready: T0's record has `spent` 7, so `remaining` 13, and T1's record, until its reap, `remaining` 10 and the effective class background; T0 returns with the reply 1 and 2, `peer-closed` or `timeout`, and the killed T0 is not made ready. The prototype's refusal to wake T0 before a separate settlement (`OutstandingLoan`), the count of that settlement and its loan identity (`StaleLoan`) do not apply | The IPC component's `reply`, `ipc::settle` and `ipc::drain_step`, with `complete`; `first_deadline`; `ledger::withdraw` |
| `waits-budgets-4` | 186 | `nested_cancellation_detaches_descendant_that_is_still_waiting_for_reply` | After the pair, T1 runs from 1 and calls E2 at 2, and T2 receives on E2 at 2: the loan T1 to T2 lends T0's context at depth 2. T2 runs from 2 to 6. At 6 T0 is killed: its call ends, and the IPC component withdraws T1 and T2, two withdrawals; T1 stays blocked in its call to E2, with its wait record unchanged and no result, and no context is lent to T2 again. T2 replies with 1 and 2 at 7: T1's call ends with the reply, with no loan to withdraw, and T1 is made ready at its effective class background. The prototype's cancellation of the outer call is the kill of its caller here | The IPC component's `call`, `receive`, `reply` and `ipc::settle`, with `complete`; `ledger::withdraw` |
| `waits-budgets-5` | 217 | `outstanding_dispatch_rejects_polling_and_timeout_withdrawal` | After the pair, T1's dispatch starts at 1 and stops late, at 50: the transition at 50 first settles the expiry of T0's call, whose withdrawal of T1 has `scheduler::requeue` charge T1's dispatch up to 50 to T0's context, so T0's record has `spent` 50, its own tick and T1's 49; T0 is made ready with `timeout`. The prototype's refusal of the settlement while a dispatch runs (`Scheduler(Busy)`) does not apply: every entry runs within the dispatch of the current thread | `first_deadline`; `ipc::settle`, with `complete`; `ledger::withdraw`, `scheduler::requeue` |
| `waits-budgets-6` | 233 | `receipt_expires_before_receive_delivery_and_cannot_gain_funding` | T0 runs from 0 and calls E1 at 1 with the deadline 3; T1 receives on E1 at 1, and the delivery lends T0's context to T1. The expiry at 3 settles the call as `timeout`, withdraws T1, whose effective class is background again, and makes T0 ready. No loan of that call follows: the prototype's loan after the expiry (`InvalidReply`) does not apply | `first_deadline`; the IPC component's `call`, `receive` and `ipc::settle`, with `complete`; `ledger::lend`, `ledger::withdraw` |

### `src/waits/tests/execution.rs`

1 vector.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `waits-execution-1` | 25 | `coupled_wake_requires_all_dispatches_settled_and_keeps_cpu_charge` | Two processes with their threads H and Q, admitted in interactive with 40 each, with `period=100 caps=5/80/5 margin=10 epoch=0` and the time slice 20, and a notification N with a capability with WAIT in H's table. H runs from 1 and waits on N at 3, with the word 0: the wait blocks H, and `scheduler::block` charges its dispatch, so H's CPU time is 2; Q runs from 3. N is signalled with 7 at 4: H's wait completes with `ok bits=7`, written into H's saved context in that transaction, and H is made ready; its CPU time stays 2. The prototype's steps between the registration of the wait, the block of its thread and its resumption, with their refusals (`InvalidState`, `Busy`, `ClockWentBackwards`, `NotFound`), and its count of wake-ups do not apply: a wait blocks in the call that begins it, and its completer writes its result | `wait`, `signal`, `complete`; `scheduler::block`, `scheduler::enqueue`; `ledger::cpu_time` |

### `src/waits/tests/lifecycle.rs`

7 vectors, with the waits fixture.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `waits-lifecycle-1` | 3 | `late_identity_cannot_cancel_any_replacement_family` | For a wait on N0 and a sleep of T0, as its first and its second wait in each of the four orders: the first wait, with the generation $g$, blocks at 1 and completes at 2, a wait on N0 by a signal of 1 and a sleep until 2 by its expiry; T0's second wait blocks at 3 with the generation $g + 1$; `complete` of T0 with the generation $g$ at 4 has no effect and gives none, and the second wait stays pending with no result. The prototype's cancellation through an old identity (`NotFound`) does not exist; its calls, receives and joins are the IPC and lifecycle components' | `complete`, `wait`, `sleep`, `signal` |
| `waits-lifecycle-2` | 28 | `deadline_wins_simultaneous_cancel_and_results_remain_immutable` | T0 waits on N0 at 1 with the deadline 10. At 10 T0 is killed: the expiry at the start of that transition settles the wait as `timeout`, written into T0's saved context, before the kill, whose `cancel` finds no pending wait and writes nothing; a second completion has no effect, and the outcome stays. A call and a receive with the deadline 10 settle in the same order in their own cases. The prototype's second cancellation (`InvalidState`) and its take of the result do not apply | `first_deadline`, `complete`, `cancel` |
| `waits-lifecycle-3` | 53 | `signal_before_block_is_retained_and_later_bits_belong_to_the_next_wait` | T0 waits on N0 at 1 and blocks. N0 is signalled with 1 at 2: the wait completes with `ok bits=1`, and the word is 0. N0 is signalled with 8 at 3: the word is 8, and the result of the first wait stays `ok bits=1`. T0's next wait on N0 at 4 returns at once with `ok bits=8`. The prototype's refused cancellation of the completed wait (`InvalidState`) does not apply: there is no cancellation but the kill | `wait`, `signal` |
| `waits-lifecycle-4` | 82 | `dead_observers_retain_capacity_until_explicit_abandon` | T0 waits on N0 at 1 and blocks; the destruction of T0's process at 2 kills T0, whose `cancel` takes it out of the queues of N0, writes no result and leaves no pending wait, in the transaction of `scheduler::remove`. No wait record outlives its thread: the prototype's record that kept its capacity after the death of its thread, its refused release of the admission (`InvalidState`) and its abandon do not apply; its calls, receives and joins are the IPC and lifecycle components' | `cancel` |
| `waits-lifecycle-5` | 118 | `expired_join_observes_published_exit_and_closure_preserves_completion` | Not applicable here: a join, its exception to expiry first for an exit that is already published, its exit records and their release belong to the lifecycle component | The lifecycle component |
| `waits-lifecycle-6` | 158 | `reply_timeout_preserves_outer_clock_and_rejects_older_events` | T0 calls at 1 with the deadline 10 and T1 receives on E1 at 2. At 10 the expiry settles T0's call as `timeout` before T1's reply in that transition, which then fails with `err=ReplyGone` of the IPC component and changes nothing ([replies](../ipc/contract.md#replies)). The second case, a closure of E1 while T1 lives, does not apply: E1 is released only with its last capability or with its owner, the process of T1, whose destruction kills T1. The prototype's refusals of times before 10 (`ClockReversed`) do not apply | `first_deadline`; the IPC component's `call`, `receive`, `reply` and `ipc::settle`, with `complete` |
| `waits-lifecycle-7` | 233 | `rejected_reply_authority_does_not_advance_outer_time` | T0 calls at 1 with the deadline 10, and T1 receives on E1 at 2, which puts a reply capability into T1's table; N2 is signalled with 1 at 3, which changes nothing of the call. A reply of T1 with the handle 0 fails its lookup, and a reply of T2 with the handle of T1's reply capability names a slot of T2's own table and fails its lookup; both change nothing, and T0 has no result. T1 replies with 3 and 4 at 4: T0's call completes with the words 3 and 4. T1's second reply, with 5 and 6, is `err=NoCapability`, since the first reply deleted the reply capability, and T0's result stays 3 and 4 | The IPC component's `reply`; `lookup` of the capabilities component; `signal` |

### `src/waits/tests/reuse.rs`

1 vector.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `waits-reuse-1` | 3 | `a_reused_thread_slot_cannot_inherit_old_wait_identity_or_membership` | A process with its thread T, whose slot has the generation $g$, and a notification of it: T waits on the notification at 1 and blocks; the destruction of the process at 2 kills T with `cancel` and releases its slots. A new process takes T's slot at the generation $g + 1$ with its thread U, whose wait record has the kind none and the generation 0; U receives on its endpoint at 3 and blocks. `complete` and `cancel` with T's reference are `err=StaleReference` of the objects component and change nothing, and U's wait stays pending with no result. The prototype's admission of a process before its waits (`Notification(PermissionDenied)`), its identities and its references that held back the reaps do not apply | `complete`, `cancel`; `ObjectTable::resolve` of the objects component; the IPC component's `receive` |

### `src/waits/tests/transfers.rs`

5 vectors, with the transfer fixture.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `waits-transfers-1` | 56 | `receive_data_and_capability_are_hidden_until_accounted_commit` | For a copy and a move, with T1 receiving on E1 before and after the call in turn: T0 calls E1 at 0 with the deadline 50 and the transfer of its capability to T2. Until the delivery T1 has no result. The delivery is one transaction that reserves and commits the capability with the message: T1's results are ok, a reply handle, the badge 17, the words 19 and 23 and the handle of the received capability, a capability of T1's table that resolves with OBSERVE and is `err=PermissionDenied` with CONTROL; T0's capability still resolves after a copy and is gone after a move. The expiry at 50 settles T0's call as `timeout`, and the received capability stays usable: a committed transfer is never withdrawn. The prototype's separate commit after the delivery, with its count, does not apply | The IPC component's `call` and `receive` with its capability transfer; `reserve` and `commit` of the capabilities component; `first_deadline` |
| `waits-transfers-2` | 134 | `full_ordinary_wait_pool_rolls_back_move_while_control_wait_still_admits` | Not applicable: the test refuses a call that moves a capability because the prototype's pool of ordinary wait records was full (`Capacity`), and then admits a wait of its control class; every thread has its wait record and no class of waits exists. That a refused call leaves the source of its transfer as it was is the rule of no change on failure of the IPC component ([errors](../ipc/contract.md#errors)) | None |
| `waits-transfers-3` | 165 | `every_precommit_terminal_path_drains_hidden_rights` | T0's capability S to T2, derived with every right from a root capability in the table of T2's process, is moved by T0's call to E1 at 0 with the deadline 20. Before the delivery, for each event in turn: the expiry at 20 gives T0 `timeout`; the kill of T0, which stands for the prototype's cancellation, the death of T0 and the teardown of the table of T0's process, ends the call; the destruction of T1's process, which owns E1 and kills T1, ends it with `peer-closed`, for both the death of the receiver and the closure of E1; and the revocation of the root by T2 settles it as `revoked`, with T0 paused until the step that removes S. No reservation exists before the delivery, so nothing is drained and T1's table stays as it was; S still resolves after the expiry and the destruction of T1's process, and not after the kill or the revocation, which remove it. After the delivery the transfer is committed, so T1 holds the capability whatever then ends the call: the expiry, the kill of T0 and the destruction of T1's process do not withdraw it, and the revocation of the root removes it from T1's table in its steps and leaves T0's call pending, since T0 no longer waits through a capability of the subtree. The prototype's settlement of these events before a commit that followed the delivery, with T1's `PeerClosed`, does not apply | The IPC component's `call`, `receive`, `ipc::settle` and `ipc::drain_step`, with `deliver` and `complete`; `revoked`, `unpause`; `revoke` and `teardown_step` of the capabilities component |
| `waits-transfers-4` | 242 | `revocable_scalar_wait_cancels_after_endpoint_grant_revocation` | T0 calls E1 at 0 through a capability with SEND that it holds by derivation from a root capability to E1 with the badge 99 in the table of T2's process, and queues. At 1 T2 revokes the root: the transition that makes the revocation pending settles T0's call as `revoked`, written into T0's saved context, and pauses T0; the step of the revocation that removes T0's capability ends the pause and makes T0 ready, and T0 returns with `revoked`. The prototype's `Cancelled` for this settlement is `revoked` here | `revoked`, `complete`, `unpause`; `ipc::settle`; `revoke` of the capabilities component |
| `waits-transfers-5` | 275 | `transfer_abi_rejects_malformed_and_forged_authority_without_reservation` | A call of T0 to E1 that transfers its capability to T2, with the version 1, a reserved word 1, a mode argument of $2^{40}$ or of 0, an endpoint handle of $2^{64} - 1$ or a source handle of $2^{64} - 1$: each fails before any write, the version at the dispatch of the ABI, then the form of the arguments, then the lookups of the handles, in the order of errors; no wait begins, nothing is reserved and every table stays as it was. The encoding of the arguments belongs to the ABI inventory | The dispatch of the ABI; the IPC component's `call`; `lookup` of the capabilities component |

### `src/notifications/tests.rs`

12 vectors, with the notification fixture.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `notifications-1` | 33 | `signal_before_wait_coalesces_and_consumes_once` | N is signalled with 1, 1, 4 and $2^{63}$ at 1, each `ok`, and its word is $2^{63} + 5$. T's wait at 2 returns at once with `ok bits=9223372036854775813`, which is $2^{63} + 5$, and the word is 0. T's next wait at 3 blocks with no result. The prototype's takes of the result (`NotFound`, `NotCompleted`) do not apply | `signal`, `wait` |
| `notifications-2` | 47 | `signal_between_registration_and_sleep_cannot_be_lost` | T waits at 1 and blocks; N is signalled with 2 at 2: T's wait completes with `ok bits=2`, written into T's saved context in that transaction, and T is made ready. The prototype's interval between the registration of a wait and the block of its thread, with its separate execution wait, does not exist: a wait blocks in the call that begins it | `wait`, `signal`, `complete` |
| `notifications-3` | 65 | `completed_outbox_is_immutable_and_later_signal_waits_for_next_call` | T waits at 1 and blocks; N is signalled with 1 at 2 and with 8 at 3. T's wait completes at 2 with `ok bits=1`, which stays its result, and the word is 8 after 3; T's next wait at 4 returns at once with `ok bits=8` | `wait`, `signal` |
| `notifications-4` | 76 | `deadline_wins_at_exact_boundary_without_losing_signal` | T waits at 1 with the deadline 10 and blocks. At 10 the expiry settles the wait as `timeout` before the signal of 4 in that transition, which then finds no waiter and leaves the word 4; T's next wait at 10, without a deadline, returns at once with `ok bits=4` | `wait`, `signal`, `first_deadline`, `complete` |
| `notifications-5` | 86 | `old_and_wrong_registry_cancellation_do_not_touch_new_wait` | Not applicable: the test cancels waits through tickets of a registry (`Cancelled`, `NotFound`); a wait has no ticket, and its only cancellation is the kill of its thread ([Cancellation](#cancellation)). That a completion of an earlier wait has no effect on a later one is `waits-lifecycle-1` | None |
| `notifications-6` | 108 | `closure_settles_at_event_time_and_clears_pending_bits` | T waits at 1 with the deadline 10. The release of N at 9 completes the wait with `peer-closed`; a release at 10 instead finds it settled as `timeout` by the expiry; no later time changes either outcome. After the release a signal through a capability to N fails its lookup with `err=StaleReference`, since there is no closed state. N signalled with $2^{64} - 1$ and then released has its word cleared with its slot. The prototype's count of the references of the thread does not apply | `drain`, `first_deadline`, `signal`; `ObjectTable::release` of the objects component |
| `notifications-7` | 127 | `signal_winner_survives_cancel_close_and_future_deadline` | T waits at 1 with the deadline 10; N is signalled with 1 at 9, and the wait completes with `ok bits=1`. The release of N at 9 and the expiry at 11 then find no pending wait of T, and the outcome stays; the prototype's cancellation after the signal (`InvalidState`) is a kill here, whose `cancel` finds no pending wait either | `signal`, `drain`, `first_deadline`, `cancel` |
| `notifications-8` | 138 | `timeout_wins_over_cancellation` | T waits at 1 with the deadline 10. At 10 T is killed: the expiry settles the wait as `timeout` before the kill, whose `cancel` then finds no pending wait | `first_deadline`, `complete`, `cancel` |
| `notifications-9` | 146 | `death_keeps_recipient_pinned_until_wait_and_object_are_drained` | T waits at 1; the destruction of T's process at 2 kills T, whose `cancel` takes it out of the queues of N and writes no result, so no queue of N names T, and neither the reap of T nor the release of N waits for the other. The prototype's references that held T and N until an abandon (`ReferencesOutstanding`) do not apply: references go stale lazily | `cancel` |
| `notifications-10` | 168 | `invalid_authority_duplicate_waits_and_bad_input_are_atomic` | N is signalled with 1 at 5. Each of these changes nothing and leaves the word 1: a wait of a thread of another process through a handle of its table that holds no capability to N fails its lookup; a wait through a capability to N without WAIT is `err=PermissionDenied`; a signal with the bits 0 is `err=InvalidBits`; a signal through a capability to N without SIGNAL is `err=PermissionDenied`. T's wait at 6 with the deadline 6 is `timeout` and consumes nothing. T's wait at 6 with the deadline 0, which is no deadline, returns at once with `ok bits=1`. The prototype's refusals of the deadline 0 (`InvalidDeadline`), of a time before the last (`ClockReversed`) and of a second wait while a result was not taken (`InvalidState`) do not apply | `signal`, `wait`; `lookup` of the capabilities component |
| `notifications-11` | 199 | `capacity_rejection_preserves_bits_but_signals_still_complete_waits` | T waits on N at 1 and blocks; a notification N2 of a second process is signalled with 2 at 2, and the thread U of that process waits on N2 at 3 and returns at once with `ok bits=2`, where the prototype's single record, held by T, refused it (`Capacity`). N is signalled with 1 at 3, and T's wait completes with `ok bits=1`. The prototype's completed record that held its capacity until its result was taken does not apply | `wait`, `signal` |
| `notifications-12` | 226 | `tokens_never_wrap_and_failed_admission_preserves_pending_bits` | T's next wait generation is $2^{64} - 1$. N is signalled with 1 at 1, and T's wait at 2 returns at once with `ok bits=1`, which begins no wait and takes no generation. T's wait at 3, with the word 0, blocks with the generation $2^{64} - 1$, and N signalled with 2 at 4 completes it with `ok bits=2`. N is signalled with 4 at 5, and T's wait at 6 returns at once with `ok bits=4`; with the word 0, T's wait at 7 would block and is `err=GenerationExhausted`, which changes nothing. The prototype's token of a wait that its word satisfied at once, and its refusal of a wait with the word 2 (`TokenExhausted`), which kept the word, do not apply | `signal`, `wait` |

### `src/notifications/tests/cancellation.rs`

7 vectors, with the notification fixture.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `notifications-cancellation-1` | 4 | `observation_is_nonallocating_and_keeps_completed_outboxes` | Not applicable: there is no query of the identity of a wait and no cancellation through it; the identity of a wait is no observable output, and the only cancellation of a wait is the kill of its thread ([Cancellation](#cancellation)) | None |
| `notifications-cancellation-2` | 23 | `old_identity_wrong_registry_and_wrong_target_cannot_cancel_replacement` | Not applicable, as `notifications-cancellation-1`: there is no cancellation through an identity, a registry or a target thread. That a completion of an earlier wait has no effect on a later one is `waits-lifecycle-1` | None |
| `notifications-cancellation-3` | 74 | `full_capacity_still_permits_observation_and_cancellation_without_releasing_slot` | Not applicable: there is no query and no cancellation of a wait, and no pool of records whose capacity a completed wait holds | None |
| `notifications-cancellation-4` | 101 | `native_observation_and_cancellation_require_both_rights` | Not applicable here: there is no query and no cancellation of a wait through a thread capability; the kill that cancels a wait needs CONTROL on the process ([rights](../../objects-capabilities/capabilities/contract.md#rights)), which the lifecycle component looks up | The capabilities and lifecycle components |
| `notifications-cancellation-5` | 121 | `cancellation_reports_newly_due_timeout_or_peer_death_without_claiming_success` | T waits at 1 with the deadline 10. A kill of T at 10 finds the wait settled as `timeout` by the expiry of that transition. The release of N at 9 completes the wait with `peer-closed`, and a kill of T at 9 after it finds no pending wait. The prototype's death of T, which it reported as `PeerClosed`, is a kill here, whose outcome T does not observe | `first_deadline`, `complete`, `drain`, `cancel` |
| `notifications-cancellation-6` | 143 | `all_signal_cancel_close_death_orders_have_one_terminal_result` | Property. T waits at 1, once with no deadline and once with the deadline 2. For each of the 24 orders of four events, at 2, 3, 4 and 5 in turn, which are a signal of 8, the prototype's cancellation and the death of T, both a kill of T here, and the release of N: with the deadline 2, the expiry at 2 settles the wait as `timeout` before the first event; without it, the first event decides, `ok bits=8` for the signal, the cancellation for a kill and `peer-closed` for the release. After every event the outcome is the same, every later event finds no pending wait of T, and no queue of N names T. The prototype's take of the result and its count of references do not apply | `signal`, `cancel`, `drain`, `first_deadline`, `complete` |
| `notifications-cancellation-7` | 195 | `identity_preserves_full_width_and_exhaustion_never_reuses_a_sequence` | T, whose next wait generation is $2^{64} - 1$, waits at 1 and blocks with that generation, in all its 64 bits; N is signalled with 1 at 2, and the wait completes with `ok bits=1`. T's next wait at 3, with the word 0, would block and is `err=GenerationExhausted`, which changes nothing. The prototype's registry number and identity of a wait, and its refusal of a time before the last (`ClockReversed`), do not apply | `wait`, `signal` |

### `src/notifications/tests/quotas.rs`

8 vectors, with the notification fixture.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `notifications-quotas-1` | 25 | `configuration_and_admission_failures_are_atomic` | Not applicable: the test configures the prototype's registry of waits and its control reserve (`InvalidConfiguration`) and admits processes to it with ceilings and rights (`InvalidConfiguration`, `Object(PermissionDenied)`, `InvalidState`); there is no registry, reserve, admission or ceiling of waits | None |
| `notifications-quotas-2` | 86 | `unadmitted_process_cannot_consume_event_or_enter_reserve` | N is signalled with 8 at 1, and T's wait at 2 returns at once with `ok bits=8`, where the prototype refused a process without an admission (`PermissionDenied`) and kept the word: no admission of waits exists | `signal`, `wait` |
| `notifications-quotas-3` | 97 | `sibling_threads_share_quota_and_completed_outboxes_still_charge_it` | Not applicable: the test shares a ceiling of waits between two threads of one process (`QuotaExceeded`) and refuses the release of the admission while a record lives (`InvalidState`, `NotFound`); a process has one thread, and there is no ceiling or admission | None |
| `notifications-quotas-4` | 132 | `ordinary_saturation_preserves_control_metadata_and_record_capacity` | Not applicable: the test fills the prototype's pools of ordinary and control records and principals (`Capacity`); every thread has its wait record, and no class of waits exists | None |
| `notifications-quotas-5` | 180 | `control_limits_are_not_overcommitted_and_never_borrow_ordinary_slots` | Not applicable: the test asserts the ceilings of the prototype's control class against its reserve (`Capacity`, `QuotaExceeded`); there is no class, ceiling or reserve of waits | None |
| `notifications-quotas-6` | 206 | `timeout_close_and_death_hold_quota_until_drain` | For the expiry at 10 of T's wait with the deadline 10, for the release of N at 2 and for the kill of T at 2 in turn: T's wait ends with `timeout`, `peer-closed` and the cancellation, as `notifications-4`, `notifications-6` and `notifications-9` state, and nothing of the wait outlives it. The prototype's record that held the ceiling of the process until an abandon, with the refused release of its admission (`InvalidState`), does not apply | `first_deadline`, `complete`, `drain`, `cancel` |
| `notifications-quotas-7` | 238 | `principal_generation_is_pinned_and_reuse_needs_fresh_admission` | Not applicable: the test pins the generation of an admitted process until the release of its admission (`ReferencesOutstanding`) and refuses a new process in the same slot without an admission (`PermissionDenied`, `Object(StaleHandle)`); there is no admission, and references go stale lazily | None |
| `notifications-quotas-8` | 269 | `stale_cross_pool_and_dead_admission_are_rejected_without_pinning` | Not applicable: the test refuses the admissions of a process of another pool and of a dead process (`Object(WrongPool)`, `InvalidState`, `NotFound`); there is no admission of waits | None |

### `src/objects/tests/wait_contract.rs`

3 vectors, with the object fixture.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `objects-wait-contract-1` | 16 | `wait_completion_counter_saturates_without_losing_result_or_counting_errors` | For a completion of T's wait on N with `ok bits=1` by a signal, and by the kill of T, in turn: the first completion of the generation $g$ ends the wait; a second completion of $g$, as `timeout`, has no effect and no error, `complete` gives none, and T's result and wait record do not change; a completion of $g$ after the wait has ended, the prototype's `StaleWait`, has none either. The prototype's count of completions and its saturation do not apply: no count is kept, and its `AlreadyCompleted` and `StaleWait` are no errors here | `complete`, `cancel`, `signal` |
| `objects-wait-contract-2` | 46 | `wait_operations_preserve_other_threads_processes_and_unrelated_metadata` | Two processes with their threads T and U: T's wait on N begins, and `complete` ends it as `peer-closed`. U's thread slot, both process slots and the fields of T's slot that are not of this page, its process, its owner and its budget record among them, do not change, and the write sets of both entries hold only the items of [Check and execute](#check-and-execute). The prototype's second thread of one process and its count of completions do not apply | `wait`, `complete` |
| `objects-wait-contract-3` | 86 | `invalid_wait_handles_obey_error_priority_without_mutating_the_pool` | A wait begins by a call of its own thread, not through a thread handle, so the prototype's thread handle of a wait does not apply. The order of the errors of the handle of a wait is that of the [lookup](../../objects-capabilities/capabilities/contract.md#lookup) of the capabilities component: a handle of a capability without WAIT to a released notification is `err=StaleReference`, since the liveness of the object comes before the rights, where the prototype checked the rights first (`PermissionDenied`), then the pool (`WrongPool`), then the slot and the generation (`StaleHandle`); each refusal changes nothing | `wait`; `lookup` of the capabilities component |

### `src/objects/tests/wait_resources.rs`

1 vector.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `objects-wait-resources-1` | 5 | `wait_reference_overflow_cannot_publish_principal_admission` | Not applicable: the test overflows the prototype's count of the wait references of a process at its admission (`Object(CounterOverflow)`) and restricts the release of the admission to a handle with every right (`Object(PermissionDenied)`); there is no admission and no count of wait references | None |

### `src/execution/tests/waits.rs`

7 vectors, with the execution fixture.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `execution-waits-1` | 32 | `repeated_owned_waits_preserve_registers_backing_and_accounting` | T, whose saved context holds the fixture's values, waits on N, blocks and is in no run queue; its wait completes in turn with `ok bits=1` by a signal, with `timeout` by the expiry of its deadline and with `peer-closed` by the release of N. Each completion writes the result registers of the wait into T's saved context, leaves its other registers, its process, its address space and its CPU time as they were and makes T ready, and a second completion of the same generation has no effect. The prototype's outcomes `Cancelled` and `Terminated` are the kill here, after which T does not run again; its resumption by the domain manager, its refusals while T was blocked (`InvalidState`), its take of the result (`StaleWait`) and its count of completions do not apply | `wait`, `complete`, `drain`; `Context::set_return_values` of the context component; `scheduler::block`, `scheduler::enqueue` |
| `execution-waits-2` | 111 | `unconfigured_waits_and_foreign_pool_handles_fail_without_mutation` | Not applicable: a wait begins only by a call of the running thread, whose saved context exists, so a thread without one never waits; a reference of another pool is `err=WrongPool` of `ObjectTable::resolve`, which the vectors of the objects contract test, and the termination of a thread is the lifecycle component's | None |
| `execution-waits-3` | 146 | `any_active_domain_blocks_wait_mutation_and_inactive_termination` | Not applicable: every entry runs within the dispatch of the current thread, so a completion, a kill or a destruction of another thread does not wait for that dispatch to stop, and the prototype's `Busy` does not apply. That a blocked thread is made ready while another runs is `scheduler-waits-3` of the [scheduler contract](../../scheduling/scheduler/contract.md#legacy-test-vectors) | None |
| `execution-waits-4` | 189 | `terminating_ready_or_blocked_domains_drains_waits_and_prevents_resurrection` | For T ready and for T blocked in a wait on N: the destruction of T's process kills T. For the blocked T, `cancel` takes its wait out of the queues of N and of the deadline table and writes no result; `scheduler::remove` takes T out of scheduling. No wait of T is then pending, `complete` of it has no effect, and T neither runs nor begins a wait again. The prototype's terminal states, exit reasons, counts and the operations that it refused on a dead domain are the lifecycle component's | `cancel`, `complete`; `scheduler::remove` |
| `execution-waits-5` | 246 | `destroying_blocked_domain_drains_owned_wait_before_failed_tlbi_retry` | In the destruction of the process of a T that is blocked in a wait, the kill completes the wait with `cancel` before the steps that reclaim the address space; a later step that stops at a failure and is repeated finds no pending wait of T. The TLB invalidation, its failure (`Asid(InvalidationFailed)`), its retry and the reclamation are the address-space and lifecycle components' | `cancel`; the lifecycle and address-space components |
| `execution-waits-6` | 290 | `reference_failure_keeps_sleeping_domain_and_wait_unchanged` | Not applicable: references go stale lazily and hold back no reclamation, so the prototype's refusal to destroy a blocked thread that a reference held (`ReferencesOutstanding`) does not apply; the destruction kills the thread as `execution-waits-4` states | None |
| `execution-waits-7` | 316 | `stale_thread_generation_cannot_wake_block_or_terminate_reused_domain` | T blocks in a wait, its process is destroyed, and a new thread U takes T's slot at the next generation and blocks in a wait: `complete` and `cancel` with T's reference are `err=StaleReference` of the objects component and change nothing, and U stays blocked; U's completion by the expiry of its deadline writes its result and leaves its saved context otherwise as it was | `complete`, `cancel`; `ObjectTable::resolve` of the objects component |

### `src/execution/tests/wait_capacity.rs`

1 vector.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `execution-wait-capacity-1` | 5 | `wait_principal_membership_prevents_domain_retirement_until_released` | Not applicable: the test holds back the destruction of a process with an admission of waits (`ReferencesOutstanding`) until the release of the admission; there is no admission of waits | None |

### `src/abi/notification/tests.rs`

8 vectors, with the ABI fixture of notifications.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `abi-notification-1` | 101 | `namespace_type_rights_and_exact_recipient_are_required` | At 10, each changing nothing: R's signal with the handle of P's capability, which names a slot of R's own table, fails its lookup; R's signal through its capability with WAIT alone is `err=PermissionDenied`; R's wait through its thread capability is `err=WrongType`. P's wait through its capability with every right blocks, since any holder of WAIT may wait: the prototype's exact recipient (`PERMISSION_DENIED`) does not exist, nor do its sibling thread and its closure | `signal`, `wait`; `lookup` of the capabilities component |
| `abi-notification-2` | 157 | `pending_and_immediate_delivery_return_only_the_authorized_mask` | R waits at 10 and blocks; P signals N with `0x81`: `ok`, and R's wait completes with `ok bits=0x81`, its other result registers 0. P signals N with `0x81` again, and R's next wait returns at once with `ok bits=0x81`. The prototype's mask in the badge of P's capability is the bits argument of `signal` here | `wait`, `signal` |
| `abi-notification-3` | 180 | `reserved_registers_version_and_unknown_operations_cannot_publish_events` | P's signal with the version 1, with a reserved word 1, with the operation number $2^{64} - 1$, or with an argument that `signal` does not use set to 1: each is refused by the dispatch of the ABI before the lookup, with the error of the first check that fails in the order of errors and its other result registers 0, and N's word stays 0. Which arguments `signal` uses belongs to the ABI inventory | The dispatch of the ABI; `signal` |
| `abi-notification-4` | 231 | `derived_signal_retains_badge_and_revocation_preserves_admitted_events` | P derives a capability with SIGNAL from its own and signals N through it with `0x81`: `ok`. P revokes its own capability; once the revocation is complete, a signal through the derived one fails its lookup, and the bits already set stay: R's wait returns at once with `ok bits=0x81`. A revocation withdraws authority, not the signals made with it | `signal`, `wait`; `derive` and `revoke` of the capabilities component |
| `abi-notification-5` | 256 | `closed_capability_does_not_cancel_admitted_wait_and_teardown_drains_refs` | Not applicable as written: R cannot close the capability through which it waits while it is blocked, since a process has one thread. That P's signal completes R's wait is `abi-notification-2`; references go stale lazily, so the prototype's count of external references after the teardown does not apply | None |
| `abi-notification-6` | 276 | `metadata_close_is_owner_authorized_and_stale_receipts_stay_rejected` | Not applicable: a notification has no closure and no closed state; it is released with its last capability or its owner, after which a capability to it fails its lookup (`StaleReference`), as `notifications-6` states | None |
| `abi-notification-7` | 301 | `zero_badge_rejected_for_signal_authority_and_clocked_wait_returns_timeout` | R's wait at 10 with the deadline 10 is `timeout` at once and begins no wait. The prototype's refusal of a capability with SIGNAL and the badge 0 (`InvalidRights`) does not apply: only endpoint capabilities carry a badge, and `signal` refuses the bits 0 (`InvalidBits`) | `wait`, `signal` |
| `abi-notification-8` | 329 | `dedicated_dispatch_preserves_native_closure_policy` | A notification N2 that the kernel signals for an interrupt, with a capability with WAIT and one with every right in R's table: the kernel's signal of N2 with 4 at 10 is `ok` and sets the word 4; R's wait through its capability with WAIT returns at once with `ok bits=4`. Which interrupt signals N2, its binding and its acknowledgement belong to the device-authority rules; the prototype's closure, refused to EL0 (`PERMISSION_DENIED`), does not exist, nor does its sibling thread | `signal`, `wait` |

### `src/abi/notification/tests/cancellation.rs`

6 vectors, with the ABI fixture of notifications.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `abi-notification-cancellation-1` | 42 | `user_cancel_is_authorized_and_wakes_only_the_exact_retained_wait` | Not applicable: there is no query of the identity of a wait and no cancellation through it from EL0; a wait is cancelled only by the kill of its thread, which completes the wait record ([Cancellation](#cancellation)) | None |
| `abi-notification-cancellation-2` | 88 | `observer_control_only_wrong_type_and_foreign_namespace_have_no_authority` | Not applicable, as `abi-notification-cancellation-1`; the kill needs CONTROL on the process, which the lifecycle component looks up with the capabilities component | None |
| `abi-notification-cancellation-3` | 140 | `revocation_between_query_and_cancel_is_checked_again_without_losing_events` | Not applicable as written: there is no cancellation through a thread capability. Its parts that hold here: a capability that a complete revocation removed fails its lookup, a rule of the capabilities component; and R's wait, which the revocation of P's capabilities to R does not touch, completes with `ok bits=0x81` when N is signalled with `0x81` at 12 | `signal`; `lookup` of the capabilities component |
| `abi-notification-cancellation-4` | 173 | `dead_nonready_restricted_and_wrong_pool_callers_cannot_cancel` | Not applicable: there is no cancellation from EL0, and the caller of an operation is the running thread, so a dead, an activating or a foreign caller does not exist | None |
| `abi-notification-cancellation-5` | 214 | `full_width_identity_validation_and_reserved_fields_reject_atomically` | Not applicable: no operation takes the identity of a wait; the version, the reserved words and the unused arguments of an operation are refused by the dispatch of the ABI, as `abi-notification-3` states | None |
| `abi-notification-cancellation-6` | 268 | `deadline_death_and_existing_completion_cannot_be_reported_as_cancelled` | R waits at 10 with the deadline 20. A kill of R at 20 finds the wait settled as `timeout` by the expiry. N signalled with 8 at 18 completes the wait with `ok bits=8`, and the release of N at 18 instead completes it with `peer-closed`; a kill of R at 19 then finds no pending wait, and the outcome stays. The prototype's death of R, which it reported as `PEER_CLOSED`, is a kill here | `first_deadline`, `complete`, `signal`, `drain`, `cancel` |

### `src/abi/notification/tests/quotas.rs`

2 vectors, with the ABI fixture of notifications.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `abi-notification-quotas-1` | 4 | `authenticated_siblings_share_wait_quota_and_cannot_supply_control_class` | Not applicable: the test shares a ceiling of waits between R and a sibling thread of its process (`NO_CAPACITY`) and refuses a class of waits chosen by an argument; a process has one thread, and there is no ceiling or class of waits. An argument that `wait` does not use, set to 1, is refused by the dispatch of the ABI, as `abi-notification-3` states | None |
| `abi-notification-quotas-2` | 70 | `notification_capability_without_process_admission_does_not_authorize_wait_capacity` | P's signal of `0x81` is `ok` and sets the word `0x81`, and R's wait then returns at once with `ok bits=0x81`, where the prototype refused it to a process whose admission had been released (`PERMISSION_DENIED`): no admission of waits exists, and a signal allocates nothing | `signal`, `wait` |

### `src/abi/waits/tests.rs`

7 vectors, with the ABI fixture of waits.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `abi-waits-1` | 110 | `cross_family_query_and_cancel_compare_identity_after_fresh_authority` | Not applicable: there is no query and no cancellation of a wait through its identity; that a completion of an earlier wait has no effect on a later one is `waits-lifecycle-1`, and joins are the lifecycle component's | None |
| `abi-waits-2` | 169 | `cancellation_rechecks_namespace_type_rights_and_revocation` | Not applicable, as `abi-waits-1`; the lookups that it repeats are those of the capabilities component | None |
| `abi-waits-3` | 228 | `malformed_operations_leave_all_waits_untouched` | For `signal` and `wait`, and for the call, receive and reply of the IPC component in their own cases: an argument that the operation does not use, set to 1, the version 1 and a reserved word 1 are each refused by the dispatch of the ABI before any lookup, and change nothing. Which arguments each operation uses belongs to the ABI inventory; the prototype's query, cancellation, join and closures do not exist here | The dispatch of the ABI |
| `abi-waits-4` | 271 | `timeout_precedes_authorized_cancel_and_join_returns_typed_exit` | T0's wait on N, and in its own case its receive on E0, with the deadline 10 at 1: at 10 the expiry settles it as `timeout` before a kill of T0 in that transition. The join with its typed exit, and its refusal through a capability of another kind, are the lifecycle component's | `first_deadline`, `complete`, `cancel`; the IPC component's `receive` |
| `abi-waits-5` | 311 | `notification_and_ipc_results_preserve_native_words_and_badges` | T2 signals N with 8 at 1: `ok`; T0's wait at 1 returns at once with `ok bits=8`. T0 calls E1 at 2 through its capability with SEND and the badge 77, with the words 11 and 12, and queues; T1, the bound thread of E1, receives on it through a capability with RECEIVE: its results are ok, a reply handle other than 0, the badge 77 and the words 11 and 12, with the last result register 0. T1 replies with 21 and 22: `ok`, and T0's call completes with ok and the words 21 and 22 | `signal`, `wait`; the IPC component's `call`, `receive` and `reply` |
| `abi-waits-6` | 362 | `closure_compares_exact_owner_identity_without_amplifying_authority` | Not applicable: there is no closure of a notification or an endpoint; each is released with its last capability or its owner, after which a capability to it fails its lookup | None |
| `abi-waits-7` | 393 | `native_irq_notifications_bind_waits_without_delegating_closure` | A notification N2 that the kernel signals for an interrupt, with a capability with WAIT in T0's table and one in T1's table, and one with every right in T0's table: a signal through T0's capability with WAIT is `err=PermissionDenied`; the kernel's signal of N2 with 8 at 1 sets the word 8, and T1's wait through its capability returns at once with `ok bits=8`, where the prototype bound N2 to T0, refused T1 (`PERMISSION_DENIED`) and gave the 8 to T0: a notification has no recipient. T0 waits at 3 with the deadline 10 and blocks, and the release of N2 at 4 completes the wait with `peer-closed`. The binding of N2 to an interrupt belongs to the device-authority rules, and the prototype's closure by EL0 does not exist | `signal`, `wait`, `drain` |

### `src/verification/waits/tests.rs`

6 vectors, with the model fixture.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `verification-waits-1` | 152 | `bounded_serial_completion_traces_match_native_mechanisms` | Property. For one wait on a notification and for one call, the join's family being the lifecycle component's: for each of the 40,320 orders of the eight actions charge, the stop of the waiter's dispatch; block, the call that begins the wait; publish, a signal, or the delivery and the reply of the call; cancel, the kill of the waiter; close, the release of the object; advance, a time past the deadline; poll, the expiry at that time; and deliver, the waiter made ready: the entries of this page and of the IPC component, driven in that order wherever the independent model of one wait accepts the action, give after each action the observations of the model: at most one outcome, which never changes once written; no thread made ready before its wait has completed and its loan has been withdrawn; and the four outcomes success, `Timeout`, `Cancelled` and `PeerClosed` all occur among the accepted orders. Here a wait blocks in the call that stops its dispatch, so charge and block are one step of the entries | `wait`, `signal`, `complete`, `cancel`, `drain`, `first_deadline`; the IPC component |
| `verification-waits-2` | 171 | `bounded_serial_death_traces_match_native_mechanisms` | Property. The property of `verification-waits-1`, without the count of outcomes, for each of the 5,040 orders of the seven actions charge, block, cancel, close, advance, poll and die, with cancel and die both the kill of the waiter; the prototype's abandon of the result of a dead waiter does not exist, since no result is taken | `wait`, `cancel`, `drain`, `first_deadline`, `complete`; the IPC component |
| `verification-waits-3` | 190 | `observer_rejects_lost_results_double_wakes_and_accounting_drift` | The observer of the property tests compares each state with the model and rejects a lost wait record, a lost or changed outcome, a thread made ready before its completion, a charge one tick off and a second wake-up: after a signal, a wait that blocks and its completion, the thread is made ready once, a second `scheduler::enqueue` of it is `err=InvalidState` of the scheduler, and a completion of its old generation has no effect. The prototype's refusal of a wake-up while a dispatch runs (`Busy`) does not apply | `complete`; `scheduler::enqueue` |
| `verification-waits-4` | 238 | `model_rejects_delivery_before_settlement_and_double_delivery` | The model of the property tests refuses a block that does not follow the stop of the dispatch, a wake-up before the completion, and, after a signal, a wait that blocks, its completion and the readiness of its thread, a second readiness and a second block of that wait. Here a wait blocks in the call that stops the dispatch, and only the completion of a wait makes its thread ready, once | None: the model of the tests |
| `verification-waits-5` | 256 | `immediate_deadline_rules_remain_family_specific` | N with the word 1: a wait at 10 with the deadline 10 is `timeout` at once and the word stays 1; a call at 10 with the deadline 10 is `timeout` at once, as the IPC component states. The join of a thread that exited with 17, which sees the exit despite the deadline 10 at 10, is the lifecycle component's exception to expiry first | `wait`; the IPC component's `call`; the lifecycle component |
| `verification-waits-6` | 289 | `released_native_receipts_cannot_affect_a_replacement_wait` | For a wait on N and a call as the first and the second wait of one thread, in each of the four orders, the joins being the lifecycle component's: the first wait ends by the expiry of its deadline, and the second begins with the next generation; a completion of the first generation has no effect, a reply through the reply capability of a first call fails with `err=ReplyGone` of the IPC component, and the second wait stays pending with no result. The prototype's notification ticket (`NotFound`), join ticket and execution ticket (`StaleWait`) do not exist | `complete`, `wait`, `first_deadline`; the IPC component's `call` and `reply` |

### Vectors of other pages

These vectors are frozen on other pages and replayed here, and the count of
93 leaves them out.

| Vector | Page and file | Line | Test | Here | Entry |
| --- | --- | ---: | --- | --- | --- |
| `objects-8` | The [objects contract](../../objects-capabilities/objects/contract.md#legacy-test-vectors), `src/objects/tests.rs` | 159 | `a_receipt_from_another_pool_cannot_name_a_matching_slot` | Its case of a wait only: `complete` with the reference of a thread of another table, whose pool numbers differ, is `err=WrongPool` of `ObjectTable::resolve`, and no wait becomes pending or ends | `complete` |
| `objects-9` | The objects contract, `src/objects/tests.rs` | 257 | `all_wait_completion_orders_have_exactly_one_winner` | For each of a signal, the expiry, the kill and the release of N as the first completion of T's wait: the first ends the wait and writes its outcome; each later completion of that generation has no effect and no error, where the prototype answered `AlreadyCompleted`; a completion of an earlier generation has none either, its `StaleWait`; the blocked T begins no second wait, its `WaitInProgress`; there is no take of the result | `complete`, `cancel`, `drain`, `signal` |
| `objects-12` | The objects contract, `src/objects/tests.rs` | 396 | `wait_generation_exhaustion_does_not_reset_to_an_old_ticket` | A thread whose next wait generation is $2^{64} - 1$: its wait blocks with that generation and completes; a further wait that would block is `err=GenerationExhausted`, and the thread stays as it was, with no pending wait | `wait`, `sleep`, `wait_set_wait`, `begin` |
| `cx-27` | The [context contract](../../boot-platform/context/contract.md#legacy-test-vectors), `src/execution/tests/returns.rs` | 204 | `ready_metadata_does_not_bypass_an_unconsumed_owned_wait` | No case: a completed wait that its thread has not consumed does not exist, since the completion writes the result into the saved context and makes the thread ready in one transaction, so a ready thread has no pending result, and only the completer writes the saved context of a blocked thread | None |

## References

- The kernel's own rules, which this page instantiates:
  [IPC, notifications and waits](../../../architecture.md#ipc-notifications-and-waits)
  for notifications that coalesce, deadlines, wait sets with the fixed
  reason of a removed source, and a timeout that means only that the caller
  stopped waiting; the execution model under
  [System calls and the ABI](../../../architecture.md#system-calls-and-the-abi)
  for the wait record, completion by continuation, the cancellation of a
  wait by the completion of its record and scheduling only before a return
  to EL0; [Scheduling and budgets](../../../architecture.md#scheduling-and-budgets)
  for the run queues that the completions feed; and
  [Multicore by design](../../../architecture.md#multicore-by-design) for
  the classes of state, the wait records as per-thread state and the
  completion as the linearization point of the single result.
- The [security model](../../../security.md): its
  [internal choices](../../../security.md#internal-choices) for the single
  winner, the wake-ups, the reports of wait sets, expiry first, the order
  of outcomes and the order of errors; its
  [effective revocation](../../../security.md#effective-revocation) for the
  pause of affected execution; its
  [observable outputs](../../../security.md#observable-outputs); and the
  register of
  [permitted nondeterminism](../../../security.md#permitted-nondeterminism).
- The rules of this page take, as clauses of their own, the rules of the
  prototype tree at `prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`:
  - `docs/features/kernel/notifications.md`, lines 116 to 148: the word of
    pending bits, the rights to signal and to wait, and the waits that keep
    their object when a capability is closed; its badge as a mask, its
    recipient and its closure do not apply;
  - `docs/features/kernel/notifications.md`, lines 149 to 206: a signal
    before and after the registration of a wait, results that never change,
    a timeout at an exact deadline that keeps the bits, the earliest
    deadline that bounds the timer, and the settlement of a wait when its
    thread dies; its registry, its take and its tickets do not apply;
  - `docs/features/kernel/notifications.md`, lines 207 to 228: the order
    of a newly due deadline and a peer death before a cancellation; its
    query and its cancellation through an identity do not apply;
  - `docs/features/kernel/waits.md`, lines 97 to 163: identities that never
    select a later wait and the cycle check between calls; its capacity
    classes and principals are only a contrast here;
  - `docs/features/kernel/waits.md`, lines 164 to 233: a signal, a timeout
    and a peer death that allocate nothing, the serial composition of
    blocking and completion, and the family rules of deadlines;
  - `docs/features/kernel/ipc.md`, lines 172 to 184: the composition of the
    waits of calls with the other waits, which the IPC component shares;
  - `docs/kernel-state.md`, lines 110 to 131: the single owner of waits and
    loans, which no interrupt path borrows.
