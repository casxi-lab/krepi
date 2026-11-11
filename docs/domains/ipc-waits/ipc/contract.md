# IPC contract

This page governs the code of the `ipc` component of the
[IPC and waits](../README.md) domain: the endpoints with the receive thread
that each binds at its creation, their queue of calls and their receiver;
`call`, `receive` and `reply` with the states of a call and of a receiver;
the refusal of a call to oneself and of a call that closes a cycle of
calls; the reply record of each thread and the one-shot reply capability;
the badge that a receiver sees; the composition of the transfer of a
capability with its message; the times at which a budget loan is made and
withdrawn; the settlement of a call by each of its outcomes; and the part of
this component in the release of an endpoint, the deletion of a reply
capability and the destruction of a bound thread. The wait records, their
deadlines and expiry, notifications and wait sets belong to the
[waits](../waits/contract.md) component; the capability tables, the lookup
of a handle and the table side of a transfer to the
[capabilities](../../objects-capabilities/capabilities/contract.md)
component; the loans of budgets to the
[budget-ledger](../../scheduling/budget-ledger/contract.md) component; the
run queues to the [scheduler](../../scheduling/scheduler/contract.md)
component; the creation of an endpoint and the lifetimes of processes and
threads to the modules `creation` and `lifecycle` (planned), which compose
the entries of this page. The observable behaviour that these rules serve,
with its evidence, is in the [requirements](requirements.md), the other
document of the component.

## Terms

- **Endpoint.** An object of the endpoint pool of the
  [objects](../../objects-capabilities/objects/contract.md#object-kinds-and-pools)
  component, which the creation component creates for a holder of the
  creation right and which its creator owns. Its slot holds the fields of
  [Endpoint queues](#endpoint-queues).
- **Bound thread.** The receive thread of an endpoint: the thread whose
  reference the creation of the endpoint binds to it, and which alone
  receives from it ([Calls and receives](#calls-and-receives)).
- **Caller and receiver.** The caller is the thread that makes a call. The
  receiver of a call is the bound thread of its endpoint, also called the
  server while it serves the call.
- **Message.** `ipc::MESSAGE_WORDS` (planned) = 2 words of 64 bits, which a
  call carries to its receiver and a reply back to the caller.
- **Call.** The call of a caller from its `call` to its end. It is
  **queued** while it waits in the queue of its endpoint, **delivered** from
  the transition that gives it to the receiver until it ends, and **ended**
  by its outcome. A call is **live** while it is queued or delivered.
- **Delivery.** The transaction that gives a queued call, or a call that
  finds its receiver waiting, to the receiver: the message, the badge, the
  reply capability, a transferred capability and the loan of the caller's
  context, all in one write-back.
- **Serving.** A thread serves a call from its delivery to the thread until
  the call ends.
- **Outcome.** How a live call or a waiting receive ends: a call by its
  reply, or by `Timeout`, `Cancelled`, `Revoked`, `PeerClosed` or the error
  of a refused delivery; a receive by a delivery, or by `Timeout`,
  `Cancelled`, `Revoked` or `PeerClosed`. An outcome is a result of an
  operation that was accepted, not an error ([Errors](#errors)).
- **Reply record.** `ipc::ReplyRecord` (planned): the record of this page
  in the slot of every thread, with the generation of its replies, the
  state of its call and the parts of a queued call that its delivery needs
  ([Replies](#replies)).
- **Reply capability.** The capability of the kind reply that a delivery
  installs in the receiver's table: it holds REPLY alone, its object is the
  reference of the caller and its badge the generation of the caller's
  reply record
  ([rights](../../objects-capabilities/capabilities/contract.md#rights)).
  It is **live** while that generation is the current generation of the
  reply record of a live caller.
- **Context, source, owner and depth.** As the
  [budget-ledger](../../scheduling/budget-ledger/contract.md#terms)
  component defines them.
- **Chain of a call.** The threads that hold the context that a delivered
  call lent: its receiver while it holds that loan and, while a thread of
  the chain waits for the reply of a delivered call of its own, the
  receiver of that call, to which it lent the same context one level
  deeper ([Budget lending](#budget-lending)). These threads are
  **downstream** of the receiver; the threads that lent the context to the
  caller are **upstream** of it.
- **Call edge.** For a thread whose call is live, queued or delivered, the
  edge from that thread to the bound thread of the endpoint of the call.
  The **call graph** is the set of all call edges.
- **Served endpoint.** An endpoint whose bound thread is live, and whose
  owner and the process of whose bound thread are alive in the lifecycle
  states of processes (planned). The composer reads these states from the
  lifecycle component and passes the result as a value.
- **Time.** `now`: the value of the virtual counter that the architecture
  crate reads once on entry to a transition, which the composer passes to
  the entries of this page that need it
  ([ND-01](../../../security.md#nd-01)). A **deadline** is an absolute value
  of that counter, or 0 for none, as the
  [waits](../waits/contract.md#deadlines-and-sleep) component states.
- **Composer.** A module of the core above this one that composes an entry
  of this page into an operation: `dispatch`, `lifecycle` or `creation`
  (planned).
- **Token.** What an access to state that is not per-CPU holds, as the
  [SMP design rules](../../../conventions/smp.md#s1-state-classes) state;
  with one CPU, the executing CPU holds every token.

## Entry points

The entries of the core are in the module `ipc` of `krepi-kernel`
(planned). Three of them are operations of the ABI inventory, in its
production range: `call`, `receive` and `reply` (planned). Their operation
numbers, the registers of their arguments and results, and the numeric
values of their errors and of the statuses of their outcomes belong to the
inventory; this page names the arguments and the results. The other entries
are called by the composers.

| Entry point | Kind | Called by | ABI operation | Rules |
| --- | --- | --- | --- | --- |
| `ipc::init_endpoint` (planned) | Write entry on the copies of a write set, host-testable | `creation` (planned), in the write set that occupies the slot of a new endpoint, with the reference of the thread that the creator's capability to a thread with CONTROL names | None | [Endpoint queues](#endpoint-queues), [Calls and receives](#calls-and-receives) |
| `ipc::call` (planned) | Write entry on the copies of a write set, host-testable | `dispatch` (planned), for the operation `call`, with whether the endpoint is served | `call` | [Calls and receives](#calls-and-receives), [Badges and sender identity](#badges-and-sender-identity), [Capability transfer](#capability-transfer), [Budget lending](#budget-lending) |
| `ipc::receive` (planned) | Write entry on the copies of a write set, host-testable | `dispatch` (planned), for the operation `receive`, with whether the endpoint is served | `receive` | [Calls and receives](#calls-and-receives), [Replies](#replies), [Capability transfer](#capability-transfer), [Budget lending](#budget-lending) |
| `ipc::reply` (planned) | Write entry on the copies of a write set, host-testable | `dispatch` (planned), for the operation `reply` | `reply` | [Replies](#replies), [Budget lending](#budget-lending), [Settlement of a call](#settlement-of-a-call) |
| `ipc::settle` (planned) | Write entry on the copies of a write set, host-testable | `dispatch` (planned): for a call or a receive whose deadline has passed, which `waits::first_deadline` gives, before the operation of the transition, and in the pending transition of a revocation, for a call or a receive that waits through its subtree, which `waits::revoked` names; `lifecycle` (planned): for the call or the receive of a thread that a forced kill ends | None | [Settlement of a call](#settlement-of-a-call) |
| `ipc::reply_deleted` (planned) | Write entry on the copies of a write set, host-testable | `dispatch` (planned), for the operation `close` of a reply capability, with `Tables::close`; `lifecycle` (planned), for a reply capability that a step of the teardown of a table deletes, with `Tables::teardown_step` | None | [Replies](#replies), [Release and peer closure](#release-and-peer-closure) |
| `ipc::drain_step` (planned) | Write entry, one settlement for each write set, host-testable | `lifecycle` (planned), in the steps of the destruction of the owner of an endpoint, before the release of its slot and `waits::drain`, and in the steps of the destruction of the process of its bound thread | None | [Release and peer closure](#release-and-peer-closure) |
| `ipc::check_receiver` (planned) | Read entry, host-testable | `dispatch` (planned), for the operation `wait_set_add` of the waits component with an endpoint as its source, after `waits::check_source` and before `waits::wait_set_add` | None | [Calls and receives](#calls-and-receives) |
| `ipc::has_call` (planned) | Read entry, host-testable | `dispatch` (planned), for the operation `wait_set_wait` of the waits component, once for each endpoint that `waits::sources` gives, before `waits::wait_set_wait` | None | [Endpoint queues](#endpoint-queues) |

## Extractability

The module `ipc` of the core (planned), below `kernel/src/` (planned),
follows the [provable Rust subset](../../../conventions/provable-subset.md):
the fields of endpoints and reply records, calls, receives and replies, the
walk of the call graph, badges, the composition of transfers, the times of
loans, settlement and drains. Its items are `pub(crate)`: the architecture
crate and the board crates call no entry of this page
([provable core](../../../architecture.md#the-provable-core)). The module is
in layer 6 of the
[module order](../../../architecture.md#module-order-in-the-core): it
refers to the modules `objects`, for references, resolution and write sets,
`capabilities`, for lookups, installation, transfer and close, `ledger`,
for loans, `waits`, for the wait records of calls and receives through
`waits::begin`, `waits::deliver` and `waits::complete` and for
`waits::source_ready`, `scheduler`, which its contract puts in layer 5, for
blocking and readiness, and to the kernel root; and to no module above it,
such as `lifecycle`, `creation` and `dispatch`. The module `waits` does not
refer to it: whether an endpoint has a queued call and whether a thread is
its bound thread reach the waits component through `dispatch`, which reads
them with `has_call` and `check_receiver`, and the bound thread of an
endpoint through `source_ready` and `drain`, to which this page and the
lifecycle component pass it. Whether an endpoint is served is a state of
the lifecycle component, in layer 7, which the composer passes as a
value.

Its write entries receive the one kernel root by `&mut`
([rule 3](../../../conventions/provable-subset.md#3-flat-relations-and-one-kernel-root)),
and the write-set buffer, the scheduler record and the budget ledger of the
executing CPU by explicit `&mut` arguments
([rule 8](../../../conventions/provable-subset.md#8-no-interior-mutability)).
The module defines no callback: the destruction of a process, the expiry of
a deadline and the steps of a revocation are composed by `lifecycle` and
`dispatch`, and each entry of this page gives only the checks and the
writes of its own part. The module has no adapter of its own: the adapters
that lend the per-CPU state are rows of the open obligations of the
[objects](../../objects-capabilities/objects/contract.md#open-obligations),
[budget-ledger](../../scheduling/budget-ledger/contract.md#open-obligations)
and [scheduler](../../scheduling/scheduler/contract.md#open-obligations)
contracts. The contract is written before its code, so this section lists
no source paths; the change that adds the module writes its `paths` block
here.

## Endpoint queues

The slot of an endpoint holds these fields of this page. It keeps no
queue of waiters of wait sets: only its bound thread can register it, and
the [waits](../waits/contract.md#wait-sets) component completes that
thread with `waits::source_ready`.

| Field | Content | Written by |
| --- | --- | --- |
| `bound` | The reference of the bound thread | `init_endpoint` |
| `first`, `last` | The first and the last thread of the queue of calls, or none | `call`, `receive`, `settle`, `drain_step` |
| `receiver` | The bound thread while it waits in a receive from the endpoint, or none | `call`, `receive`, `settle`, `drain_step` |

- **Initialization.** `init_endpoint(endpoint, thread)` resolves `thread`
  with `resolve` of the objects component (`WrongPool`, `StaleReference`)
  and writes `bound` with its reference, an empty queue and no receiver.
  The right that binds the thread is CONTROL on a capability to it, which
  the creation component looks up
  ([rights](../../objects-capabilities/capabilities/contract.md#rights));
  the bound thread may belong to another process than the creator.
- **Fixed binding.** No operation changes `bound`. The binding is a
  reference, which goes stale lazily when the thread is reaped and holds
  back no reclamation; the endpoint then has no bound thread that lives,
  and it is not served ([Release and peer closure](#release-and-peer-closure)).
- **Queue of calls.** The queue links the queued callers through the queue
  links of their wait records, which the waits component defines, in the
  order in which the calls were made. A call joins the tail, and a delivery
  takes the head; a settlement or a drain takes a call out wherever it is.
- **One receiver.** Only the bound thread receives, and a thread waits in at
  most one receive, so an endpoint has at most one receiver and a thread is
  the receiver of at most one endpoint. For the same reason only the bound
  thread registers the endpoint in a wait set, so the endpoint has at most
  one waiter of a wait set.
- **Invariants.** After every write-back: every thread in the queue of an
  endpoint is blocked in a queued call of that endpoint, and every queued
  call is in the queue of its endpoint; a thread is in at most one queue; a
  receiver is the bound thread, blocked in a receive from the endpoint; and
  while an endpoint has a receiver, its queue is empty, since a receive
  that finds a call takes it and a call that finds the receiver is
  delivered at once.
- **Readiness.** `has_call(endpoint)` gives whether the queue holds a call.
  It writes nothing; `dispatch` passes it to `waits::wait_set_wait` as the
  readiness of the endpoint as a source of a wait set.
- **A call that queues.** A call that joins the queue of an endpoint calls,
  in the same write set, `waits::source_ready` of the
  [waits](../waits/contract.md#wait-sets) component with the endpoint and
  its bound thread, which completes that thread when it waits on its wait
  set with the endpoint registered, and then `scheduler::enqueue` for the
  thread that it gives.

## Calls and receives

**The call.** `call(caller, endpoint, words, deadline, transfer, served,
now)` sends the two words of `words` through the caller's capability
`endpoint`, which needs SEND. `transfer` is none, or the handle of a source
with the requested rights and the mode, copy or move
([Capability transfer](#capability-transfer)). `served` is the value that
the composer passes. It makes these checks in this order and returns the
first error, writing nothing:

1. the transfer: its rights mask is well formed (`InvalidRights`), and a
   move does not name as its source the handle of the call itself
   (`SelfTransfer`);
2. the lookups of `endpoint`, for the kind endpoint with SEND, and of the
   source of a transfer, for any kind with GRANT and the requested rights,
   with `Tables::lookup` of the
   [capabilities](../../objects-capabilities/capabilities/contract.md#lookup)
   component; when both fail, the error of the earlier place in the order
   of [Errors](#errors) decides, and at the same place that of `endpoint`;
3. the caller's reply record has a generation below $2^{64} - 1$
   (`ReplyExhausted`, [Replies](#replies));
4. the bound thread of the endpoint is not the caller (`SelfCall`), and the
   call closes no cycle of the call graph (`Cycle`), as the walk below
   states;
5. when the call would block its caller, since its deadline has not passed
   and the endpoint is served, the caller's wait generation is below
   $2^{64} - 1$ (`GenerationExhausted` of the
   [waits](../waits/contract.md#wait-records) component, the check of
   `waits::begin`);
6. the new path of the transferred capability holds at most `MAX_DEPTH`
   references (`DepthExceeded` of the capabilities component); and, when
   the call would be delivered at once, since its deadline has not passed,
   the endpoint is served and the receiver waits, the loan of its delivery
   passes the depth check of `ledger::lend` (`LoanDepth` of the
   [budget-ledger](../../scheduling/budget-ledger/contract.md#lending)
   component).

Then, in this order:

- a deadline that is not 0 and not later than `now` ends the call at once
  with `Timeout`, and the call changes nothing;
- an endpoint that is not served ends the call at once with `PeerClosed`,
  and the call changes nothing;
- when the receiver waits, the call is delivered at once
  ([delivery](#delivery)), and the caller blocks, waiting for the reply;
- otherwise the call joins the tail of the queue and the caller blocks.

A call that blocks writes, after its checks, the reply record of the
caller: the state, queued or delivered, and for a queued call its badge,
its words and its transfer. It starts the wait record of the caller with
`waits::begin` of the [waits](../waits/contract.md#wait-records)
component: the endpoint as the object of its wait, the entry references
through which it waits, the capability of the call and, for a queued call
with a transfer, the source, its deadline, the result registers `x0` to
`x5` and the next wait generation; a queued call is linked into the queue
through the `queue` field of that record. `scheduler::block` stops the
dispatch of the caller
([blocking](../../scheduling/scheduler/contract.md#blocking-and-readiness)).

**The receive.** `receive(receiver, endpoint, deadline, reply_slot,
transfer_slot, served, now)` takes a call from the receiver's capability
`endpoint`, which needs RECEIVE. `reply_slot` and `transfer_slot` are slots
of the receiver's own table, which take the reply capability and a
transferred capability. It makes these checks in this order and returns the
first error, writing nothing:

1. both slots are below `capability_slots` (`InvalidSlot` of the
   capabilities component), and they are different slots (`SameSlot`);
2. the lookup of `endpoint` for the kind endpoint with RECEIVE;
3. the receiver is the bound thread of the endpoint (`NotReceiver`);
4. the receiver serves no call (`ReplyPending`,
   [Budget lending](#budget-lending));
5. each slot, the reply slot first, holds no capability (`SlotOccupied`)
   and has not retired (`GenerationExhausted` of the capabilities
   component), the checks of `Tables::install` and `Tables::reserve` of the
   [capabilities](../../objects-capabilities/capabilities/contract.md#derivation-and-badges)
   component on the receiver's table;
6. when the receive would block, since its deadline has not passed, the
   endpoint is served and no queued call passes the checks of its
   delivery, the receiver's wait generation is below $2^{64} - 1$
   (`GenerationExhausted` of the
   [waits](../waits/contract.md#wait-records) component, the check of
   `waits::begin`); to find whether it would block, the receive reads the
   queued calls and makes the checks of their deliveries, and writes
   nothing.

Then, in this order:

- a deadline that is not 0 and not later than `now` ends the receive at
  once with `Timeout`; it takes no call and changes nothing;
- an endpoint that is not served ends the receive at once with
  `PeerClosed`, and it changes nothing;
- while the queue holds a call, the receive takes the first: when the
  checks of its delivery pass, it is delivered at once and the receive
  returns its results without blocking; when they fail, the call ends with
  their error as its outcome, in a transaction of its own
  ([Settlement of a call](#settlement-of-a-call)), and the receive takes
  the next;
- with the queue empty, the receive blocks: the receiver becomes the
  receiver of the endpoint and starts its wait record with `waits::begin`
  of the [waits](../waits/contract.md#wait-records) component, with the
  endpoint, the entry reference of its capability and its deadline; its
  reply record keeps its two slots, and `scheduler::block` stops its
  dispatch.

A receive makes all its checks, also whether it can block, before it ends
the first queued call whose delivery fails, so after such an end it
delivers a call or blocks, and never fails. A receive that finds a call
whose delivery passes never blocks: its results are those of its return,
and the scheduler takes part only through `scheduler::requeue`, which
charges the receiver's dispatch up to the loan of the delivery.

### Delivery

A delivery of the call of C to the receiver R is one transaction. Its checks
are those of `Tables::reserve` for a transfer and of `ledger::lend` for the
loan; a call that is delivered at once has made them among its own checks.
Then it:

1. installs the reply capability into R's reply slot with
   `Tables::install`, with the reference of C, REPLY and the generation of
   C's reply record;
2. reserves and commits a transfer into R's transfer slot
   ([Capability transfer](#capability-transfer));
3. lends C's context to R with `ledger::lend`; when R runs, as at a
   receive, it calls `scheduler::requeue` for R
   ([lending](../../scheduling/budget-ledger/contract.md#lending));
4. sets C's reply record to delivered, and R's `serving` to C; the wait of
   C becomes the wait for the reply of a delivered call, with the same
   deadline: for a queued call, `waits::deliver` removes the transfer
   source from its entries, and a call delivered at once begins its wait
   without it;
5. gives R its results: when R waits in a receive, by `waits::complete` of
   its wait record, which writes them into its saved context with
   `Context::set_return_registers`, and `scheduler::enqueue` of R; at a
   receive, as the results of its return.

The checks of a delivery made by a receive can fail only for a source of a
transfer whose object has been released since the call
(`StaleReference`), and for a loan whose depth would exceed
`MAX_LOAN_DEPTH` (`LoanDepth`): the caller is blocked, so no other check of
the transfer or of the loan can change.

### Results

The results of `call`, `receive` and `reply` are written to the six result
registers, `x0` to `x5`: a status and the values that the table names, in
the positions that the ABI inventory gives, every other register 0.

| Operation and outcome | Status | Values |
| --- | --- | --- |
| A call, ended by its reply | Success | The two words of the reply |
| A call, ended by `Timeout`, `Revoked` or `PeerClosed`, or by the error of a refused delivery | That outcome or error | None |
| A receive, ended by a delivery | Success | The handle of the reply capability, the badge, the two words of the call and the handle of the transferred capability, 0 without one |
| A receive, ended by `Timeout`, `Revoked` or `PeerClosed` | That outcome | None |
| A reply | Success | None |
| A refused operation | Its error | None |

A thread ended by `Cancelled` is killed and observes no result. A result is
written once, by the first completion of the wait, and never changes; the
woken thread only returns with it
([internal choices](../../../security.md#internal-choices)).

### States and transitions

A call:

| From | Entry or event | To | Result, and who is woken |
| --- | --- | --- | --- |
| No call | `call` with a deadline not later than `now`, or on an endpoint that is not served | Ended: `Timeout` or `PeerClosed` | The caller's results at once; it does not block |
| No call | `call`, the receiver waits | Delivered | The receiver's results; the receiver is made ready |
| No call | `call`, otherwise | Queued | None; the caller blocks |
| Queued | `receive` by the bound thread, the call first in the queue | Delivered | The receiver's results, at its return |
| Queued | `receive`, the checks of the delivery fail | Ended: `StaleReference` or `LoanDepth` | The caller's results; the caller is made ready |
| Delivered | `reply` with the live reply capability | Ended: the reply | The caller's results; the caller is made ready |
| Queued or delivered | The expiry of the deadline | Ended: `Timeout` | The caller's results; the caller is made ready |
| Queued or delivered | The forced kill of the caller | Ended: `Cancelled` | None: the caller does not run again |
| Queued or delivered | The pending transition of a revocation whose subtree holds an entry through which the call waits | Ended: `Revoked` | The caller's results; the caller is paused, and the step of the revocation that removes that entry makes it ready |
| Queued or delivered | A drain of the endpoint; for a delivered call, also the deletion of its live reply capability | Ended: `PeerClosed` | The caller's results; the caller is made ready |

An ended call has no transition: every later event finds no wait and
changes nothing of it.

A receiver:

| From | Entry or event | To | Result, and who is woken |
| --- | --- | --- | --- |
| Idle | `receive` with a deadline not later than `now`, or on an endpoint that is not served | Idle | `Timeout` or `PeerClosed` at once |
| Idle | `receive`, a call is queued and its delivery passes | Serving | The receive's results at its return |
| Idle | `receive`, the queue is empty | Waiting | None; the receiver blocks |
| Waiting | `call` | Serving | The receiver's results; the receiver is made ready |
| Waiting | The expiry of the deadline | Idle | `Timeout`; the receiver is made ready |
| Waiting | The forced kill of the receiver | Idle | `Cancelled`, which it does not observe: the receiver does not run again |
| Waiting | The pending transition of a revocation whose subtree holds its capability | Idle | `Revoked`; the receiver is paused until the step that removes that capability |
| Waiting | A drain of the endpoint | Idle | `PeerClosed`; the receiver is made ready |
| Serving | The end of the served call, by any outcome | Idle | As for the call |

A serving thread runs, calls and waits as any thread does; it does not
receive until its served call ends ([Budget lending](#budget-lending)).

### Bound thread

- **Only the bound thread receives.** `receive` by any other thread, also
  one that holds a capability to the endpoint with RECEIVE, is refused with
  `NotReceiver`, and so is `check_receiver(endpoint, thread)` for the
  registration of the endpoint in a wait set by such a thread. RECEIVE stays
  the right of `receive`, a constant of the operation that the lookup
  checks; the binding is a state of the endpoint, which this page checks
  after the lookup.
- **A bound thread that has gone.** When the process of the bound thread
  is no longer alive, or the binding has gone stale, the endpoint is not
  served: a call to it ends at once with `PeerClosed` and queues nothing.
  The calls that are live on it when the process of its bound thread is
  destroyed end by the drains of
  [Release and peer closure](#release-and-peer-closure).

### Calls to oneself and cycles

Before its first write, `call` follows the call edges from the bound thread
of its endpoint:

1. if the bound thread is the caller, the call is refused with `SelfCall`;
2. otherwise, from $t_0$, the bound thread, while $t_i$ is live and its
   call is live, queued or delivered, the walk takes $t_{i+1}$, the bound
   thread of the endpoint of that call; if $t_{i+1}$ is the caller, the
   call is refused with `Cycle`;
3. the walk ends without an error at a thread that is not live or has no
   live call.

Each step reads the slot of $t_i$, with its wait record and its reply
record, and the slot of the endpoint of its call: two items, and no write.
A queued call is an edge as a delivered one is: its caller cannot receive
until the call ends, so a call to it would wait as well. A wait whose
deadline has expired settles before the operation of its transition, so its
edge is gone when the walk runs.

- **The call graph.** After every write-back, each thread has at most one
  outgoing call edge, since a thread has at most one live call, and the
  graph has no cycle: an edge is added only by the call that blocks its
  caller, which runs and so has no edge of its own, after the walk found no
  path from the bound thread back to the caller; a binding never changes;
  and an edge is removed when its call ends.
- **Bound.** So the threads of a walk are distinct and none is the caller:
  the walk takes at most the thread capacity of the
  [capacity record](../../objects-capabilities/objects/contract.md#capacity-record)
  less one steps.
- **What it detects.** The walk detects dependencies of calls, not every
  deadlock of an application: a wait on a notification or a wait set, a
  sleep and a server that does not receive are no edge.
- **Loans.** The receiver of a delivery is not the caller and not upstream
  of it in the chain of its context, since that would be a cycle; so no
  loan closes a cycle ([Budget lending](#budget-lending)).

## Replies

The reply record of a thread has these fields:

| Field | Content | Written by |
| --- | --- | --- |
| `generation` | The generation of the replies of the thread, 64 bits, from 1 | The end of a delivered call of the thread |
| `call` | The state of the thread's call: none, queued or delivered | `call`, the delivery, the end of the call |
| `badge`, `words`, `transfer` | Of a queued call: the badge of the capability of the call, the two words, and the transfer, none or the entry reference of its source with the requested rights and the mode | `call`; cleared by the delivery and the end of the call |
| `slots` | While the thread waits in a receive: its reply slot and its transfer slot | `receive`; cleared at the end of its wait |
| `serving` | The caller whose delivered call the thread serves, or none | The delivery; cleared by the end of the served call |

- **One reply capability.** A delivery installs one reply capability into
  the slot that the receiver named, with the reference of the caller as its
  object and the generation of the caller's reply record as its badge, as
  [Derivation and badges](../../objects-capabilities/capabilities/contract.md#derivation-and-badges)
  of the capabilities component states. It has no GRANT, so it is never
  copied, derived or transferred, and it stays in the table of the server.
- **The reply.** `reply(replier, reply, words, now)` makes the lookup of
  the handle `reply` for the kind reply with REPLY, which fails with
  `StaleReference` once the caller has been reaped; then it checks that the
  caller's call is delivered and that the generation of its reply record
  equals the badge of the capability (`ReplyGone`). It then ends the call
  with the reply, in one write set: it withdraws the loan of the replier
  ([Budget lending](#budget-lending)), ends the caller's wait with
  `waits::complete`, which writes its results with the two words, raises
  the generation by 1, deletes the reply capability with `Tables::close`,
  and then makes the caller ready with `scheduler::enqueue`.
- **Once.** The reply deletes its capability, so a second use of its handle
  fails in the lookup (`NoCapability`, or `StaleHandle` once the slot holds
  another capability) and changes nothing.
- **After the end of a call.** Every end of a delivered call raises the
  generation of the caller's reply record by 1, also by `Timeout`,
  `Cancelled`, `Revoked` and `PeerClosed`, in the write set that settles
  it, and touches no table of the server. The reply capability stays in the
  server's table, and a reply with it fails with `ReplyGone` and changes
  nothing: this is the fixed error of a reply to a caller whose call has
  timed out, of the
  [internal choices](../../../security.md#internal-choices). The server
  deletes it with `close`, which needs no right.
- **Close of a live reply capability.** When the server closes a reply
  capability that is live, or a step of the teardown of its table deletes
  it, the composer adds `reply_deleted(caller, generation, now)`, with the
  object and the badge of the deleted entry: the call ends with
  `PeerClosed` ([Settlement of a call](#settlement-of-a-call)), its loans
  withdrawn before the caller is made ready. For a capability that is not
  live, because its caller has been reaped or its generation is old,
  `reply_deleted` gives `none` and writes nothing.
- **Exhaustion.** A call by a thread whose reply record has the generation
  $2^{64} - 1$ is refused with `ReplyExhausted`, since the end of its
  delivery would have no next generation; a thread retires its replies as
  a slot of a table retires, and the generation never wraps.
- **Reuse of a thread slot.** The reply record belongs to the slot of the
  thread and is cleared when the slot is released; a new thread in the
  slot starts at generation 1. A reply capability of the earlier thread
  names its reference, which is no longer live, so its lookup fails with
  `StaleReference`, whatever its generation.
- **One live reply capability in a table.** A thread serves at most one
  call ([Budget lending](#budget-lending)) and a process has one thread, so
  the table of a process holds at most one live reply capability; every
  other reply capability in it is old.

The reply record of a thread:

| From | Entry or event | To | Generation |
| --- | --- | --- | --- |
| No call | `call` that queues | Queued | Kept |
| No call | `call` that is delivered at once | Delivered | Kept; the reply capability holds it |
| Queued | Its delivery | Delivered | Kept; the reply capability holds it |
| Queued | Any other end of the call | No call | Kept |
| Delivered | `reply` with the live reply capability | No call | Raised by 1; the reply capability deleted |
| Delivered | Any other end of the call | No call | Raised by 1; the reply capability stays, old |

## Badges and sender identity

- **One source.** The badge that a receiver gets is the `badge` field of the
  capability through which the caller called, as `Tables::lookup` gives it
  at the call; a queued call keeps it in its reply record until its
  delivery. A capability without a badge gives 0.
- **Set once.** The badge is set by the derivation that mints a send
  capability and kept by every derivation, copy and transfer
  ([derivation and badges](../../objects-capabilities/capabilities/contract.md#derivation-and-badges));
  no operation of this page writes it.
- **No identity in the request.** The words, the deadline, the transfer and
  every other argument of the call are never taken into the badge, and the
  kernel delivers no other identity of the caller: neither the reference
  nor a handle of its process or its thread. So a caller cannot claim the
  identity of another through its request.
- **Counterexample.** A caller whose send capability has the badge 5 and
  whose words are the badge 9 of another client's capability and the
  value of a handle of that client is delivered with the badge 5, and with
  its words as the two words of the message, unchanged.
- **Output.** The badge is an output of the receiver, whose source is the
  capability of the caller, which the party that minted it chose
  ([sender identity](../../../security.md#unforgeable-authority)).

## Capability transfer

A call carries at most one capability. The transfer commits at its
delivery: the message and the capability become visible to the receiver in
the same write-back.

- **The receive slot.** The receiver names its transfer slot when it starts
  to receive, and `receive` checks that the slot is empty and has not
  retired. While the receiver waits, no operation fills it: a process has
  one thread, and only operations of the receiver's own thread fill slots of
  its table. So the slot is held for the transfer from the start of the
  receive, before the message is sent, as the
  [IPC](../../../architecture.md#ipc-notifications-and-waits) of the kernel
  requires.
- **At the call.** The call checks the source as a derivation does, with
  GRANT and the requested rights, and the depth of the new path. A queued
  call reserves nothing, since its receive slot is not yet known; it keeps
  the entry reference of the source, the rights and the mode in its reply
  record, and its wait record names the source among the entries through
  which it waits.
- **At the delivery.** The delivery reserves the capability into the
  receiver's transfer slot with `Tables::reserve` and commits it with
  `Tables::commit`, in the write set that also installs the reply
  capability and gives the receiver its results
  ([transfer](../../objects-capabilities/capabilities/contract.md#transfer)).
  A copy leaves the source; a move deletes it at the commit, so the
  received capability takes its place among its siblings.
- **A source that has gone.** A delivery by a receive checks the source
  again. When the object of the source has been released since the call,
  the check fails with `StaleReference`: no delivery takes place, the call
  ends with that error ([Settlement of a call](#settlement-of-a-call)), and
  the receive takes the next call. The source itself stays in its entry: the
  caller is blocked and cannot close it, a revocation of it settles the call
  first, and the teardown of its table follows the end of the call.
- **No reservation across transitions.** A reservation exists only within
  the write set of a delivery, whose checks are all made before its first
  write. So this page never calls `Tables::abort`, and no failure can come
  between a reservation and its commit: the restoration of a moved source
  before the commit holds because nothing is reserved before it. The entry
  reference of the reservation, which the capabilities component leaves to
  this component, lives only within that write set.
- **Not the capability of the call.** A move whose source is the capability
  through which the call is sent is refused (`SelfTransfer`). A caller keeps
  the capability through which it waits until its call ends, which
  [Release and peer closure](#release-and-peer-closure) relies on; a copy of
  it is allowed.
- **After the commit.** A later outcome of the call does not undo the
  transfer: a timeout, a kill or a revocation of the call leaves the
  received capability in the receiver's table.
- **The prototype's vectors.** The vectors of the prototype's transfers,
  which the [waits](../waits/contract.md#legacy-test-vectors) contract
  freezes, are read in this model. In `waits-transfers-1`, "no result
  before the commit" is no result before the delivery, after which the
  receiver has the words, the badge, the reply capability and the received
  capability at once; the caller's later timeout leaves the committed
  capability, as stated above. In `waits-transfers-3`, for a call that is
  still queued, the seven events end the call before any reservation, so
  only the assertions that the caller has a result and that the source
  stays apply, the source being deleted by the caller's death, by the
  revocation and by the teardown of its table; for a delivered call, the
  transfer has committed at its delivery and the receiver keeps the
  capability, where the prototype aborted a reservation that its commit had
  not yet published.

## Budget lending

- **When a loan is made.** A delivery lends the context of the caller to
  the receiver with `ledger::lend(caller, receiver)` of the
  [budget-ledger](../../scheduling/budget-ledger/contract.md#lending)
  component: the caller's own record at depth 1, or the context that the
  caller borrows, one level deeper. So nested calls lend one context along
  their chain, and the receiver runs at the effective class that the
  ceiling of its admission bounds. When the receiver is the current thread,
  at a receive, the delivery calls `scheduler::requeue` for it.
- **One holder.** A context has one holder that runs: the threads that use
  it form one chain from its owner, each blocked in a delivered call but
  the last. A caller lends only at the delivery of its own call, blocks in
  that call until it ends, and is made ready only after the settlement has
  withdrawn the loans of its call; and a thread has at most one call.
- **The premises of `lend` and `release`.** These two rules of the
  composition, which `ledger::lend` and `ledger::release` rely on and do
  not check, hold:
  - the lender has lent its context to no other thread: a caller has lent
    nothing before the delivery of its call, since that delivery is its
    only loan, so the lender of every `lend` is the last thread of the
    chain of its context;
  - the loans downstream of a thread are withdrawn before the reap of its
    process: the destruction ends the call of its thread by the kill, which
    withdraws the chain of that call, and the call that its thread serves
    by the deletion of its reply capability in the teardown of its table,
    which withdraws the thread and its downstream, both before the reap.
- **No refused loan.** The other checks of `lend` do not fail at a
  delivery: the receiver serves no call, since `receive` refuses a thread
  that does (`ReplyPending`) and a waiting receiver serves none, so it has
  no source; it is not the caller (`SelfCall`), and it is not upstream of
  the caller in its chain (`Cycle`), so `OutstandingLoan` is never reached.
  The depth is checked at the delivery: a delivery that would lend at a
  depth beyond `MAX_LOAN_DEPTH` = 8 refuses a call that is delivered at
  once (`LoanDepth`), changing nothing, and ends a queued call with
  `LoanDepth` when a receive takes it.
- **A server that serves a call.** A server that holds the loan of a call
  that has not ended does not receive again: its `receive` is refused with
  `ReplyPending`, so no delivery to it would need a second loan. It ends
  the served call first, by its reply, or the call ends by another outcome;
  the next receive then takes the next call.
- **Withdrawal before the wake.** Every end of a delivered call, by any
  outcome, withdraws the context that the call lent, in the write set that
  settles it, before it writes the caller's results and makes the caller
  ready: `ledger::withdraw` of the receiver and, while a withdrawal gives
  `withdrawn`, of the receiver of the delivered call that the withdrawn
  thread waits for, at most `MAX_LOAN_DEPTH` withdrawals; and
  `scheduler::requeue` of the last thread withdrawn when it is ready or
  running, the only one that can be.
- **The chain that is withdrawn.** A thread gets its source only at the
  delivery of the call that it serves, loses it only by a withdrawal, and
  receives no other call until that call ends; its own call comes after
  that delivery. So a receiver whose withdrawal gives `withdrawn` has held
  the context of the call since its delivery and has lent it at the
  delivery of its own call, and so on down the chain: the threads
  withdrawn are the chain of the call, each one level deeper, at most
  eight. A receiver whose withdrawal gives `none` has lost the context to
  the end of a call upstream, which withdrew the chain with it; the calls
  that it and the threads after it made since then lent other contexts,
  which stay, and the settlement withdraws nothing more and requeues no
  thread.
- **Loans that stay.** The loans upstream of the receiver stay, and so do
  those that a thread further along the calls made after it lost the
  context: when, in
  a chain from A through B and C to D, the call of B to C ends, C and D
  return to their own records, and B keeps running on the context of A.
  When D, still serving the call of C, then calls E, its delivery lends D's
  own record to E; the later end of the call of C to D withdraws nothing,
  since D has no source, and E keeps the context of D while D waits for
  it.
- **No re-lending.** A thread that a withdrawal returned to its own record
  and that waits for the reply of its own call stays blocked, with no
  context lent to it, until that call ends; nothing lends it a context
  again.
- **Full return.** Each outcome of a delivered call withdraws in this way,
  in the write set that ends the call: the reply in that of `reply`;
  `Timeout` in the settlement of the expiry; `Cancelled` in the settlement
  of the kill, before the reap of the caller's process; `Revoked` in the
  settlement of the pending transition, while the caller is paused; and
  `PeerClosed` in that of the drain step or of the deletion of the reply
  capability. The owner's context returns whole, less what has been charged
  to it, and nothing is refunded. A queued call has lent nothing, and its
  end withdraws nothing.
- **No fallback.** A receiver whose borrowed context has no credit does not
  run on its own budget until the context is replenished or the loan is
  withdrawn
  ([lending](../../scheduling/budget-ledger/contract.md#lending)).
- **Write set.** The withdrawal of a chain writes at most 11 items, which
  the [budget-ledger](../../scheduling/budget-ledger/contract.md#check-and-execute)
  contract counts, within the write set of the settlement of the call
  ([Check and execute](#check-and-execute)).

## Settlement of a call

A settlement ends a live call, or a waiting receive, by an outcome other
than a delivery or a reply. Each settlement is one transaction, whose
write set holds the withdrawal of the chain of a delivered call, the end of
its wait and the caller's results. `settle(thread, outcome, now)` settles
the call or the receive of `thread` with `Timeout`, `Cancelled` or
`Revoked`, the last with the entry that `waits::revoked` names; it gives
`settled`, or `none` without a write when the thread has no live call and
does not wait in a receive.

- **Timeout.** A call or a receive whose deadline is not later than the
  time of the transition settles with `Timeout` before the operation of the
  transition, by the composer of the expiry of the
  [waits](../waits/contract.md#deadlines-and-sleep) component, which takes
  the waits whose deadlines have passed from `waits::first_deadline` in the
  order of the deadline table and calls `settle` for those of this page. A
  queued call leaves the queue and is never delivered; a delivered call
  raises the caller's generation, so the reply that the server sends later
  fails with `ReplyGone`. A timeout means that the caller stopped waiting:
  it does not undo what the server has received or done.
- **Cancellation.** The cancellation of a call is the forced kill of its
  caller: the lifecycle component, in the destruction of its process,
  calls `settle` with `Cancelled`, and the composition removes the thread
  instead of making it ready. The kill of a receiver ends its receive the
  same way. The kill of a server ends the call that it serves when the
  teardown of its table deletes the reply capability, with `PeerClosed`,
  and the calls queued on the endpoints that it is bound to by drains.
- **Revocation.** In the pending transition of a revocation, after the mark
  is written, the composer `dispatch` calls `settle` with `Revoked` for
  each blocked thread that waits in a call or a receive through an entry of
  the subtree: the capability of the call, the source of a queued call or
  the capability of the receive, which `waits::revoked` of the
  [waits](../waits/contract.md#revocation-and-release) component names in
  its scan. The thread is paused instead of made ready, and the entry is
  recorded with its pause; the step of the revocation that removes that
  entry makes it ready with `waits::unpause`, with the result `Revoked`.
- **Peer closure.** `PeerClosed` ends a call by a drain of its endpoint and
  a delivered call also by the deletion of its live reply capability
  ([Release and peer closure](#release-and-peer-closure)); it ends a
  receive by a drain.
- **A refused delivery.** A queued call whose delivery a receive refuses
  ends with the error of that check, `StaleReference` or `LoanDepth`, as
  its outcome.
- **Effects.** A settlement of a queued call takes it out of the queue of
  its endpoint; of a delivered call, it withdraws the chain, raises the
  caller's generation and clears the `serving` of the receiver; of a
  receive, it clears the receiver of the endpoint. Each ends the wait
  record with `waits::complete`, which takes the thread out of the deadline
  table, writes the results into its saved context except for `Cancelled`,
  and records the pause for `Revoked`; then, except for `Cancelled` and
  `Revoked`, the settlement calls `scheduler::enqueue` for the thread.
- **One result.** Only the first completion of a wait takes effect: a later
  settlement, reply, deletion of the reply capability or drain finds no live
  call or waiting receive and changes nothing of it.
- **Order.** When one transition brings several of these events to one
  call, the first in this order decides: timeout, cancellation,
  revocation, peer closure, and the reply or a refused delivery. The expiry
  settles before the operation of every transition, so a timeout comes
  first; a composer that brings more than one of the others to a call in
  one transition makes them in this order.

## Release and peer closure

No operation closes an endpoint: it is released when the last capability
of its current generation is deleted
([capability counts](../../objects-capabilities/capabilities/contract.md#capability-counts)),
or in the steps of the destruction of its owner, as the lifecycle component
destroys the objects of a process. A released endpoint does not resolve: a
capability of it fails its lookup with `StaleReference` until its holder
closes it, so no operation refuses a closed endpoint and there is no closed
state.

- **The last capability.** While a thread is blocked in a call or a
  receive on an endpoint, the entry of its capability to the endpoint is
  filled: the thread cannot close it while it waits; the pending transition
  of a revocation of it settles the wait first; the destruction of the
  thread's process ends the wait, by the kill, before the teardown of its
  table, a rule of the composition that the lifecycle component keeps; and
  a move of it by the call itself is refused. A waiter of a
  wait set on the endpoint is its bound thread and holds a capability to it
  in the same way. So the deletion of the last capability of an endpoint
  finds no queued call, no receiver, no call delivered through it that is
  live and no waiter: the release adds no part of this page to the write
  set of that deletion.
- **Drains.** When the owner of an endpoint is destroyed, its endpoint can
  still be the endpoint of live calls, through the capabilities of other
  processes. The lifecycle component, in the steps of the destruction,
  calls `drain_step(endpoint, now)` until it gives `drained`; then, in the
  transition of the release, `waits::drain` with the endpoint and the bound
  thread that `drained` gives, which completes that thread when it waits on
  its wait set with the endpoint registered
  ([release](../waits/contract.md#revocation-and-release)); and then it
  releases the slot. The owner is not alive from the start of its
  destruction, so the endpoint is not served and no call or receive joins
  it meanwhile.
- **A drain step.** `drain_step` resolves the endpoint and settles one wait
  on it with `PeerClosed`, the first of these: the receiver; else the first
  queued call; else the call that the bound thread serves when it is a call
  to this endpoint. It gives `more` after a settlement, and `drained`, with
  the reference of the bound thread, when none of them remains, writing
  nothing. Each step is one settlement within the bounds of
  [Check and execute](#check-and-execute); how many steps a step of the
  destruction makes is a rule of the lifecycle component.
- **The bound thread destroyed.** When the process of the bound thread of
  an endpoint is destroyed, the lifecycle component drains the endpoint in
  the same way, without releasing it: its calls end with `PeerClosed`, and
  a call made later ends at once with `PeerClosed`, since the endpoint is
  not served. The call that the thread serves ends when the teardown of its
  table deletes the reply capability, or by the drain, whichever comes
  first. Finding the endpoints that a thread is bound to is a rule of the
  lifecycle component.
- **The holder of a reply capability destroyed.** The teardown of the table
  of the server deletes its reply capabilities; for the live one,
  `reply_deleted` ends the call with `PeerClosed`. So the death of a peer
  and the release of an endpoint report the same outcome
  ([internal choices](../../../security.md#internal-choices)).
- **The binding.** The binding holds back no reclamation: the thread of a
  process is reaped whatever endpoints it is bound to, and the binding then
  goes stale.

## Errors

| Error | Rule broken | Entries | Place in the order of errors |
| --- | --- | --- | --- |
| `InvalidRights` of the capabilities component | A rights mask of a transfer that is 0, or that has a bit above bit 4 | `call` | The form of the register arguments |
| `SelfTransfer` | A transfer by move whose source handle is the handle of the call | `call` | The form of the register arguments |
| `InvalidSlot` of the capabilities component | A reply slot or a transfer slot not below `capability_slots` | `receive` | The form of the register arguments |
| `SameSlot` | A reply slot and a transfer slot that are the same slot | `receive` | The form of the register arguments |
| `InvalidHandle`, `NoCapability`, `StaleHandle`, `WrongType` of the capabilities component | A handle that does not name a usable capability of the kind in the caller's table | `call`, `receive`, `reply` | Handle resolution: the range, the empty slot, the generation, the type |
| `WrongPool` of the objects component | A reference of another pool than its kind's | `init_endpoint`, `settle`, `drain_step`, `check_receiver`, `has_call` | Handle resolution: the type |
| `StaleReference` of the objects component | A reference that is not live: the endpoint or the source of a capability, the caller of a reply capability, or a reference that a composer passes | Every entry but `reply_deleted`, which gives `none` for a caller that has been reaped; a delivery by a receive | Handle resolution: the liveness of the object |
| `PermissionDenied` of the capabilities component | A capability without SEND for `call`, without RECEIVE for `receive`, without REPLY for `reply`, or a source without GRANT or a requested right | `call`, `receive`, `reply` | Rights |
| `RevocationPending`, `TransferPending` of the capabilities component | A capability of the subtree of a pending revocation or its target, or the source of a pending move | `call`, `receive`, `reply` | Object state |
| `NotReceiver` | A receive, or the registration of the endpoint in a wait set, by a thread other than the bound thread | `receive`, `check_receiver` | Object state |
| `ReplyPending` | A receive by a thread that serves a call | `receive` | Object state |
| `SlotOccupied`, `GenerationExhausted` of the capabilities component | A reply slot or a transfer slot that holds a capability or has retired | `receive` | Object state |
| `ReplyExhausted` | A call by a thread whose reply record has the generation $2^{64} - 1$ | `call` | Object state |
| `SelfCall` | A call to an endpoint whose bound thread is the caller | `call` | Object state |
| `Cycle` | A call whose edge would close a cycle of the call graph | `call` | Object state |
| `GenerationExhausted` of the waits component | A call or a receive that would block while the wait generation of its thread is $2^{64} - 1$, the check of `waits::begin`; a receive would block when no queued call passes the checks of its delivery | `call`, `receive` | Object state |
| `ReplyGone` | A reply with a capability whose call has ended | `reply` | Object state |
| `DepthExceeded` of the capabilities component | A transferred capability whose new path would be longer than `MAX_DEPTH` | `call` | Shared capacity |
| `LoanDepth` of the budget-ledger component | A delivery whose loan would be deeper than `MAX_LOAN_DEPTH` | `call`; a delivery by a receive | Shared capacity |

- **Order.** Each entry checks in the order that its rule section states
  and returns the first error. The places of the last column are those of
  the order of errors of the
  [security model](../../../security.md#internal-choices), after the
  operation number and version and the reserved registers, which the
  dispatch component checks as the ABI inventory states. `SelfCall` and
  `Cycle` depend on the calls of other threads; [Determinism](#determinism)
  states their sources.
- **Outcomes are not errors.** `Timeout`, `Revoked` and `PeerClosed` are
  outcomes of an accepted call or receive, written into its results, and so
  is the error of a refused delivery, which ends a queued call; `Cancelled`
  is an outcome as well, which writes no result, since the killed thread
  never runs again. They are not refusals, and the operation that they end
  has had its effect, the call queued or delivered and the receive waiting.
  An operation that ends at once with `Timeout` or `PeerClosed` changes
  nothing.
- **No change on failure.** No error changes state: an entry of this page
  that returns an error leaves every field of the kernel state as it was,
  the copies in the write set included, and writes no counter; a composing
  operation that meets an error discards its buffer, so the kernel state
  after any failed operation equals the state before it. There is no
  exception. The result registers of a failed system call follow the
  [observable outputs](../../../security.md#observable-outputs) of the
  security model.
- **Totality.** `WrongPool` and `StaleReference` of `init_endpoint`,
  `settle`, `drain_step`, `check_receiver` and `has_call` answer a
  reference that no composer passes, since each composer resolves its
  references in its own checks; the answer changes nothing. `settle` and
  `reply_deleted` give `none`, and `drain_step` `drained`, for a thread or
  an endpoint without a wait of this page.
- **Names.** The names are those of this contract; the numeric values of
  the errors and of the statuses of the outcomes belong to the ABI
  inventory. `SelfCall` and `Cycle` reach EL0 as one status, that of a call
  dependency, and `NotReceiver` with the status of a missing right.

The prototype's IPC had fourteen errors, and its ABI five statuses of its
own. Here:

| Prototype error or status | Here |
| --- | --- |
| `InvalidConfiguration` | Not applicable: there is no registry of calls and receives, whose capacity could be 0; the queues of endpoints hold threads of the thread pool |
| `Object(_)` | Not kept as a wrapper: the errors of the objects and capabilities components that this page meets are returned as they are |
| `InvalidState` | Replaced: a receive by a thread that serves a call is `ReplyPending`; a call or a receive by a thread that already waits does not arise, since only a running thread makes one; a call on an endpoint that the prototype closed, or whose bound thread is dead, ends with `PeerClosed`, since the endpoint is not served, and a released endpoint fails its lookup with `StaleReference`; a cancellation of an ended call is a kill that finds no wait |
| `InvalidDeadline` | Not applicable: every 64-bit deadline is valid, and 0 is none |
| `ClockReversed` | Not applicable: the time does not decrease within a boot, a premise that no entry checks |
| `Capacity` | Not applicable: there is no registry; a call or a receive uses the records embedded in its thread and the queue of its endpoint, which have no capacity of their own |
| `TokenExhausted` | Replaced by `ReplyExhausted`: the generation of a thread's reply record at its limit; there is no global token |
| `SelfCall` | Kept, for a call to an endpoint whose bound thread is the caller |
| `Cycle` | Kept, for a call whose edge would close a cycle along queued and delivered calls |
| `PermissionDenied` | Split: a missing right is `PermissionDenied` of the capabilities component, in the lookup; a receive by a thread other than the bound thread is `NotReceiver`; a reply or a loan by a thread other than the server does not arise, since the reply capability stays in the table of the server and a loan is a part of a delivery |
| `InvalidReply` | Renamed `ReplyGone`, for a reply with a capability whose call has ended; a reply handle that names no reply capability fails its lookup |
| `NotFound` | Not applicable: results are written at the end of a wait and never taken |
| `NotCompleted` | Not applicable, as `NotFound` |
| `TimedOut` | The outcome `Timeout`, also for a deadline that is due at the call or the receive |
| `WRONG_TYPE`, the status 10 | `WrongType` of the capabilities component, in the lookup |
| `TIMED_OUT`, the status 11 | The status of the outcome `Timeout` |
| `CANCELLED`, the status 12 | Not applicable: the cancellation of a call is the kill of its caller, which observes no result |
| `PEER_CLOSED`, the status 13 | The status of the outcome `PeerClosed` |
| `DEADLOCK`, the status 14 | Kept as the status of `SelfCall` and `Cycle`, of a call dependency; its value belongs to the ABI inventory |

## Check and execute

Every write entry of this page makes all its checks, the lookups of its
handles and the walk of the call graph among them, before its first write,
and then changes only the copies in the write set of its caller
([write sets](../../objects-capabilities/objects/contract.md#write-set-transactions)).
The items of this page are thread slots, which hold the reply records, and
endpoint slots, each keyed by its pool and slot; the entries that it
composes add theirs. The write phase of every entry allows only
`WriteSetFull` of `stage`, which the write sets below never reach, and the
fault-injection points of test builds (`InjectedFault`), each of which
discards the buffer and leaves the state from before the entry. A
settlement that a composer makes before the operation of a transition or
between its parts, by `settle`, and the end of a queued call by a delivery
that a receive refuses, takes no fault-injection point, so no part of a
transition fails after an earlier part has committed.

| Entry | Checks before the first write | Write set | Items |
| --- | --- | --- | ---: |
| `init_endpoint` | The reference of the thread | The endpoint slot, with the items of `ObjectTable::occupy` | 1 |
| `call`, ended at once | Those of [Calls and receives](#calls-and-receives) | None | 0 |
| `call`, queued | Those of [Calls and receives](#calls-and-receives) | The slots of the caller, of the endpoint and of the former last caller of the queue; the items of `waits::begin` for the deadline, at most 3; and for `scheduler::block`, the scheduler record, with the slot of the owner of the context and the class ledger of `ledger::charge`: 9. When the bound thread waits on its wait set with the endpoint registered, also `waits::source_ready`, at most 9, and its `scheduler::enqueue`, at most 2, as the [waits](../waits/contract.md#check-and-execute) contract counts them | 20 |
| `call`, delivered at once | Those of [Calls and receives](#calls-and-receives) and of the delivery | The slots of the caller, of the receiver and of the endpoint; the items of the waits component for the end of the receiver's deadline and the start of the caller's, at most 5; `install`: the entry and the process slot of the receiver; `reserve` and `commit`: at most 11, 5 for a copy; `enqueue` of the receiver: the last thread of its queue and the scheduler record; `block` of the caller: the slot of the owner of the context and the class ledger | 25 |
| `receive`, blocked | Those of [Calls and receives](#calls-and-receives) | The slots of the receiver and of the endpoint; the items of the waits component for the deadline, at most 3; `block`: the scheduler record, the slot of the owner of the context and the class ledger | 8 |
| `receive`, delivered at once | Those of [Calls and receives](#calls-and-receives) and of the delivery | The slots of the receiver, of the caller, of the endpoint and of the next caller of the queue; `install`: 2; `reserve` and `commit`: at most 11; `requeue` of the receiver: the scheduler record and the class ledger | 19 |
| `reply` | The lookup and the generation | The slots of the replier and of the caller; the items of the waits component for the caller's deadline, at most 3; `withdraw` of the replier and its `requeue`: the scheduler record, the slot of the owner of the context and the class ledger; `Tables::close` of the reply capability: at most 7 beside the caller's slot; `enqueue` of the caller: the last thread of its queue | 16 |
| `settle`, a queued call | The reference and the state of the wait | The slots of the caller and of the endpoint and of the callers before and after it in the queue; the items of the waits component for the deadline, at most 3; `enqueue`: at most 2 | 9 |
| `settle`, a delivered call | The reference and the state of the wait | The slot of the caller; the withdrawal of the chain, at most 11, the receiver's slot among them; the items of the waits component for the deadline, at most 3; `enqueue`: at most 2 | 17 |
| `settle`, a receive | The reference and the state of the wait | The slots of the receiver and of the endpoint; the items of the waits component for the deadline, at most 3; `enqueue`: at most 2 | 7 |
| `reply_deleted` | The reference, the generation and the state of the call | None, or the write set of `settle` of a delivered call | 17 |
| `drain_step` | The reference of the endpoint and the wait that it settles | The write set of one settlement | 17 |
| `check_receiver`, `has_call` | The reference | None: they write nothing | 0 |

- **Settlements.** A settlement writes at most 17 items: for `Cancelled` and
  `Revoked` at most 15, without `enqueue`. That is within the 27 items that
  the [capabilities](../../objects-capabilities/capabilities/contract.md#check-and-execute)
  contract leaves beside its largest write set, so the pending transition
  of a revocation settles each wait through its subtree in a transaction of
  its own, a `close` of a live reply capability writes at most 27 items,
  and a step of the teardown of a table, which deletes at most one live
  reply capability, at most 54.
- **The last capability.** The release of an endpoint at the deletion of
  its last capability adds no item of this page
  ([Release and peer closure](#release-and-peer-closure)).
- **Several transactions in a transition.** The expiry settlements, the
  settlements of a pending revocation, the end of each queued call whose
  delivery a receive refuses, and the operation of the transition are
  transactions of their own. Each rolls back on its own to the state before
  it: an operation that fails leaves the settlements before it, which are
  the results of time and of revocation, not of the operation. The ends of
  the refused deliveries are parts of a receive that has made all its
  checks, also whether it can block, before the first of them, so that
  receive does not fail after them.
- **Reads that decide the effect.** The walk of the call graph, the state
  of the queue and of the receiver, and the generation of a reply record
  decide what an entry does, not whether it fails after its checks, and
  cannot fail.
- **Within W.** Every write set of this page, with those of the entries that
  it composes, is within $W$ = 64 of the objects contract.

## Work bounds

- `init_endpoint` resolves one reference and writes one item.
- `call` makes two lookups, each of at most 17 entries and one slot of an
  object table; the walk of the call graph, at most the thread capacity
  less one steps of two reads each; the checks of a delivery, those of
  `Tables::reserve` and of `ledger::lend`; and a fixed number of writes,
  with `waits::begin`, whose insertion into the deadline table the
  [waits](../waits/contract.md#work-bounds) contract bounds by the thread
  capacity. The walk has no preemption point: the transition that makes it
  takes time in proportion to the thread capacity, as the expiry of
  deadlines that expire together does.
- `receive` makes one lookup and the checks of two slots; at the limit of
  its wait generation, the checks of the deliveries of at most the queued
  calls of its endpoint, without a write; and it takes at most those calls,
  at most the thread capacity less one: each call whose delivery its checks
  refuse ends in a settlement of its own, a fixed number of steps, before
  the receive delivers a call or blocks. A receive that blocks calls
  `waits::begin`, whose insertion into the deadline table walks at most the
  thread capacity of waits.
- `reply` makes one lookup and one check of a generation, one withdrawal and
  a fixed number of writes.
- `settle`, `reply_deleted` and `drain_step` make one settlement each: at
  most `MAX_LOAN_DEPTH` = 8 withdrawals along the chain of a delivered
  call, and a fixed number of writes.
- `check_receiver` and `has_call` read one slot.
- The component has no long operation: every entry runs to its end, and no
  progress is stored between two calls. The drain of an endpoint is part of
  the destruction of a process, the long operation of the lifecycle
  component, whose preemption points are between its steps; its progress is
  the queue and the receiver of the endpoint, which each step shortens, and
  at most the thread capacity steps drain one endpoint.
- The constants are `MESSAGE_WORDS` = 2; `MAX_LOAN_DEPTH` = 8 of the
  budget-ledger component; `MAX_DEPTH` = 16 of the capabilities component;
  $W$ = 64 of the objects component; and the thread capacity of the
  capacity record.

## Determinism

- **Requests.** Requests that contend for an endpoint or a reply record
  take effect in the order in which they enter the kernel.
- **Queue.** The calls queued on an endpoint are delivered in the order in
  which they were made; a receive takes the first.
- **Receivers.** An endpoint has at most one receiver, its bound thread, and
  at most one waiter of a wait set, the same thread, so no choice among
  receivers arises; a call that finds the receiver waiting is delivered to
  it at once.
- **Expiry first.** A call or a receive whose deadline is not later than
  the time of the transition settles with `Timeout` before the operation of
  the transition, as the waits component orders the expiries; one whose
  deadline is not later than `now` when it is made ends at once with
  `Timeout`, delivers nothing, takes no queued call and reserves nothing.
  Deadlines that expire together all settle, in the loop of the waits
  component.
- **Outcomes.** When one transition brings several events to one call, the
  first of timeout, cancellation, revocation, peer closure and the reply or
  a refused delivery decides, as [Settlement of a call](#settlement-of-a-call)
  states; in different transitions the first transition decides.
- **Wake-ups.** Each write set of this page makes at most one thread
  ready. The calls whose delivery a receive refuses end in the order of the
  queue, each in its own write set, before that of the receive; and the
  composer orders the threads that one transition makes ready as the
  [scheduler](../../scheduling/scheduler/contract.md#determinism) states:
  those woken by timeouts first, then those woken by the event of the
  operation.
- **Loans.** A loan is made in the write set of its delivery and withdrawn,
  with every loan of its context downstream of it, in the write set of the
  end of its call, before the caller is woken; it settles as a whole within
  one transition.
- **Badges and handles.** The badge of a delivery is that of the caller's
  capability; the handles of the reply capability and of a transferred
  capability name the slots that the receiver named, with their
  generations.
- **Sources of the call dependencies.** `SelfCall` depends only on the
  binding of the endpoint of the call. `Cycle` depends on the wait records
  of the threads of the walk, whether each is blocked in a call and on
  which endpoint, and on the bindings of those endpoints; these threads may
  belong to processes whose state the caller has no right to observe. It is
  not one of the two global flows that the
  [information-flow boundary](../../../security.md#information-flow-boundary)
  declares, and the kernel claims no confidentiality, so this page gives its
  source, as the specification gives the source of every output.
- **Time.** The time of each transition, which decides which deadlines have
  expired, is the time that [ND-01](../../../security.md#nd-01) of the
  register of
  [permitted nondeterminism](../../../security.md#permitted-nondeterminism)
  allows; for each value of it, the rules of this page fix the result.
- **Interrupts.** An interrupt of a device reaches this component only
  through the thread that its notification makes ready, whose transition
  [ND-02](../../../security.md#nd-02) allows.
- **Several CPUs.** With more than one CPU, the order in which CPUs take the
  tokens of the same endpoint or reply record is the multicore interleaving
  of [ND-03](../../../security.md#nd-03); for each such order, the rules of
  this page fix the result. Before it writes a result, the settlement of a
  wait checks that no revocation of an entry through which the wait passes
  has become pending, so that a settlement that another CPU interleaves
  with the pending transition of a revocation reports `Revoked`; with one
  CPU the check always passes.

The component leaves no other choice open.

## State fields

| Field | Class | Lock or owner | Linearization point | Publication |
| --- | --- | --- | --- | --- |
| The `bound` of each endpoint, in its slot | Shared, read-only after the creation of the endpoint | The token of the endpoint, which the creation holds in the write set that occupies its slot; with one CPU, the executing CPU | The write-back of that write set | Under the token, by the release of the lock that provides it once CPUs share it |
| The queue, `first` and `last`, and the `receiver` of each endpoint | Shared | The token of the endpoint, which every call, receive, settlement and drain step on it holds | The release of the token after the write-back of the write set that changes them | Under the token |
| The `generation`, `call`, `badge`, `words`, `transfer` and `slots` of the reply record of each thread, in its slot | Per-thread | The CPU that runs the thread; while the thread waits in a call or a receive, the token of the endpoint of its wait, which every access to the record holds | The write-back of the write set that changes them, under the token of their owner | At the handover from the running thread to its wait, by the release of the token of the endpoint after the write-back that blocks it, and back by the release of that token after the write-back that ends the wait |
| The `serving` of the reply record of each thread | Shared | The token of the thread slot of the server, which the delivery that sets it and the end of the call that clears it hold, with the token of the endpoint of the call | The release of the tokens after the write-back | Under the token |

The wait records of the threads, with their queue links, deadlines and
pauses, the deadline table and the registrations of wait sets are fields
of the [waits](../waits/contract.md#state-fields) component; the sources
and effective classes of the budget records, of the
[budget-ledger](../../scheduling/budget-ledger/contract.md#state-fields)
component; the scheduling states and run queues, of the
[scheduler](../../scheduling/scheduler/contract.md#state-fields); the
entries of the reply capabilities and the counts of endpoints, of the
[capabilities](../../objects-capabilities/capabilities/contract.md#state-fields)
component; and the slots of the endpoint and thread pools, of the
[objects](../../objects-capabilities/objects/contract.md#state-fields)
component. Endpoint queues are shared, as the
[multicore](../../../architecture.md#multicore-by-design) rules of the
kernel classify them; no lock order is stated here.

## Testing obligations

- The host tests of the module `ipc` (planned) replay every vector of
  [Legacy test vectors](#legacy-test-vectors) whose entry is on this page,
  with its expected output, and the parts of the vectors of the
  [waits contract](../waits/contract.md#legacy-test-vectors) whose entry is
  on this page, and write their results for the comparison with the
  specification
  ([host results](../../../formal-verification.md#host-results)). The
  forced kill, the destruction of a process and the steps of a revocation
  that a vector names are driven through `settle`, `reply_deleted` and
  `drain_step` in the order that its row gives, as their composers would
  call them.
- Calls and receives: a call that finds the receiver waiting, a receive
  that finds a call, and a receive that blocks, with deadlines 0, $2^{32}$
  and $2^{64} - 1$; a deadline equal to the time of the call and of the
  receive; the queue in the order of the calls after settlements in its
  middle; `NotReceiver` for a receive and for `check_receiver` by a thread
  of another process that holds RECEIVE; a call and a receive on an
  endpoint whose bound thread's process, or whose owner, is not alive; and
  a call and a receive at the wait generation $2^{64} - 1$, refused with
  `GenerationExhausted` when they would block and ending at once with
  `Timeout` when their deadline has passed; and at that generation, a
  receive that finds a call whose delivery passes, which delivers it, and
  one whose queued calls all fail the checks of their deliveries, which is
  refused with `GenerationExhausted` and ends none of them.
- Calls to oneself and cycles: `SelfCall`; for every length from 2 to the
  thread capacity of the fixture, a cycle closed through queued calls,
  through delivered calls and through both, refused with `Cycle`, and the
  same chains without the last edge accepted; an edge of a call that has
  timed out or been replied to is not part of the walk; a walk of the
  greatest length makes at most two reads per step; and a property test
  that drives calls, receives, replies and settlements of several threads
  and checks after every write-back, against an independent model of the
  call graph, that each thread has at most one edge and that the graph has
  no cycle.
- Replies: a second reply with the same handle; a reply after each of
  `Timeout`, `Cancelled`, `Revoked` and `PeerClosed`, which is `ReplyGone`;
  the `close` of a live and of an old reply capability; the teardown of a
  table that holds both; a reply capability of a caller that has been
  reaped, which is `StaleReference`; and `ReplyExhausted` for a reply
  record that a test sets to the generation $2^{64} - 1$, after a reply at
  $2^{64} - 2$.
- Badges: the badges 0, 1 and $2^{64} - 1$; the counterexample of
  [Badges and sender identity](#badges-and-sender-identity).
- Transfer: copy and move, delivered at once and by a receive; a source
  whose object is released while the call is queued, which ends the call
  with `StaleReference` while the receive takes the next call; a move of
  the capability of the call, which is `SelfTransfer`; the revocation of
  the source of a queued call; a timeout after the delivery, which leaves
  the received capability; and a property check that no reserved entry
  exists after any write-back of this page.
- Lending: chains of every depth from 1 to 8 and a ninth delivery, refused
  at a call and ending a queued call at a receive; the end of a call in the
  middle of a chain, which leaves the loans upstream; each outcome, after
  whose write-back the caller is ready and no thread holds the context
  that the call lent; the chain from A to E of
  [Budget lending](#budget-lending), after which E keeps the context of D; a
  chain whose last thread, after the end of a call upstream, lends its own
  record along eight more deliveries, whose ends each withdraw at most eight
  loans; and `ReplyPending` for a receive by a thread that serves a call.
- Outcomes: for each pair of a timeout and another event in one
  transition, the timeout; and the order of
  [Settlement of a call](#settlement-of-a-call) for the events that a
  composer brings together.
- Release: the drain of an endpoint with queued calls, a receiver or a
  served call, by the destruction of its owner and of the process of its
  bound thread, with calls made between the steps, which end at once with
  `PeerClosed`; and a property check that the deletion of the last
  capability of an endpoint finds no thread waiting on it.
- For each error of [Errors](#errors), a call that gives it leaves every
  field of the kernel state as before, compared field by field.
- Write sets: the largest write set of each entry is reached and stays
  within the item counts of [Check and execute](#check-and-execute); for
  each fault-injection point, an operation that fails there leaves the
  state as before, and no settlement meets one.
- QEMU tests: two processes call, receive and reply from EL0 with deadlines
  and transfers, once the operations of the ABI inventory exist.
- Time: every test passes its times; no test reads a counter, depends on the
  speed of the host or uses a fixed instruction count
  ([testing](../../../conventions/testing.md#determinism-and-time)).
- The tests take their expected values from this page, from the vectors and
  from independent models, never from an earlier run of the code under test
  ([testing](../../../conventions/testing.md#independent-evidence)).

## Open obligations

The module `ipc` has no `unsafe` code, no assembly and no MMIO, and its
entries are to be covered by its targets. An entry that a later contract
adds to this component beyond the entries of this page is an open
obligation of the contract that adds it, carried by the proof of object
lifetimes, waits and sequential composition, by release 0.2. The code of
this page adds no obligation, so the table has no row.

| Obligation | Kind | Verified state | Carrier | Stage |
| --- | --- | --- | --- | --- |

## Legacy test vectors

The vectors are host tests of the prototype tree at
`prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`, 48 in all. Their
expected outputs are those that the test bodies assert, written in the
rules of this page. The vectors are not yet in a file of the repository, so
the section holds no `vectors` block.

| File | Vectors |
| --- | ---: |
| `src/ipc/tests/admission.rs` | 7 |
| `src/ipc/tests/closure.rs` | 4 |
| `src/ipc/tests/lifetime.rs` | 6 |
| `src/ipc/tests/ordering.rs` | 7 |
| `src/abi/ipc/tests/authority.rs` | 7 |
| `src/abi/ipc/tests/lifecycle.rs` | 9 |
| `src/abi/ipc/tests/validation.rs` | 8 |

- `src/ipc` holds 24 tests and `src/abi/ipc` 24, all in the files above;
  `src/ipc/tests.rs` and `src/abi/ipc/tests.rs` hold only fixtures and
  module declarations, and the other files of the two directories no test.
- The id of a vector is the path of its file below `src/`, without every
  path component `tests` and the suffix `.rs`, with `/` and `_` written as
  `-`, followed by the position of its test among all the tests of that
  file, counted from 1.

A vector of this page is one test function. The vector file is to hold one
line for each case of it through an entry of this page, with the id
`<vector>.<n>`, `n` counting those cases from 1 in the order of the test; a
case that its row marks not applicable has no line, and a vector whose
Entry column names no entry of this page has none.

**Notation.** Times are decimal ticks, and a deadline of 0 is none. The
events of a row happen in the transitions at the times that it gives, each
after the expiries of that time. A process and its thread have one name.
"A calls E at t" is `call` by A through its send capability to E, with the
badge, the words and the deadline that the row gives, and otherwise the
badge 0, the words `[0, 0]`, no deadline and no transfer; "S receives at t"
is `receive` by S from E, or from the endpoint that the row names, with the
deadline that the row gives and, unless the row gives others, slot 1 of its
own table for the reply capability and slot 2 for a transferred capability.
"S replies w with r at t" is `reply` with the handle r. A handle is written
`<slot>@<generation>`, the value 65,536 times the generation plus the slot.
The output of a call is `reply [w0, w1]`, an outcome, `queued` or
`delivered` while it blocks, or `err=<error>` for a refused call; that of a
receive is `ok reply=<handle> badge=<badge> words=[w0, w1]
transfer=<handle>`, an outcome, `blocked`, or `err=<error>`; that of a reply
is `ok` or `err=<error>`. "The kill of X at t" is the forced kill of X,
whose destruction ends the wait of X's thread with `settle` and
`Cancelled`; "the destruction of X" is the kill and the later steps,
among them the teardown of X's table and the drains of the endpoints that X
owns or that X's thread is bound to. "A drain of E at t" is `drain_step` of
E until it gives `drained`, as such a destruction makes it. "Changes
nothing" means that every field of the kernel state is as before.

**Fixtures.**

- `src/ipc/tests/`: the processes A, B, S, D and O, each with its thread,
  beside the root. O creates the endpoint E, which it owns, with the thread
  of S bound as its receive thread, where the prototype's endpoint held its
  service thread. A, B and D each hold a send capability to E in slot 0,
  `0@1`, and S a capability to E with RECEIVE in slot 0; a call whose row
  gives a badge uses a send capability with that badge, which a derivation
  minted. A row that adds an endpoint names its bound thread, and O creates
  it in the same way; its bound thread holds a capability to it with
  RECEIVE in slot 3, and each caller that the row names a send capability
  to it in slot 4. The prototype's registry of
  eight calls and eight receives has no counterpart, and its check at the
  end of a test, of no record and of the counts of references, is here that
  no thread waits on an endpoint.
- `src/abi/ipc/tests/`: the processes C, S, N and X, each with its thread,
  with tables of 12 slots, 8 for X. S creates the endpoint E, which it owns,
  with its own thread bound. C holds in slot 0, `0@1`, a send capability to
  E with SEND, GRANT and REVOKE and the badge B = 0x8877665544332211, which
  a derivation minted; S holds in slot 0 a capability to E with RECEIVE.
  The words W are [18446744073709551615, 9223372036854775809].
  A process has one thread, so the prototype's second thread of the
  process of S is the thread of N, another process. "C's call is
  delivered" is C's call at 10 with the deadline that the row gives and S's
  receive at 11, which gives `ok reply=1@1 badge=B words=W transfer=0`,
  the handle of slot 1 at its generation.

**Behaviour changes.** These rules differ from the prototype:

- A handle names a slot of the caller's own table: the prototype's tokens
  of calls and replies from one counter, their order and their exhaustion,
  are the handles of reply capabilities in the table of the server and the
  generation of each thread's reply record.
- A result is written into the saved context of its thread at the end of
  its wait: the prototype's completed records, which a thread took or
  abandoned (`NotCompleted`, `NotFound`) and which kept their capacity and
  references until then, do not apply.
- There is no registry of calls and receives: its capacities (`Capacity`,
  `NO_CAPACITY`) and counts of records do not apply.
- No operation closes an endpoint: the prototype's closure is the release
  of the endpoint, with its drain when its owner or the process of its
  bound thread is destroyed, and its closed state does not exist.
- References carry no rights and hold back no reclamation: the prototype's
  references of a call to its endpoint and threads and of an endpoint to
  its service thread, its refused reaping (`ReferencesOutstanding`) and its
  handles with OBSERVE alone do not apply; the binding of an endpoint goes
  stale lazily.
- The cancellation of a call is the forced kill of its caller, which
  observes no result: the prototype's cancellation by a trusted controller
  and its status `CANCELLED` do not apply, and where a vector
  asserts `Cancelled`, its row checks the order of the outcomes and the
  fixed error of a later reply.
- A call that waits through a capability of a subtree whose revocation
  becomes pending ends with `Revoked`, where the prototype kept admitted
  calls.
- Every transition settles its due deadlines first, where the prototype
  settled the deadlines of other waits at its next poll.
- The time does not decrease within a boot: the prototype's refusals of an
  earlier time (`ClockReversed`) do not apply.
- The caller of an operation is the thread that runs: the prototype's
  checks of a caller that was active elsewhere, waiting, dead or reaped do
  not apply.
- The version, the operation number, the reserved registers and the
  numbers of operations and statuses are those of the dispatch component
  and the ABI inventory.
- The binding of an endpoint to its receive thread and the refusal of a
  call to oneself and of a cycle of calls are kept from the prototype, with
  queued and delivered calls as the edges.

### `src/ipc/tests/admission.rs`

`src/ipc/tests/admission.rs`, 7 vectors, with the fixture of
`src/ipc/tests/`.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `ipc-admission-1` | 4 | `waiting_receiver_gets_copied_badge_and_reserved_reply_authority` | S receives at 1: `blocked`. A calls with the badge 0xabc and the words [18446744073709551615, 7] at 2: `delivered`, and S is made ready with `ok reply=1@1 badge=0xabc words=[18446744073709551615, 7] transfer=0`. S replies [11, 12] with `1@1` at 3: `ok`, and A has `reply [11, 12]`. No thread waits on E. The prototype's counts of references, 2 of E, 1 of A and 2 of S, do not apply | `receive`, `call`, `reply` |
| `ipc-admission-2` | 43 | `queued_calls_are_fifo_across_record_slot_reuse` | A calls with the badge 10 and the words [1, 2] at 1, and B with 20 and [3, 4] at 2: both `queued`. S receives at 3: `ok reply=1@1 badge=10 words=[1, 2] transfer=0`; it replies [5, 6] at 4, and A has `reply [5, 6]`. A calls with 30 and [7, 8] at 5: `queued`, behind B. S receives at 6: `ok reply=1@2 badge=20 words=[3, 4] transfer=0`; it replies [9, 10] at 7, and B has `reply [9, 10]`. S receives at 8: `ok reply=1@3 badge=30 words=[7, 8] transfer=0`; it replies [11, 12] at 9, and A has `reply [11, 12]`. The prototype's tokens, which increased, are the handles of the reply slot at its successive generations | `call`, `receive`, `reply` |
| `ipc-admission-3` | 72 | `saturated_call_table_preserves_receive_capacity_and_existing_requests` | A calls with the badge 1 and the words [1, 2] at 1, and B with 2 and [3, 4] at 2: both `queued`. D calls with 3 and [5, 6] at 3: `queued`, behind them, where the prototype's table of two calls refused it (`Capacity`): a queue has no capacity of its own. S receives at 3: badge 1 and words [1, 2]. The kill of A at 4, in place of the prototype's abandonment of its call, ends that call with `Cancelled`, and S serves no call; S closes the old reply capability `1@1` and receives at 4: badge 2 and words [3, 4]. D's call stays `queued`. The prototype's counts of references do not apply | `call`, `receive`, `settle` |
| `ipc-admission-4` | 112 | `native_authority_owner_and_ready_validation_are_fail_atomic` | A call of A at 1 through a capability to E without SEND, in place of the prototype's handle with OBSERVE alone, is `err=PermissionDenied`. A receive of A at 1 through a capability to E with RECEIVE, which the row gives A in slot 3, is `err=NotReceiver`. A call of S at 1 through a send capability to E, which the row gives S in slot 3, is `err=SelfCall`. Each changes nothing. The prototype's call of a thread that was already waiting (`InvalidState`) does not apply: a thread that waits does not run, so it makes no call | `call`, `receive` |
| `ipc-admission-5` | 142 | `three_thread_wait_cycle_is_rejected_before_admission` | O creates the endpoints EB and EA, with the threads of B and of A bound. A calls EB at 1: `queued`, since B does not receive; B calls E at 2: `queued`. S calls EA at 3: `err=Cycle`, along the edges from A, the bound thread of EA, to B and from B to S, and the two queues and every record stay as they were. The prototype's abandonment of the two calls at the end is not a case here | `call` |
| `ipc-admission-6` | 163 | `final_token_is_valid_then_exhaustion_never_reuses_authority` | The prototype's registry without a record (`InvalidConfiguration`) does not apply, and there is no global token. With A's reply record at the generation $2^{64} - 2$, which the test sets: A calls at 1, and S receives at 1 with a reply capability whose badge is $2^{64} - 2$; S replies at 2, and A's generation becomes $2^{64} - 1$. A calls at 3: `err=ReplyExhausted`, which changes nothing; B calls at 3: `queued`, since the generation is A's own | `call`, `receive`, `reply` |
| `ipc-admission-7` | 188 | `foreign_pool_receipts_cannot_alias_local_endpoint_or_thread` | A call cannot name an object of another object table: its handles name slots of the caller's own table, whose references are of this table. The entries that take references refuse one of another pool: `init_endpoint` with a thread of a table whose pools have other numbers is `err=WrongPool`, and so is `settle` of such a thread, and both change nothing | `init_endpoint`, `settle` |

### `src/ipc/tests/closure.rs`

`src/ipc/tests/closure.rs`, 4 vectors, with the fixture of
`src/ipc/tests/`. The prototype's closure of E is the drain of E at the
destruction of its owner O here.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `ipc-closure-1` | 4 | `closure_timestamp_orders_queued_and_delivered_calls_against_their_deadlines` | For a queued call and for a delivered one, and for the drain of E at 9, 10 and 11 in turn: A calls with the badge 1, the words [1, 2] and the deadline 10 at 1, and in the second case S receives at 2. The drain at 9 ends A's call with `PeerClosed`; at 10 and at 11 the expiry ends it first with `Timeout`, and the drain finds no call. A later expiry at 20 changes neither result, and in the second case S's reply [3, 4] with `1@1` at 20 is `err=ReplyGone`. The prototype's closed state of E does not apply: E is released after its drain | `drain_step`, `settle`, `reply` |
| `ipc-closure-2` | 37 | `closure_completes_receiver_immediately_without_touching_other_endpoints` | The root, not O, creates the endpoint ED, which it owns, with the thread of D bound and the capabilities of an added endpoint, so that the destruction of O does not drain it. S receives with the deadline 10 at 1: `blocked`; A calls ED with the badge 2, the words [3, 4] and the deadline 12 at 2: `queued`, since D does not receive. The drain of E at 9 ends S's receive with `PeerClosed`, and S is made ready; A's call stays `queued`, and ED is untouched. The expiry at 10 does not change S's result, and A's call stays `queued`. The prototype's abandonment of A's call at 10 is not a case here | `receive`, `call`, `drain_step` |
| `ipc-closure-3` | 62 | `invalid_or_reversed_closure_preserves_native_state_and_pending_outcomes` | A calls with the badge 1, the words [1, 2] and the deadline 10 at 5: `queued`. The prototype's refusals of a closure at 4, before the last time (`ClockReversed`), and through a handle with OBSERVE alone (`PermissionDenied`) do not apply: the time does not decrease, and no operation closes an endpoint. `drain_step` of an endpoint of a table whose pools have other numbers is `err=WrongPool` and changes nothing. The drain of E at 9 ends A's call with `PeerClosed` | `drain_step` |
| `ipc-closure-4` | 99 | `closing_again_preserves_an_earlier_reply_or_cancellation` | A calls with the badge 1, the words [1, 2] and the deadline 10 at 1. Either S receives at 2 and replies [3, 4] at 3, after which A has `reply [3, 4]`; or the kill of A at 3 ends its call with `Cancelled`. The drain of E at 4, at the destruction of O, finds no wait of A and changes neither result, and E is then released, where the prototype closed it a second time at 20: the first end of a call is its only one | `receive`, `reply`, `settle`, `drain_step` |

### `src/ipc/tests/lifetime.rs`

`src/ipc/tests/lifetime.rs`, 6 vectors, with the fixture of
`src/ipc/tests/`.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `ipc-lifetime-1` | 4 | `endpoint_closure_completes_queued_and_delivered_calls_before_reaping` | A calls with the badge 1 and the words [1, 2] at 1, and S receives at 2: badge 1 and words [1, 2]; B calls with 2 and [3, 4] at 3: `queued`. The drain of E at 4, at the destruction of O, makes two settlements: B's call, queued, and then A's, which S serves, each ending with `PeerClosed`; after them E is released. S's reply [5, 6] with `1@1` at 4 is `err=ReplyGone`. The prototype's refused reaping of E while references remained (`ReferencesOutstanding`) and its reference of E to S do not apply | `call`, `receive`, `drain_step`, `reply` |
| `ipc-lifetime-2` | 35 | `peer_death_completes_calls_and_caller_death_invalidates_delivered_reply` | A calls with the badge 1 and the words [1, 2] at 1, and S receives at 2. The kill of A at 3 ends its call with `Cancelled` and withdraws S's loan; S's reply [3, 4] with `1@1` at 3 is `err=ReplyGone`. The prototype's refused reaping of A while S held a reference (`ReferencesOutstanding`) and its abandonment do not apply: A is reaped, after which a reply with `1@1` fails in its lookup with `StaleReference`. B calls with 2 and [5, 6] at 4: `queued`. The fault of S's process at 5 is its destruction: the drain of E, whose bound thread is S's, ends B's call with `PeerClosed`, and a call of D at 5 ends at once with `PeerClosed`, since E is not served | `call`, `receive`, `settle`, `reply`, `drain_step` |
| `ipc-lifetime-3` | 67 | `blocked_receive_closes_and_reused_endpoint_generation_cannot_alias` | S receives at 1: `blocked`. The drain of E at 2, at the destruction of O, ends S's receive with `PeerClosed`, and E is released; the root creates the endpoint E2, bound to S, with the capabilities of an added endpoint, and E2 takes the slot of E at the next generation. A's call through its capability to E at 3 is `err=StaleReference`, since the capability names the old generation, where the prototype gave `StaleHandle`, and changes nothing; A's call through a send capability to E2 with the badge 3 and the words [7, 8] at 3 is `queued` | `receive`, `drain_step`, `init_endpoint`, `call` |
| `ipc-lifetime-4` | 94 | `saturated_receive_table_still_admits_calls_and_counts_both_quotas` | O creates the endpoint ED, with the thread of D bound. S receives at 1: `blocked`. D receives from ED at 2: `blocked`, where the prototype's table of one receive refused it (`Capacity`). A calls with the badge 12 and the words [13, 14] at 2: `delivered`, and S is made ready with badge 12 and words [13, 14]. S replies [15, 16] at 3, and A has `reply [15, 16]`. The prototype's counts of records and references do not apply | `receive`, `call`, `reply` |
| `ipc-lifetime-5` | 121 | `failed_take_preserves_completion_and_both_native_references` | Not applicable: a result is written into the saved context of its thread at the end of its wait and is never taken, so the prototype's take before the end (`NotCompleted`) and its takes through another pool and through a handle with OBSERVE alone do not exist; its cancellation of A is the kill of A, whose result A does not observe | None |
| `ipc-lifetime-6` | 148 | `retired_caller_generation_cannot_abandon_replacement_call` | A calls with the badge 1 and the words [1, 2] at 1: `queued`. The kill of A at 2 ends its call with `Cancelled`, and A is reaped; a new process A2, created at 3, has its thread in the slot of A's at the next generation, and calls E with the badge 2 and the words [3, 4] at 3: `queued`. `settle` of the old reference of A at 4 is `err=StaleReference` and leaves A2's call `queued`. The prototype's abandonment of a call is the kill here | `call`, `settle` |

### `src/ipc/tests/ordering.rs`

`src/ipc/tests/ordering.rs`, 7 vectors, with the fixture of
`src/ipc/tests/`.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `ipc-ordering-1` | 4 | `expired_admission_never_delivers_or_advances_other_waits` | S receives with the deadline 10 at 1: `blocked`. In the transition of A's call with the badge 1, the words [1, 2] and the deadline 10 at 10, the expiry first ends S's receive with `Timeout`, and S is made ready, where the prototype settled it only at its next poll; the call then ends at once with `Timeout`, delivers nothing and changes nothing. No deadline remains | `settle`, `call` |
| `ipc-ordering-2` | 22 | `deadline_wins_over_exact_time_reply_and_stale_token_cannot_complete_next_call` | A calls with the badge 1, the words [1, 2] and the deadline 10 at 1, and S receives at 2 with `1@1`; the earliest deadline is 10. In the transition of S's reply [3, 4] with `1@1` at 10, the expiry first ends A's call with `Timeout`, so the reply is `err=ReplyGone`. A calls with 2 and [5, 6] at 11; S receives at 12 with slot 3 for the reply, since slot 1 still holds the old capability: reply `3@1`, another handle. S's reply [7, 8] with `1@1` at 13 is `err=ReplyGone` and changes nothing, and A has no result; S's reply [9, 10] with `3@1` at 13 is `ok`, and A has `reply [9, 10]` | `call`, `receive`, `settle`, `reply` |
| `ipc-ordering-3` | 54 | `unknown_wrong_server_and_replayed_replies_do_not_mutate_other_calls` | A calls with the badge 1 and the words [1, 2] at 1, and S receives at 2 with `1@1`. D's reply [3, 4] with `1@1` at 3 names slot 1 of D's own table, which is empty: `err=NoCapability`, where the prototype gave `PermissionDenied`. S's reply with the handle 0, slot 0 at the generation 0, is `err=StaleHandle`, slot 0 holding a capability of generation 1. Both change nothing. S's reply [5, 6] with `1@1` at 3 is `ok`; a second reply [7, 8] with `1@1` at 4 is `err=NoCapability`, since the reply deleted the capability; `settle` of A at 4 gives `none`, where the prototype's cancellation gave `InvalidState`; each changes nothing. A drain of E at 99 finds no wait, and A has `reply [5, 6]` | `reply`, `settle`, `drain_step` |
| `ipc-ordering-4` | 91 | `cancellation_before_and_after_delivery_is_single_winner` | In three runs, each from the fixture. A calls with the badge 1 and the words [1, 2] at 1, and the kill of A at 2 ends the queued call with `Cancelled`. A calls with 2, [3, 4] and the deadline 10 at 3, S receives at 4, and the kill of A at 5 ends the delivered call with `Cancelled`; the expiry at 10 finds no wait, and S's reply [5, 6] with `1@1` at 10 is `err=ReplyGone`. A calls with 3, [7, 8] and the deadline 20 at 11, and in the transition of the kill of A at 20 the expiry first ends the call with `Timeout`. A killed thread observes no result: the rows check the order of the outcomes and the fixed error of the reply, where the prototype's cancelled thread took its result and called again | `call`, `receive`, `settle`, `reply` |
| `ipc-ordering-5` | 121 | `queued_timeout_is_not_delivered_and_received_snapshot_remains_immutable` | A calls with the badge 1, the words [1, 2] and the deadline 3 at 1: `queued`. In the transition of S's receive with the deadline 9 at 3, the expiry first ends A's call with `Timeout`, so the receive finds no call: `blocked`. A calls with 2, [3, 4] and the deadline 5 at 4: `delivered`, and S is made ready with badge 2 and words [3, 4]. The expiry at 5 ends A's call with `Timeout`; S's results stay as they were, and S's reply [0, 0] with `1@1` at 5 is `err=ReplyGone` | `call`, `receive`, `settle`, `reply` |
| `ipc-ordering-6` | 146 | `backward_time_rejects_every_timed_mutator_without_reference_changes` | Not applicable: the calls, receive, reply, cancellation, poll and abandonment at 9 after a transition at 10, which the prototype refused (`ClockReversed`), lie outside the premise that the time does not decrease within a boot, which no entry checks | None |
| `ipc-ordering-7` | 180 | `an_expired_wait_edge_does_not_reject_a_new_acyclic_call` | O creates the endpoint EA, with the thread of A bound. A calls E with the badge 1, the words [1, 2] and the deadline 5 at 1: `queued`, since S does not receive. In the transition of S's call to EA with the badge 2 and the words [3, 4] at 5, the expiry first ends A's call with `Timeout`, so A has no edge and the call is `queued`, not `err=Cycle`. A receives from EA at 6: badge 2 and words [3, 4]; it replies [5, 6] at 7, and S has `reply [5, 6]` | `call`, `settle`, `receive`, `reply` |

### `src/abi/ipc/tests/authority.rs`

`src/abi/ipc/tests/authority.rs`, 7 vectors, with the fixture of
`src/abi/ipc/tests/`.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `abi-ipc-authority-1` | 4 | `endpoint_tokens_are_resolved_only_in_the_actual_callers_process` | X's call with C's send handle `0@1`, and X's receive with S's receive handle `0@1`, name slot 0 of X's own table, which is empty: each is `err=NoCapability`, where the prototype gave `INVALID_HANDLE`, and changes nothing. The prototype's closure does not apply | `call`, `receive` |
| `abi-ipc-authority-2` | 23 | `send_does_not_grant_receive_or_close_and_receive_does_not_grant_send` | C's receive with its send capability `0@1` and S's call with its receive capability `0@1` are `err=PermissionDenied` and change nothing. The prototype's closure through a send capability does not apply: no operation closes an endpoint, and the `close` of a capability needs no right | `call`, `receive` |
| `abi-ipc-authority-3` | 42 | `thread_and_endpoint_capabilities_are_never_reinterpreted_as_each_other` | C holds in slot 1 a capability to the thread of S with every right of its kind. C's call and receive with `1@1` are `err=WrongType`, and so is the lookup of `0@1`, the send capability, for the query of a thread by the lifecycle component; nothing changes. The prototype's closure does not apply | `call`, `receive` |
| `abi-ipc-authority-4` | 69 | `a_sibling_thread_in_the_server_process_cannot_receive_close_or_reply` | N holds in slot 0 a capability to E with RECEIVE. N's receive at 10 is `err=NotReceiver`, where the prototype gave `PERMISSION_DENIED`, and changes nothing. C's call is delivered; N's reply with the value of `1@1` names slot 1 of N's own table, which is empty: `err=NoCapability`, which changes nothing, and C has no result. The prototype's closure does not apply | `receive`, `call`, `reply` |
| `abi-ipc-authority-5` | 92 | `caller_receipts_require_full_authority_and_inactive_ready_state` | The caller of an operation is the thread that runs, which the dispatch passes, so the prototype's caller through a handle with OBSERVE alone (`PERMISSION_DENIED`), a caller active elsewhere, waiting or dead (`INVALID_STATE`) and a reaped caller (`OBJECT_GONE`) do not exist. A new process, in the slot of C's process at the next generation after C is reaped, has a table of its own, in which `0@1` names no capability: its call with `0@1` at 10 is `err=NoCapability`, where the prototype gave `PERMISSION_DENIED` | `call` |
| `abi-ipc-authority-6` | 142 | `self_call_rejects_with_a_deadlock_status_before_publication` | S holds in slot 3 a send capability to E with the badge 9. S's call with `3@1` at 10 is `err=SelfCall`, which reaches EL0 with the status of a call dependency, and changes nothing | `call` |
| `abi-ipc-authority-7` | 157 | `closing_or_revoking_send_authority_does_not_retract_an_admitted_call` | C's send capability is a child of a capability to E with every right in slot 4 of S's table. C derives from `0@1` into slot 1 a capability with SEND, `1@1`, and calls with it at 10: `queued`. S's revocation of the descendants of `4@1` at 11 is pending: in that transition C's call ends with `Revoked`, and C is paused; its steps remove C's `1@1` and `0@1`, and the step that removes `1@1` makes C ready, with the result `Revoked`. The revocation reports completion, where the prototype returned the count 1. S's receive at 12 is `blocked`, and C's call with `1@1` at 13 is `err=NoCapability`. The prototype's admitted call that kept its authority does not apply, and its close of the child while C waits does not arise: only C's thread could close it | `call`, `settle`, `receive` |

### `src/abi/ipc/tests/lifecycle.rs`

`src/abi/ipc/tests/lifecycle.rs`, 9 vectors, with the fixture of
`src/abi/ipc/tests/`.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `abi-ipc-lifecycle-1` | 4 | `receiver_first_copies_payload_and_badge_without_waking_object_waits` | S receives at 10: `blocked`. C calls with the words W at 11: `delivered`, C has no result, and S is made ready with `ok reply=1@1 badge=B words=W transfer=0`. S replies [9, 10] with `1@1` at 12: `ok`, and C has `reply [9, 10]`. The reply capability is deleted, and no thread waits on E | `receive`, `call`, `reply` |
| `abi-ipc-lifecycle-2` | 32 | `caller_first_receive_consumes_only_its_own_completion_and_reply_is_one_shot` | C calls with W at 10: `queued`; S receives at 11 and returns at once, without blocking, with `ok reply=1@1 badge=B words=W transfer=0`. S replies [0, 18446744073709551615] with `1@1` at 12: `ok`, and C has `reply [0, 18446744073709551615]`. S's replies [99, 99] with `1@1` at 13 and at 14 are `err=NoCapability`, since the reply deleted the capability, and change nothing | `call`, `receive`, `reply` |
| `abi-ipc-lifecycle-3` | 57 | `timeout_after_receive_invalidates_reply_and_zeroes_all_unused_results` | C's call with the deadline 20 is delivered. The expiry at 20 ends C's call with `Timeout`, every other result register 0, and withdraws S's loan; S's reply [99, 99] with `1@1` at 20 is `err=ReplyGone`. No thread waits on E | `call`, `receive`, `settle`, `reply` |
| `abi-ipc-lifecycle-4` | 70 | `cancelled_calls_publish_a_distinct_status_without_restoring_reply_authority` | C's call is delivered. The kill of C at 12 ends its call with `Cancelled`, which C does not observe, where the prototype gave C the status `CANCELLED`; S's reply with `1@1` at 13 is `err=ReplyGone` | `call`, `receive`, `settle`, `reply` |
| `abi-ipc-lifecycle-5` | 82 | `endpoint_close_settles_at_request_time_and_leaves_wait_delivery_to_controller` | C calls with W and the deadline 12 at 10: `queued`. The drain of E at 11, at the destruction of S, which owns E and whose thread is bound to it, in place of the prototype's closure by S: C's call ends with `PeerClosed`, every other result register 0, and C is made ready. The expiry of the deadline 12 finds no wait | `call`, `drain_step` |
| `abi-ipc-lifecycle-6` | 103 | `server_death_publishes_peer_closed_without_losing_deadline_precedence` | For the deadlines 0 and 12 in turn, C's call with that deadline is delivered, and the destruction of S runs at 12, its teardown deleting the reply capability `1@1`. With the deadline 0, `reply_deleted` ends C's call with `PeerClosed`; with the deadline 12, the expiry at 12 first ends it with `Timeout`, and `reply_deleted`, whose generation is then old, gives `none`. Every other result register is 0 | `call`, `receive`, `reply_deleted`, `settle` |
| `abi-ipc-lifecycle-7` | 119 | `reused_call_record_cannot_be_completed_by_an_old_reply` | C's call is delivered, and S replies [1, 2] with `1@1` at 12: `ok`, and C has `reply [1, 2]`. C calls at 13: `queued`; S receives at 14 with the same reply slot: reply `1@2`, the next generation of the slot. S's reply [99, 99] with `1@1` at 15 is `err=StaleHandle`, and C has no result; S's reply [3, 4] with `1@2` at 16 is `ok`, and C has `reply [3, 4]` | `call`, `receive`, `reply` |
| `abi-ipc-lifecycle-8` | 148 | `endpoint_close_rejects_reversed_time_without_closing_or_settling_waits` | Not applicable: the prototype's closure at 9 after a call at 10, which it refused with `INVALID_ARGUMENT`, lies outside the premise that the time does not decrease, and no operation closes an endpoint | None |
| `abi-ipc-lifecycle-9` | 168 | `endpoint_close_at_the_call_deadline_preserves_timeout_precedence` | C calls with the deadline 11 at 10: `queued`. In the transition of the drain of E at 11, at the destruction of S, the expiry first ends C's call with `Timeout`, and the drain finds no call | `call`, `settle`, `drain_step` |

### `src/abi/ipc/tests/validation.rs`

`src/abi/ipc/tests/validation.rs`, 8 vectors, with the fixture of
`src/abi/ipc/tests/`.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `abi-ipc-validation-1` | 4 | `full_width_version_and_operation_reject_without_side_effects` | The versions 1, $2^{32}$ and $2^{64} - 1$ of a call, and the operation numbers 0, the prototype's query, 20, $2^{32}$ plus the number of a call and $2^{64} - 1$, are refused by the dispatch component (planned) before any entry of this page, with its errors of the version and of the operation number, and change nothing; which values are valid belongs to the ABI inventory | None of this page: the dispatch component (planned) |
| `abi-ipc-validation-2` | 31 | `every_reserved_argument_is_rejected_before_registration_or_endpoint_closure` | For `call`, `receive` and `reply`, a reserved register, or an argument register that the operation does not use, holding 1, $2^{63}$ or $2^{64} - 1$ is refused by the dispatch component (planned) as a malformed register argument, before any entry of this page, and changes nothing; which registers an operation uses belongs to the ABI inventory. The prototype's closure does not apply | None of this page: the dispatch component (planned) |
| `abi-ipc-validation-3` | 61 | `expired_admission_has_no_delivery_or_retained_authority` | For each of the deadlines 1, 9 and 10: C's call with that deadline at 10, and S's receive with it at 10, each from the fixture, end at once with `Timeout`, deliver nothing, take no call and change nothing | `call`, `receive` |
| `abi-ipc-validation-4` | 79 | `deadline_zero_is_unbounded_and_nonzero_values_keep_all_sixty_four_bits` | C's call at 10 is `queued` for each deadline in turn: with the deadline 0 the wait has no deadline, and the CPU has no earliest deadline; with $2^{32}$ and with $2^{64} - 1$ the earliest deadline of the CPU is that value, all 64 bits of it | `call` |
| `abi-ipc-validation-5` | 94 | `malformed_endpoint_tokens_cannot_mutate_any_namespace` | For C's call, S's receive and S's reply: the handles 0 and $2^{32}$ name slot 0 at the generations 0 and 65,536, and slot 0 holds a capability of generation 1, so each is `err=StaleHandle`; the handle $2^{64} - 1$ names slot 65,535, beyond the 12 slots of the table: `err=InvalidHandle`. None changes anything. The prototype's closure does not apply | `call`, `receive`, `reply` |
| `abi-ipc-validation-6` | 117 | `full_registry_and_reversed_clock_map_to_explicit_zeroed_errors` | X holds in slot 0 a send capability to E with the badge 17. C calls with W at 10, and X calls at 11: both `queued`, where the prototype's registry of one call refused X's with `NO_CAPACITY`. S's receive at 11 returns at once with C's call, the first in the queue: `ok reply=1@1 badge=B words=W transfer=0`. The prototype's receive at 9, before the last time, does not apply | `call`, `receive` |
| `abi-ipc-validation-7` | 148 | `existing_scalar_dispatch_does_not_accept_ipc_operation_numbers` | Not applicable: the prototype had a second dispatcher for its scalar operations, which refused the operation numbers of IPC; the kernel has one dispatch component, whose operation numbers the ABI inventory gives | None |
| `abi-ipc-validation-8` | 175 | `ipc_operation_and_status_numbers_are_frozen_independently_of_rust_enums` | Not applicable to this page: the numbers of `call`, `receive` and `reply`, and the numeric statuses of the outcomes and of the call dependencies, belong to the ABI inventory, which fixes them apart from the names of this page; the prototype's operation numbers 16 to 19 and statuses 10 to 14 are not carried over, and its closure and its status `CANCELLED` do not exist | None |

## References

- The kernel's own rules, which this page instantiates:
  [IPC, notifications and waits](../../../architecture.md#ipc-notifications-and-waits)
  for calls, one-shot replies with a generation, the competing outcomes,
  budget lending within a ceiling with one active holder and its
  withdrawal before the caller is woken, timeouts that only mean that the
  caller stopped waiting, and transfers that become visible with their
  message; [Scheduling and budgets](../../../architecture.md#scheduling-and-budgets)
  for the budgets that a loan lends; the execution model under
  [System calls and the ABI](../../../architecture.md#system-calls-and-the-abi)
  for blocking by wait records, completion by continuation and the forced
  kill that cancels a wait; and
  [Multicore by design](../../../architecture.md#multicore-by-design) for
  the shared endpoint queues and the per-thread reply records.
- The [security model](../../../security.md): its
  [internal choices](../../../security.md#internal-choices) for the order of
  errors, the queues of endpoints, the first registered waiter, expiry
  first, the order of completion and the settlement of a loan as a whole;
  its [sender identity](../../../security.md#unforgeable-authority) and
  [information-flow boundary](../../../security.md#information-flow-boundary);
  its [observable outputs](../../../security.md#observable-outputs); and the
  register of
  [permitted nondeterminism](../../../security.md#permitted-nondeterminism).
- The rules of this page take, as clauses of their own, the rules of the
  prototype tree at `prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`:
  - `docs/features/kernel/ipc.md`, lines 85 to 118: the rights of an
    endpoint and its badge set once, the bound service thread that alone
    receives, the delivery in order of calls, and the refusal of calls to
    oneself and of cycles of pending calls before anything is published;
    its registry with fixed tables and tokens is not taken;
  - `docs/features/kernel/ipc.md`, lines 119 to 171: the receive that
    returns at once, deadlines settled before every other outcome, results
    that never change, the timeout that does not undo the server's work,
    the closure and the death of a peer that report the same outcome, and
    no fused reply and receive, direct handoff or latency guarantee; its
    closure operation, its strong references and its outbox are not taken;
  - `docs/features/kernel/ipc.md`, lines 172 to 184: the composition of IPC
    with the shared waits; its aggregate registry and control admission are
    the waits component's records embedded in threads here;
  - `docs/features/kernel/capability-transfer.md`, lines 64 to 116: the
    message side of a transfer, copy and move, the source hidden until the
    commit, the capability visible with the message, and the transfer that
    a later timeout does not undo; its reservation before admission and its
    abort are replaced by the commit at delivery;
  - `docs/features/kernel/synchronous-budgets.md`, lines 77 to 137: the loan
    of the caller's context to one receiver, nested loans of one context
    with at most eight edges, the effective priority within the ceiling, no
    fallback to the receiver's own budget, the withdrawal of the receiver's
    and every downstream loan before the caller wakes, no automatic
    re-lending and one loan for each participant at a time; the records of
    loans are the budget-ledger component's;
  - `docs/kernel-state.md`, lines 43 to 76: the division into per-CPU,
    per-thread, per-process and shared state, with one terminal outcome for
    each wait and the aggregate budget that donated execution cannot
    multiply;
  - `docs/kernel-state.md`, lines 110 to 131: the owner of waits, IPC and
    loans, every loan belonging to one blocked call and one receiver, and
    no wake of the owner of a context while it is lent.
