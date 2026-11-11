# IPC and waits

## Overview

The IPC and waits domain decides how threads exchange messages and
capabilities, how they wait for events and for time, and how every wait
ends. It covers synchronous calls through endpoints, each of which binds
one receive thread, with `call`, `receive` and `reply`; the one-shot reply
right that each delivered call gives its receiver; the transfer of a
capability together with its message; shared buffers for data larger than
a message; notifications, whose signals coalesce in a word of pending
bits; deadlines, timeouts and sleeps; the wait sets of threads; and
futex-style waits on words of memory.

Four limits bound the domain. A message is two 64-bit words and carries at
most one capability, so larger data goes through shared buffers or through
several calls. Every thread has one wait record embedded in its slot, so it
waits for one thing at a time, no wait allocates memory and no wait can be
refused for want of a record; a process has one thread, so a thread that
is blocked in a call cannot receive, and the kernel refuses a call that
could never be delivered for that reason. Time is the count of the
virtual counter of the board, read once on entry to each transition, and
every deadline is an absolute value of it; a result on one CPU does not
show the order in which several CPUs reach an endpoint or a notification.
The kernel detects the dependencies of calls on one another, not every
deadlock of an application: a wait on a notification, a wait set or a
sleep is no such dependency.

The domain builds on others, listed in the
[subject-domain index](../README.md). The kernel objects and capabilities
domain holds the slots of endpoints, notifications and threads, the
handles, rights and lookups of capabilities, the table side of a transfer,
revocation, the write-set transactions, and the creation and destruction of
processes, whose kill cancels a wait and whose teardown ends the calls of a
dying peer; the scheduling and budgets domain gives the loans of budgets
that calls make, blocking and the readiness of the threads whose waits
complete, and the timer deadline of a dispatch; the memory and
address-spaces domain gives the VM objects that shared buffers map and
that futex keys name, and the EL0 policy that lets EL0 read the virtual
counter; the boot and platform domain gives the saved context into which a
completion writes its results; the devices and DMA domain signals
notifications from the interrupts of devices. The [ipc](ipc/requirements.md)
component holds the endpoints with their bound threads and queues, calls,
receives and replies, the refusal of calls to oneself and of cycles of
calls, the reply records, badges, the composition of a transfer with its
message, the times of loans, and the settlement of a call by each of its
outcomes. The [waits](waits/requirements.md) component holds the wait
records and their completion, notifications, deadlines and sleeps, wait
sets, the single winner of an event, the part of a kill in a wait, and the
settlement of waits under revocation and at the release of their objects.

## Conventions

- **Authority by capability.** Every operation of the domain acts through a
  capability of the caller's own table, with the right that its contract
  states; RECEIVE on an endpoint is valid only for its bound thread. A
  receiver learns of its caller only the badge of the caller's capability,
  which the party that minted it chose; no word of a request changes it.
- **Outcomes are not errors.** `Timeout`, `PeerClosed` and `Revoked` are
  outcomes of a wait that was accepted and are written into its result
  registers; `Cancelled`, the outcome of a kill, is an outcome as well but
  writes no result, since the killed thread never runs again. An error
  refuses its operation and changes no state.
- **One result.** A wait ends by its first completion, which writes its
  result into the saved context of its thread in that transition; the
  result never changes, and the woken thread only returns with it.
- **Expiry first.** At the entry of every transition, every wait whose
  deadline is not later than the time of the transition settles as a
  timeout before the operation of the transition runs, and a wait whose
  deadline has passed when it is made times out at once and consumes
  nothing.
- **Order of outcomes.** When one transition brings several events to one
  wait, the first of timeout, cancellation, revocation, peer closure and
  the event of the wait decides; in different transitions the first
  transition decides.
- **Single winner.** Each event completes at most one waiter: the one that
  began to wait first, and a thread that waits on the object directly
  before a wait set that holds it.
- **Bounded entries.** No operation of the domain is a long operation: the
  walks of an entry are bounded by the thread capacity or by constants, and
  the drains of a destruction and the steps of a revocation take their
  part of a step from the contracts of the components.

## Feature index

| Feature | Scope | Feature documents | Components |
| --- | --- | --- | --- |
| [Calls](#calls) | Endpoints and their bound receive threads, `call`, `receive` and `reply`, the queue of calls, the outcomes of a call, the refusal of calls to oneself and of cycles of calls, badges, and the release of an endpoint | - | [ipc](ipc/requirements.md) |
| [One-shot replies](#one-shot-replies) | The reply capability of each delivered call, its generation, the fixed error of a late reply, and the close of a reply capability | - | [ipc](ipc/requirements.md) |
| [Capability transfer](#capability-transfer) | The copy and the move of one capability with a message, the receive slot, and the commit at the delivery | - | [ipc](ipc/requirements.md); [capabilities](../objects-capabilities/capabilities/requirements.md), for the table side |
| [Shared buffers](#shared-buffers) | Memory that two processes map for data larger than a message, and the private snapshot of its shared indices and descriptors | - | The VM of the core, for the shared objects and their mappings |
| [Notifications](#notifications) | The word of pending bits, `signal` and `wait`, coalescing and consumption, and the signals of the kernel | - | [waits](waits/requirements.md) |
| [Timeouts](#timeouts) | Deadlines, expiry first, deadlines that pass together, `sleep`, and the deadline table | - | [waits](waits/requirements.md) |
| [Wait sets](#wait-sets) | The registrations of a thread, `wait_set_add`, `wait_set_remove` and `wait_set_wait`, readiness, reports and removed sources | - | [waits](waits/requirements.md) |
| [Futex-style waits](#futex-style-waits) | Waits and wakes on a word of memory, keys from the memory that holds the word, and the end of waits when the memory goes | - | The futex waits of the core, which extend the wait records of [waits](waits/requirements.md) |

## Calls

**Description.** An endpoint is an object that its creator owns. Its
creation binds one receive thread, given by a capability to the thread with
CONTROL, and the binding never changes. `call` sends a message of two 64-bit
words through a capability with SEND, with a deadline and at most one
capability to transfer; `receive` takes a call through a capability with
RECEIVE, which only the bound thread may use; `reply` answers a delivered
call through its reply capability. A call that finds the bound thread
waiting in `receive` is delivered to it at once, and otherwise joins the
tail of the FIFO queue of the endpoint; a receive takes the first queued
call without blocking, or else blocks as the receiver of the endpoint. A
delivered call waits for its reply, and its caller lends its budget to the
receiver, which serves that call and receives no other until it ends. A call
or a receive ends by its reply or its delivery, or by an outcome: `Timeout`
at its deadline, `Cancelled` when its thread is killed, `Revoked` when a
capability through which it waits comes under revocation, and `PeerClosed`
when its endpoint, its bound thread or the holder of its reply capability
goes. A call to an endpoint whose bound thread is the caller is refused with
`SelfCall`, and a call that would close a cycle, from the bound thread along
the calls in which threads are blocked back to the caller, with `Cycle`;
both change nothing. No operation closes an endpoint: it is released with
its last capability or with its owner; when its owner is destroyed, the
calls on it end with `PeerClosed`. Replies are not fused with receives, and
the kernel makes no direct switch to the receiver and no promise of latency.

**Design background.** Synchronous calls with a short message in registers
and a reply right made for each call follow the IPC of the L4 family
(Liedtke 1993) and of seL4. Binding one receive thread to each endpoint
makes the receiver of a call known when the call is made, so the kernel can
refuse a call that its receiver could never take: a process has one thread,
and a thread blocked in a call does not receive. The binding is a reference
that holds back no reclamation, and an endpoint whose bound thread has gone
ends every call at once. Delivering calls in the order in which they were
made, and settling deadlines first, make each outcome a fixed rule of the
[internal choices](../../security.md#internal-choices).

**Consumers.** The services that answer calls, such as the file, block,
stream and process services, the root and supervisors; their clients, the
runtimes and applications of EL0; the runtime of each POSIX environment,
which reaches its services by calls; the
[synchronous budget lending](../scheduling/README.md#synchronous-budget-lending)
of the scheduling and budgets domain, which charges a service to its
client.

**Interface.** `call` takes the handle of the endpoint, the two words, the
deadline and a transfer, and returns the two words of the reply or an
outcome; `receive` takes the handle of the endpoint, the deadline, the slot
for the reply capability and the slot for a transferred capability, and
returns the handle of the reply capability, the badge, the two words and the
handle of the transferred capability, 0 without one
([calls and receives](ipc/contract.md#calls-and-receives)). Errors refuse
the operation: those of the lookup of a handle; `NotReceiver` for a thread
other than the bound thread; `ReplyPending` for a receive by a thread that
serves a call; `SelfCall` and `Cycle`, which reach EL0 as one status, that
of a call dependency. The outcomes are states written into the results. The
creation of an endpoint, with its receive thread, is an operation of the
creation of objects.

**Prerequisites.** [One-shot replies](#one-shot-replies),
[Capability transfer](#capability-transfer), [Timeouts](#timeouts); the
[ipc contract](ipc/contract.md#endpoint-queues); the
[capability tables](../objects-capabilities/README.md#capability-tables),
[delegation and revocation](../objects-capabilities/README.md#delegation-and-revocation)
and
[process and thread lifetimes](../objects-capabilities/README.md#process-and-thread-lifetimes)
of the kernel objects and capabilities domain;
[Synchronous budget lending](../scheduling/README.md#synchronous-budget-lending)
and [Priority classes](../scheduling/README.md#priority-classes) of the
scheduling and budgets domain.

**Engineering notes.** `MESSAGE_WORDS` = 2. An endpoint has at most one
receiver, its bound thread, and its queue links the queued callers through
their wait records, so a queue has no capacity of its own. The check of
cycles takes at most the thread capacity less one steps, with two reads
each and no preemption point; the delivery of a call writes at most 25
items, a settlement at most 17, and the withdrawal of a chain of loans at
most `MAX_LOAN_DEPTH` = 8 records. The queues of endpoints are shared state
and the reply records per-thread state, classified in the
[State fields](ipc/contract.md#state-fields) of the ipc contract.

**Verification.** Invariants: every thread in the queue of an endpoint is
blocked in a queued call of it; while an endpoint has a receiver, its queue
is empty; each thread has at most one call edge, and the graph of calls has
no cycle; every call ends once. Required counterexamples: a receive by
another thread that holds RECEIVE; a call to oneself; cycles of every
length through queued calls, delivered calls and both; a deadline equal to
the time of the call; a call on an endpoint whose bound thread's process is
dead; the end of a call in the middle of a chain of loans. Environments:
host tests with the frozen vectors of the prototype's IPC and its ABI, and
a property test against an independent model of the graph of calls; QEMU
runs of two processes that call, receive and reply from EL0.

## One-shot replies

**Description.** Each delivered call gives its receiver one reply
capability, in the slot that the receiver named: it holds REPLY alone, so
it is never copied, derived, transferred or revoked, and it names the
caller with the generation of the caller's reply record. `reply` ends the
call with two words, deletes the reply capability and makes the caller
ready after the loans of the call are withdrawn. Every end of a delivered
call raises that generation, so a reply after a timeout, a kill, a
revocation or a peer closure fails with `ReplyGone` and changes nothing,
and a second use of the handle fails in its lookup. A server deletes a
reply capability with `close`; the close of a live one, or the destruction
of the server, ends the call with `PeerClosed`. A thread whose reply
generation has reached its limit makes no further call (`ReplyExhausted`),
and the generation never wraps.

**Design background.** A reply right made for each call, as the reply
capabilities of seL4, needs no global token: its handle names a slot of the
server's own table, and the generation of the caller's record makes a late
reply fail with a fixed error instead of reaching a later call of the same
caller. A generation for each thread exposes no counter of the system, as
the [identifiers](../../security.md#internal-choices) rule requires.

**Consumers.** Every server; the clients, whose runtimes see the fixed
error of a late reply as the server's; services that give up a call, which
close its reply capability.

**Interface.** `reply` takes the handle of the reply capability and two
words and returns success. Its errors are those of the lookup of the
handle, among them `StaleReference` once the caller has been reaped, and
`ReplyGone`; `close` of the capabilities component deletes a reply
capability. `ReplyExhausted` refuses a call
([replies](ipc/contract.md#replies)).

**Prerequisites.** [Calls](#calls); the
[ipc contract](ipc/contract.md#replies); the
[capability tables](../objects-capabilities/README.md#capability-tables)
and [generations](../objects-capabilities/README.md#generations) of the
kernel objects and capabilities domain.

**Engineering notes.** A thread serves at most one call and a process has
one thread, so a table holds at most one live reply capability; the others
are old and occupy slots of the server's table until it closes them. A
reply writes at most 16 items. The reply record is per-thread state,
classified in the [State fields](ipc/contract.md#state-fields) of the ipc
contract.

**Verification.** Invariants: a reply capability is live only while its
call is delivered; a call ends once, by its reply or by another outcome.
Required counterexamples: a second reply with one handle; a reply after
each other outcome; the close of a live and of an old reply capability; the
teardown of a table that holds both; a reply capability of a reaped caller;
a reply record at the generations $2^{64} - 2$ and $2^{64} - 1$.
Environments: host tests with the frozen vectors of the prototype's IPC and
its ABI; QEMU runs of servers that reply from EL0.

## Capability transfer

**Description.** A call carries at most one capability, copied or moved,
with rights that the caller can only reduce: the source needs GRANT and
every right that the call asks for. The receiver names the slot for it when
it starts to receive, and the slot must be empty. The transfer commits at
the delivery, in the write-back that also gives the message, so the
receiver sees the message and the capability together. A queued call
reserves nothing; its source is checked again at its delivery, and when
the object of the source has been released meanwhile the call ends with
`StaleReference` and the receive takes the next call. A move deletes its
source at the commit, and a move of the capability through which the call
is sent is refused. A later outcome of the call does not undo a committed
transfer, and the revocation of the source of a queued call ends the call
with `Revoked`.

**Design background.** Committing the transfer in the transaction of the
delivery leaves no reservation from one transition to the next, so no
failure between a reservation and its commit can arise and no moved source
has to be restored. A slot that the receiver names, and that only its own
thread can fill, is held for the transfer from the start of the receive,
before the message is sent, as the
[IPC](../../architecture.md#ipc-notifications-and-waits) of the kernel
requires; copy and move stay distinct operations of the table.

**Consumers.** The root and the process manager, which hand out the
authority of services; the services that return capabilities to their
clients, such as the file and block services; clients that pass a shared
buffer or a device grant to a service.

**Interface.** `call` takes the handle of the source, the mask of the
rights asked for and the mode, copy or move; `receive` takes the transfer
slot and returns the handle of the received capability
([capability transfer](ipc/contract.md#capability-transfer)). Errors refuse
the call or the receive: `InvalidRights`, `SelfTransfer`, `SameSlot`, the
lookup of the source with GRANT, an occupied or retired slot, and a path
deeper than the capabilities component allows; `StaleReference` of a
source that has gone is the outcome of a queued call.

**Prerequisites.** [Calls](#calls); the
[ipc contract](ipc/contract.md#capability-transfer); the
[transfer](../objects-capabilities/capabilities/contract.md#transfer) of
the capabilities component; the
[delegation and revocation](../objects-capabilities/README.md#delegation-and-revocation)
of the kernel objects and capabilities domain.

**Engineering notes.** The reservation and the commit write at most 11
items within the write set of the delivery, whose checks all come before
its first write, so the IPC component never aborts a reservation. A
received capability is a child of its source, and a move puts it in the
place of the source among its siblings. The entries of a transfer are
per-process state of the tables, classified in the
[State fields](../objects-capabilities/capabilities/contract.md#state-fields)
of the capabilities contract.

**Verification.** Invariants: no reserved entry exists after any
write-back of a call or a receive; a receiver that holds the message of a
call holds its capability too. Required counterexamples: a copy and a
move, delivered at once and by a receive; a source released while its
call is queued; a move of the capability of the call; the revocation of
the source of a queued call; a timeout after the delivery. Environments:
host tests with the frozen vectors of the prototype's transfers; QEMU runs
that pass capabilities between processes.

## Shared buffers

**Description.** Data larger than a message goes through a shared buffer:
a VM object that the processes of both parties map, each through a
capability that the owner of the object has passed to it. The kernel copies
nothing for a transfer through the buffer and takes no part in its
protocol: the parties tell each other with calls or notifications which
part of the buffer holds data. A process that reads indices or descriptors
from a buffer that the other party can write reads them once into a
private snapshot and validates them there before it uses them. A buffer has
no queue or wait of its own, and the release of its object, its mappings
and its reclamation follow the rules of VM objects. Without a shared
buffer, large data goes in pieces through successive calls.

**Design background.** Shared memory with indices that the parties
exchange moves bulk data without a copy by the kernel, while calls and
notifications keep their short messages. Another thread can change shared
memory between two reads, so a value that decides an action is read once
([S6d](../../conventions/smp.md#s6d-user-memory)).

**Consumers.** The block, file and stream services and their clients;
services that exchange large data with processes, such as those of
display and input devices.

**Interface.** No operation of its own: the buffer is a VM object of the
[memory and address spaces](../memory/README.md) domain, mapped with its
operations, its capability passes by
[capability transfer](#capability-transfer), and data is announced by
[calls](#calls) or [notifications](#notifications).

**Prerequisites.** [Calls](#calls), [Notifications](#notifications),
[Capability transfer](#capability-transfer); the
[VM objects and their kinds](../memory/README.md#vm-objects-and-their-kinds),
[user-buffer access](../memory/README.md#user-buffer-access) and
[reclamation barriers](../memory/README.md#reclamation-barriers) of the
memory and address-spaces domain.

**Engineering notes.** A party assumes that the other party changes the
buffer at any time, also while it validates its snapshot. A buffer outlives
the unmapping by one party, and its pages return only after its release has
completed. The mappings and objects are classified by the contracts of the
VM of the core.

**Verification.** Invariants: a party acts only on values of its snapshot;
no page of a released buffer is reused while a mapping of it remains.
Required counterexamples: indices that the other party changes between
two reads, descriptors that point outside the buffer, the release of a
buffer that the other party still maps. Environments: host tests of the
snapshot and validation of each protocol against an independent model of
an adversarial writer; QEMU runs of two processes that exchange data
through a shared object while one of them writes concurrently.

## Notifications

**Description.** A notification is an object with a 64-bit word of pending
bits and the FIFO queues of the threads that wait on it. `signal`, through
a capability with SIGNAL, ORs a nonzero set of bits into the word; when a
thread waits on the notification directly, the first is completed with the
whole word, which becomes 0, and otherwise the first thread whose wait set
holds it is completed with its report while the word stays. `wait`,
through a capability with WAIT, returns at once with the whole word when it
is not 0 and clears it; otherwise it blocks until a signal or another
outcome. Signals coalesce: the word is a reason to look at a queue, not a
count of messages, and repeated bits merge. A signal allocates nothing and
never blocks, so the interrupt paths of drivers and the death notifications
of processes use it as it is. A notification has no recipient and no
closure, and its capability carries no badge; its release by the
destruction of its owner ends its direct waits with `PeerClosed` and
reports it removed to its wait-set waiters.

**Design background.** A word of pending bits, as the notifications of
seL4, holds any number of signals in a fixed size, so a signal needs no
memory and can come from an interrupt; the state of the queue that the
signal points to counts the messages, as the
[IPC](../../architecture.md#ipc-notifications-and-waits) of the kernel
states. Completing a direct waiter before a wait set keeps a thread from
blocking in `wait` while the word is set, since a report consumes nothing.

**Consumers.** EL0 drivers, whose interrupts the devices and DMA domain
delivers through notifications; the lifecycle of processes, whose death
notifications signal one; services and clients that announce data in
shared buffers; the event loops of runtimes.

**Interface.** `signal` takes the handle of the notification and the bits
and returns success; `wait` takes the handle and a deadline and returns the
bits or an outcome ([notifications](waits/contract.md#notifications)). Bits
of 0 are refused (`InvalidBits`); the errors of the lookup, and a wait that
would block while the generation of the thread's waits is at its limit,
refuse the operation as well, and `Timeout`, `Revoked` and `PeerClosed` are
outcomes.

**Prerequisites.** [Timeouts](#timeouts), [Wait sets](#wait-sets); the
[waits contract](waits/contract.md#notifications); the
[capability tables](../objects-capabilities/README.md#capability-tables)
and the
[process and thread lifetimes](../objects-capabilities/README.md#process-and-thread-lifetimes)
of the kernel objects and capabilities domain; the
[interrupt controllers](../boot-platform/README.md#interrupt-controllers)
of the boot and platform domain.

**Engineering notes.** A notification keeps two queues, one of all its
waiters and one of its direct waiters, so a signal takes the first thread
of one queue in a fixed number of steps; a signal with its completion and
the readiness of the woken thread writes at most 14 items. The word and the
queues are shared state, classified in the
[State fields](waits/contract.md#state-fields) of the waits contract.

**Verification.** Invariants: no direct waiter is blocked while the word is
not 0; each signal completes at most one waiter, the first; an outcome
never changes once written. Required counterexamples: a signal before a
wait, after a wait that blocked and after a completed wait; a signal at the
deadline of a wait; bits of 0; repeated and overlapping bits; the release of
a notification with direct and wait-set waiters in mixed order.
Environments: host tests with the frozen vectors of the prototype's
notifications and their ABI, and a property test against an independent
model of FIFO queues; QEMU runs in which a signal from another process
wakes a waiter.

## Timeouts

**Description.** A deadline is an absolute time in ticks of the virtual
counter, which EL0 reads too, and 0 is no deadline. The time of a
transition is read once on its entry, and at that entry every wait whose
deadline is not later than that time settles as `Timeout`, the earliest
deadline first and equal deadlines in the order of their registration,
before the operation of the transition, so the event of that operation
does not complete it: a signal leaves its bits for the next wait, and a
reply to a caller that timed out fails with a fixed error. A wait whose
deadline has passed when it is made returns `Timeout` at once, consumes
nothing and reserves nothing. `sleep` waits on no object until a time; for
a time not later than the time of the call, 0 among them, it returns at
once, and its end is a success, not a timeout. A timeout means only that
the caller stopped waiting: it does not undo a delivered message, a
committed transfer or the work that a server has done. The deadlines of
pending waits form one deadline table, whose earliest deadline bounds the
dispatch of the CPU so that its timer wakes the kernel then.

**Design background.** Absolute deadlines in the count of a counter that
EL0 reads need no conversion between EL0 and the kernel and do not drift
when a call is retried. Expiry first makes the outcome of a deadline that
coincides with an event a fixed rule, as the
[internal choices](../../security.md#internal-choices) require, and a
table in the order of the deadlines gives the earliest one in a fixed
number of steps.

**Consumers.** Clients that bound their calls and waits by deadlines; the
timed waits and sleeps of runtimes and of the POSIX environments;
supervisors that watch services; the
[preemption](../scheduling/README.md#preemption) of the scheduling and
budgets domain, whose dispatch ends at the earliest deadline.

**Interface.** The deadline is an argument of `call`, `receive`, `wait` and
`wait_set_wait`, and `sleep` takes the time to wake
([deadlines and sleep](waits/contract.md#deadlines-and-sleep)). `Timeout`
is a state of the result, not an error, and every 64-bit deadline is valid.
No operation reads a clock: EL0 reads `CNTVCT_EL0` and `CNTFRQ_EL0`.

**Prerequisites.** [Notifications](#notifications), [Calls](#calls); the
[waits contract](waits/contract.md#deadlines-and-sleep); the
[EL0 controls](../memory/address-space/contract.md#el0-controls) of the
address-space component; [Preemption](../scheduling/README.md#preemption)
of the scheduling and budgets domain.

**Engineering notes.** A deadline is only compared with times, never added
to, so no value overflows; within a boot the time does not decrease and
stays below $2^{63}$, premises that no entry checks. The insertion into the
deadline table walks it, at most the thread capacity of waits, and the
expiry of every deadline that has passed runs in one transition without a
preemption point, bounded by the thread capacity. The deadline table is
shared state, classified in the
[State fields](waits/contract.md#state-fields) of the waits contract.

**Verification.** Invariants: after the expiry of a transition, no pending
wait has a deadline that is not later than its time; a timeout never
undoes a delivery or a transfer. Required counterexamples: deadlines one
tick before, at and after the time of the call, 0 and $2^{64} - 1$; a
signal at the deadline of a wait; three waits whose deadlines pass
together, two of them equal; a sleep until 0, until the time of the call
and one tick later. Environments: host tests that pass their times, with
the frozen vectors of the prototype's notifications, waits and IPC; QEMU
runs of a wait that times out at the timer interrupt.

## Wait sets

**Description.** Each thread has `WAIT_SET_SOURCES` = 4 positions.
`wait_set_add` registers a source at a position: a notification through a
capability with WAIT, or an endpoint through a capability with RECEIVE when
the caller is its bound thread; `wait_set_remove` clears a position, and a
registration stays across waits until then. `wait_set_wait` checks each
registration again: a source whose capability has been closed or removed or
is under revocation, or whose object has been released, is removed, which
the report gives as a fixed reason, with success, and its registration is
cleared; a source is ready while its notification has pending bits or its
endpoint has a queued call. With a ready or a removed source the wait
returns at once, with the positions of each kind in their order; otherwise
it blocks until a source becomes ready or is removed, or another outcome
ends it. A report consumes nothing: the thread takes the event with `wait`
or `receive`, which may find it taken in the meantime. A thread that waits
on a notification directly wins against a wait set; an endpoint has no such
choice, since only its bound thread waits on it, in `receive` or in a wait
set, and in one of them at a time. A wait set is no object: it cannot be
created, held or shared. A futex key can be a source of a wait set; when the
region of the key is released, the source is removed.

**Design background.** Readiness that is a level, as the level-triggered
mode of Linux `epoll`, lets a thread wait for several sources and lets a
compatibility layer build `poll` and `epoll` on it. Registrations kept in
the thread alone, not linked to their sources while the thread does not
wait, spare the release of a source and a revocation a scan of idle
registrations: the next wait finds a removed source by its lookup.

**Consumers.** The event loops of services and runtimes; the `poll` and
`epoll` of the compatibility personalities; drivers that wait for
interrupts and requests together.

**Interface.** `wait_set_add` takes a position and a handle,
`wait_set_remove` a position, and `wait_set_wait` a deadline; the result of
a wait is its outcome with the ready and the removed positions
([wait sets](waits/contract.md#wait-sets)). Errors: a position out of
range, the errors of the lookup, `NotReceiver` for an endpoint of which the
caller is not the bound thread, a source that another position registers,
an occupied or an empty position, a wait set without a registration, and
a wait that would block while the generation of the thread's waits is at
its limit.

**Prerequisites.** [Notifications](#notifications), [Calls](#calls),
[Timeouts](#timeouts), [Futex-style waits](#futex-style-waits); the
[waits contract](waits/contract.md#wait-sets).

**Engineering notes.** A wait makes at most `WAIT_SET_SOURCES` lookups and
joins at most as many queues when it blocks; a signal and a call that joins
a queue take only the first waiter, in a fixed number of steps. Only its
bound thread can register an endpoint, so an endpoint keeps no queue of
waiters of wait sets. The registrations are per-thread state, classified
in the [State fields](waits/contract.md#state-fields) of the waits
contract.

**Verification.** Invariants: each event completes at most one waiter; no
waiter of a wait set is completed while a direct waiter of the same
notification waits; a registration exists only in its thread. Required
counterexamples: each error; a source removed by a close before the wait,
by a revocation while the thread waits and while it does not, and by the
release of its object while it waits; a report followed by a wait that
takes the word; an endpoint with a call queued before the wait and after
it. Environments: host tests with a property test against an independent
model of FIFO queues; QEMU runs of a wait set over a notification and an
endpoint.

## Futex-style waits

**Description.** A futex lets threads wait on a word of their memory and
wake one another through it. A wait blocks only while the word holds the
value that the caller expects, and a wake of $n$ threads wakes the $n$
waiters registered first. The key of the word decides whether a wait and a
wake name the same futex, and it follows from the memory that holds the
word, not from a flag of the operation: a word in private anonymous memory
has a private key of its address space, its region and the offset in the
region; a word in a shared object has a shared key of the object and the
offset in it, which every address space that maps the object reaches; a
word in a mapping that the kernel installs has a key of its address space
and that mapping. When the release of a region completes, every wait on a
key of that region completes with a fixed error; a wait on a shared key
completes when its object is destroyed, and one on a mapping that the
kernel installs when its process is destroyed. Deadlines expire first, a
kill or a timeout cancels a futex wait by completing its record, and a
futex operation on a page of device registers fails with a fixed error.
Keys are never visible to EL0: a wait and a wake return only their result
and the number of threads woken.

**Design background.** Futexes keep uncontended locks in EL0 and enter the
kernel only to wait or to wake (Franke et al. 2002). A key derived from the
memory makes private and shared operations on one word agree, which the
robust mutexes of the C library need, and the generations of the slots of
regions keep a new region at the address of a released one from matching
its old keys ([futexes](../../architecture.md#futexes-and-upcalls)).

**Consumers.** The mutexes, condition variables and one-time
initialization of the C library and of Rust `std`; the Go runtime; the
futex operations of the Linux compatibility, wait and wake.

**Interface.** A wait takes the address of the word, the expected value and
a deadline, and a wake takes the address and a number of threads and
returns the number woken; the operations and their errors belong to the
contract of the futex waits. A key is a source that a wait set can
register.

**Prerequisites.** [Timeouts](#timeouts), [Wait sets](#wait-sets); the
[VM objects and their kinds](../memory/README.md#vm-objects-and-their-kinds)
of the memory and address-spaces domain; the
[process and thread lifetimes](../objects-capabilities/README.md#process-and-thread-lifetimes)
of the kernel objects and capabilities domain; the
[waits contract](waits/contract.md#wait-records), whose wait records hold a
key in place of an object.

**Engineering notes.** The chains of waiters hang on the regions, the
mapping records and the objects of their keys, so no wait allocates; the
release of a region completes its waits one by one in bounded steps whose
progress it stores in the region. A word that a program uses with private
and shared operations has one key, so it sees at most spurious wake-ups,
after which the caller checks the value again. The contract of the futex
waits classifies their state.

**Verification.** Invariants: a wake never completes a wait on another key;
no wait outlives the release of the region or the destruction of the
object of its key. Required counterexamples: private and shared operations
on one word; a new region at the address of a released one; the private
keys of a parent and its child after a fork; a wake and a deadline in one
transition; a futex operation on a page of device registers. Environments:
host tests of keys against an independent model of address spaces and
objects; QEMU runs of the mutexes of the C library across processes that
share an object.

## Dependencies

| Feature | Depends on | Reason |
| --- | --- | --- |
| Calls | Capability tables, Process and thread lifetimes, Synchronous budget lending, Priority classes, Timeouts | A call goes through a capability, binds a thread at the creation of its endpoint, lends its budget, blocks and wakes threads and has a deadline |
| One-shot replies | Calls, Capability tables, Generations | A reply capability is installed by a delivery into a table and carries the generation of the caller's reply record |
| Capability transfer | Calls, Delegation and revocation | The capability moves with a message as a derivation of its source |
| Shared buffers | VM objects and their kinds, User-buffer access, Capability transfer | The buffer is a VM object whose capability passes by transfer and whose contents are read into a snapshot |
| Notifications | Capability tables, Timeouts | A signal and a wait go through capabilities, and a wait has a deadline |
| Timeouts | Preemption, QEMU virt and Pi 5 board support | The earliest deadline bounds the dispatch, and the counter frequency of the board gives its ticks |
| Wait sets | Notifications, Calls, Futex-style waits | The sources of a wait set are notifications, endpoints and futex keys |
| Futex-style waits | VM objects and their kinds, Timeouts, Wait sets | A key comes from the memory that holds its word, and its waits have deadlines and can be in wait sets |

## Exclusions

- Calls, waits and loans between CPUs, how the waits of several CPUs
  divide among their timers, the pending queues between CPUs and the locks
  that provide the tokens belong to the multicore domain.
- The creation of endpoints and notifications with their arguments, the
  kill, destruction and reaping of processes, joins and death
  notifications, and the rights that operations need belong to the
  [kernel objects and capabilities](../objects-capabilities/README.md)
  domain; this domain gives the parts of a wait in a kill and in a
  destruction, and the signal of a death notification.
- The budgets that a call lends, their charge and the run queues that the
  completions of waits feed belong to the
  [scheduling and budgets](../scheduling/README.md) domain; this domain
  decides when a loan is made and withdrawn and which thread a completion
  makes ready.
- VM objects, their regions, mappings and release, which shared buffers and
  futex keys use, belong to the [memory and address spaces](../memory/README.md)
  domain.
- The binding and acknowledgement of the interrupts of devices, and which
  notification an interrupt signals, belong to the devices and DMA domain.
- The operation numbers, the registers of the arguments and results, and
  the numeric values of errors and statuses belong to the operation
  inventory of the runtime ABI and SDK domain, and so do the locks and
  event loops of its libraries.
- The POSIX and Linux interfaces built on calls, waits, wait sets and
  futexes belong to the compatibility personalities.

## References

- Arm Limited, *Arm Architecture Reference Manual for A-profile
  architecture*, DDI 0487, version M.d, 2026,
  <https://documentation-service.arm.com/static/6abbec2a6db85c5e6614a4a1>.
- H. Franke, R. Russell, M. Kirkwood, "Fuss, Futexes and Furwocks: Fast
  Userlevel Locking in Linux", Ottawa Linux Symposium 2002,
  <https://www.kernel.org/doc/ols/2002/ols2002-pages-479-495.pdf>.
- J. Liedtke, "Improving IPC by Kernel Design", SOSP 1993,
  <https://doi.org/10.1145/168619.168633>.
- The Linux man-pages project, *epoll(7)*,
  <https://man7.org/linux/man-pages/man7/epoll.7.html>.
- Trustworthy Systems, *seL4 Reference Manual*,
  <https://sel4.systems/Info/Docs/seL4-manual-latest.pdf>.
