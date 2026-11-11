---
features: none
---

# IPC requirements

The observable behaviour of the `ipc` component of the
[IPC and waits](../README.md) domain: endpoints with the receive thread that
each binds, `call`, `receive` and `reply`, the refusal of calls to oneself
and of cycles of calls, one-shot replies, badges, the transfer of a
capability with a message, the times of budget loans, the outcomes of a
call and the release of an endpoint. The rules that its code and tests
follow are in the [contract](contract.md). No feature document covers the
component, so the metadata lists none.

## Sources

- The messages of two words, the endpoint bound to one service thread that
  alone receives, the delivery of calls in the order in which they were made,
  the refusal of calls to oneself and of cycles of pending calls, one reply
  right for each delivered call that is used once, deadlines that settle
  before every other outcome, results that never change, one outcome for the
  death of a peer and the end of an endpoint, the copy and move of a
  capability that becomes visible with its message, and the loan of the
  caller's context, nested to a bounded depth within a ceiling and withdrawn
  before the caller wakes, take the rules of the prototype's IPC, capability
  transfer and synchronous budgets, which the
  [references](contract.md#references) of the contract list, with their host
  tests as the frozen [vectors](contract.md#legacy-test-vectors).
- The reply capability in the table of the server with the generation of
  the caller's reply record, results written at the end of a wait, the
  commit of a transfer at its delivery, the release of an endpoint at its
  last capability or with its owner in place of a closure, the forced kill
  as the cancellation of a call, the settlement of calls that wait through
  revoked capabilities, the refusal to receive while serving a call, and
  the time of a transition as an input are new, from the kernel's
  [IPC, notifications and waits](../../../architecture.md#ipc-notifications-and-waits)
  and its
  [execution model](../../../architecture.md#system-calls-and-the-abi); the
  [behaviour changes](contract.md#legacy-test-vectors) of the contract list
  where they differ from the prototype.
- The order of errors, the queues of endpoints, expiry first and the order
  of the outcomes of a call follow the
  [security model](../../../security.md#internal-choices), the badge its
  [sender identity](../../../security.md#unforgeable-authority), and the
  time of a transition its entry [ND-01](../../../security.md#nd-01); the
  classes of state follow the
  [SMP design rules](../../../conventions/smp.md#s5-state-field-tables).
- The handles, rights, lookups, reply capabilities and the table side of a
  transfer are those of the
  [capabilities](../../objects-capabilities/capabilities/requirements.md)
  component; the references and write sets those of the
  [objects](../../objects-capabilities/objects/requirements.md) component;
  the loans those of the
  [budget-ledger](../../scheduling/budget-ledger/requirements.md)
  component; blocking and readiness those of the
  [scheduler](../../scheduling/scheduler/requirements.md) component; and
  the wait records, deadlines and wait sets those of the
  [waits](../waits/requirements.md) component.

## Configurations

- **QEMU virt.** The machine `virt-8.2` without EL2 and EL3, with GICv2, one
  Cortex-A76 and 128 MiB of RAM at `0x4000_0000`: the machine of
  `cargo xtask qemu`, with the QEMU version that `toolchains.toml` pins for
  the host.
- **Raspberry Pi 5.** Only the 8 GB model is run on a board in release 0.1,
  with one of its four Cortex-A76 cores running.
- **Host.** The host tests of the module `ipc` of the core (planned) run on
  the development host and in CI, with the frozen vectors and the tests that
  the [contract](contract.md#testing-obligations) adds, each with the times
  that it passes.
- One CPU. The queues of endpoints are shared state and the reply records
  per-thread state, classified as for several CPUs also while one CPU runs;
  no requirement here covers calls between CPUs or the locks that provide
  the tokens.

## Requirements

### IPC-R01

**Endpoints and their receive thread.** The creation of an endpoint binds
one thread, named through a capability with CONTROL, as its receive thread,
and the binding never changes. Only that thread receives from the endpoint
or registers it in a wait set: any other thread, also one that holds a
capability to the endpoint with RECEIVE, is refused with `NotReceiver` and
changes nothing. The binding holds back no reclamation; once the bound
thread's process has ended, a call to the endpoint ends at once with
`PeerClosed`. The criterion: a receive by a thread of another process with
RECEIVE is refused, and a call to an endpoint whose bound thread has been
destroyed queues nothing.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `ipc::init_endpoint`, `ipc::receive`,
  `ipc::check_receiver` and `ipc::call` (planned).
- **Contract.** [Endpoint queues](contract.md#endpoint-queues) and
  [Calls and receives](contract.md#calls-and-receives).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `ipc-admission-4`, `ipc-admission-7`,
  `ipc-lifetime-2`, `ipc-lifetime-3` and `abi-ipc-authority-4` as host
  tests, and the host tests of the bound thread of the
  [contract](contract.md#testing-obligations). The creation of an endpoint
  from EL0 is shown by the tests of the creation component.

### IPC-R02

**Calls and receives.** A call sends two words through a capability with SEND
and, unless it ends at once, blocks until its outcome. A call that finds the
receiver waiting is delivered at once; otherwise it waits in the queue of its
endpoint, and the calls of an endpoint are delivered in the order in which
they were made. A receive through a capability with RECEIVE returns at once
with the first queued call, without blocking, or blocks until a call arrives.
The receiver gets the reply capability, the badge, the two words and the
handle of a transferred capability in its result registers; the caller gets
the two words of the reply. The criterion: three calls of two callers are
received in the order of the calls with their badges and words, also after
earlier calls have ended, and a receive before the call and one after it give
the same results.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `ipc::call`, `ipc::receive` and `ipc::has_call`
  (planned).
- **Contract.** [Calls and receives](contract.md#calls-and-receives) and
  [Endpoint queues](contract.md#endpoint-queues).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `ipc-admission-1`, `ipc-admission-2`,
  `ipc-admission-3`, `ipc-lifetime-4`, `abi-ipc-lifecycle-1`,
  `abi-ipc-lifecycle-2`, `abi-ipc-validation-4` and `abi-ipc-validation-6`
  as host tests, and the host tests of calls and receives of the
  [contract](contract.md#testing-obligations). The register form of the
  results at EL0 is shown by the QEMU tests, once the operations exist.

### IPC-R03

**Calls to oneself and cycles.** A call to an endpoint whose bound thread
is the caller is refused with `SelfCall`, and a call that would close a
cycle of calls, along the calls that are queued or delivered and the bound
threads of their endpoints, with `Cycle`; both are refused before any
write, change nothing and reach EL0 as one status, that of a call
dependency. A call whose deadline has expired is no part of a cycle. The
check takes at most the thread capacity less one steps, each of two reads.
The criterion: a cycle of three threads through queued calls is refused,
the same calls are accepted once one of them has timed out, and after
every write-back no thread has more than one outgoing call and the calls
form no cycle.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `ipc::call` (planned).
- **Contract.** [Calls to oneself and cycles](contract.md#calls-to-oneself-and-cycles)
  and [Determinism](contract.md#determinism).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `ipc-admission-4`, `ipc-admission-5`,
  `ipc-ordering-7` and `abi-ipc-authority-6` as host tests, and the host
  tests of calls to oneself and cycles of the
  [contract](contract.md#testing-obligations), among them the property test
  of the call graph against an independent model. That the graph stays
  acyclic is a property that the host tests sample and do not prove.

### IPC-R04

**One-shot replies.** Each delivered call gives its receiver one reply
capability, which holds the generation of the caller's reply record. A
reply with it ends the call, wakes the caller with the two words and
deletes the capability, so a second reply fails in its lookup. Every other
end of the call raises the generation, after which a reply with the
capability fails with `ReplyGone` and changes nothing. A server that closes
a reply capability whose call has not ended ends that call with
`PeerClosed`. The criterion: a reply after a timeout, a kill, a revocation
or a peer closure is `ReplyGone`, a second reply finds no capability, and
an old reply capability never completes a later call of the same caller.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `ipc::reply`, `ipc::receive` and `ipc::reply_deleted`
  (planned).
- **Contract.** [Replies](contract.md#replies).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `ipc-admission-6`, `ipc-ordering-2`,
  `ipc-ordering-3`, `ipc-ordering-5`, `abi-ipc-lifecycle-2`,
  `abi-ipc-lifecycle-3`, `abi-ipc-lifecycle-4`, `abi-ipc-lifecycle-6` and
  `abi-ipc-lifecycle-7` as host tests, and the host tests of replies of the
  [contract](contract.md#testing-obligations).

### IPC-R05

**Badges and sender identity.** The badge that a receiver gets is the badge
of the capability through which the caller called, 0 for a capability
without one, which the derivation that minted that capability set. No word
or other argument of a request changes it, and no other identity of the
caller is delivered. The criterion: a call whose words hold the badge of
another client's capability is delivered with the badge of the caller's own
capability and its words unchanged.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `ipc::call` and `ipc::receive` (planned).
- **Contract.** [Badges and sender identity](contract.md#badges-and-sender-identity).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `ipc-admission-1`, `ipc-admission-2` and
  `abi-ipc-lifecycle-1` as host tests, and the host tests of badges of the
  [contract](contract.md#testing-obligations), among them its
  counterexample.

### IPC-R06

**Capability transfer.** A call can carry one capability, copied or moved,
from a source with GRANT and the requested rights into the slot that the
receiver named when it started to receive. The capability and the message
become visible to the receiver in the same transition, its delivery; a copy
keeps the source and a move deletes it. A later outcome of the call does not
undo a delivered transfer. A source whose object has been released before
the delivery ends the call with `StaleReference` without a delivery, and the
receive takes the next call. A move of the capability through which the
call is sent is refused with `SelfTransfer`. The criterion: before its
delivery the receiver has no part of the message or of the capability, and
afterwards all of them, for a copy and a move, delivered at once and by a
receive.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `ipc::call` and `ipc::receive` (planned).
- **Contract.** [Capability transfer](contract.md#capability-transfer).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The host tests of transfer of the
  [contract](contract.md#testing-obligations), and the frozen vectors of
  transfers of the [waits contract](../waits/contract.md#legacy-test-vectors)
  whose entry is on this page, as host tests. That no reservation outlives
  the write set of its delivery is a property that the host tests check
  after every write-back.

### IPC-R07

**Budget lending.** A delivered call lends the caller's context, its own
budget or the one that it borrows, to the receiver, which runs on it within
the ceiling of its admission; nested calls lend the same context on, to a
depth of at most eight. A context has one holder that runs, and no credit
is copied. When a call ends, by any outcome, the context that it lent is
withdrawn from its receiver and from every thread further along the
delivered calls that holds it, before the caller is made ready; the loans
upstream stay, and so do the contexts that such a thread lent after it had
lost that one. A server that serves a call does not receive again until the
call ends (`ReplyPending`). The criterion: after the end of each kind of
call, no thread holds the context that the call lent and the caller is
ready, a context that such a thread lent later stays with its borrower, and
a ninth nested delivery is refused with `LoanDepth`.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `ipc::call`, `ipc::receive`, `ipc::reply`,
  `ipc::settle`, `ipc::reply_deleted` and `ipc::drain_step` (planned).
- **Contract.** [Budget lending](contract.md#budget-lending) and
  [Settlement of a call](contract.md#settlement-of-a-call).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `ipc-admission-3`, `ipc-lifetime-2` and
  `abi-ipc-lifecycle-3` as host tests, the host tests of lending of the
  [contract](contract.md#testing-obligations), and the vectors of loans of
  the [budget-ledger contract](../../scheduling/budget-ledger/contract.md#legacy-test-vectors)
  and of the [waits contract](../waits/contract.md#legacy-test-vectors)
  whose entry is on this page. The charges and effective classes of a loan
  are shown by the tests of the budget-ledger component.

### IPC-R08

**Deadlines and the order of outcomes.** A call or a receive with a
deadline that has passed when it is made ends at once with `Timeout` and
changes nothing; one whose deadline expires while it waits ends with
`Timeout` before the operation of the transition at that time. When one
transition brings several outcomes to a call, the first of timeout,
cancellation, revocation, peer closure and the reply decides, and an outcome
never changes afterwards. A timeout means that the caller stopped waiting
and undoes nothing that the server has received. The criterion: a reply,
a kill and a drain at the time of the deadline of the call each leave
`Timeout`, and a later event leaves an earlier outcome as it was.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `ipc::call`, `ipc::receive` and `ipc::settle` (planned).
- **Contract.** [Settlement of a call](contract.md#settlement-of-a-call),
  [Calls and receives](contract.md#calls-and-receives) and
  [Determinism](contract.md#determinism).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `ipc-closure-1`, `ipc-closure-4`,
  `ipc-ordering-1`, `ipc-ordering-2`, `ipc-ordering-4`, `ipc-ordering-5`,
  `abi-ipc-validation-3`, `abi-ipc-lifecycle-6` and `abi-ipc-lifecycle-9`
  as host tests, and the host tests of outcomes of the
  [contract](contract.md#testing-obligations). The expiry of deadlines by
  the timer is shown by the tests of the waits component.

### IPC-R09

**Peer closure and release.** No operation closes an endpoint. An endpoint
is released when its last capability is deleted, which no wait on it can
outlast, or in the destruction of its owner, which first ends every call
and receive on it with `PeerClosed`. The destruction of the process of the
bound thread ends the calls on its endpoints in the same way, and that of a
server ends the call that it serves, by the deletion of its reply
capability. After either, a new call or receive on the endpoint ends at
once with `PeerClosed`. The criterion: the queued calls, the waiting
receiver and the served call of an endpoint each end with `PeerClosed` in
the steps of the destruction, also with calls made between the steps.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `ipc::drain_step`, `ipc::reply_deleted` and `ipc::call`
  (planned).
- **Contract.** [Release and peer closure](contract.md#release-and-peer-closure).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `ipc-closure-1` to `ipc-closure-4`,
  `ipc-lifetime-1` to `ipc-lifetime-3`, `abi-ipc-lifecycle-5` and
  `abi-ipc-lifecycle-6` as host tests, and the host tests of release of the
  [contract](contract.md#testing-obligations). The steps of the destruction
  of a process are shown by the tests of the lifecycle component.

### IPC-R10

**Revocation of a waiting call.** A call or a receive that waits through a
capability of a subtree whose revocation becomes pending, its endpoint
capability or the source of the transfer of a queued call, ends with
`Revoked` in that transition, with its loans withdrawn, and its thread is
paused until the step of the revocation that removes that capability. The
criterion: a call through a derived send capability whose ancestor is
revoked ends with `Revoked` and its caller runs only after the removal of
the capability.

- **Examples.** None: no feature document covers the component.
- **Entry points.** `ipc::settle` (planned).
- **Contract.** [Settlement of a call](contract.md#settlement-of-a-call).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vector `abi-ipc-authority-7` as a host test, and
  the host tests of transfer and of outcomes of the
  [contract](contract.md#testing-obligations). The scan of the pending
  transition and the end of the pause are shown by the tests of the waits
  component.

### IPC-R11

**No change on failure.** Every error of the component leaves every field
of the kernel state as it was: a refused call, receive or reply queues,
delivers, installs, lends and writes nothing, and no refusal is counted.
The criterion: for each error of the contract, a call that gives it leaves
every field compared before and after unchanged.

- **Examples.** None: no feature document covers the component.
- **Entry points.** Every row of the
  [entry table](contract.md#entry-points).
- **Contract.** [Errors](contract.md#errors) and
  [Check and execute](contract.md#check-and-execute).
- **Specification.** None: the component has no specification.
- **Proof path.** None: the component has no proof path.
- **Evidence.** The frozen vectors `ipc-admission-4` to `ipc-admission-7`,
  `ipc-closure-3`, `abi-ipc-authority-1` to `abi-ipc-authority-3`,
  `abi-ipc-authority-6` and `abi-ipc-validation-5` as host tests, and the
  host test of each error of the
  [contract](contract.md#testing-obligations).

## Liveness, time and performance

- Every entry of the component runs to its end within the bounds of the
  [contract](contract.md#work-bounds); none waits, retries or takes a lock
  of its own, and the component has no long operation.
- The check for cycles of a call and the calls that a receive ends for a
  refused delivery are at most the thread capacity; a settlement makes at
  most eight withdrawals.
- A call or a receive with a deadline ends at the latest in the first
  transition at or after its deadline, which the timer of the scheduler
  starts. No requirement bounds when a server receives or replies, so a
  call without a deadline can wait as long as its server does.
- No requirement bounds the time that an entry takes.

## Scope

- One CPU. Calls between CPUs, the tokens and their locks are not covered.
- The wait records, the expiry of deadlines, notifications, wait sets and
  the pause of a revoked thread are not covered; they are the
  [waits requirements](../waits/requirements.md).
- The creation of an endpoint with its arguments, the steps of the
  destruction of a process and how they find the endpoints of a bound
  thread are not covered; the creation and lifecycle components compose
  the entries of this component and have their own requirements.
- The charges and effective classes of loans are the
  [budget-ledger requirements](../../scheduling/budget-ledger/requirements.md).
- Messages hold two words; bulk data goes through shared buffers, which are
  not covered. A fused reply and receive, direct handoff and guarantees of
  the latency of a call are not provided.
- A process has one thread; further threads of a process are not covered.
- Whether the dependency of calls that `Cycle` reports may reveal the state
  of threads that the caller cannot observe is not covered: the kernel
  claims no confidentiality.
- The operation numbers and numeric statuses of the ABI inventory are not
  covered.

## Contract sections without a requirement

- [Terms](contract.md#terms): definitions only.
- [Extractability](contract.md#extractability) states the module and its
  layer, which no requirement observes.
- [State fields](contract.md#state-fields) binds the code without an
  observable behaviour of its own.
- [Work bounds](contract.md#work-bounds) states the bounds that
  [Liveness, time and performance](#liveness-time-and-performance) relies
  on.
- [Open obligations](contract.md#open-obligations) has no row: the code of
  the component adds no obligation.
