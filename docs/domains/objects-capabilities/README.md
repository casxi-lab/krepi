# Kernel objects and capabilities

## Overview

The kernel objects and capabilities domain decides which objects the kernel
keeps, how they are named inside the kernel and by EL0, who pays for them,
how a change of kernel state is made all at once or not at all, how
processes and threads live and die, and how authority over objects is held,
passed on and withdrawn. It covers the object table with its pools, the
capacities that the boot fixes, the generations that tell the occupants of
a slot apart, the metadata quotas of calling domains, the write-set
transactions of the kernel's entries, the lifetimes of processes and
threads, the capability table of each process, and delegation and
revocation.

Three limits bound the domain. The kernel allocates no object memory after
boot: every pool and table has the capacity that the boot fixes, so what
EL0 can create is bounded by the capacity record and by the quotas that
divide it. A generation is 64 bits wide inside the kernel and 48 bits wide
in a handle. A slot of a pool retires after $2^{64} - 1$ occupants and is
not used again before the next boot. A slot of a capability table retires
after $2^{48} - 1$ capabilities of one process and stays retired while that
process occupies the process slot of the table; a new process counts the
generations of the table from 1. Revocation and destruction proceed in
steps of bounded work, so the time until they complete grows with the size
of what they withdraw, while every step stays short. A result on one CPU
does not show the order in which several CPUs reach shared objects.

The domain builds on others, listed in the
[subject-domain index](../README.md). The memory and address-spaces domain
holds the page ownership table from which the boot carves the pools, the
address spaces of processes, their ASIDs and the VM objects of their
regions; the boot and platform domain gives the CPU topology for the
per-CPU buffers; the IPC and waits domain completes the waits and calls
that a revocation or a destruction ends; the scheduling domain runs and
stops threads; the devices and DMA domain gives the meaning of the device
directory and of device grants; the EL0 services and storage domain builds
the root's grants and process creation on these objects. The
[objects](objects/requirements.md) component holds the kinds and pools, the
identities and generations, the capacity record, the metadata quotas and
the write-set transactions. The [capabilities](capabilities/requirements.md)
component holds the capability tables with their handles and rights, and
delegation and revocation. The [creation](creation/requirements.md)
component holds the creation of objects, and the
[lifecycle](lifecycle/requirements.md) component the lifetimes of
processes and threads.

## Conventions

- **Fixed capacities.** Every pool and table has the capacity that the boot
  fixes from the capacity record; a request beyond it fails before any
  write, and no pool borrows the slots of another.
- **References and handles.** Inside the kernel, objects refer to each other
  by pool, slot and generation; EL0 names objects only by handles of its
  own capability table. Neither ever names a later occupant of its slot.
- **Owners pay.** Every object is charged to the calling domain that created
  it, its owner, which never changes; the kernel's own objects are charged
  to the kernel domain.
- **Checks first.** An operation makes all its checks before its first
  write; after the checks only the capacity and quota failures that its
  contract lists can stop it, and then the state is that from before.
- **Errors in a fixed order.** When several checks fail, the error is the
  first in the order of the
  [security model](../../security.md#internal-choices), and a failure
  changes no state and counts nothing.
- **Rights only shrink.** Copying, deriving and transferring a capability
  can only reduce its rights, and no request can forge a handle.
- **Bounded steps.** Revocation and destruction run in steps of bounded
  work, with their progress stored in the object that they work on.

## Feature index

| Feature | Scope | Feature documents | Components |
| --- | --- | --- | --- |
| [Object table](#object-table) | The kinds of kernel objects, their pools and slots, and the records that are not objects | - | [objects](objects/requirements.md) |
| [Boot-time capacities](#boot-time-capacities) | The capacity record, its checks and defaults, and the storage that the boot carves for the object table | - | [objects](objects/requirements.md) |
| [Generations](#generations) | The generations of slots, their retirement, the references inside the kernel and the generations in handles | - | [objects](objects/requirements.md); [capabilities](capabilities/requirements.md), for handles |
| [Metadata quotas](#metadata-quotas) | Calling domains and owners, the seven quota items, split and returned limits, and the conservation of usages | - | [objects](objects/requirements.md) |
| [Write-set transactions](#write-set-transactions) | Check, then execute; the write set of an entry, its buffer, its write-back and its failure | - | [objects](objects/requirements.md) |
| [Process and thread lifetimes](#process-and-thread-lifetimes) | Creation, the states alive, dying, dead and reaped, exit reasons, destruction in bounded steps and reaping | - | [creation](creation/requirements.md), for creation; [lifecycle](lifecycle/requirements.md), for the states, exit reasons, destruction and reaping |
| [Capability tables](#capability-tables) | The capability table of each process, handles, rights and lookup | - | [capabilities](capabilities/requirements.md) |
| [Delegation and revocation](#delegation-and-revocation) | Copy, derivation and transfer of capabilities, badges, close, and revocation in two phases | - | [capabilities](capabilities/requirements.md) |

## Object table

**Description.** The kernel keeps eight kinds of object: processes,
threads, endpoints, replies, notifications, VM regions, the device
directory and device grants. Processes, threads, endpoints, notifications
and device grants each live in a pool of fixed capacity; the device
directory is the one slot of a pool of its own; a reply lives in the reply
record of the calling thread, and a VM region in the region table of its
process. EL0 holds every kind except VM regions through capabilities.
Capability table entries, wait records, ASID records, per-CPU records, the
progress of revocation and destruction, quota records and the capacity
record are kernel records, not objects. A slot is free, allocated or
retired; an allocated slot holds one object with its owner. An allocation
takes a free slot and a release frees it; a full pool refuses an
allocation, and no pool lends its slots.

**Design background.** Objects live in flat tables and refer to each other
by index, so that invariants quantify over whole tables, as Atmosphere
keeps its permissions (Chen et al. 2025). The kernel allocates no object
memory after boot, as seL4 hands out memory only through its untyped
objects (Klein et al. 2014). A process carries its own capability table,
quota record and address space, so that its authority, its accounting and
its memory have one owner.

**Consumers.** Every operation of the kernel that names an object: the
creation of objects, IPC, waits and notifications, the VM, device grants
and the lifecycle of processes; the root and the services, which hold
their objects through capabilities.

**Interface.** No operation of its own: objects are created, used and
released by the operations of the other features of this and other
domains. Inside the kernel, the object table resolves a reference to its
slot, chooses and occupies a slot and releases it
([entry points](objects/contract.md#entry-points)). A reference of another
pool and a stale reference are errors; a full pool is an error of shared
capacity.

**Prerequisites.** [Boot-time capacities](#boot-time-capacities),
[Generations](#generations); the
[objects contract](objects/contract.md#object-kinds-and-pools).

**Engineering notes.** A process has one thread, created with it, so the
thread pool holds no more allocated slots than the process pool. The
choice of a slot scans at most one pool. The slots of the pools are shared
state, classified in the [State fields](objects/contract.md#state-fields)
of the objects contract.

**Verification.** Invariants: the free, allocated and retired slots of a
pool add up to its capacity; an allocated slot holds an object of the kind
of its pool. Required counterexamples: an allocation from a full pool, a
pool whose every slot is reserved, a reference of another table.
Environments: host tests with the frozen vectors of the prototype's object
pool; QEMU runs that fill a pool and empty it again.

## Boot-time capacities

**Description.** A typed capacity record in the boot-bundle directory sets
the capacity of each pool, the capability slots and VM regions of each
process, the control reserve of each pool and the limits of VM and
loading. The kernel checks it once, as untrusted input, before it carves
any storage: every capacity is at least 1 and fits its width, there are at
least as many threads as processes, each control reserve fits its pool,
the storage fits the free memory, and there are no more processes than
ASIDs. A record that fails a check stops the boot with a fixed error, and
the kernel does not fall back to the defaults; without a record the kernel
uses the defaults of the board, which provide at least 64 processes and 256
threads. The boot then carves the storage of the object table from the
page ownership table, in eight allocations with an owner identity each,
and nothing is allocated afterwards.

**Design background.** Capacities fixed at boot let every bound of a kernel
path be a constant of the boot, and a record checked like any other input
keeps a damaged boot bundle from making the kernel misbehave. A control
reserve at the tail of each pool keeps slots for the root and for the
paths that stop processes, notify faults and clean up, so that recovery
does not depend on ordinary usage.

**Consumers.** The root, whose image ships the capacity record in the boot
bundle; every feature that creates objects; the memory domain, whose page
ownership table and table pools of address spaces share the free memory
with the object table.

**Interface.** The capacity record and its defaults; no operation. A record
that fails its checks is an error of the boot, which stops before any
entry from EL0.

**Prerequisites.** [Object table](#object-table); the
[page ownership](../memory/README.md#physical-page-ownership) and the
[ASIDs](../memory/README.md#asids) of the memory domain; the
[objects contract](objects/contract.md#capacity-record).

**Engineering notes.** The eight allocations add at most eight extents to
the page ownership table, whatever the capacities, which leaves most of its
160 extents to the table pools of address spaces and the pages of VM
objects. The per-CPU kernel stacks are part of the image. The capacity
record is shared state, read-only after boot, classified in the
[State fields](objects/contract.md#state-fields) of the objects contract.

**Verification.** Invariants: the capacities that the boot uses passed
every check; the eight allocations have distinct owner identities.
Required counterexamples: each check at its limit and one beyond, a record
that breaks two checks with different errors, a record whose storage does
not fit. Environments: host tests of the checks and of the default record
of each board; QEMU boots with the default record and with a record that
does not fit.

## Generations

**Description.** Every slot of a pool and of a capability table has a
generation, which starts at 1, stays while the slot is occupied and grows
by one when the slot is freed. A slot of a pool whose generation reaches
its maximum retires when it is freed and is not used again before the next
boot. The generations of a capability table count for the process that
occupies its process slot: a slot of the table that retires stays retired
while that process occupies the process slot, and a new process finds
every slot of the table at generation 1. Inside the kernel, a reference is
a pool, a slot and a 64-bit generation; a handle of EL0 is a 64-bit value
of the slot number of the caller's table and the generation of that slot,
and the value 0 is never a valid handle. A reference or a handle whose
generation is not that of its slot names nothing: its use fails with a
fixed error and changes no state.

**Design background.** A generation that never wraps keeps a stale name from
matching a later occupant of its slot, without a global counter that other
processes could observe. A capability in EL0 goes stale lazily: its entry
can outlive the object, and every lookup compares generations.

**Consumers.** Every holder of a handle or of a reference: EL0 programs,
which see stale handles fail, and the components of the kernel, which
follow references between objects.

**Interface.** The errors of a stale reference and of a stale handle. No
operation returns a generation or a slot of an object table: they are not
observable outputs of the
[security model](../../security.md#information-flow-boundary).

**Prerequisites.** [Object table](#object-table),
[Capability tables](#capability-tables); the
[objects contract](objects/contract.md#identities-and-generations) and the
[capabilities contract](capabilities/contract.md#handles).

**Engineering notes.** Retired slots are counted apart: free, allocated and
retired slots add up to the capacity. The generations of ASIDs are of the
memory domain and follow their own rule.

**Verification.** Invariants: no reference that kernel state holds has a
generation above the current generation of its slot, and where the two are
equal the slot holds a live object of its kind. Required counterexamples:
a reference of every representable slot number and generation, a slot
released at its largest generation. Environments: host tests with
generations set by the tests and the frozen vectors of the prototype.

## Metadata quotas

**Description.** The calling domain of an operation is the process of the
calling thread, and every object that it creates records it as its owner;
the kernel domain owns the root's process and thread and the device
directory. The quota record of a process holds, for each of seven items, a
limit, an ordinary usage and a control usage: child processes, endpoints,
notifications, capability slots, committed VM pages, private pages of
loaded images and page-table pages. A creation checks the caller's quota
before the shared capacity and before its first write. The limits of a
child are split from what its parent has left and return to the parent
when the child is reaped; the capability slots and page-table pages of a
process are given by its own fixed structures. The root starts with a
limit of child processes equal to the smaller of the ordinary capacities of
the process and the thread pool, and with limits of endpoints and
notifications equal to the ordinary capacities of their pools. For every
item, the usages of different calling domains never overlap and add up to
what is allocated.

**Design background.** Charging metadata to the creator, with the limits
carved down a tree of processes, bounds what any process can take without
a global allocator, and the conservation of usages makes that bound a
statement about the whole table. A parent is reaped after its children, so
their limits return to it before its own return to its owner, and no quota
moves to another owner.

**Consumers.** The root and the process manager, which split limits for the
services and workers that they create; the process service of each POSIX
environment, whose processes take their limits from it; every creation of
an object.

**Interface.** The limits that a creation gives the child, as arguments of
the creation; the quota error of the caller's own record, distinct from the
error of shared capacity.

**Prerequisites.** [Object table](#object-table),
[Process and thread lifetimes](#process-and-thread-lifetimes); the
[objects contract](objects/contract.md#metadata-quotas).

**Engineering notes.** Ordinary creation never uses the control reserve of
a pool. The limits of pages are not split from the free pages, so the page
limits of all processes together may exceed them, and running out of pages
is an error of shared capacity. The quota records are shared state,
classified in the [State fields](objects/contract.md#state-fields) of the
objects contract.

**Verification.** Invariants: the two statements of conservation, and for
each split item the sum of the limits of the live domains equal to the
root's starting limit. Required counterexamples: a charge beyond the limit,
a split beyond what is left, the return of the limits of a child with
objects left. Environments: host property tests against an independent
model of owners, limits and usages, including the destruction of a parent
with children.

## Write-set transactions

**Description.** An entry of the kernel first makes all its checks and
determines its write set, the object slots, capability entries, quota
records and queue links that it changes, each once, and writes no state
while it checks. It then copies the write set into the write-set buffer of
its CPU, changes the copies and writes them back; the write-back stores
distinct items in any order and cannot fail. After the checks, only the
capacity and quota failures that its contract lists and the
fault-injection points of test builds can stop an entry, and then the
buffer is discarded and the state is that from before. No operation copies
the whole kernel state, and no failure is counted.

**Design background.** The checking and executing phases follow those of
seL4, whose execution phase never fails (Klein et al. 2014). A write set
of a bounded number of items makes the failure of an operation cheap to
undo and lets the specification state the change of an operation as the
change of its write set.

**Consumers.** Every entry of the kernel that changes more than one item:
creation and destruction, IPC with capability transfer, revocation, the VM.

**Interface.** None of its own: the contract of every entry lists its
write set and the failures of its write phase.

**Prerequisites.** [Object table](#object-table),
[Metadata quotas](#metadata-quotas); the
[objects contract](objects/contract.md#write-set-transactions).

**Engineering notes.** The buffer holds 64 items, the largest write set of
an entry; a contract that needs more raises that constant. The buffer is
per-CPU and empty before and after every entry; on several CPUs an entry
holds the tokens of its write set from its checks to its write-back, as
the [State fields](objects/contract.md#state-fields) of the objects
contract classify them.

**Verification.** Invariants: a failed operation leaves every item as it
was; the write-back of distinct keys does not depend on its order.
Required counterexamples: a failure at each fault-injection point, a
creation of a pair whose second slot is missing. Environments: host tests
of every fault-injection point with the state compared field by field.

## Process and thread lifetimes

**Description.** A process is created by a holder of the creation right, a
right on a process, together with its first thread, and is charged to its
creator; the kernel creates the root at boot. A process moves through
alive, dying, dead and reaped, and its exit reason is exited, killed or
faulted. A dying process destroys its objects other than processes and
then its child processes, children before their parents and siblings in the
order of their creation; each step stays within its bound and stores its
progress in the dying process. A process becomes dead once its objects are
destroyed and its children reaped, and only its owner, which holds the
control right, reaps it; its exit reason and exit code stay readable until
then. A process destroyed because its owner is destroyed exits as killed,
and when its own exit and the destruction of its owner compete, the first
to arrive decides. A thread is reclaimed only after it runs on no CPU.
Processes and threads are distinct identities, and the threads of one
process form its POSIX thread group.

**Design background.** Destruction in bounded steps, with its progress in
the object, keeps every kernel path short however many objects a process
holds; the order of destruction follows that of cascading revocation. A
death notification is delivered once.

**Consumers.** The root and the process manager, which create and reap
services and workers; the process service of each POSIX environment, which
builds POSIX processes, their exit statuses and their waiting on them;
every holder of a process capability that observes it.

**Interface.** The operations that create processes, endpoints and
notifications with the creation right; the exit of a process by its own
thread; the forced kill and reaping with the control right; the queries of
state, exit reason, exit code, CPU time and fault record with the
observation right. The state of a process is a result, not an error;
acting on a process in the wrong state is an error.

**Prerequisites.** [Object table](#object-table),
[Metadata quotas](#metadata-quotas),
[Delegation and revocation](#delegation-and-revocation); the address spaces
of the [memory](../memory/README.md) domain and the waits of the IPC and
waits domain.

**Engineering notes.** A process has one thread, created with it, which is
a limit of the implementation and not of the identities. The capability
table of a dying process is closed in steps of at most as many entries as a
step of revocation removes
([teardown](capabilities/contract.md#teardown-of-a-table)).

**Verification.** Invariants: a process is reaped only after its children;
its exit reason never changes once set. Required counterexamples: a reap
by a holder without the control right, a reap of a process that is not
dead, an exit that competes with the destruction of the owner.
Environments: host tests of the lifecycle state machine; QEMU runs that
create, kill and reap processes.

## Capability tables

**Description.** Each process has a capability table of fixed size. An
entry records the type of its object, its rights, the reference of the
object and its derivation links; an entry for an endpoint also records the
sender badge. A handle names a slot of the caller's own table with the
generation of that slot, and the rights live in the entry, not in the
handle. A lookup checks the slot, its generation, the type and the
liveness of the object, and then the rights; a lookup that fails returns a
fixed error and changes no state. Each kind of object that EL0 holds has
its set of rights; the rights of a process include control, observation
and the creation right. A capability whose object has gone stays in its
slot, and fails every operation that uses its object, until its holder
closes it.

**Design background.** Handles that name slots of the caller's own table
depend only on the caller's state, so they leak nothing about other
processes ([internal choices](../../security.md#internal-choices)), and a
generation per slot makes a forged or stale handle fail as surely as one
out of range.

**Consumers.** Every operation of EL0 that names an object; the root, which
holds the first capabilities; the services, which hold their endpoints.

**Interface.** Handles as the arguments of operations; the errors of a slot
out of range, an empty slot, a stale generation, another type, an object
that is gone and missing rights, in this order
([lookup](capabilities/contract.md#lookup)).

**Prerequisites.** [Generations](#generations),
[Object table](#object-table); the
[capabilities contract](capabilities/contract.md#rights).

**Engineering notes.** A table has at most 65,536 slots, so a handle holds
a 16-bit slot number and a 48-bit generation. A lookup checks at most 16
ancestors of the capability for a pending revocation. The tables are
per-process state, classified in the
[State fields](capabilities/contract.md#state-fields) of the capabilities
contract.

**Verification.** Invariants: a lookup succeeds only for a filled slot of
the caller's table at its generation with the rights asked. Required
counterexamples: a forged handle, a handle out of range, a stale handle.
Environments: host tests with the frozen vectors of the prototype's
capability registry; QEMU runs of lookups from EL0.

## Delegation and revocation

**Description.** A capability is passed on by copy, which keeps its rights
and badge, and by derivation, which takes a subset of its rights; both need
the grant right and put the new capability into a free slot that the
caller names, as a child of its source in the derivation tree. The party
that mints an endpoint send capability chooses its badge once, which the
kernel stores and derivation keeps. A capability moves to another process
through IPC by the same rules, or through the creation of a child, which
puts initial capabilities into the child's table before the child first
runs, in slots that the rules of creation fix or that the creator names.
`close` removes one capability of the caller and leaves those derived from
it in place. `revoke` withdraws, in two phases, everything derived from a
capability, and the capability itself stays usable: once the revocation is
pending, every operation that resolves to a capability of the revoked
subtree fails, the subtree derives nothing more, and calls that wait through
it settle as revoked; the subtree is then removed in post-order in bounded
steps, mappings derived from it are removed and their TLB invalidation and
CPU references drained, and only then is the revocation complete. A
revocation reports completion, not a count.

**Design background.** A derivation tree with revocation follows the
capability derivation of seL4 (Klein et al. 2014); the two phases make the
withdrawal effective at once while the work that it implies proceeds in
bounded steps, as the security model's
[effective revocation](../../security.md#effective-revocation) requires.

**Consumers.** The root, which grants each domain the least authority it
needs and withdraws it; services that hand out endpoints with badges;
supervisors that withdraw the authority of a session.

**Interface.** Copy, derivation, `close` and `revoke` on handles of the
caller's table, each with the slot that it fills where it creates a
capability; the transfer of capabilities with a message
([entry points](capabilities/contract.md#entry-points)). A pending
revocation is a state of the capability that started it; operations on its
subtree fail with an error of their own.

**Prerequisites.** [Capability tables](#capability-tables),
[Write-set transactions](#write-set-transactions); the IPC of the IPC and
waits domain for transfer, and the device grants of the devices and DMA
domain, whose mappings a revocation drains; the
[capabilities contract](capabilities/contract.md#revocation).

**Engineering notes.** A step of revocation removes at most four
capabilities, each with a walk of the tree of at most 16 entries; the
progress stays in the capability that started the revocation and in the
subtree that remains, so an interrupt that is pending at a preemption point
ends the call, which is dispatched again and continues from it. A
capability has at most 16 live ancestors when it is made. The derivation
links and the revocation mark are per-process state, classified in the
[State fields](capabilities/contract.md#state-fields) of the capabilities
contract.

**Verification.** Invariants: a derived capability has at most the rights
of its source; after completion the subtree holds no usable capability and
no mapping derived from it. Required counterexamples: a derivation that
widens rights, a use of the subtree after the pending transition, a
completion with a mapping left. Environments: host tests with the frozen
vectors of the prototype's capability registry; QEMU runs of revocation
with long chains of derivation.

## Dependencies

| Feature | Depends on | Reason |
| --- | --- | --- |
| Object table | Boot-time capacities | The pools have the capacities of the record and the storage that the boot carves |
| Boot-time capacities | Physical page ownership, ASIDs | The storage comes from the page ownership table; the process capacity is bounded by the ASIDs |
| Generations | Object table | A generation belongs to a slot of a pool or of a capability table |
| Metadata quotas | Object table | Usages count the slots, entries and pages of owners |
| Write-set transactions | Object table, Metadata quotas | A write set holds slots and quota records |
| Process and thread lifetimes | Metadata quotas, Delegation and revocation | Creation charges the creator; destruction follows the order of cascading revocation |
| Capability tables | Generations, Object table | A handle carries the generation of its slot; an entry holds the reference of its object |
| Delegation and revocation | Capability tables, Write-set transactions | Derivation links live in table entries; each step is a transaction |

## Exclusions

- Call, receive and reply, one-shot replies, notifications, timeouts, wait
  sets and the settlement of waits, and the visibility of a transferred
  capability together with its message, belong to the IPC and waits
  domain; this domain gives the table side of a transfer.
- Priorities, budgets and their lending, preemption and the activation of
  threads on CPUs belong to the scheduling domain.
- VM regions and VM objects, address spaces, their table pools and ASIDs,
  and the counting of committed and loaded pages belong to the
  [memory and address spaces](../memory/README.md) domain; this domain
  gives the quota items that count them.
- The meaning of the device directory and of device grants, and the
  draining of a grant's mappings and interrupts, belong to the devices and
  DMA domain.
- Process IDs, process groups, sessions and POSIX job control belong to the
  process services of the EL0 services and storage and the compatibility
  domains; service-level objects, such as files, jobs and surfaces, to the
  services that validate them.
- The order in which several CPUs reach shared objects, cross-CPU
  revocation and the locks that provide the tokens belong to the multicore
  domain.

## References

- X. Chen, Z. Li, J. Zhang, V. Narayanan, A. Burtsev, "Atmosphere: Practical
  Verified Kernels with Rust and Verus", SOSP 2025,
  <https://mars-research.github.io/doc/2025-sosp-atmo.pdf>.
- G. Klein, J. Andronick, K. Elphinstone, T. Murray, T. Sewell, R. Kolanski,
  G. Heiser, "Comprehensive Formal Verification of an OS Microkernel", ACM
  Transactions on Computer Systems 32(1), 2014,
  <https://trustworthy.systems/publications/nicta_full_text/7371.pdf>.
