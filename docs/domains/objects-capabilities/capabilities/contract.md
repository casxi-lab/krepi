# Capabilities contract

This page governs the code of the `capabilities` component of the
[kernel objects and capabilities](../README.md) domain: the capability
table of each process, the handles that name its slots, the rights of each
kind of capability, the lookup of a handle, the derivation links between
capabilities, derivation, copy and badges, `close`, revocation in two
phases, the table side of the transfer of a capability, the teardown of
the table of a process that is destroyed, and the count of the
capabilities of each object. The objects that capabilities name, with
their references, owners and quotas, and the write-set transactions
through which the entries of this page change kernel state belong to the
[objects](../objects/contract.md) component; the creation of objects and
the lifetimes of processes and threads belong to the modules `creation`
and `lifecycle` (planned); the messages that carry capabilities belong to
the module `ipc` (planned). The observable behaviour that these rules
serve, with its evidence, is in the [requirements](requirements.md), the
other document of the component.

## Terms

- **Capability table.** The table of one process slot: `capability_slots`
  entries of the capacity record of the
  [objects contract](../objects/contract.md#capacity-record), numbered from
  0, in the storage that the boot carves for every slot of the process pool
  ([storage](../objects/contract.md#storage-carved-at-boot)). The table
  belongs to the process slot, and the generations of its slots count
  afresh for each process that occupies the process slot
  ([Handles](#handles)).
- **Entry.** A slot of a capability table with the fields of
  [Derivation links](#derivation-links). Its state is empty, usable,
  reserved for a copy, reserved for a move or retired; a **filled** entry
  is usable or reserved, and holds a capability.
- **Capability.** The authority of a filled entry: the kind and reference
  of its object, its rights and, for an endpoint, its badge.
- **Kind.** One of the seven kinds of object that EL0 holds through
  capabilities: process, thread, endpoint, reply, notification, device
  directory and device grant
  ([Object kinds and pools](../objects/contract.md#object-kinds-and-pools)).
- **Handle.** `capabilities::Handle` (planned): the 64-bit value that names
  a slot of the caller's own table with the generation of that slot
  ([Handles](#handles)).
- **Entry reference.** `capabilities::EntryRef` (planned): a process slot
  with the generation of the process that occupies it, a table slot and
  the generation of that table slot, 160 bits in all; the reference with
  table generation 0, which no slot has, is **none**. An entry reference is
  **live** while the entry of its table slot is filled with both of its
  generations, as [Handles](#handles) states. Entry references name entries
  inside the kernel, also entries of the tables of other processes, and
  are never handles.
- **Caller.** The process of the calling thread, whose table every handle of
  an operation names.
- **Derivation tree.** The relation that the derivation links of the filled
  entries form: an entry made from another by derivation, copy or transfer
  is its **child**, and that one its parent; **ancestors** and
  **descendants** follow. A filled entry without a filled ancestor is a
  **root entry**.
- **Nearest live ancestor.** The entry that the first live entry reference
  of the path of an entry names
  ([Derivation links](#derivation-links)).
- **Subtree of a revocation.** The descendants of the entry that a pending
  revocation started from, its **target**, which itself is not part of it.
- **Reservation.** A reserved entry: the receive slot of a pending transfer
  of a capability, which holds the capability that the transfer delivers
  and which no lookup reaches until its commit.
- **Step.** One transaction of a long operation of this page: a step of a
  revocation or a step of the teardown of a table, each within the bounds
  of [Work bounds](#work-bounds).
- **Count of capabilities.** For each object of a pool, the number of filled
  entries whose reference names it at its current generation
  ([Capability counts](#capability-counts)).

## Entry points

The entries of the core are in the module `capabilities` of `krepi-kernel`
(planned). Four of them are operations of the ABI inventory, in its
production range: `copy`, `derive`, `close` and `revoke` (planned), each
with the handles and slots of the caller's own table as arguments. Their
operation numbers and the numeric values of their errors belong to the
inventory. The other entries are called by the components that compose
them.

| Entry point | Kind | Called by | ABI operation | Rules |
| --- | --- | --- | --- | --- |
| `Tables::new` (planned) | Write entry, host-testable | The boot wiring, once, on the slice of the capability tables of the carved storage, before the kernel root exists | None | [Handles](#handles), [Derivation links](#derivation-links) |
| `Tables::lookup` (planned) | Read entry, host-testable | Every module of the core that takes a handle: `vm`, `waits`, `ipc`, `lifecycle`, `creation` and `dispatch` (planned), and the write entries of this page | None | [Lookup](#lookup), [Rights](#rights) |
| `Tables::derive` (planned) | Write entry on the copies of a write set, host-testable | `dispatch`, for the operation `derive` (planned) | `derive` | [Derivation and badges](#derivation-and-badges) |
| `Tables::copy` (planned) | Write entry on the copies of a write set, host-testable | `dispatch`, for the operation `copy` (planned) | `copy` | [Derivation and badges](#derivation-and-badges) |
| `Tables::close` (planned) | Write entry on the copies of a write set, host-testable | `dispatch`, for the operation `close` (planned); `ipc`, for a reply capability once its reply is sent | `close` | [Close](#close), [Capability counts](#capability-counts) |
| `Tables::revoke` (planned) | Long write entry, one step for each write set, host-testable | `dispatch`, for the operation `revoke` (planned), which composes with each step the drains of [Revocation](#revocation) | `revoke` | [Revocation](#revocation) |
| `Tables::install` (planned) | Write entry on the copies of a write set, host-testable | `creation`, for the first capability of a new object; the boot of the root by the kernel root, for the root's first capabilities; `ipc`, for the reply capability of a received call; and the creation of a device grant through the device directory, which the device-authority rules define (planned) | None | [Derivation and badges](#derivation-and-badges), [Capability counts](#capability-counts) |
| `Tables::reserve` (planned) | Write entry on the copies of a write set, host-testable | `ipc`, for a capability that a message carries, before the message is sent (planned) | None | [Transfer](#transfer) |
| `Tables::commit` and `Tables::abort` (planned) | Write entries on the copies of a write set, host-testable | `ipc`: `commit` at the commit point of the message, `abort` when the transfer ends without it (planned) | None | [Transfer](#transfer) |
| `Tables::teardown_step` (planned) | Write entry, one step of a long operation, host-testable | `lifecycle`, in the steps of the destruction of a process (planned) | None | [Teardown of a table](#teardown-of-a-table) |
| `Tables::count` (planned) | Read entry, host-testable | The write entries of this page, and the tests | None | [Capability counts](#capability-counts) |

## Extractability

The module `capabilities` of the core (planned), below `kernel/src/`
(planned), follows the
[provable Rust subset](../../../conventions/provable-subset.md): the
tables and their entries, the handles, the rights, the lookups, the
derivation links, derivation, copy, `close`, the steps of revocation and of
teardown, the table side of transfer and the counts. Its items are
`pub(crate)` except `Tables::new`, the row of the entry table that the boot
wiring calls, with the value types that it takes and returns
([provable core](../../../architecture.md#the-provable-core)). The module
is in layer 4 of the
[module order](../../../architecture.md#module-order-in-the-core): it
refers to the module `objects` and to the kernel root, and to no module of
its own layer or above. Its entries other than `Tables::new` receive the
one kernel root, by `&mut` for the write entries
([rule 3](../../../conventions/provable-subset.md#3-flat-relations-and-one-kernel-root)),
and the write-set buffer of the executing CPU by an explicit `&mut`
argument
([rule 8](../../../conventions/provable-subset.md#8-no-interior-mutability)).
The module defines no callback: an operation whose effect spans other
modules, such as the release of an endpoint, the settlement of a wait or
the drain of a device grant, is composed by `dispatch`, `ipc` or
`lifecycle`, and each entry of this page gives only the checks and the
writes of its own part.

The module has no adapter of its own. Its entries use the write-set buffer
that the adapter of the objects component lends, and the storage of the
tables is formed by the board's forming of the slices of the carved
storage; the objects contract lists both among its
[open obligations](../objects/contract.md#open-obligations). The contract
is written before its code, so this section lists no source paths; the
change that adds the module writes its `paths` block here.

## Handles

- **Format.** A handle is 64 bits: the low 16 bits are a slot number of the
  caller's table, and the high 48 bits the generation of that slot. The
  handle of the entry of slot $s$ at generation $g$ is $g \cdot 2^{16} + s$.
  A table has at most $2^{16}$ = 65,536 slots, the limit that the objects
  component checks for `capability_slots`.
- **Generations.** The generations of a table count for the process that
  occupies its process slot. Each entry records in its `epoch` the
  generation of the process for which its own generation counts, and an
  entry whose `epoch` is not the generation of the process that occupies
  the process slot is empty at generation 1 for that process, whatever it
  held for an earlier one. `Tables::new` makes every entry of every table
  empty at generation 1 with the epoch 0, which no process has. Filling an
  empty entry keeps its generation and sets its `epoch`, so the handle of a
  new capability carries the generation of its slot. Deleting a filled
  entry at generation $g < 2^{48} - 1$ empties it at $g + 1$; deleting it at
  $2^{48} - 1$ retires the slot, which stays retired while the same process
  occupies the process slot. For one process, a generation never wraps,
  never decreases and never repeats for a slot, so a handle that has gone
  stale never names a capability again. An entry reference carries the
  generation of the process as well, and a process generation is never
  reused for a process slot, so an entry reference that has gone stale
  never names a capability again within the boot.
- **Earlier processes.** A process slot is released only when the
  capability slots of its process count no usage
  ([release](../objects/contract.md#identities-and-generations)), as the
  [teardown](#teardown-of-a-table) of its table leaves them, so no filled
  entry has an epoch other than the generation of the process that
  occupies its process slot.
- **Value 0.** No slot has generation 0, so the handle 0, and every handle
  whose high 48 bits are 0, names no capability.
- **Own table.** A handle names a slot of the caller's own table only; the
  same value in another process names a slot of that process's table. The
  kernel returns a handle only for a capability that it puts into the
  caller's table, at the slot that the caller named, so the value depends
  only on the caller's table since the caller's process occupied its
  process slot, and on no earlier process of that slot
  ([internal choices](../../../security.md#internal-choices)).
- **Rights.** A handle carries no rights: the rights live in the entry.

## Rights

The rights of a capability are a mask of five bits. Each kind gives the
bits their meaning, and the rights of an entry hold only bits that its kind
defines:

| Kind | Bit 0, value 1 | Bit 1, value 2 | Bit 2, value 4 | Bit 3, value 8 | Bit 4, value 16 |
| --- | --- | --- | --- | --- | --- |
| Process | OBSERVE: query its state, exit reason, exit code and CPU time, and subscribe to its death notification | CONTROL: kill it, and reap it as its owner | GRANT | REVOKE | CREATE: the creation right of the creation component |
| Thread | OBSERVE: query its state | CONTROL: the operations of the lifecycle and scheduling components that change its execution, such as the interrupt of its wait | GRANT | REVOKE | - |
| Endpoint | SEND: `call` | RECEIVE: `receive` | GRANT | REVOKE | - |
| Reply | REPLY: the one reply | - | - | - | - |
| Notification | SIGNAL: signal it | WAIT: wait on it | GRANT | REVOKE | - |
| Device directory | OBSERVE: query the devices that it exposes | ISSUE: create device grants from it | - | - | - |
| Device grant | MAP: map its MMIO window | INTERRUPT: bind and acknowledge its interrupt | GRANT | REVOKE | - |

- **GRANT and REVOKE.** GRANT authorizes derivation, copy and transfer of
  the capability, and REVOKE the revocation of its descendants; neither
  implies any other right, so a capability with GRANT alone cannot observe
  or control its object.
- **Masks.** A rights mask that an operation takes is well formed when it
  is not 0 and has no bit above bit 4 (`InvalidRights`). A well-formed mask
  that holds a bit that the source does not hold, a bit that its kind does
  not define among them, is a missing right (`PermissionDenied`).
- **Rights of an operation.** Every operation that takes a handle needs the
  rights that its contract states, a constant of the operation and never an
  argument; the lookup checks that the entry holds all of them.
- **Reply.** A reply capability holds REPLY alone. Having no GRANT and no
  REVOKE, it is never derived, copied, transferred or revoked, and it has
  no descendants; it is deleted by its reply or by `close`.
- **Device directory.** The capability to the device directory holds
  neither GRANT nor REVOKE, so only the root, which receives it at boot,
  ever holds it. The operations of OBSERVE and ISSUE on the device
  directory and of MAP and INTERRUPT on a device grant are those of the
  device-authority rules of the devices and DMA domain; this page names
  their bits.
- **Encoding.** The names and bits are those of `capabilities::Rights`
  (planned); the values that reach EL0 through the ABI belong to the
  inventory.

**Control and observation of a process.** CONTROL on a capability to a
process authorizes the forced kill of the process, and its reaping by a
caller whose process is the owner of the process; no other right
authorizes either, and no right authorizes the reaping by another process.
OBSERVE authorizes the queries of the state, the exit reason, the exit code
and the CPU time of the process and the subscription to its death
notification; it authorizes no change of the process. CREATE is the right
that the creation component requires for the creation of processes,
endpoints and notifications. The lifecycle and creation components define
these operations and their states; this page fixes which right each needs.

## Lookup

`lookup(root, caller, handle, kind, rights)` gives the entry of a usable
capability of the caller's table, with the reference of its object and its
badge. It makes these checks in this order and returns the first error:

1. The slot number of the handle is below `capability_slots`
   (`InvalidHandle`).
2. The slot holds a usable capability: it is not empty, reserved or retired
   (`NoCapability`).
3. The generation of the slot equals that of the handle (`StaleHandle`).
4. The kind of the entry is the kind that the operation needs
   (`WrongType`).
5. The reference of the entry is live: `resolve` of the objects component
   gives its slot, and for a reply the reference of the calling thread is
   live (`StaleReference`). The generation of the reply record is checked by
   the IPC component when the reply is used.
6. The entry holds every right that the operation needs
   (`PermissionDenied`).
7. Neither the entry nor any live ancestor named by its path is marked for
   revocation (`RevocationPending`), except that `revoke` of the marked
   entry itself continues its revocation
   ([Revocation](#revocation)).
8. The entry is not the source of a pending move (`TransferPending`).

Checks 1 to 5 are the resolution of the handle, check 6 the rights and
checks 7 and 8 the state of the entry, in the order of errors of the
[security model](../../../security.md#internal-choices). `close` and
`revoke`, which do not use the object, skip checks 4 and 5, so a
capability whose object has gone can be closed and revoked; `close` needs
no right, so it skips check 6 as well. A lookup writes nothing.

The three kinds of bad handle each fail at a fixed check, without a change
of any field:

- **Forged.** A handle whose slot number is in range but whose slot holds
  no usable capability gives `NoCapability`, and one whose slot holds a
  capability of another generation gives `StaleHandle`; a value that the
  caller made up is one of these or out of range.
- **Out of range.** A handle whose slot number is not below
  `capability_slots` gives `InvalidHandle`.
- **Stale.** A handle of a capability that has since been deleted gives
  `NoCapability` while its slot is empty or retired, and `StaleHandle` once
  the slot holds another capability.

## Derivation links

Each entry of a table holds these fields, in this order; an entry
reference is 160 bits, a 32-bit process slot, the 64-bit generation of its
process, a 16-bit table slot and a 48-bit generation, and none is the
reference with table generation 0:

| Field | Width | Content |
| --- | ---: | --- |
| `state` | 8 bits | Empty, usable, reserved for a copy, reserved for a move or retired |
| `generation` | 48 bits | The generation of the slot, from 1 |
| `epoch` | 64 bits | The generation of the process for which `generation` counts, or 0 |
| `kind` | 8 bits | The kind of the object |
| `rights` | 8 bits | The rights mask of [Rights](#rights) |
| `revocation` | 8 bits | The revocation mark: clear, or removing while a revocation of the descendants of the entry is pending |
| `object` | 160 bits | The reference of the object, a 64-bit pool number, a 32-bit slot number and a 64-bit generation; for a reply, the reference of the calling thread |
| `badge` | 64 bits | The badge of an endpoint capability, 0 for none; for a reply, the generation of the reply record of the calling thread; 0 for the other kinds |
| `moving` | 160 bits | The reservation of a pending move of this entry, or none |
| `path` | `MAX_DEPTH` × 160 bits | The entry references of the ancestors of the entry when it was filled, nearest first, the unused ones none |
| `previous`, `next` | 2 × 160 bits | The neighbours of the entry in its sibling chain, or none |
| `first_child`, `last_child` | 2 × 160 bits | The ends of the chain of its children, or none |

The fields are those of `capabilities::Entry` (planned); an empty or
retired entry keeps only its `state`, `generation` and `epoch`, the others
none or 0. `MAX_DEPTH` is 16
([Derivation and badges](#derivation-and-badges)).

- **Path.** A capability that `install` puts into a table has an empty path.
  One made from a source by derivation, copy or transfer has as its path
  the entry reference of the source followed by the references of the path
  of the source that are live at that moment, in their order. A path never
  changes afterwards; its references go stale as their entries are deleted.
- **Ancestors.** The ancestors of a filled entry in the derivation tree are
  exactly the entries that the live references of its path name, nearest
  first. The **nearest live ancestor** of an entry is the first of them,
  and it has none when no reference of its path is live, as a root entry
  has none. The **depth** of an entry is the length of its path.
- **Sibling chains.** The filled entries whose nearest live ancestor is the
  same entry form one chain through `previous` and `next`, which that
  entry's `first_child` and `last_child` end. A new child joins the end of
  the chain of its source, so the chain holds the children in the order in
  which they were made. A chain whose entries have no live ancestor, which
  the close of a root entry leaves, belongs to no entry.
- **No parent field.** An entry stores no parent and no depth. The nearest
  live ancestor follows from the path, and the depth is its length, so a
  close rewrites neither the children nor the descendants of the entry.

## Derivation and badges

- **Two operations, one rule.** `derive(root, buffer, caller, source,
  rights, slot, badge)` and `copy(root, buffer, caller, source, slot)` put
  a new capability into the slot of the caller's own table that the caller
  names. Both need GRANT on the source, and the new capability is a child of
  the source, so a revocation of the source or of any of its ancestors
  withdraws it. `derive` gives the new capability the requested rights,
  which must be a well-formed mask of rights that the source holds; `copy`
  gives it the rights and the badge of the source.
- **Only attenuation.** Derivation, copy and [transfer](#transfer) never
  add a right: the rights of every filled entry are a subset of the rights
  of each of its ancestors. Installation is the only way a capability
  enters a table without a source, for the first capability of an object
  and for a reply.
- **Target slot.** The caller names the slot, and the kernel only checks
  that it is in range (`InvalidSlot`), holds no capability
  (`SlotOccupied`) and has not retired (`GenerationExhausted`).
- **Badges.** A badge is a nonzero 64-bit value of an endpoint capability,
  which the party that mints an endpoint send capability chooses
  ([internal choices](../../../security.md#internal-choices)). `derive`
  with a nonzero badge sets it on the new capability, which requires an
  endpoint capability without a badge as the source and SEND among the
  requested rights (`InvalidBadge`); `derive` with the badge 0 keeps the
  badge of the source. Derivation, copy and transfer keep a badge, and no
  operation changes it, so a badge is set once. `install` puts no badge,
  and the `badge` field of a reply holds the generation of its reply
  record instead.
- **Depth.** The path of a new capability holds at most `MAX_DEPTH` =
  16 references, `capabilities::MAX_DEPTH` (planned); a derivation, copy or
  transfer whose new path would be longer is refused (`DepthExceeded`).
  The limit allows the chain of twelve capabilities of the frozen vectors,
  whose last has eleven ancestors, and it bounds the checks of the
  ancestors in a lookup and the walk down a subtree in a revocation. A
  closed ancestor does not count, since its reference has gone stale.
- **Installation.** `install(root, buffer, process, slot, kind, reference,
  rights, record)` puts the capability to a live reference of the kind,
  with the rights that its caller gives, a well-formed mask of bits that
  the kind defines, into a slot of the table of the process: a root entry,
  without badge. For a reply, the reference is that of the calling thread,
  and `record` is the generation of its reply record, which the IPC
  component gives and the entry keeps in its `badge` field; for every other
  kind, `record` is 0 (`InvalidBadge`). Its callers name the slot as their
  own rules state: the creation operation and the receive of a call take
  the slot from their caller, and the boot of the root fixes the slots of
  the root's first capabilities.
- **Order of checks.** `derive` checks its rights mask (`InvalidRights`)
  and the range of its target slot (`InvalidSlot`); then its source, as
  [Lookup](#lookup) states, with GRANT and the requested rights; then
  `InvalidBadge`, `SlotOccupied` and `GenerationExhausted`, after the state
  of the source; and last `DepthExceeded`. `copy` and `reserve` check in
  the same order, without a badge, and `copy` without a mask. `install`
  checks its rights mask, which holds only bits of the kind
  (`InvalidRights`), the range of its slot (`InvalidSlot`), its reference
  with `resolve` (`WrongPool`, `StaleReference`), and then `InvalidBadge`,
  `SlotOccupied` and `GenerationExhausted`.

Each of these entries charges one capability slot to the process of the
table, with `QuotaRecord::charge` of the
[objects component](../objects/contract.md#metadata-quotas), and, for
every kind but a reply, adds one to the count of its object
([Capability counts](#capability-counts)), in the write set that fills
the entry. The charge never fails, since the limit of capability slots is
the size of the table and the slot is empty.

## Close

- **Effect.** `close(root, buffer, caller, handle)` deletes one capability
  of the caller's table. It needs no right. The entry is emptied at its next
  generation, or retired, as [Handles](#handles) states; the process of the
  table is credited one capability slot; and when the entry is not a reply
  and its reference is live, the count of its object loses one.
- **Descendants stay.** The children of the closed entry take its place in
  its sibling chain, in their order. Their paths are not rewritten: the
  reference of the closed entry in them has gone stale, so their nearest
  live ancestor becomes the nearest live ancestor of the closed entry. Every
  descendant keeps its rights and stays a descendant of the ancestors of
  the closed entry, so a revocation of any of them still withdraws it.
- **Order of siblings.** The children that take the place of a closed entry
  keep the position that it had among its siblings. A sibling chain
  therefore holds its capabilities in the order of a post-order reading of
  the derivation tree by creation, with the closed entries left out; this
  page reads the siblings "in the order in which their derivations were
  made" of the cascading revocation of the
  [security model](../../../security.md#internal-choices) as this order.
- **Stale capabilities.** A capability whose object has been released
  stays in its slot, and fails every lookup that uses its object
  (`StaleReference`), until its holder closes it.
- **Last capability.** When the close deletes the last capability of the
  current generation of an endpoint or a notification, the same write set
  releases the object and credits its owner
  ([Capability counts](#capability-counts)). For a reply capability, the
  composing operation adds the part of the IPC component for the call that
  waits for the reply.
- **Refused.** A close of an entry of the subtree of a pending revocation,
  or of its target, is refused (`RevocationPending`), and so is a close of
  the source of a pending move (`TransferPending`).

The prototype kept a closed capability with descendants as a tombstone;
here a close always frees the slot.

## Revocation

`revoke(root, buffer, caller, handle)` withdraws every descendant of a
capability of the caller that holds REVOKE, in two phases. Each item below
is one rule of it.

- **Subtree.** The subtree of the revocation is every descendant of the
  target, through every table. The target itself is not part of it: it
  stays in its slot and, once the revocation is complete, is usable and can
  derive again. A holder withdraws its own capability with `close`.
- **Pending.** If the target has no child, `revoke` completes at once.
  Otherwise its first transition sets the revocation mark of the target to
  removing. From that write-back on, every operation that resolves to a
  capability of the subtree fails (`RevocationPending`), since its lookup
  finds the mark on a live ancestor, so the subtree derives nothing more and
  no reservation of it commits; affected execution is paused, since every
  call that waits through a capability of the subtree settles, in that same
  transition, as revoked, with an error of its own and its thread paused, as
  the waits and IPC components state, and a budget loan of such a call
  settles as a whole. While the mark is set, the target itself accepts only
  a `revoke` that continues the revocation; its lookup by any other
  operation, `close` and every derivation, copy and transfer from it among
  them, fails (`RevocationPending`), so no new capability joins the subtree.
- **Drains.** Each removal of a capability of the subtree, in the steps
  below, carries in its write set the part of the component of its object
  that the removal needs: for a device grant whose holder mapped its MMIO
  window or bound its interrupt, the masking and draining of the interrupt,
  the removal of the mappings and the completed TLB invalidation of the
  device-authority rules; for a reservation, the end of its pending
  transfer ([Transfer](#transfer)), which releases the receive slot and its
  charge and, when the source of a move is outside the subtree, ends the
  move; for the last capability of an endpoint or a notification, its
  release ([Capability counts](#capability-counts)). The source of a move
  inside the subtree is removed too and never restored. In release 0.1 the
  only mappings derived from capabilities are the MMIO windows of device
  grants.
- **Completion.** The revocation is complete when the subtree is empty and
  every drain that its removals carried has completed: no page table holds
  a mapping derived from the subtree, the TLB invalidation of every removed
  mapping has completed and no CPU holds a reference to what was removed.
  Only then does a step clear the mark, in its write set: the step that
  removes the last capability of the subtree, or one that finds the subtree
  empty, as the teardown of other tables can leave it; and `revoke` reports
  completion
  ([effective revocation](../../../security.md#effective-revocation)). With
  one CPU, a TLB invalidation completes on the executing CPU within the
  step that removes its mapping.
- **Order and steps.** After the pending transition the subtree is removed
  in steps, each a transaction. A step removes at most `REVOKE_BATCH` = 4
  capabilities, `capabilities::REVOKE_BATCH` (planned): each time it walks
  from the target by `first_child` down to an entry without children and
  removes that leaf. So the subtree is removed in post-order, children
  before parents and siblings in the order of their chain, as the security
  model's cascading revocation states. A removal deletes the leaf as
  `close` does, which unlinks it from the chain of its nearest live ancestor
  and credits the process of its table. A chain of eight capabilities below
  a target takes at least two steps.
- **Continuation and progress.** The progress of a revocation is the mark of
  its target and the capabilities that the subtree still holds; no other
  field is kept, and both are in the tables. Between two steps is a
  preemption point of the
  [execution model](../../../architecture.md#system-calls-and-the-abi):
  when an interrupt is pending there, `revoke` returns without a result,
  the interrupted call is dispatched again from the saved user registers,
  repeats its checks and, finding the mark of its target set, continues
  with the next step. Another `revoke` of the same target continues the same
  work. A revocation pending on an entry inside the subtree of another is
  taken over by the outer one, whose steps remove that entry too; a
  continuing call of the inner one then fails at its checks.
- **Result.** `revoke` reports completion and returns no count: the number
  of capabilities removed depends on derivations made by other processes,
  which are not a source of the observable outputs of the caller
  ([information flow](../../../security.md#information-flow-boundary)). A
  caller that finds the revocation complete, or the target without
  children, gets the same result.

## Transfer

The capability that a message carries moves through three entries, which
the IPC component composes with its message: the data and the capability
become visible together at its commit point, and a failure before it
restores a moved source.

- **Reservation.** `reserve(root, buffer, sender, source, rights, mode,
  receiver, slot)` checks the source of the sender's table as a derivation
  does, with GRANT and the requested rights, and puts into the receive slot
  of the receiver's table, which the receiver named when it waited to
  receive, a reserved entry: a child of the source with the requested
  rights and the badge of the source, charged to the receiver and counted
  for its object. The mode is copy or move, and the `state` of the reserved
  entry records it; a move also records the reservation in the `moving`
  field of the source, which hides the source from every lookup
  (`TransferPending`). No lookup reaches a reserved entry
  (`NoCapability`), so the receiver does not see the capability before the
  commit, and the slot is not free for another capability
  (`SlotOccupied`).
- **Commit.** `commit(root, buffer, reservation)` makes the reserved entry
  usable and gives the receiver's handle of it. For a move it then deletes
  the source as `close` does, so the received capability takes the place of
  the source among its siblings. The `state` of the reservation tells a
  move from a copy, and the source of a move is the entry that the first
  reference of its path names. A commit refuses a reservation that is no
  longer reserved at its generation, or a reservation for a move whose
  source is no longer live with the reservation in its `moving` field
  (`TransferGone`), and a reservation in the subtree of a pending
  revocation (`RevocationPending`). A reservation for a copy whose source
  has been closed commits all the same, below the nearest live ancestor
  that it then has.
- **Abort.** `abort(root, buffer, reservation)` deletes a reservation that
  is still reserved at its generation, crediting the receiver and taking it
  from the count of its object, and, for a move whose source is live,
  clears the `moving` field of the source, which is usable again with its
  original rights. It returns `aborted`, or `gone` without a change when
  the reservation no longer exists; it never fails, never restores a source
  that has been deleted and never touches a slot that another capability
  has taken since.
- **Revocation.** A reservation is a descendant of its source, so it is in
  the subtree of every revocation of the source or of an ancestor: from the
  pending transition its commit is refused, and a step removes it as a
  leaf, as an abort does; afterwards its abort returns `gone` and its commit
  fails (`TransferGone`).
- **Teardown.** The teardown of the receiver's table removes a reservation
  as an abort does. The teardown of the sender's table deletes the source of
  a move as `close` does, so the reservation stays until its abort below
  the nearest live ancestor of the source, or as a root entry when the
  source had none, and a revocation of that ancestor still removes it; its
  commit fails (`TransferGone`), since the source of its move is no longer
  live.

The reservation is named by its entry reference, which the IPC component
keeps with its message; it is never a handle of EL0.

## Teardown of a table

`teardown_step(root, buffer, process, next)` closes the table of a process
that is destroyed, in steps, for the lifecycle component, which stores the
progress `next`, a slot number, in the dying process and starts from 0. A
step takes the slots from `next` up to, but not including,
`next + REVOKE_BATCH`, within the table, in ascending order: it deletes each
usable entry as `close` does, without its refusals for a pending
revocation or a pending move, and each reservation as `abort` does; empty
and retired slots it passes. When one of these slots is the target of a
pending revocation, the step instead makes one step of the revocation of
the lowest such slot and returns `next` unchanged, so the slots are closed
by a later step once that revocation is complete. The step returns the next
progress, or completion after the last slot.

- **Outward descendants stay.** Deleting an entry of the dying table moves
  its children into its place, so the capabilities that it gave to other
  processes keep their rights and their ancestors in other tables.
- **Entries of other subtrees.** An entry of the dying table that is in the
  subtree of a revocation pending elsewhere is closed all the same; its
  children stay in that subtree.
- **End.** After the last step every slot of the table is empty or retired,
  and the capability slots of the process count no usage, which the release
  of its process slot requires
  ([release](../objects/contract.md#identities-and-generations)).

This page gives the step; the lifecycle component orders it among the
other steps of the destruction of a process.

## Capability counts

- **Counts.** Every slot of the process, thread, endpoint, notification,
  device-directory and device-grant pools holds, beside the fields of its
  object, the count of capabilities of the object at its current
  generation: the number of filled entries, usable or reserved, whose
  reference names the slot at that generation, replies left out. A reply
  capability counts for no object, though its `object` field names the
  calling thread. A free slot has the count 0, and the release of a slot
  clears its count with its other fields, so a capability of an earlier
  generation is never counted.
- **Changes.** Filling an entry other than a reply by `install`, `derive`,
  `copy` or `reserve` adds one to the count of its object; deleting a filled
  entry other than a reply whose reference is live, by `close`, a step of
  revocation or of teardown, `abort`, or the commit of a move, takes one
  away. A deletion of an entry whose reference has gone stale, or of a
  reply, changes no count. `commit` of a reservation changes none either.
- **Bound.** A count is at most the number of entries of all tables, at
  most $2^{32} \cdot 2^{16}$, so it fits its 64 bits, and the only entries
  that change it are those of this page.
- **Release at the last capability.** When a deletion makes the count of an
  endpoint or a notification 0, the same write set releases the object,
  with `ObjectTable::release`, and credits its owner one item of endpoints or
  notifications, with `QuotaRecord::credit`
  ([metadata quotas](../objects/contract.md#metadata-quotas)); the
  operation that composes the deletion adds the part of the IPC and waits
  components for the queue and the waits of the object. The other kinds are
  released by their own components, whatever their count: processes and
  threads when they are reaped, device grants by the device-authority rules,
  and the device directory never. A count holds back no reclamation.
- **Query.** `count(root, reference)` gives the count of a live reference,
  and `resolve`'s error for another.

## Errors

| Error | Rule broken | Entries | Place in the order of errors |
| --- | --- | --- | --- |
| `InvalidConfiguration` of the objects component | Storage of another size than the process capacity times `capability_slots` entries | `Tables::new` | At boot |
| `InvalidRights` | A rights mask of 0, or with a bit above bit 4; for `install`, with a bit that the kind does not define | `derive`, `reserve`, `install` | The form of the register arguments |
| `InvalidSlot` | A target or receive slot, or the progress of a teardown, not below `capability_slots` | `derive`, `copy`, `install`, `reserve`, `teardown_step` | The form of the register arguments |
| `InvalidHandle` | A handle whose slot number is not below `capability_slots` | `lookup` and every entry that takes a handle | Handle resolution: the range |
| `NoCapability` | A handle of a slot that is empty, reserved or retired | `lookup` and every entry that takes a handle | Handle resolution: the empty slot |
| `StaleHandle` | A handle whose generation differs from that of its slot | `lookup` and every entry that takes a handle | Handle resolution: the generation |
| `WrongType` | An entry of another kind than the operation needs | `lookup` | Handle resolution: the type |
| `WrongPool` of the objects component | A reference of another pool than its kind's | `install`, `count` | Handle resolution: the type |
| `StaleReference` of the objects component | A reference that is not live | `lookup`, `derive`, `copy`, `reserve`, `install`, `count` | Handle resolution: the liveness of the object |
| `TransferGone` | A reservation that is no longer reserved at its generation, or a reservation for a move whose source is no longer live with it in its `moving` field | `commit` | Handle resolution: the liveness of the reservation |
| `PermissionDenied` | A right that the operation needs and the entry lacks: GRANT, REVOKE, a requested right, or a right of the operation | `lookup`, `derive`, `copy`, `revoke`, `reserve` | Rights |
| `RevocationPending` | An entry, or a live ancestor, whose revocation mark is set, other than for a `revoke` that continues the revocation of the entry | `lookup`, `derive`, `copy`, `close`, `revoke`, `reserve`, `commit` | Object state |
| `TransferPending` | The source of a pending move | `lookup`, `derive`, `copy`, `close`, `revoke`, `reserve` | Object state |
| `InvalidBadge` | A badge set on a source that is not an endpoint capability without a badge, or without SEND among the requested rights; for `install`, a nonzero record for another kind than a reply | `derive`, `install` | Object state |
| `SlotOccupied` | A target or receive slot that holds a capability | `derive`, `copy`, `install`, `reserve` | Object state |
| `GenerationExhausted` | A target or receive slot that has retired | `derive`, `copy`, `install`, `reserve` | Object state |
| `DepthExceeded` | A new path longer than `MAX_DEPTH` | `derive`, `copy`, `reserve` | Shared capacity |

- **Order.** Each entry checks in the order that [Lookup](#lookup) and its
  rule section state, and returns the first error. The places of the last
  column are those of the order of errors of the
  [security model](../../../security.md#internal-choices), and within one
  place the order of the rows holds: a derivation checks its rights mask
  before the range of its target slot, and, in the state of its entries,
  `RevocationPending`, `TransferPending`, `InvalidBadge`, `SlotOccupied` and
  `GenerationExhausted` in this order.
- **Shared capacity.** The depth of a new capability counts the live
  ancestors of its source, which may be in the tables of other processes and
  go stale as their holders close them, so `DepthExceeded` is an error of
  shared capacity, one of the declared global flows of the
  [information-flow boundary](../../../security.md#information-flow-boundary).
  The charge of a capability slot is the caller's quota and never fails.
- **No change on failure.** No error changes state: an entry of this page
  that returns an error leaves every field of the kernel state as it was,
  the copies in the write set included, and writes no counter; a composing
  operation that meets an error discards its buffer, so the kernel state
  after any failed operation equals the state before it. There is no
  exception. The result registers of a failed system call follow the
  [observable outputs](../../../security.md#observable-outputs) of the
  security model. `abort` has no error: a reservation that no longer exists
  is its result `gone`.
- **Names.** The names are those of this contract; the numeric values of the
  errors that reach EL0 belong to the ABI inventory.

The prototype's capability registry had sixteen errors. Here:

| Prototype error | Here |
| --- | --- |
| `InvalidConfiguration` | Moved to the objects component: the slots of a table are `capability_slots` of the capacity record, whose checks refuse 0 and more than 65,536 |
| `InvalidRights` | Kept, for a rights mask of 0 or with a bit above bit 4 |
| `Object(_)` | Not kept as a wrapper: the errors of the objects component that this page meets, `WrongPool` and `StaleReference`, are returned as they are |
| `WrongRegistry` | Not applicable: there is no registry number, and each process has its table |
| `StaleSpace` | Not applicable: there is no namespace receipt; a table belongs to its process slot |
| `UnknownCaller` | Not applicable: every process has its table, and the caller is the process of the running thread |
| `UnknownToken` | Replaced by `InvalidHandle`, `NoCapability` and `StaleHandle`: a handle out of range, a slot without a usable capability and a generation that differs |
| `DuplicateOwner` | Not applicable: a table is never registered; it is that of its process slot |
| `SpaceCapacity` | Not applicable: the number of tables is the process capacity of the objects component |
| `NodeCapacity` | Not applicable: there is no global pool of nodes; a filled target slot is `SlotOccupied` |
| `QuotaExceeded` | Replaced by `InvalidSlot` and `SlotOccupied`: the caller names the slot, and the quota of capability slots is the size of the table, so its charge never fails |
| `GenerationExhausted` | Kept, for a target slot that has retired |
| `TokenExhausted` | Not applicable: there is no global token; each slot retires on its own |
| `PermissionDenied` | Kept, for missing rights |
| `InvalidState` | Replaced by `RevocationPending` and `TransferPending` for the state of an entry; the states of the caller and of the object are not checks of this page, and a commit of a transfer that no longer exists is `TransferGone` |
| `WrongType` | Kept, for an entry of another kind |

## Check and execute

- `lookup` and `count` write nothing.
- `Tables::new` checks that its storage holds `capability_slots` entries
  for every slot of the process pool (`InvalidConfiguration` of the objects
  component) before its first write, then writes every entry empty at
  generation 1. It runs once at boot and cannot fail after its check.
- `derive`, `copy`, `install`, `reserve`, `close` and `commit` make all
  their checks, the lookup of their handle, the ancestors of the new path
  and the target slot among them, before their first write, and then change
  only the copies in the write set of their caller.
- `revoke` makes the checks of its lookup before the pending transition,
  and a call dispatched again after a preemption point repeats them before
  its next step. A step determines the capabilities that it removes, with
  their walks and the nearest live ancestors that it unlinks them from,
  before its first write.
- `teardown_step` checks its progress before its first write; its callers
  make the checks of the destruction.
- `abort` checks that the reservation is reserved at its generation before
  its first write, and writes nothing when it is not.
- The write phase of every entry of this page allows only `WriteSetFull` of
  `stage`, which the write sets below never reach, `QuotaExceeded` of the
  charge of a capability slot, which an empty target slot excludes, and the
  fault-injection points of test builds (`InjectedFault`), each of which
  discards the buffer and leaves the state from before the entry
  ([write-set transactions](../objects/contract.md#write-set-transactions)).

The write set of each write entry of this page, by the items of the
objects contract: an entry of a table, an object slot with its count, the
counts of a pool and a process slot with its quota record:

| Entry | Write set | Items |
| --- | --- | ---: |
| `Tables::new` | Every entry of every table, in place, at boot, before any token exists | - |
| `install` | The entry; the object slot; the process slot of the table | 3 |
| `derive`, `copy`, `reserve` | The new entry; the source, whose `last_child` changes and, for a move, its `moving`; the former last child of the source; the object slot; the process slot of the table that receives | 5 |
| `close` | The entry; its previous and next siblings; its first and last children; its nearest live ancestor; the object slot; the process slot of the table; for the last capability of an endpoint or a notification, the counts of its pool and the process slot of its owner | 10 |
| `revoke`, pending transition | The target | 1 |
| `revoke`, a step | For each removed capability: the entry; its previous and next siblings; its nearest live ancestor; the object slot; the process slot of its table; the counts of the pool and the process slot of the owner of its object | 32 |
| `commit` | The reservation; for a move, the write set of the close of the source | 9 |
| `abort` | The reservation; its previous and next siblings; its nearest live ancestor, which is the source of a move while that source is live; the object slot; the counts of its pool and the process slot of the owner of its object; the process slot of the receiver | 8 |
| `teardown_step` | The write sets of at most `REVOKE_BATCH` closes and aborts, with the process slot of the dying table once; or the write set of one step of a revocation | 37 |

The largest write set of this page, 37 items, is within $W$ = 64 of the
objects contract, which leaves at least 27 items for the parts that the
components of a released object, of a settled wait and of a drain add to
the same operation; their contracts keep their parts within that rest. The
pending transition of a revocation writes one item of this page; the
settlement of the waits through the subtree in the same transition is the
part of the waits and IPC components, with the bounds of their contracts.

## Work bounds

- `Tables::new` writes each entry of each table once: the process capacity
  times `capability_slots` entries, at boot.
- `lookup` reads the entry, at most `MAX_DEPTH` = 16 entries named by its
  path, each for its epoch, generation and revocation mark, and one slot of
  the object table: at most 17 entries and one slot.
- `derive`, `copy` and `reserve` make the lookup of their source, form the
  new path from the same at most 16 references, read the target slot and
  write the 5 items of their write set.
- `install` reads the target slot and one slot of the object table and
  writes 3 items.
- `close` makes its lookup, reads at most 16 entries to find its nearest
  live ancestor and writes at most 10 items.
- `revoke` is a long operation. Its pending transition writes the mark.
  Each step removes at most `REVOKE_BATCH` = 4 capabilities; for each it
  walks at most 16 entries down from the target, since every descendant of
  the target has the target and its ancestors in its path of at most 16,
  and reads at most 16 entries of the path of the leaf for its nearest live
  ancestor, so a step reads at most 128 entries and writes at most 32
  items. The preemption points are after the pending transition and
  between two steps; the progress is the mark of the target and the
  subtree that remains, in the tables. The number of steps grows with the
  subtree, at most the entries of all tables divided by 4, rounded up.
- `commit` reads at most 17 entries, its reservation, its source and the
  ancestors of the source, and writes at most 9 items; `abort` reads at
  most 17 and writes at most 8.
- `teardown_step` examines at most `REVOKE_BATCH` slots and makes at most
  that many closes and aborts, or one step of a revocation, and writes at
  most 37 items. The destruction of a process is the long operation: its
  preemption points are between two steps, and its progress, the next slot,
  is stored in the dying process by the lifecycle component; a table takes
  `capability_slots` divided by 4, rounded up, steps, and one more step for
  each step of a pending revocation that it meets.
- `count` reads one slot.
- The constants are `MAX_DEPTH` = 16, from the depth of the chains that the
  frozen vectors and the tests of the implementation build, with a margin;
  `REVOKE_BATCH` = 4, below 8 so that a chain of eight capabilities is
  removed in more than one step; $W$ = 64 of the objects contract; and
  `capability_slots` at most 65,536.

## Determinism

- **Slots.** The slot of every capability that an entry puts into a table
  is an argument: the caller names it for `derive`, `copy`, `install` and
  `reserve`, as the rule for capabilities of the
  [internal choices](../../../security.md#internal-choices) states. The
  slots of the root's first capabilities are fixed by the boot of the root.
- **Handles.** A handle is the slot number and the generation of that slot
  in the caller's own table, which follows from the history of that slot
  since the caller's process occupied its process slot, and from nothing
  else.
- **Badges.** The badge of an endpoint capability is the value that the
  party that mints the send capability gives to `derive`; the kernel stores
  it, and derivation, copy and transfer keep it, as the rule for
  identifiers of the
  [internal choices](../../../security.md#internal-choices) states.
- **Ancestors.** The nearest live ancestor of an entry is the entry that
  the first live reference of its path names.
- **Order of removal.** A revocation removes its subtree in post-order,
  children before parents and siblings in the order of their chain, at most
  `REVOKE_BATCH` in a step; a close puts the children of the closed entry
  into its place in their order; a teardown takes the slots of the table in
  ascending order, at most `REVOKE_BATCH` in a step.
- **Results.** `revoke` reports completion only; `abort` reports `aborted`
  or `gone`, which follow from the state of the reservation.
- **Requests.** Requests that contend for an entry, a table or a count take
  effect in the order in which they enter the kernel. With more than one
  CPU, the order in which CPUs take the tokens of the same tables and object
  slots is the multicore interleaving that [ND-03](../../../security.md#nd-03)
  of the register of
  [permitted nondeterminism](../../../security.md#permitted-nondeterminism)
  allows; for each such order, the rules of this page fix the result.

The component leaves no other choice open.

## State fields

| Field | Class | Lock or owner | Linearization point | Publication |
| --- | --- | --- | --- | --- |
| The `state`, `generation`, `epoch`, `kind`, `rights`, `object`, `badge` and `moving` of each entry of the table of a process | Per-process | The token of the process of the table; an operation that changes the entry through a capability of another process, a transfer, a step of revocation or of teardown, or a close that splices it, holds that token too; with one CPU, the executing CPU | The release of the tokens after the write-back of the write set that changes the entry | Under the token, by the release of the lock that provides it once CPUs share it |
| The derivation links of each entry: `path`, `previous`, `next`, `first_child` and `last_child` | Per-process | The token of the process of the table; a lookup that reads the epochs, generations and marks of ancestors in other tables holds their tokens, at most 17 in all, and a close, a transfer and a step of revocation or of teardown that write entries of other tables hold the tokens of those tables | The release of the tokens after the write-back | Under the token |
| The revocation mark of each entry, which with the subtree is the progress of its revocation | Per-process, with its entry | The token of the process of the table, which the pending transition and every step of the revocation hold | The release of the token after the write-back of the pending transition, and after that of the step that clears it | Under the token |
| The count of capabilities of each object, in its object slot | Shared | The token of the pool of the object | The release of the token after the write-back | Under the token |

Every access to an entry holds the token of the process of its table, and
an operation that acts on another process's table through a capability
holds that process's token as well
([multicore by design](../../../architecture.md#multicore-by-design)); no
lock order is stated here. The progress of the teardown of a table is a
field of the dying process, which the lifecycle component classifies; the
object slots, the counts of pools and the quota records that the entries
change are fields of the
[objects](../objects/contract.md#state-fields) component.

## Testing obligations

- The host tests of the module `capabilities` (planned) replay every vector
  of [Legacy test vectors](#legacy-test-vectors) whose entry is on this
  page, with its expected output, and the vector `objects-7` of the
  [objects contract](../objects/contract.md#legacy-test-vectors), whose
  rules of rights are on this page, and write their results for the
  comparison with the specification
  ([host results](../../../formal-verification.md#host-results)).
- Lookup: for each pair of consecutive checks of [Lookup](#lookup) whose
  errors differ, a handle that breaks both gives the error of the earlier;
  the handle 0, every handle whose generation is 0, every slot number from
  `capability_slots` to 65,535 and a slot that a test sets to generation
  $2^{48} - 1$, whose deletion retires it; and a process that occupies a
  process slot after another, whose table it finds empty at generation 1 in
  every slot, retired ones included, while every entry reference to an
  entry of the earlier process stays stale.
- Rights: for each kind and each of the 32 masks, a derivation from a
  capability with every right of its kind gives exactly the requested
  rights or the error of [Rights](#rights); a capability with GRANT alone,
  or REVOKE alone, fails every lookup for another right.
- Derivation and badges: a chain of `MAX_DEPTH` derivations below a root
  entry succeeds and one more is `DepthExceeded`; after the close of an
  ancestor in the middle, the chain extends again; a badge is set once and
  kept by derivation, copy and transfer, and every other case of
  `InvalidBadge` is refused.
- Derivation links: a property test drives installations, derivations,
  copies, closes, transfers, steps of revocation and of teardown over
  several tables and checks after every write-back, against an independent
  model of the derivation tree, that the ancestors of every filled entry are
  the live references of its path, that every sibling chain holds the
  children of its nearest live ancestor in post-order of creation with the
  closed entries left out, that no filled entry has a right that an
  ancestor lacks, and that every count equals the filled entries other
  than replies that name its object.
- Revocation: a chain of eight capabilities below a target is removed in
  at least two steps of at most four removals, in post-order; between the
  pending transition and completion, every operation on the subtree and on
  the target other than a continuing `revoke` is `RevocationPending`; a
  step interrupted at a preemption point with an interrupt pending, after
  the dispatch again, continues from the stored progress to the same final
  state as an uninterrupted run; the target stays usable and derives again
  after completion; a revocation inside the subtree of another is taken
  over; `revoke` returns no count.
- Transfer: copy and move, each committed and aborted; the commit and abort
  after the pending transition and after the removal of the reservation;
  the teardown of the sender's and of the receiver's table while a move is
  pending; a copy whose source is closed before the commit, which commits,
  and a move whose source, a child of another capability, is deleted before
  the commit, which is `TransferGone` and leaves the reservation in the
  subtree of that capability until its abort.
- Teardown: a table with descendants in other tables, whose rights and
  ancestors stay; a table that holds the target of a pending revocation;
  after the last step every slot is empty or retired and the capability
  slots of the process count no usage.
- Counts: an endpoint and a notification are released, and their owners
  credited, in the write set that deletes their last capability, and not
  before; a capability of a released object fails with `StaleReference`
  and its close changes no count.
- For each error of [Errors](#errors), a call that gives it leaves every
  entry, count and quota record as before, compared field by field.
- Write sets: for each fault-injection point, an operation that fails there
  leaves the tables, counts and records as before; the largest write set of
  each entry is reached and stays within the item counts of
  [Check and execute](#check-and-execute).
- The drains of device grants are tested by the device-authority rules, the
  settlement of waits by the waits and IPC components, with the steps of
  this page that carry them.
- QEMU tests make lookups from EL0, with forged, out-of-range and stale
  handles, and revoke long chains of derivation from EL0, once the
  operations of the ABI inventory exist.
- The tests take their expected values from this page, from the vectors and
  from independent models, never from an earlier run of the code under test
  ([testing](../../../conventions/testing.md#independent-evidence)).

## Open obligations

The module `capabilities` has no `unsafe` code, no assembly and no MMIO,
and its entries are to be covered by its targets. An entry that a later
contract adds to the capability tables beyond the entries of this page is
an open obligation of the contract that adds it, carried by the proof of
object lifetimes, waits and sequential composition, by release 0.2. The
entries use the write-set buffer that the adapter of the objects component
lends and the storage that the board's forming of slices gives, which are
rows of the
[open obligations of the objects contract](../objects/contract.md#open-obligations);
the code of this page adds no obligation, so the table has no row.

| Obligation | Kind | Verified state | Carrier | Stage |
| --- | --- | --- | --- | --- |

## Legacy test vectors

The vectors are host tests of the prototype tree at
`prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`, 38 in all. Their
expected outputs are those that the test bodies assert, written in the
rules of this page. The vectors are not yet in a file of the repository, so
the section holds no `vectors` block.

| File | Vectors |
| --- | ---: |
| `src/capabilities/tests/admission.rs` | 8 |
| `src/capabilities/tests/endpoints/admission.rs` | 5 |
| `src/capabilities/tests/endpoints/lifetime.rs` | 5 |
| `src/capabilities/tests/lifetime.rs` | 9 |
| `src/capabilities/tests/quota.rs` | 4 |
| `src/capabilities/tests/transfers.rs` | 7 |

`src/capabilities/tests.rs` and `src/capabilities/tests/endpoints.rs` hold
only fixtures and module declarations, and no vector.

A vector of this page is one test function. The vector file is to hold one
line for each case of it through an entry, with the id `<vector>.<n>`, `n`
counting those cases from 1 in the order of the test; a case that its row
marks not applicable has no line.

**Notation.** Counts, slot numbers and generations are decimal. A table of
the objects component is written by the fields of its capacity record that
the fixture sets, as the objects contract writes it. The processes of a
fixture are A, B, C and D, each with its thread; `X[s]` is slot $s$ of the
capability table of X, and a handle is written `<slot>@<generation>`, the
value generation × 65,536 + slot. Rights are written by their names in
[Rights](#rights), `all` for every right of the kind. `count(O)` is the
count of capabilities of object O. The output of a call is `ok`, followed
by its fields, or `err=<error>`, with the error by its name on this page or
on the objects contract; the results of `abort` are `aborted` and `gone`.
A structured value is a list of `key=value` fields separated by single
spaces, in the order of the expected output below.

**Operations.** "X[s] holds O with R" is an installation of a capability to
O with the rights R into X[s]. "A derivation from h into X[t]" is
`derive` by X; with a badge, the row gives it. "A send of h from X to Y[t]
with R" is a reservation of a copy with the rights R into the receive slot
Y[t] followed by its commit; "a move" is the same with the mode move, and a
row that separates the reservation from its commit or abort says so. The
prototype's trusted derivation into another space, which no entry of this
page offers, is such a send. "The teardown of X's table" is the steps of
`teardown_step` from progress 0 to completion; a host test calls them
without the rest of the destruction of X.

**Fixtures.**

- `src/capabilities/tests.rs`, for `admission.rs`, `endpoints/` and
  `lifetime.rs`: table `processes=8 threads=16 endpoints=2
  capability_slots=8 reserved_processes=1 reserved_threads=1`, with the
  root's pair in the reserved tails and the processes A, B and C in process
  slots 0, 1 and 2; `T` is the thread of C, and `E` an endpoint owned by C,
  where a row creates one. The prototype's registry of four spaces and
  twelve nodes, with a space of 8 live capabilities for each of A, B and C,
  is the capability tables of 8 slots of these processes. A row that sets
  `capability_slots` otherwise builds its own table.
- `quota.rs`: table `processes=8 threads=16 capability_slots=1
  reserved_processes=1 reserved_threads=1` with the root's pair and the
  processes A and B; `TA` is the thread of A. The prototype ran each case
  with a registry with control reserves and one without; here the two are
  one table, so each case runs once. Its preparation of a further thread,
  which its quotas refused, does not apply: a process has one thread.
- `transfers.rs`: table `processes=8 threads=16 capability_slots=6
  reserved_processes=1 reserved_threads=1` with the root's pair and the
  processes A, B, C and D; `T` is the thread of C. The prototype's control
  space of D, of 4 capabilities, is a table of 6 slots as the others are.

**Behaviour changes.** These rules differ from the prototype:

- A handle is a slot number with the generation of that slot in the
  caller's own table, where the prototype's tokens came from one counter of
  its registry: the values of handles, their exhaustion and their failure
  in another table change.
- A close deletes its capability and frees its slot, where the prototype
  kept a closed capability with descendants as a tombstone that held a node
  and a reference: the counts, usages and refusals that the tombstones
  caused change.
- A revocation reports completion, where the prototype returned the number
  of nodes that it removed.
- A capability does not hold its object: an endpoint or a notification is
  released at its last capability, the other kinds by their components, and
  a capability of a released object goes stale. The prototype's references
  that held back reclamation, the reference of an endpoint to its service
  thread and the tests that damaged a count do not apply.
- A table belongs to its process slot, and its generations start again
  for each process that occupies the slot: the prototype's spaces, with
  their registration, owners, limits, generations, receipts and control
  reserves, and its global node capacity, do not apply.
- References carry no rights, and the rights of a lookup are those of its
  operation: the prototype's native handles with restricted rights and its
  resolution for GRANT or REVOKE do not apply.
- The caller is the process of the running thread, and the lifecycle states
  of the caller and of the object, and the closure of an endpoint, are not
  checks of this page: the prototype's refusals for a dead caller, a dead
  target, a closed endpoint and an endpoint whose owner is dead do not
  apply to its entries. Whether an operation that composes them refuses
  such a state is for the contracts of the lifecycle and IPC components to
  state.
- A badge is set by the derivation that mints it, not by an installation:
  where a test asserts the badge of an endpoint that it seeds, or is about
  distinct badges, its row puts that derivation in place of the seeding,
  and the counts of the row include it; where the badge plays no part, the
  row installs the endpoint without one.
- The caller names the slot of a new capability: a slot beyond the table is
  `InvalidSlot` and a filled one `SlotOccupied`, where the prototype's
  quotas gave `QuotaExceeded`.
- A rights mask has five bits, the fifth the creation right of a process.
- The errors take the names of this page: a reserved entry is
  `NoCapability` and the source of a move `TransferPending`, where the
  prototype gave `UnknownToken` for both.

### Admission vectors

`src/capabilities/tests/admission.rs`, 8 vectors.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `caps-admission-1` | 4 | `configuration_rights_and_exact_owner_are_checked` | The records `processes=0` and `capability_slots=0`, for the prototype's registries of no space and of no node, are each `err=InvalidConfiguration`; its registry number 0 does not apply. A[0] holds T with all rights, `0@1`: a derivation from `0@1` into A[1] with the rights mask 0, 32 or 18446744073709551615 is `err=InvalidRights`; with 16, the creation right, which a thread capability never holds, `err=PermissionDenied`; with each mask $m$ from 1 to 15 it gives `1@<m>` with the rights $m$, the slot closed again before the next mask. The prototype's second space of A (`DuplicateOwner`), its space limits 0 and 13 and its owner receipts with restricted rights (`PermissionDenied`) do not apply. The refusals leave the tables, counts and usages unchanged | `validate_capacities` of the objects component, `install`, `derive`, `close` |
| `caps-admission-2` | 47 | `foreign_namespace_and_forged_tokens_confer_no_authority` | A[0] holds T with all rights, `0@1`. A's lookups for a thread with OBSERVE of the handle values 0, that is `0@0`, and 18446744073709551615, that is `65535@281474976710655`, and of `0@2` are `err=StaleHandle`, `err=InvalidHandle` and `err=StaleHandle`, and of `1@1`, an empty slot, `err=NoCapability`; B's lookup of `0@1` names slot 0 of B's own table, which is empty: `err=NoCapability`. The prototype's foreign registry (`WrongRegistry`) and caller of another pool (`WrongPool`) do not apply: there is no registry number, and the caller is never an argument | `install`, `lookup` |
| `caps-admission-3` | 73 | `resolution_returns_only_requested_native_authority` | A[0] holds T with all rights: A's lookups of `0@1` for a thread with OBSERVE and with CONTROL each give the reference of T. The prototype's native handles restricted to the rights asked, which refused a termination and a query, and its refusal of GRANT and REVOKE as the rights of a resolution (`InvalidRights`) do not apply: a reference carries no rights, and each operation looks up its handle for the rights that it needs, derivation and revocation for GRANT and REVOKE | `install`, `lookup` |
| `caps-admission-4` | 103 | `derivation_can_only_reduce_granted_rights` | A[0] holds T with all rights; a derivation from `0@1` into A[1] with OBSERVE gives `1@1`. From `1@1`, which lacks GRANT and REVOKE, a derivation into A[2] with OBSERVE and one with all rights are each `err=PermissionDenied`, its revocation is `err=PermissionDenied`, and a lookup for a thread with CONTROL is `err=PermissionDenied`. The refusals leave the tables unchanged, and `count(T)=2` | `install`, `derive`, `revoke`, `lookup`, `count` |
| `caps-admission-5` | 133 | `full_local_quota_and_global_nodes_fail_without_retaining` | Table with `capability_slots=1`. A[0] holds T with all rights; a derivation from `0@1` into A[0] is `err=SlotOccupied` and into A[1] `err=InvalidSlot`, where the prototype's limit of one live capability gave `QuotaExceeded`. A send of `0@1` from A to B[0] with OBSERVE gives B `0@1`; an installation into B[0] is then `err=SlotOccupied`. The prototype's global capacities of two nodes (`NodeCapacity`) and two spaces (`SpaceCapacity`) do not apply. The refusals leave the tables unchanged, and `count(T)=2` | `install`, `derive`, `reserve`, `commit`, `count` |
| `caps-admission-6` | 161 | `closed_ancestry_keeps_global_node_quota_charged` | Table with `capability_slots=2`. A[0] holds T with all rights and sends it to B[0] with OBSERVE. The close of A's `0@1` deletes it, where the prototype kept a tombstone: B[0] becomes a root entry, A's usage of capability slots is 0 and `count(T)=1`; an installation of T with all rights into A[0] then gives `0@2`, where the tombstone gave `NodeCapacity`. After the close of B's `0@1`, `count(T)=1`, the new capability of A, where the prototype's count reached 0 since its installation had failed | `install`, `reserve`, `commit`, `close`, `count` |
| `caps-admission-7` | 183 | `token_and_space_generations_never_wrap` | A test sets the generation of A[0] to $2^{48} - 1$: an installation of T with all rights there gives `0@281474976710655`, the handle value 18446744073709486080; its close retires the slot; a further installation into A[0] is `err=GenerationExhausted` and leaves the table unchanged, and one into A[1] gives `1@1`. The prototype's global token counter (`TokenExhausted`) and its space generations (`GenerationExhausted` of a space) do not apply: each slot has its own generation, and a table is that of its process slot, whose own generations are those of the objects component | `install`, `close` |
| `caps-admission-8` | 210 | `dead_target_and_attenuated_native_seed_fail_atomically` | The prototype's installation from a native thread handle restricted to OBSERVE (`PermissionDenied`) does not apply: `install` takes a reference, which carries no rights. Its refusal after the termination of T (`InvalidState`) does not apply: the lifecycle state of T is not a check of this page. With the slot of T released, an installation of the reference of T into A[0] is `err=StaleReference` and leaves the table unchanged | `install` |

### Endpoint admission vectors

`src/capabilities/tests/endpoints/admission.rs`, 5 vectors, with the common
fixture and the endpoint E.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `caps-endpoint-admission-1` | 4 | `endpoint_and_thread_capabilities_reject_cross_kind_resolution` | A[0] holds E with all rights, `0@1`; a derivation from `0@1` into A[1] with SEND and the badge 71 gives `1@1`, the prototype's seeded capability; and A[2] holds T with all rights, `2@1`. A's lookup of `1@1` for a thread is `err=WrongType`, and of `2@1` for an endpoint `err=WrongType`; A's lookup of `1@1` for an endpoint with SEND gives E with the badge 71; with RECEIVE, `err=PermissionDenied`; B's lookup of `1@1` with SEND is `err=NoCapability`. `count(E)=2`, the prototype's 1 and the capability that sets the badge, and `count(T)=1`. The teardown of A's table deletes the three in one step, after which `count(T)=0` and E, whose last capability is deleted, is released, its slot free at generation 2. The prototype's resolution for GRANT (`InvalidRights`) and its native receipts of E and of its owner do not apply | `install`, `derive`, `lookup`, `count`, `teardown_step` |
| `caps-endpoint-admission-2` | 55 | `derivation_preserves_badge_kind_and_attenuation` | A[0] holds E with all rights; a derivation from `0@1` into A[1] with all rights and the badge 18446744073709551615 gives `1@1`, the prototype's seeded capability. A send of `1@1` from A to B[0] with SEND gives B `0@1`, and a derivation from `1@1` into A[2] with RECEIVE gives `2@1`. B's lookup of `0@1` for an endpoint with SEND and A's of `2@1` with RECEIVE each give E with the badge 18446744073709551615; A's lookup of `2@1` with SEND is `err=PermissionDenied`. B's derivation from `0@1` into B[1] with SEND and A's from `2@1` into A[3] with all rights are each `err=PermissionDenied` and leave the tables unchanged. `count(E)=4`: the prototype's 3 and the capability that sets the badge | `install`, `derive`, `reserve`, `commit`, `lookup`, `count` |
| `caps-endpoint-admission-3` | 94 | `seed_rejects_attenuated_foreign_and_stale_endpoints_atomically` | The prototype's installations from native endpoint handles restricted to OBSERVE or CONTROL (`PermissionDenied`) do not apply: a reference carries no rights. An installation into A[0] of the reference of an endpoint of another table, whose pools have other numbers, is `err=WrongPool`; with the slot of E released, an installation of the reference of E is `err=StaleReference`. The table is unchanged | `install` |
| `caps-endpoint-admission-4` | 126 | `closed_endpoint_cannot_gain_new_authority_but_keeps_cleanup_identity` | A[0] holds E with all rights. The closure of E is a state of the IPC component, which no check of this page reads, so the prototype's refusals of a derivation and an installation after it (`InvalidState`) do not apply. A's lookup of `0@1` for an endpoint with RECEIVE gives E with no badge. The prototype's refused reaping of E (`ReferencesOutstanding`) does not apply: the close of `0@1` deletes the last capability of E and so releases it; a new endpoint then takes its slot at generation 2, and A's lookup of `0@1` is `err=NoCapability` | `install`, `lookup`, `close` |
| `caps-endpoint-admission-5` | 163 | `token_and_capacity_failure_do_not_retain_endpoint` | A test sets the generation of A[0] to $2^{48} - 1$; an installation of E with all rights there gives `0@281474976710655`. The prototype's global token counter, which refused a further installation and a derivation (`TokenExhausted`), does not apply: an installation of E with all rights into A[1] gives `1@1`, a derivation from `0@281474976710655` into A[2] with SEND gives `2@1`, and `count(E)=3`. In a table with `capability_slots=1` whose A[0] holds E with all rights, a second installation into A[0] is `err=SlotOccupied` and leaves the table and `count(E)=1` unchanged | `install`, `derive`, `count` |

### Endpoint lifetime vectors

`src/capabilities/tests/endpoints/lifetime.rs`, 5 vectors, with the common
fixture and the endpoint E.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `caps-endpoint-lifetime-1` | 4 | `endpoint_tombstones_preserve_nonlocal_descendants_until_revoke` | A[0] holds E with all rights; a derivation from `0@1` into A[1] with all rights and the badge 41 gives `1@1`, the prototype's root. A sends `1@1` to B[0] with all rights, and B sends its `0@1` to A[2] with SEND. B's close of its `0@1` deletes it, where the prototype kept a tombstone, and A[2] becomes a child of A[1]: `count(E)=3`, the capabilities of A[0], A[1] and A[2]. A's lookup of `2@1` for an endpoint with SEND gives E with the badge 41. The revocation of `1@1` reports completion, where the prototype returned 2, and removes A[2]: A's lookup of `2@1` is then `err=NoCapability`, and `count(E)=2`. After the close of `1@1`, `count(E)=1`, the capability of A[0] | `install`, `derive`, `reserve`, `commit`, `close`, `lookup`, `revoke`, `count` |
| `caps-endpoint-lifetime-2` | 35 | `dead_service_rejects_new_authority_and_pins_backing_until_cleanup` | A[0] holds E with all rights, and a derivation from `0@1` into A[1] with all rights and the badge 12 gives `1@1`, the prototype's root. C, the owner of E, is terminated: its states, and the release of E in the steps of its destruction, are rules of the lifecycle component, which no check of this page reads, so the prototype's refusals of an installation and a derivation (`InvalidState`) do not apply. Before that release, A's lookup of `1@1` for an endpoint with SEND gives E with the badge 12. The prototype's references of the capabilities to E and of E to its service thread, which held back the reaping of the thread (`ReferencesOutstanding`), do not apply; the close of `1@1` succeeds | `install`, `derive`, `lookup`, `close` |
| `caps-endpoint-lifetime-3` | 68 | `mixed_target_cleanup_preflights_every_reference_before_releasing` | A[0] holds the thread of B and A[1] holds E, each with all rights. The teardown of A's table deletes both in one step, after which the count of the thread of B is 0 and `count(E)=0`, and E is released. The prototype's damaged count of E, which made its teardown fail without a change (`CounterUnderflow`), does not apply: only the entries of this page change a count | `install`, `teardown_step`, `count` |
| `caps-endpoint-lifetime-4` | 91 | `cleanup_aggregates_one_endpoint_across_distinct_badges` | A[0] holds E with all rights; derivations from `0@1` into A[1] and A[2] with all rights and the badges 1 and 2 give `1@1` and `2@1`, and `count(E)=3`. The teardown of A's table deletes the three in one step, after which `count(E)=0` and E is released. The prototype's damaged count (`CounterUnderflow`) does not apply, as in `caps-endpoint-lifetime-3` | `install`, `derive`, `teardown_step`, `count` |
| `caps-endpoint-lifetime-5` | 112 | `dead_namespace_cleanup_and_reuse_preserve_outward_endpoint_caps` | A[0] holds E with all rights, a derivation from `0@1` into A[1] with all rights and the badge 20 gives `1@1`, and A sends `1@1` to B[0] with SEND. A is terminated: its thread runs no more, so the prototype's lookup by a dead caller (`InvalidState`) does not apply. The teardown of A's table deletes A[0] and A[1]: B[0] becomes a root entry and `count(E)=1`. A new process in the process slot of A has the table of that slot, which it finds empty at generation 1 in every slot, whatever A did there: its lookup of `1@1` is `err=NoCapability`. B's lookup of `0@1` for an endpoint with SEND gives E with the badge 20. The teardown of B's table leaves `count(E)=0` and releases E. The prototype's second teardown of the same space (`StaleSpace`) does not apply: a table is torn down once, in the destruction of its process | `install`, `derive`, `reserve`, `commit`, `teardown_step`, `lookup`, `count` |

### Lifetime vectors

`src/capabilities/tests/lifetime.rs`, 9 vectors, with the common fixture.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `caps-lifetime-1` | 4 | `closed_intermediate_survives_until_ancestor_revocation` | A[0] holds T with all rights; A sends `0@1` to B[0] with all rights, and B sends its `0@1` to A[1] with OBSERVE. B's close of its `0@1` makes A[1] a child of A[0]: A's lookup of `1@1` for a thread with OBSERVE gives T, B's lookup of `0@1` is `err=NoCapability`, and `count(T)=2`, where the prototype's tombstone made 3. The revocation of A's `0@1` reports completion, where the prototype returned 2, and removes A[1]: A's lookup of `1@1` is `err=NoCapability`, its lookup of `0@1` with OBSERVE gives T, and `count(T)=1`. A second revocation of `0@1`, with no child left, reports completion at once, where the prototype returned 0 | `install`, `reserve`, `commit`, `close`, `lookup`, `revoke`, `count` |
| `caps-lifetime-2` | 39 | `dead_target_remains_queryable_but_cannot_be_derived_or_reaped` | A[0] holds T with all rights, and C, the process of T, is terminated. A's lookup of `0@1` for a thread with OBSERVE gives the reference of T, whose state, dead, is the lifecycle component's. The prototype's refused reaping of T (`ReferencesOutstanding`) and its refused derivation from a dead target (`InvalidState`) do not apply: a capability holds back no reclamation, and the lifecycle state of the object is not a check of this page. After the close of `0@1`, the release of T and of C and a new pair, whose thread takes the slot of T at a larger generation, A's lookup of `0@1` is `err=NoCapability` | `install`, `lookup`, `close` |
| `caps-lifetime-3` | 75 | `dead_caller_loses_access_before_explicit_table_teardown` | A[0] holds T with all rights, and A is terminated. The prototype's refusals of a lookup, a close, a revocation and a derivation by the dead caller (`InvalidState`) do not apply: the caller is the process of the running thread, and the thread of a terminated process runs no more. The teardown of A's table leaves `count(T)=0` | `install`, `teardown_step`, `count` |
| `caps-lifetime-4` | 106 | `owner_space_reuse_does_not_inherit_tombstone_authority` | A[0] holds T with all rights and A sends `0@1` to B[0] with OBSERVE. The teardown of A's table deletes A[0], where the prototype kept a tombstone, and B[0] becomes a root entry; A's lookup of `0@1` is then `err=NoCapability`. B's lookup of `0@1` for a thread with OBSERVE gives T. The teardown of B's table leaves `count(T)=0`. The prototype's space receipts, their generations and their refusal after the teardown (`StaleSpace`) do not apply | `install`, `reserve`, `commit`, `teardown_step`, `lookup`, `count` |
| `caps-lifetime-5` | 137 | `recycled_cap_slot_gets_a_distinct_scalar_token` | An installation of T with all rights into A[0] gives `0@1`; after its close, a second installation into A[0] gives `0@2`. A's lookup of `0@1` is `err=StaleHandle`, and of `0@2` for a thread with OBSERVE gives T | `install`, `close`, `lookup` |
| `caps-lifetime-6` | 158 | `full_depth_chain_prunes_in_reverse_order` | Property. A[0] holds T with all rights. For $i$ from 0 to 10, round $i$ sends the capability of the previous round, `0@1` of A in round 0, with all rights from A to B when $i$ is even and from B to A when it is odd, into the lowest empty slot of the receiving table: the rounds fill B[0], A[1], B[1], A[2], B[2], A[3], B[3], A[4], B[4], A[5] and B[5], twelve capabilities in one chain, of which the last, B's `5@1`, has eleven ancestors. The teardown of A's table, in two steps, deletes its six; B's lookup of `5@1` for a thread with OBSERVE then gives T. The teardowns of B's and C's tables leave every table empty and `count(T)=0`. Lines `caps-lifetime-6.1` to `caps-lifetime-6.11`, one for each round: `received=<handle>`; line `caps-lifetime-6.12`: the output of the lookup; line `caps-lifetime-6.13`: `count=0` | `install`, `reserve`, `commit`, `teardown_step`, `lookup`, `count` |
| `caps-lifetime-7` | 184 | `revoke_only_removes_the_selected_subtree` | A[0] holds T with all rights; A sends `0@1` to B[0] and to C[0] with all rights, and B derives from its `0@1` into B[1] with OBSERVE. B's revocation of its `0@1` reports completion, where the prototype returned 1, and removes B[1]: B's lookup of `1@1` is `err=NoCapability`, C's lookup of `0@1` for a thread with OBSERVE gives T, and `count(T)=3` | `install`, `reserve`, `commit`, `derive`, `revoke`, `lookup`, `count` |
| `caps-lifetime-8` | 211 | `cleanup_preflight_is_atomic_across_multiple_targets` | A[0] holds the thread of B and A[1] T, each with all rights. The teardown of A's table deletes both in one step, after which the counts of both threads are 0. The prototype's damaged count of T (`CounterUnderflow`) does not apply, as in `caps-endpoint-lifetime-3` | `install`, `teardown_step`, `count` |
| `caps-lifetime-9` | 233 | `full_depth_reserved_chain_returns_both_namespace_reservations` | Table with `capability_slots=1`. A[0] holds T with all rights and A sends `0@1` to B[0] with all rights. The teardown of A's table deletes A[0], and B's lookup of `0@1` for a thread with OBSERVE gives T; the teardown of B's table leaves both tables empty and `count(T)=0`. The prototype's ordinary and control spaces, their reservations of nodes and their receipts (`StaleSpace`) do not apply: no table has a control reserve | `install`, `reserve`, `commit`, `teardown_step`, `lookup`, `count` |

### Quota vectors

`src/capabilities/tests/quota.rs`, 4 vectors, with the fixture of
`quota.rs`.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `caps-quota-1` | 42 | `hidden_receive_reserves_live_quota_before_commit` | A[0] holds TA with all rights. A reservation of a copy of `0@1` into B[0] with OBSERVE makes B's usage of capability slots 1 and `count(TA)=2`; while it is reserved, B's lookup of `0@1` is `err=NoCapability`, and a second reservation into B[0] and an installation into B[0] are each `err=SlotOccupied` and leave the tables, the usages and `count(TA)` unchanged. The commit gives B `0@1`, whose lookup for a thread with OBSERVE gives TA. After its close, B's usage is 0 | `install`, `reserve`, `lookup`, `commit`, `close` |
| `caps-quota-2` | 92 | `pending_move_retains_source_live_quota_until_resolution` | Two cases, each with A[0] holding TA with all rights and a reservation of a move of `0@1` into B[0] with OBSERVE: A's lookup of `0@1` is `err=TransferPending`, and an installation into A[0] `err=SlotOccupied`, A's usage staying 1. With the commit: B gets `0@1`; A[0] is deleted, where the prototype kept a tombstone, so A's usage is 0 and an installation of TA with OBSERVE into A[0] gives `0@2`; the abort is then `gone`; A's lookup of `0@1` is `err=StaleHandle`; after the closes of A's `0@2` and B's `0@1`, `count(TA)=0`. With the abort instead: it is `aborted`; A's lookup of `0@1` with CONTROL gives TA; after its close, `count(TA)=0` | `install`, `reserve`, `lookup`, `commit`, `abort`, `close`, `count` |
| `caps-quota-3` | 149 | `cancelled_or_revoked_receive_releases_only_its_reservation` | Two cases, each with A[0] holding TA with all rights and a reservation of a copy of `0@1` into B[0] with OBSERVE: either A's revocation of `0@1` reports completion, where the prototype returned 1, and removes the reservation, or its abort is `aborted`; in both, B[0] is empty at generation 2 and B's usage is 0. An installation of TA with OBSERVE into B[0] then gives `0@2`; a further abort of the reservation is `gone`, and its commit `err=TransferGone`. B's lookup of `0@2` for a thread with OBSERVE gives TA, B's usage is 1, and `count(TA)=2` | `install`, `reserve`, `revoke`, `abort`, `commit`, `lookup`, `count` |
| `caps-quota-4` | 186 | `closed_source_does_not_release_destination_reservation_before_abort` | A[0] holds TA with all rights, and a reservation of a move of `0@1` into B[0] with OBSERVE is made. The teardown of A's table deletes A[0], the source of the move, and the reservation becomes a root entry: its commit is `err=TransferGone`, an installation into B[0] is `err=SlotOccupied`, and B's usage stays 1. Its abort is `aborted`, after which `count(TA)=0` and B's usage is 0 | `install`, `reserve`, `teardown_step`, `commit`, `abort`, `count` |

### Transfer vectors

`src/capabilities/tests/transfers.rs`, 7 vectors, with the fixture of
`transfers.rs`.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `caps-transfer-1` | 40 | `hidden_copy_reserves_capacity_and_commits_attenuated_rights_once` | A[0] holds T with all rights, and `count(T)=1`. A reservation of a copy of `0@1` into B[0] with OBSERVE makes `count(T)=2`; B's lookup of `0@1` is `err=NoCapability`, and A's lookup of `0@1` for a thread with CONTROL gives T. The commit gives B `0@1`, whose lookup with OBSERVE gives T and with CONTROL is `err=PermissionDenied`. A second commit of the reservation is `err=TransferGone`, and its abort `gone`. After the close of B's `0@1`, `count(T)=1` | `install`, `reserve`, `lookup`, `commit`, `abort`, `close`, `count` |
| `caps-transfer-2` | 82 | `pending_move_locks_source_and_abort_restores_only_original_authority` | A[0] holds T with all rights, and a reservation of a move of `0@1` into B[0] with OBSERVE is made. A's lookup of `0@1`, its close and a derivation from it into A[1] with all rights are each `err=TransferPending`. The abort is `aborted`: the counts and usages equal those before the reservation, and B[0] is empty at generation 2. A's lookup of `0@1` for a thread with CONTROL gives T; a second abort is `gone`. The prototype's resolution with every right as the rights of an operation (`InvalidRights`) does not apply | `install`, `reserve`, `lookup`, `close`, `derive`, `abort`, `count` |
| `caps-transfer-3` | 119 | `committed_move_keeps_closed_ancestry_charged_until_destination_closes` | A[0] holds T with all rights, and a move of `0@1` into B[0] with OBSERVE is reserved and committed: B gets `0@1`, and A[0] is deleted, where the prototype kept a tombstone charged to A, so A's usage is 0 and A's lookup of `0@1` is `err=NoCapability`. After the close of B's `0@1`, `count(T)=0`. The prototype's spaces, their duplicate owner (`DuplicateOwner`) and their receipts (`StaleSpace`) do not apply | `install`, `reserve`, `commit`, `lookup`, `close`, `count` |
| `caps-transfer-4` | 153 | `revocation_drains_pending_move_without_resurrecting_source_or_reused_slot` | C[0] holds T with all rights, and C sends `0@1` to A[0] with all rights; a reservation of a move of A's `0@1` into B[0] with OBSERVE is made. C's revocation of its `0@1` reports completion, where the prototype returned 2, after one step that removes the reservation and then A[0], children before parents: B[0] and A[0] are empty at generation 2. An installation of T with OBSERVE into B[0] gives `0@2`. The abort of the reservation is `gone`, and its commit `err=TransferGone`. B's lookup of `0@2` for a thread with OBSERVE gives T, and A's lookup of `0@1` is `err=NoCapability` | `install`, `reserve`, `commit`, `revoke`, `abort`, `lookup` |
| `caps-transfer-5` | 186 | `failed_offer_is_atomic_on_rights_and_capacity` | A[0] holds T with OBSERVE: a reservation of a copy of `0@1` into B[0] with OBSERVE is `err=PermissionDenied`. A[1] holds T with all rights, and B[0] to B[5], the whole table of B, hold T with OBSERVE: a reservation of a move of `1@1` into B[0] is `err=SlotOccupied`, where the prototype's full space gave `QuotaExceeded`. Each refusal leaves the tables and `count(T)` unchanged, and A's lookup of `1@1` for a thread with CONTROL gives T | `install`, `reserve`, `lookup`, `count` |
| `caps-transfer-6` | 231 | `source_and_destination_death_each_abort_without_revival` | Two cases, each with A[0] holding T with all rights and a reservation of a move of `0@1` into B[0] with OBSERVE. The source dies: the teardown of A's table deletes A[0], and the reservation becomes a root entry; its commit is `err=TransferGone` and its abort `aborted`; A's lookup of `0@1` is `err=NoCapability`, and `count(T)=0`. The destination dies: the teardown of B's table removes the reservation as an abort does, which ends the move of A[0]; the commit is `err=TransferGone` and the abort `gone`; A's lookup of `0@1` for a thread with CONTROL gives T, and `count(T)=1`. The termination is the lifecycle component's: the prototype refused the commit once the process was terminated, and here the teardown removes what the commit needs | `install`, `reserve`, `teardown_step`, `commit`, `abort`, `lookup`, `count` |
| `caps-transfer-7` | 266 | `ordinary_closed_nodes_cannot_consume_reserved_control_capacity` | A[0] holds T with all rights. Five rounds each derive from `0@1` into A[1] with all rights, send `1@<n>` of round $n$ with OBSERVE to the lowest empty slot of B, B[0] to B[4], and close A[1], which makes the sent capability a child of A[0]. A[1] ends empty at generation 6 and A's usage of capability slots is 1, where the prototype's five tombstones and the root made 6, and a further derivation from `0@1` into A[1] gives `1@6`, where the prototype's limit of nodes gave `QuotaExceeded`. D's installations of T with CONTROL into D[0] to D[3] succeed. The teardown of A's table leaves the five capabilities of B as root entries; after the teardown of B's table, `count(T)=4`, the capabilities of D. The prototype's control space and its reserved nodes do not apply | `install`, `derive`, `reserve`, `commit`, `close`, `teardown_step`, `count` |

## References

- The kernel's own rules, which this page instantiates:
  [Kernel objects and capabilities](../../../architecture.md#kernel-objects-and-capabilities)
  for the capability tables, handles, generations, dangling references,
  quotas and revocation; the execution model under
  [System calls and the ABI](../../../architecture.md#system-calls-and-the-abi)
  for entries that run to completion, long operations with their
  preemption points and the progress that they store in their objects; and
  the capability transfer of
  [IPC, notifications and waits](../../../architecture.md#ipc-notifications-and-waits).
- The [security model](../../../security.md): its
  [effective revocation](../../../security.md#effective-revocation), and
  its [internal choices](../../../security.md#internal-choices) for slots,
  identifiers, badges, the completion of waits, cascading revocation and
  the order of errors.
- G. Klein, J. Andronick, K. Elphinstone, T. Murray, T. Sewell, R. Kolanski,
  G. Heiser, "Comprehensive Formal Verification of an OS Microkernel", ACM
  Transactions on Computer Systems 32(1), 2014,
  <https://trustworthy.systems/publications/nicta_full_text/7371.pdf>: the
  capability derivation tree, revocation of what was derived from a
  capability, and long operations that store their progress in the
  objects.
- The rules of this page take, as clauses of their own, the rules of the
  prototype tree at `prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`:
  - `docs/kernel-state.md`, lines 43 to 76: the division into per-CPU,
    per-thread, per-process and shared state, with the capability namespace
    of each process;
  - `docs/features/kernel/capabilities.md`, lines 55 to 82: the operations,
    their status codes and the right bits;
  - `docs/features/kernel/capabilities.md`, lines 99 to 135: authority and
    namespaces, tokens meaningful only to their holder, and derivation that
    only reduces rights;
  - `docs/features/kernel/capabilities.md`, lines 136 to 162: the order of
    validation, its results and the cleanup that leaves nothing half done;
  - `docs/features/kernel/capabilities.md`, lines 163 to 211: references,
    close and revoke, outward descendants and the bounded walks;
  - `docs/features/kernel/capability-transfer.md`, lines 66 to 116: the
    transaction of a transfer, copy and move, commit and abort, and the
    reservations of the receive.
