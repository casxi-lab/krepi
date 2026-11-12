# Creation contract

This page governs the code of the `creation` component of the
[kernel objects and capabilities](../README.md) domain: the operations that
create endpoints, notifications and child processes with the creation
right; the staged creation of a child, with the validation of its image by
the loading component and the mapping of that image; the initial
capabilities that a creator puts into the table of its child; the checks,
charges, splits and admission of every creation; the first capabilities of
new objects; and the boot of the root. The objects, their pools, owners and
quotas, and the write sets through which the entries of this page change
kernel state belong to the [objects](../objects/contract.md) component; the
capability tables, with their rights, lookups, installation and the
reservation and commit through which a capability enters a table, to the
[capabilities](../capabilities/contract.md) component; the states of
processes, their destruction and their reaping to the
[lifecycle](../lifecycle/contract.md) component; the validation of loading
requests, with the loading part of the capacity record and the image
window, to the dispatch component (planned), which the address-space and
objects contracts call the loading component; and the page pool and the VM
head of each process to the [vm](../../memory/vm/contract.md) component.
The observable behaviour that these rules serve, with its evidence, is in
the [requirements](requirements.md), the other document of the component.

## Terms

- **Creation right.** CREATE, bit 4 of the rights of a capability to a
  process ([rights](../capabilities/contract.md#rights)), on a capability
  that names the caller's own process.
- **Caller.** The process of the calling thread, whose table every handle
  of an operation names; it is the owner of every object that its creation
  makes ([calling domains](../objects/contract.md#metadata-quotas)).
- **Child.** A process that a creation of this page makes for its caller,
  the **creator**, which is its owner; a child has one thread, created with
  it ([object kinds](../objects/contract.md#object-kinds-and-pools)).
- **Image.** An entry of the kind Image of the
  [boot-bundle directory](../../memory/address-space/contract.md#boot-bundle-directory),
  named by its index in the directory.
- **Segment.** A range of bytes of an image, with the virtual address, the
  size in memory and the access, R, RX or RW, at which a child maps it, as
  the loading component accepts it (planned).
- **Plan of an image.** `loader::Plan` (planned), the value of the loading
  component that names an image and holds the segments that
  `loader::validate` (planned) has accepted for it.
- **Private pages.** The pages of the memory of the RW segments of an image
  and of its initial stack. Those of a child are frames of the page pool,
  loaded frames of the child
  ([the pool](../../memory/vm/contract.md#configuration-and-the-page-pool));
  those of the root are pages of its private allocation at boot
  ([first process](../../memory/address-space/contract.md#first-process-and-boot-information)).
- **Shares.** The five limits that a creator splits to its child from what
  it has left: child processes, endpoints, notifications, committed VM
  pages and private pages of loaded images
  ([splitting limits](../objects/contract.md#metadata-quotas)).
- **Fixed slots.** `PROCESS_SLOT`, slot 0, and `THREAD_SLOT`, slot 1
  (planned): the slots of the table of a new process that hold its first
  capability to itself and to its thread.
- **Grant.** One of at most `SPAWN_GRANTS` = 4 (planned) capabilities of
  the creator's table that `spawn_grant` stages, each with the rights and
  the slot of the child's table that the creator gives, and that the commit
  copies into that slot.
- **Initial capabilities.** The capabilities of the fixed slots and of the
  grants of a child, which the commit puts into its table before its first
  instruction ([Initial capabilities](#initial-capabilities)).
- **Staging record.** `creation::Staging` (planned): the record in the
  process slot of each process that holds the creation of a child in
  progress: the two slots of the creator's table, the masks of the fixed
  slots, the shares, the image, its plan and the grants. It is empty when
  no creation is staged, and from the write-back of a commit to its result
  it holds the cursor of the commit instead.
- **Cursor.** The field of the staging record that holds, from the
  write-back of a commit or of the boot of the root to its result, the
  child, the step of the creation in progress and the frame of the plan in
  flight. It is empty between transitions.
- **Plan.** What an entry of this page gives the architecture crate to
  execute: a write plan of the
  [page-tables](../../memory/page-tables/contract.md#write-plans-and-publication)
  component, or a frame plan of the
  [vm](../../memory/vm/contract.md#acknowledgement-and-reclamation)
  component.
- **Step.** `creation::Step` (planned): what `spawn_commit`, `boot_root`
  and `acknowledge` give: a plan, or the result of the creation.
- **Composer.** `dispatch` (planned), the module of the core above this one
  that composes the operations of this page into transitions and
  acknowledges their plans; and the boot wiring, for the boot of the root.
- **Boot wiring.** The code of a board crate that runs on the boot CPU
  before the first entry from EL0, as in the
  [objects](../objects/contract.md#terms) and
  [address-space](../../memory/address-space/contract.md#terms) contracts.
- **Token.** What an access to state that is not per-CPU holds, as the
  [SMP design rules](../../../conventions/smp.md#s1-state-classes) state;
  with one CPU, the executing CPU holds every token.

## Entry points

The entries of the core are in the module `creation` of `krepi-kernel`
(planned). Seven entries are operations of the ABI inventory, in its
production range: `create_endpoint`, `create_notification`, `spawn_begin`,
`spawn_segment`, `spawn_grant`, `spawn_commit` and `spawn_abort`
(planned). Every argument of them is in a register, at most six for a call,
so no operation of this page reads a user buffer. Their operation numbers,
the registers of their arguments and results, the values of the classes
and the numeric values of their errors belong to the inventory; this page
names the arguments and the results and fixes the fields of the registers
that pack several of them. The other entries are called by the composers.
The first row holds constants.

| Entry point | Kind | Called by | ABI operation | Rules |
| --- | --- | --- | --- | --- |
| `creation::SPAWN_GRANTS`, `PROCESS_SLOT` and `THREAD_SLOT` (planned) | Constants, host-testable | The entries of this page; the boot wiring, for the handles of the root's first capabilities in the boot information; the ABI inventory, which gives the fixed slots to EL0 (planned) | None | [Initial capabilities](#initial-capabilities), [The boot of the root](#the-boot-of-the-root) |
| `creation::create_endpoint` (planned) | Write entry on the copies of a write set, host-testable | `dispatch` (planned), for the operation `create_endpoint` | `create_endpoint` | [Rights](#rights), [Endpoints](#endpoints), [Quotas and admission](#quotas-and-admission), [Capabilities of new objects](#capabilities-of-new-objects) |
| `creation::create_notification` (planned) | Write entry on the copies of a write set, host-testable | `dispatch` (planned), for the operation `create_notification` | `create_notification` | [Rights](#rights), [Notifications](#notifications), [Quotas and admission](#quotas-and-admission), [Capabilities of new objects](#capabilities-of-new-objects) |
| `creation::spawn_begin` (planned), with the value type `creation::Staging` | Write entry on the copies of a write set, host-testable | `dispatch` (planned), for the operation `spawn_begin` | `spawn_begin` | [Rights](#rights), [Child processes](#child-processes), [Quotas and admission](#quotas-and-admission) |
| `creation::spawn_segment` (planned) | Write entry on the copies of a write set, host-testable | `dispatch` (planned), for the operation `spawn_segment` | `spawn_segment` | [Child processes](#child-processes) |
| `creation::spawn_grant` (planned) | Write entry on the copies of a write set, host-testable | `dispatch` (planned), for the operation `spawn_grant` | `spawn_grant` | [Initial capabilities](#initial-capabilities) |
| `creation::spawn_commit` (planned), with the value type `creation::Step` | Write entry on the copies of a write set, host-testable; gives plans | `dispatch` (planned), for the operation `spawn_commit` | `spawn_commit` | [Rights](#rights), [Child processes](#child-processes), [Initial capabilities](#initial-capabilities), [Quotas and admission](#quotas-and-admission), [Capabilities of new objects](#capabilities-of-new-objects) |
| `creation::spawn_abort` (planned) | Write entry on the copies of a write set, host-testable | `dispatch` (planned), for the operation `spawn_abort` | `spawn_abort` | [Child processes](#child-processes) |
| `creation::acknowledge` (planned) | Write entry on the copies of a write set, host-testable; gives the next step | The dispatch of the core (planned), after the architecture crate has executed a plan that a commit gave, for the caller whose staging record holds the cursor; the boot wiring, after it has executed a plan of the boot of the root | None | [Child processes](#child-processes), [The boot of the root](#the-boot-of-the-root) |
| `creation::boot_root` (planned) | Write entry on the copies of a write set, host-testable; gives plans | The boot wiring, once, after it has built the kernel root with the page pool and before the first return of the root | None | [The boot of the root](#the-boot-of-the-root) |

## Extractability

The module `creation` of the core (planned), in `kernel/src/creation.rs`
(planned), follows the
[provable Rust subset](../../../conventions/provable-subset.md): the
checks and write sets of the seven operations, the staging records with
their cursors, the steps of a commit and of the boot of the root, and the
acknowledgement of their plans. It is in layer 8 of the
[module order](../../../architecture.md#module-order-in-the-core). It
refers to `objects`, for slots, owners, quota records and write sets;
`context`, for the initial context of a thread; `loader`, for
`loader::validate` and the plan of an image; and `address_space`, for the
directory of the boot bundle, the ASIDs, the segments of the table pool and
the layout of the EL0 window, all of layer 1; to `page_tables` of layer 2,
for the lower tables of a new process and their write plans; to
`capabilities` and `ledger` of layer 4, for lookups, installation,
reservation and commit, and for the admission of budgets; to `vm` and
`scheduler` of layer 5, for the page pool and the VM head, and for the
admission of a thread; to `ipc` of layer 6, for the initialization of an
endpoint; to `lifecycle` of layer 7, for the state of a new process and
whether a process is alive; and to the kernel root. It refers to no module
of its own layer or above it, which is `dispatch`, and not to `waits`: the
free slot of a notification already holds its initial state
([Notifications](#notifications)).

- **Reads across layers.** Whether the process of the thread that an
  endpoint binds is alive is a state of `lifecycle`, a lower layer, which
  `create_endpoint` reads with `lifecycle::is_alive` (planned). No entry of
  this page reads or writes the destruction of a process; the composition
  of its steps with the entries of `vm` and the other components below is
  the lifecycle component's.
- **Visibility.** Its items are `pub(crate)` except the rows that the boot
  wiring calls, `boot_root` and `acknowledge`, with the value type `Step`
  and the constants of the first row
  ([provable core](../../../architecture.md#the-provable-core)). The write
  entries receive the one kernel root by `&mut`
  ([rule 3](../../../conventions/provable-subset.md#3-flat-relations-and-one-kernel-root))
  and the write-set buffer, the scheduler record and the budget ledger of
  the executing CPU by explicit `&mut` arguments
  ([rule 8](../../../conventions/provable-subset.md#8-no-interior-mutability)).
- **No hardware action.** The module touches no register, writes no frame
  and defines no callback for a hardware action: every change of a table
  and of the bytes of a frame is a plan that the architecture crate
  executes, with `krepi_arch::mmu::apply` and `krepi_arch::frames::apply`,
  which are open obligations of the
  [page-tables](../../memory/page-tables/contract.md#open-obligations) and
  [vm](../../memory/vm/contract.md#open-obligations) contracts, and a
  creation continues through `acknowledge` once a plan has been executed.
  The module has no adapter of its own.

The prototype's spawn controller and execution manager allocated, zeroed
and prepared the memory of a new domain through callbacks; their rules are
sources of this page ([References](#references)). The contract is written
before its code, so this section lists no source paths; the change that
adds the module writes its `paths` block here.

## Rights

- **The creation right.** `create_endpoint`, `create_notification`,
  `spawn_begin` and `spawn_commit` look up a handle `create` for a process
  with CREATE, and the process that the capability names must be the
  caller's own (`NotOwnProcess`, object state). So the owner of every
  object that a creation makes is the caller's process, and no right
  authorizes a creation that another process owns or pays for. CREATE on a
  capability to another process holds the right and names the wrong
  process; it is not `PermissionDenied` of the capabilities component,
  which names a right that an entry lacks.
- **Who holds it.** The root holds CREATE on itself from its boot
  ([The boot of the root](#the-boot-of-the-root)). A child holds it only
  when its creator sets CREATE in the mask of the fixed slot of its process
  ([Initial capabilities](#initial-capabilities)): that capability is a
  descendant of an entry of the creator, so the creator withdraws the
  creation right that it gave by a
  [revocation](../capabilities/contract.md#revocation) of that entry or of
  an ancestor.
- **By operation.** Each operation needs the rights below, constants of the
  operation that its lookups check, and never an argument
  ([rights of an operation](../capabilities/contract.md#rights)):

| Operation | Handle | Kind | Rights |
| --- | --- | --- | --- |
| `create_endpoint` | `create`; `thread` | Process; thread | CREATE; CONTROL, which binds the thread as the receive thread of the endpoint |
| `create_notification` | `create` | Process | CREATE |
| `spawn_begin` | `create` | Process | CREATE |
| `spawn_segment` | None | - | None: it changes only the staging record of the caller |
| `spawn_grant` | `source` | Any kind | GRANT and every requested right, as for a derivation |
| `spawn_commit` | `create`; the source of each grant | Process; any kind | CREATE; GRANT and the requested rights of the grant |
| `spawn_abort` | None | - | None: it changes only the staging record of the caller |

- **Rights of the new capabilities.**

| Capability | Table and slot | Rights |
| --- | --- | --- |
| The first capability of an endpoint | The caller's, at the slot that it names | Every right of the kind: SEND, RECEIVE, GRANT and REVOKE |
| The first capability of a notification | The caller's, at the slot that it names | Every right of the kind: SIGNAL, WAIT, GRANT and REVOKE |
| The first capability of a child | The creator's, at the slot that it names in `spawn_begin` | Every right of the kind: OBSERVE, CONTROL, GRANT, REVOKE and CREATE |
| The first capability of the thread of a child | The creator's, at the slot that it names in `spawn_begin` | Every right of the kind: OBSERVE, CONTROL, GRANT and REVOKE |
| The capability of `PROCESS_SLOT` of a child | The child's, slot 0 | The mask of that slot, a subset of OBSERVE, CONTROL, GRANT, REVOKE and CREATE; none for the mask 0 |
| The capability of `THREAD_SLOT` of a child | The child's, slot 1 | The mask of that slot, a subset of OBSERVE, CONTROL, GRANT and REVOKE; none for the mask 0 |
| A grant | The child's, at the slot that the creator names in `spawn_grant` | The requested rights, a subset of the rights of the source |
| The root's capability to itself | The root's, slot 0 | OBSERVE, CONTROL, GRANT, REVOKE and CREATE |
| The root's capability to its thread | The root's, slot 1 | OBSERVE, CONTROL, GRANT and REVOKE |

- **Masks of the fixed slots.** The mask of the fixed slot of the process
  takes the bits 0 to 4 and that of the thread the bits 0 to 3; a mask of
  the thread with bit 4, which the kind of a thread does not define, is
  refused with `InvalidRights` of the capabilities component, as
  `Tables::install` refuses such a bit. A mask of 0 leaves its slot empty.
  CREATE reaches a child only when its creator sets it.
- **The rechecks of a commit.** The rights of a creator can change between
  its `spawn_begin` and its commit, so the commit makes again, before its
  first write, four kinds of checks: the lookup of `create`, of any handle
  of the caller with CREATE on its own process, not only the handle of its
  `spawn_begin`; the two slots of the creator's table; the shares against
  what the creator has left, with the quotas and the admission; and each
  grant, whose source it looks up again as `Tables::reserve` does
  ([Child processes](#child-processes)). So a revocation of the creation
  right or of the source of a grant that is pending refuses the commit with
  `RevocationPending`, and one that has removed the capability with the
  error of its lookup, and the staging record stays as it was. The checks
  of `spawn_begin` and of `spawn_grant` refuse early only.
- **The child.** The creator's two new capabilities hold CONTROL and
  OBSERVE on the child and its thread; the kill, the reaping by the owner,
  the queries and the subscription to the death notification that these
  rights authorize are operations of the
  [lifecycle](../lifecycle/contract.md#entry-points) component.

## Endpoints

`create_endpoint(create, thread, slot)` creates an endpoint bound to the
thread that the caller's capability `thread` names, owned by the caller,
and puts its first capability into slot `slot` of the caller's table. Its
result is the handle of that capability.

- **Checks.** In this order, each before the first write:
  1. the form of the arguments: `slot` is below `capability_slots`
     (`InvalidSlot` of the capabilities component);
  2. the lookups of `create`, for a process with CREATE, and of `thread`,
     for a thread with CONTROL, with `Tables::lookup` of the
     [capabilities](../capabilities/contract.md#lookup) component; when
     both fail, the error of the earlier place in the order of
     [Errors](#errors) decides, and at the same place that of `create`;
  3. object state, after the errors of object state of the lookups: the
     process of `create` is the caller's (`NotOwnProcess`); the process of
     the bound thread, which the thread slot records, is alive by
     `lifecycle::is_alive` (`ProcessNotAlive`); `slot` holds no capability
     (`SlotOccupied`) and has not retired (`GenerationExhausted` of the
     capabilities component), the checks of `Tables::install`;
  4. the caller's quota: `QuotaRecord::check` of its item of endpoints with
     1 (`QuotaExceeded` of the objects component);
  5. shared capacity: `ObjectTable::choose` of the endpoint pool in the
     ordinary class (`PoolExhausted` of the objects component).
- **Write.** In one write set: `ObjectTable::occupy` of the chosen slot
  with the caller as its owner; `QuotaRecord::charge` of one endpoint to the
  caller, ordinary; `ipc::init_endpoint(endpoint, thread)` with the
  reference of the thread that the lookup gave
  ([endpoint queues](../../ipc-waits/ipc/contract.md#endpoint-queues));
  and `Tables::install` of the first capability into `slot`, with every
  right of an endpoint
  ([Capabilities of new objects](#capabilities-of-new-objects)).
- **The bound thread.** It may belong to another process than the caller.
  The creation writes nothing into its thread slot or its process: no
  count of references and no pin, so the endpoint holds back the
  reclamation of neither. The binding is a reference that goes stale when
  the thread is reaped; while the process of the bound thread is not alive,
  the endpoint is not served and a call to it ends with `PeerClosed`
  ([bound thread](../../ipc-waits/ipc/contract.md#bound-thread)), and the
  destruction of that process ends the calls queued on it
  ([destruction](../lifecycle/contract.md#destruction)).
- **Release.** The endpoint is released when the last capability of its
  current generation is deleted
  ([capability counts](../capabilities/contract.md#capability-counts)), or
  in a step of the destruction of its owner; no entry of this page takes
  part in either.

## Notifications

`create_notification(create, slot)` creates a notification owned by the
caller and puts its first capability into slot `slot` of the caller's
table. Its result is the handle of that capability.

- **Checks.** In this order, each before the first write: the form,
  `slot` below `capability_slots` (`InvalidSlot`); the lookup of `create`
  for a process with CREATE; object state, after the errors of object state
  of the lookup: the process of `create` is the caller's (`NotOwnProcess`),
  and `slot` holds no capability (`SlotOccupied`) and has not retired
  (`GenerationExhausted`); the caller's quota, `QuotaRecord::check` of its
  item of notifications with 1 (`QuotaExceeded`); shared capacity,
  `ObjectTable::choose` of the notification pool in the ordinary class
  (`PoolExhausted`).
- **Write.** In one write set: `occupy` of the chosen slot with the caller
  as its owner, `charge` of one notification to the caller, ordinary, and
  `install` of the first capability into `slot`, with every right of a
  notification.
- **The initial state.** A free notification slot holds the word 0 and an
  empty waiter queue and direct queue, the initial state of the
  [waits](../../ipc-waits/waits/contract.md#notifications) component: the
  boot zeroes the storage of the pools and the release of a slot clears
  the fields of its object
  ([identities and generations](../objects/contract.md#identities-and-generations)).
  So `occupy` gives the new notification its initial state, and no entry of
  the waits component takes part in its creation.
- **No recipient.** The operation takes no thread: a notification has no
  recipient, any holder of WAIT may wait on it and any holder of SIGNAL may
  signal it. The binding of an interrupt to a notification belongs to the
  device-authority rules of the devices and DMA domain (planned).
- **Release.** As for an endpoint.

## Child processes

A child is created in steps, each a call: `spawn_begin` stages the
creation, `spawn_segment` adds a segment of its image, `spawn_grant` adds a
grant, `spawn_commit` checks everything again and creates the child, and
`spawn_abort` discards what is staged. All their arguments are in
registers.

**The staging record.**

- Each process slot holds one staging record, so a process stages at most
  one creation at a time. The release of a process slot clears it with the
  other fields of the process, so a new process finds it empty.
- It holds values only: the two slots of the creator's table, the two
  masks, the five shares, the image, the plan of the image with at most as
  many segments as the hard limit of the loading component allows, 8
  (planned), and at most `SPAWN_GRANTS` grants, each the handle of its
  source in the creator's table, its rights and its slot in the child's
  table. A handle names an entry of the caller's own table with the
  generation of its slot, so a grant whose source has been deleted goes
  stale lazily and its commit fails at the lookup.
- It occupies no object slot, page, table or ASID, so the destruction of a
  process that has staged a creation has nothing of it to release, and the
  lifecycle component does not read it. No transaction identifier exists:
  the staging record is named by its process.

**Staging.** `spawn_begin(create, slots_and_masks, page_shares,
object_shares, image)` stages a creation. Its packed registers hold these
fields, every other bit 0:

| Register | Bits | Field |
| --- | --- | --- |
| `slots_and_masks` | 0 to 15 | The slot of the creator's table for the capability to the child |
| `slots_and_masks` | 16 to 31 | The slot of the creator's table for the capability to the thread of the child |
| `slots_and_masks` | 32 to 36 | The mask of `PROCESS_SLOT` |
| `slots_and_masks` | 37 to 41 | The mask of `THREAD_SLOT` |
| `page_shares` | 0 to 31 | The share of committed VM pages |
| `page_shares` | 32 to 63 | The share of private pages of loaded images |
| `object_shares` | 0 to 20 | The share of child processes |
| `object_shares` | 21 to 41 | The share of endpoints |
| `object_shares` | 42 to 62 | The share of notifications |
| `image` | 0 to 63 | The index of the image in the directory |

- **Checks.** In this order, each before the first write:
  1. the form of the arguments: no bit outside the fields is set
     (`ReservedBits`); both slots are below `capability_slots`
     (`InvalidSlot`) and differ (`SameSlot`); the mask of the thread has no
     bit 4 (`InvalidRights`); and a fixed slot whose mask is not 0 is below
     `capability_slots` (`InvalidSlot`), so in a table of one slot only the
     mask of the process may be set;
  2. handle resolution and rights: the lookup of `create` for a process
     with CREATE; then the image: `Directory::entry` of `image` gives an
     entry of the kind Image (`NoImage`);
  3. object state, after the errors of object state of the lookup: the
     process of `create` is the caller's (`NotOwnProcess`); the caller's
     staging record is empty (`Staged`); each of the two slots, the slot of
     the process first, holds no capability (`SlotOccupied`) and has not
     retired (`GenerationExhausted`);
  4. the caller's quota: for the items child processes, endpoints,
     notifications, committed VM pages and private pages of loaded images,
     in this order, `QuotaRecord::check` of the share, with the share and 1
     for child processes, since the child itself is charged to that item
     (`QuotaExceeded`).
- **Write.** 1 item: the caller's process slot, whose staging record
  becomes the slots, the masks, the shares and the plan of the image with
  no segment. The result is `ok`.
- **Early checks.** `spawn_begin` refuses early what its commit would
  refuse; the commit makes these checks again.

**Segments.** `spawn_segment(offset, file_bytes, address, memory_bytes,
flags)` adds one segment to the plan of the staging record: the range of
`file_bytes` bytes from the offset `offset` of the image, mapped at the
virtual address `address` with `memory_bytes` bytes in memory and the
access `flags`.

- **Checks.** `loader::validate(plan, step, limits)` (planned), a function
  of the loading component that writes nothing, with the plan of the
  staging record, none when the record is empty, the step of a segment and
  the limits of the loading part of the capacity record. Its checks of the
  form of the segment come first; a plan of none is refused with
  `NotStaged` at the first place of object state; its other checks of
  object state, the range within the image and no page shared with a
  staged segment, and of the caller's quota, the number of segments and
  the private pages of the image within their limits, follow
  (planned). The errors of `spawn_segment` are those of `validate` in its
  order, and `NotStaged`.
- **Write.** 1 item: the caller's process slot, whose plan gains the
  segment. The result is `ok`.

**Abort.** `spawn_abort()` refuses an empty staging record (`NotStaged`,
object state) and otherwise empties it, 1 item; the result is `ok`. It
takes no handle, so a creator whose creation right has been revoked still
discards its staging.

**The commit.** `spawn_commit(create, entry, class_and_ceiling,
amount_control, amount_interactive, amount_background)` creates the child
of the staging record. `entry` is the virtual address of its first
instruction. `class_and_ceiling` holds, in bits 0 to 7, the class of the
thread of the child and, in bits 8 to 15, its service ceiling, each one of
the three classes in the encoding of the ABI inventory, every other bit 0;
the three amounts are the amounts of the classes control, interactive and
background that the thread receives
([admission](../../scheduling/scheduler/contract.md#admission)). Its
result is the handles of the two new capabilities of the creator's table,
the child's first.

- **Checks.** The commit calls `loader::validate` with the plan of the
  staging record and the step of a commit, and makes its own checks; when
  both find errors, the error of the earlier place in the order of
  [Errors](#errors) decides, and at the same place the order below. Each
  is made before the first write:
  1. the form of the arguments: `class_and_ceiling` sets no other bit and
     names two classes (`InvalidClass`); the amount of the class is not 0,
     and every amount of a class above it is 0 (`InvalidConfiguration` of
     the budget-ledger component, the first check of `ledger::admit`);
     `entry` is a multiple of 4 (the step of a commit of `validate`,
     planned);
  2. handle resolution and rights: the lookup of `create` for a process
     with CREATE; then the lookup of the source of each grant, in the order
     in which they were staged, for any kind with GRANT and the rights of
     the grant, as `Tables::reserve` makes it; at the same place, that of
     `create` first;
  3. object state, after the errors of object state of these lookups: the
     process of `create` is the caller's (`NotOwnProcess`); the staging
     record holds a creation (`NotStaged`); the plan holds at least one
     segment and `entry` lies in an RX segment (the step of a commit of
     `validate`, planned); each of the two slots of the creator's table,
     the slot of the process first, holds no capability (`SlotOccupied`)
     and has not retired (`GenerationExhausted`);
  4. the caller's quota: the checks of the shares of `spawn_begin` against
     the quota record of the caller at the time of the commit
     (`QuotaExceeded`); the private pages of the image, the pages of the
     memory of its RW segments and of its initial stack, within the limit
     of the loading part (the step of a commit of `validate`, planned) and
     at most the share of private pages (`ImageShare`); the class and the
     ceiling not above the class of the caller's thread (`AdmissionRejected`
     of the scheduler); each amount at most the holding of the caller's
     thread of its class (`AdmissionRejected` of the budget-ledger
     component);
  5. shared capacity: `ObjectTable::choose` of the process pool and then of
     the thread pool, in the ordinary class (`PoolExhausted`);
     `Asids::choose` (`Exhausted` or `GenerationExhausted` of the
     [address-space](../../memory/address-space/contract.md#address-spaces-and-asids)
     component); `Pool::free` at least the private pages of the image
     (`OutOfPages` of the vm component); and the new path of each grant at
     most `MAX_DEPTH` long (`DepthExceeded` of the capabilities component).
- **Fixed by the checks.** The checks also fix every plan and every value
  of the steps that follow the write-back. The initial context of the
  thread passes `Context::validate` with the bounds of the EL0 window,
  since `entry` lies in an RX segment and the top of the image window is a
  multiple of 4096. The check of the loading part at boot leaves every
  child the tables of its image window and at least the level 2 table and
  one level 3 table of its VM window (planned), so no `map_page` of a
  commit meets `OutOfTables`
  ([tables](../../memory/vm/contract.md#tables-and-extents)); the segments
  share no page and lie below the guard of the stack, so none meets
  `AlreadyMapped`.
- **Write.** In one write set, whose items
  [Check and execute](#check-and-execute) lists: `occupy` of the process
  slot and of the thread slot of the child, one pair, with the creator as
  their owner; `split` of each of the five shares from the creator to the
  child; `charge` of one child process to the creator and of the private
  pages of the image to the child, ordinary; `install` of the first
  capability of the child and of its thread into the two slots of the
  creator's table; `reserve` and `commit` of the fixed slots and then of
  the grants, in the order in which they were staged
  ([Initial capabilities](#initial-capabilities)); `ledger::admit` and
  `scheduler::admit` of the thread of the child for the creator's thread,
  with the class, the ceiling, the amounts and the time `now`, and, when
  the creator's record is the owner of the context of the current
  dispatch, `scheduler::requeue` of the current thread first
  ([admission and release](../../scheduling/budget-ledger/contract.md#admission-and-release));
  `lifecycle::init` (planned), which makes the child alive and links it
  last among the children of the creator
  ([children](../lifecycle/contract.md#children)); `Regions::new()` into
  the VM head of the region table of the child
  ([the VM head](../../memory/vm/contract.md#vm-window-and-regions)); and
  the staging record becomes the cursor of the commit.
- **After the write-back.** These writes and plans follow, in this order.
  None of them is an item of a write set, the checks fixed each of them,
  and none fails:
  1. `Asids::take` of the choice of the checks, and `Space::new` of its
     token, the record of the address space of the child
     ([ASIDs](../../memory/address-space/contract.md#address-spaces-and-asids));
  2. `Tables::new` on the segment of the process slot of the child,
     `TablePool::segment`
     ([table pools](../../memory/address-space/contract.md#table-pools));
  3. `Pool::take(child)` once for each private page, the pages of the RW
     segments in the order of the plan and of their addresses and then the
     pages of the initial stack from the lowest, before the first plan,
     so that no plan in flight needs a free frame
     ([the pool](../../memory/vm/contract.md#configuration-and-the-page-pool));
  4. the write plan of `Tables::clone_kernel_from` from the lower kernel
     set
     ([copying](../../memory/page-tables/contract.md#copying-the-kernel-tables));
  5. for each segment, in the order of the plan, and each of its pages in
     address order: for an RX segment, the write plan of
     `Tables::map_page` of the page of the boot bundle that holds it, with
     `UserReadExecute`; for an R segment, the same with `UserReadOnly`; for
     an RW segment, first, when the page holds bytes of the file, the frame
     plan `Copy(source, frame, bytes)` of those bytes, at most 4096, from
     their offset in the boot bundle into the frame of the page, and then
     the write plan of `map_page` of that frame with `UserReadWrite`;
  6. for each page of the initial stack, from the lowest, the write plan of
     `map_page` of its frame with `UserReadWrite`; the guard page below the
     stack stays unmapped;
  7. after the acknowledgement of the last plan: `Context::new(entry,
     top)` of the
     [context](../../boot-platform/context/contract.md#initial-context)
     component, `top` being the top of the image window, written as the
     saved context of the thread of the child, and the cursor emptied, in
     one write set of 2 items; then the result.
<!-- STOP: no entry of the vm contract lets this component name, after the takes of step 3, the frame that a take gave for a private page: Pool::take gives the address at the take, the vm contract requires every take before the first plan, the frames are found later only through the committed chain, which only the vm entries read, and the vm entry table holds its 12 core entries; a read entry of the chain, or a change of the order of the takes, is needed -->
- **The frame of a private page.** The frame of each private page is the
  one that the take of that page gave: the takes link the frames at the
  head of the committed chain of the child in the order of the pages, so
  the frame of each page is linked just before the frame of the page
  before it, as for a commit of the vm component, and the cursor holds the
  frame of the plan in flight.
- **The round trip of plans.** `spawn_commit` gives its first plan as its
  step; the architecture crate executes it, and the dispatch of the core
  (planned) calls `acknowledge` of the caller, whose staging record holds
  the cursor, for the next step. One plan is executed before the next is
  given, and no other entry runs on the lower tables of the child in
  between
  ([write plans](../../memory/page-tables/contract.md#write-plans-and-publication)).
  The vm component continues only the plans of its own entries
  ([frame plans](../../memory/vm/contract.md#acknowledgement-and-reclamation)),
  so `acknowledge` of this page continues the frame plans of a commit as
  well. No plan fails, so a commit has no error after its first plan.
- **One transition.** A commit runs to its result in one transition,
  without a preemption point, and its cursor is empty between transitions.
  It holds the token of the child from its checks to its result, so no CPU
  runs the child before its address space and its context are complete,
  and the token of the page pool from its check of `Pool::free` to its last
  take; with one CPU, no other thread runs before the result. The child
  first runs when the scheduler chooses its thread, which
  `scheduler::admit` has made ready.
- **Rollback.** Every check, the rechecks of the staging record among them,
  is made before the first write. The write phase can meet only
  `WriteSetFull` of `stage`, which a write set of at most 31 items never
  meets, and the fault-injection points of test builds
  ([write-set transactions](../objects/contract.md#write-set-transactions)),
  which discard the buffer; then no write outside the write set has been
  made and no plan given, the state is the state from before the commit,
  and the staging record is kept, to be committed again or discarded.
- **Image authority.** The images of release 0.1 come only from the boot
  bundle, which is part of the kernel image and read only
  ([integrity policy](../../../security.md#integrity-policy)), so any
  holder of CREATE on its own process may load any entry of the kind Image
  by its index.
- **W^X.** The loading component accepts only R, RX and RW segments
  (planned). The pages of RX and R segments are pages of the boot bundle,
  which no mapping makes writable; the pages of RW segments and of the
  stack are frames of the page pool, which no mapping makes executable. So
  no page of a child is writable and executable, by the same argument as
  for the root
  ([first process](../../memory/address-space/contract.md#first-process-and-boot-information)).
- **Code.** The RX pages of a child are pages of the boot bundle, which no
  CPU writes after the boot, so a commit makes no maintenance of the
  instruction cache. This relies on the maintenance of the image at boot
  covering the boot bundle to its end, with the functions of the
  [cache maintenance](../../boot-platform/boot/contract.md#cache-and-tlb-maintenance)
  of the boot component, whose `invalidate_code_to_pou` is one of its
  [open obligations](../../boot-platform/boot/contract.md#open-obligations);
  that range and its tests belong to the boot of each board and to the
  tests of the limits of loading (planned).
- **The child at its result.** It is alive, its thread is ready at the tail
  of the queue of its class, its address space maps its segments and its
  stack in its image window, its VM window holds no region, its table holds
  its initial capabilities and nothing else, and its private pages, frames
  that came zero from the pool, hold the bytes of the file of its RW
  segments and zero beyond them. A creation makes no registration for the
  death notification of its child: slot 0 of the registrations of the
  child, which is kept for its owner, stays empty until the owner watches
  the child
  ([death notifications](../lifecycle/contract.md#death-notifications)).

## Initial capabilities

The commit puts into the table of the child, in the write set that creates
it and so before the child's first instruction, the capabilities of its
fixed slots and its grants. Each is a child, in the derivation tree, of an
entry of the creator's table, and enters the table through
`Tables::reserve` and `Tables::commit` of the
[capabilities](../capabilities/contract.md#transfer) component, a copy whose
reservation and commit are in the same write set.

- **Fixed slots.** `PROCESS_SLOT`, slot 0, receives a derivation of the
  creator's new capability to the child, and `THREAD_SLOT`, slot 1, one of
  its new capability to the thread of the child, each with the mask of
  `spawn_begin` as its rights; a mask of 0 leaves the slot empty. Both
  sources are entries that the same write set installs, with every right of
  their kinds, GRANT among them. The capacity record allows a table of one
  slot, so `spawn_begin` refuses a fixed slot that is not below
  `capability_slots` and whose mask is not 0 (`InvalidSlot`), and
  `Tables::reserve` checks the slot again at the commit.
- **Grants.** `spawn_grant(source, rights, slot)` stages a copy of the
  caller's capability `source` with the rights `rights` into slot `slot`
  of the child's table. Its checks, in this order, each before the first
  write:
  1. the form of the arguments: `rights` is a well-formed mask
     (`InvalidRights`), and `slot` is below `capability_slots`
     (`InvalidSlot`);
  2. handle resolution and rights: the lookup of `source`, for any kind,
     with GRANT and every right of `rights`, as a derivation makes it
     ([derivation](../capabilities/contract.md#derivation-and-badges));
  3. object state, after the errors of object state of the lookup: the
     staging record holds a creation (`NotStaged`), and `slot` is neither a
     fixed slot nor the slot of a staged grant (`SlotTaken`);
  4. the caller's quota: fewer than `SPAWN_GRANTS` grants are staged
     (`GrantsFull`);
  5. shared capacity: the new path of the copy is at most `MAX_DEPTH` long
     (`DepthExceeded`).

  Its write is 1 item, the caller's process slot, whose staging record
  gains the grant, and its result is `ok`. The commit makes the checks of
  `Tables::reserve` again for each grant and then copies it, with the mode
  copy, after the fixed slots.
- **Slots.** An initial capability goes only to a fixed slot, which the
  rules of this page fix, or to the slot of a grant, which the creator
  names; the slots of the grants differ from each other and from the fixed
  slots. The kernel chooses no slot of the child's table: it only checks
  that each slot is below `capability_slots` and free. The table of a new
  process is empty in every slot at generation 1
  ([handles](../capabilities/contract.md#handles)), so the free slot is a
  check of the staging alone.
- **Descendants.** Every initial capability is a descendant of its source
  in the creator's table, so a revocation of that source, or of an
  ancestor of it, by a holder with REVOKE withdraws it in the two phases of
  [revocation](../capabilities/contract.md#revocation), whichever process
  holds it.
- **Only attenuation.** The rights of an initial capability are a subset of
  those of its source; a grant keeps the badge of its source, and the
  capabilities of the fixed slots have no badge. No initial capability
  enters a table without a source: installation stays the way of the first
  capability of an object and of a reply alone
  ([derivation](../capabilities/contract.md#derivation-and-badges)).
- **Confinement.** The commit is a channel that the creator and the child
  share, over which the creator, which holds GRANT on every source, passes
  the initial capabilities to the child; the child gains no authority
  otherwise before its first instruction
  ([unforgeable authority](../../../security.md#unforgeable-authority)).
- **Handles.** The result of the commit gives EL0 the two handles of the
  creator's table, and no slot number, generation or ASID of the child. The
  child names its fixed slots by the handles `0@1` and `1@1`, slot and
  generation, since its table is new, and the slots of its grants by a
  convention with its creator.
- **Start information.** A message of IPC carries two words, and a reply
  carries no capability
  ([messages](../../ipc-waits/ipc/contract.md#terms)). A creator gives its
  child the information to start with through a grant of SEND on an
  endpoint whose thread is the creator's: the runtime of the child calls
  that endpoint before its main function, and the creator replies with two
  words, 16 bytes, at a time, until the arguments and the environment are
  delivered. Which slot of the child's table holds that grant is a
  convention between the creator and the runtime of EL0 (planned), not a
  rule of this page; the kernel fixes slots 0 and 1 only. A child needs no
  endpoint of its own to start.

## Quotas and admission

**Items of each creation.**

| Operation | Checks of the caller's quota | Charges | Splits |
| --- | --- | --- | --- |
| `create_endpoint` | Endpoints, 1 | Endpoints, 1, and capability slots, 1, to the caller | None |
| `create_notification` | Notifications, 1 | Notifications, 1, and capability slots, 1, to the caller | None |
| `spawn_begin` | The five shares, the share of child processes with 1 more | None | None |
| `spawn_commit` | The five shares as for `spawn_begin`, against the record at the commit; the private pages of the image within the share of private pages | Child processes, 1, and capability slots, 2, to the creator; private pages of loaded images, the private pages of the image, and capability slots, one for each initial capability, to the child | The five shares, from the creator to the child |
| `boot_root` | None | [The boot of the root](#the-boot-of-the-root) | None |

- **Order in the write set.** `occupy` sets the quota record of the child
  to its starting state, the splits raise its limits by the shares, and the
  charge of its private pages then lies within its limit. Every charge and
  split of this page is of the ordinary class, except the charge of the
  root's pair to the kernel domain.
- **The child and its thread.** A child counts 1 in the child processes of
  its creator, together with its thread
  ([object kinds](../objects/contract.md#object-kinds-and-pools)).
- **Pages.** The committed VM pages of a child are limited by its share and
  by the cap of the capacity record, which its commits check
  ([quotas of the vm component](../../memory/vm/contract.md#quotas)). Its
  private pages are charged to its own item, whose limit is its share, in
  the write set of the commit, and are frames of the page pool, which
  return with the credit of each page in the revocation at its destruction.
  The limits of pages are not carved out of the pool, so a commit whose
  pool has fewer free frames than the private pages of its image fails for
  shared capacity, `OutOfPages`.
- **Tables.** The page-table pages of a child are those of the segment of
  its process slot, which `occupy` records; no creation charges them.
- **Admission.** The class, the ceiling and the amounts of the thread of a
  child are arguments of the commit, in registers, so their form is checked
  before handle resolution
  ([errors of the scheduler](../../scheduling/scheduler/contract.md#errors)).
  The commit composes `scheduler::admit` and `ledger::admit` for the
  creator's thread in the write set that creates the thread, with the time
  that the dispatch read on entry. When the record of the creator's thread
  is the owner of the context of the current dispatch, as it is when the
  creator runs on its own context, `scheduler::requeue` of the current
  thread comes first, which charges the dispatch up to `now`.
- **Order.** The caller's quota comes before shared capacity
  ([order](../objects/contract.md#metadata-quotas)). Within the caller's
  quota, a commit checks the quotas of the objects component, then the
  limit of private pages of the loading part, then the share of private
  pages, then the class and the ceiling, then the amounts. Within shared
  capacity, it checks the process pool, the thread pool, the ASIDs, the
  page pool and the depth of the grants, in this order.
- **The owner.** The owner of a child is the process of its creator, from
  the occupation of the child to its reap, and never changes
  ([calling domains](../objects/contract.md#metadata-quotas)); a process
  has one thread, created with it. So, when the owner reaps a child, the
  thread of the owner is the thread that created the child, as
  `ledger::release(owner, child)` requires
  ([release](../../scheduling/budget-ledger/contract.md#admission-and-release)),
  and the limits of the child return to the record from which they were
  split. The reaping of the lifecycle component
  ([reaping](../lifecycle/contract.md#reaping)) relies on this rule. A
  release in which a process has several threads restates it.
- **The root.** The boot of the root charges the root's pair to the
  control usage of the kernel domain, writes the root's starting limits,
  and charges the pages of the memory of the root's RW segments and of its
  stack to the root's own item of private pages of loaded images, as the
  private pages of a child count in its own
  ([The boot of the root](#the-boot-of-the-root)).
- **Conservation.** Every charge and split of this page is in the write
  set that occupies what it counts, so the
  [conservation](../objects/contract.md#metadata-quotas) of the objects
  component holds after every write-back; the private pages that a commit
  has charged and not yet taken count as the vm component counts them
  ([counting](../../memory/vm/contract.md#quotas)).

## Capabilities of new objects

- **Installation.** The first capability of a new endpoint, notification,
  child or thread of a child enters the caller's table by
  `Tables::install` into the slot that the caller names, a root entry with
  every right of its kind and no badge
  ([installation](../capabilities/contract.md#derivation-and-badges)); the
  slot is an argument, as the
  [internal choices](../../../security.md#internal-choices) of the security
  model state for capabilities.
- **Results.** A creation gives EL0 only handles of the caller's own table:
  no slot number of a pool, no generation of an object and no ASID, which
  are not observable outputs
  ([observable outputs](../../../security.md#observable-outputs)).
- **Counts.** A new object starts with one capability, its count of
  capabilities 1, or, for a child and its thread, one more for each fixed
  slot whose mask is not 0
  ([capability counts](../capabilities/contract.md#capability-counts)).
- **No reference.** A creation writes no count of references, no pin and no
  strong reference into any object: not into the bound thread of an
  endpoint, its owner or the creator of a child. An endpoint or a
  notification is released when its last capability is deleted or when its
  owner is destroyed, and a process and its thread when they are reaped,
  whatever capabilities to them remain
  ([releases](../objects/contract.md#metadata-quotas)).

## The boot of the root

`boot_root` makes steps 3, 5 and 7 of
[the first process](../../memory/address-space/contract.md#first-process-and-boot-information)
of the address-space component; the boot wiring makes the others. It is the
boot of the root that the entry tables of the objects, capabilities,
budget-ledger and scheduler components name, and not an operation of the
ABI. The boot wiring calls it once, after it has checked the directory and
the capacity record, the object part, the VM part and the loading part
among them, carved the storage of the objects component, the table pool,
the root's private allocation, the page pool and its metadata, and built
the object table, the ASID allocator, the ledger and the run queues of the
boot CPU, the page pool and the kernel root.

- **Arguments.** The capacities of the objects component; the `Config` of
  the VM part, from which it reads `root_vm_pages`
  ([configuration](../../memory/vm/contract.md#configuration-and-the-page-pool));
  the limits of the loading part (planned), from which it reads the root's
  limit of private pages of loaded images; the root plan of
  `Directory::root_plan`; the base of the root's private allocation; the
  root entry of the header of the directory; and the time `now`.
- **Check.** `capability_slots` is at least 2, so that the table of the
  root holds its fixed slots (`RootSlots`). The objects component allows a
  table of one slot, so the boot checks this before the first write and
  stops at the error, without a fallback to the defaults. The other checks
  of its entries hold at boot: the pools are empty, the first ASID is free,
  the root flag of the ledger is clear, and the checks of the directory and
  of the root plan have passed.
- **Write.** In one write set: `occupy` of the root's process slot and
  thread slot in the control class, owned by the kernel domain; `charge` of
  the pair to the control usage of the kernel domain's child processes;
  `start_root` of the root's starting limits that `root_limits` gives, with
  `root_vm_pages` and the root's limit of private pages of the loading part
  ([the root](../objects/contract.md#metadata-quotas)); `charge` of the
  root's private pages, the pages of the memory of its RW segments and its
  16 pages of stack, to its item of private pages of loaded images,
  ordinary; `install` of the root's capability to itself into
  `PROCESS_SLOT`, with OBSERVE, CONTROL, GRANT, REVOKE and CREATE, and of
  its capability to its thread into `THREAD_SLOT`, with OBSERVE, CONTROL,
  GRANT and REVOKE; the capability to the device directory as the
  device-authority rules of the devices and DMA domain state (planned);
  `ledger::admit` of the root; `scheduler::admit` of the root's thread in
  the class control with the ceiling control, the kernel domain as its
  creator; `lifecycle::init` of the root with the kernel domain as its
  owner, which keeps no chain of children; `Regions::new()` into the root's
  VM head; and the staging record of the root becomes the cursor of the
  boot.
- **After the write-back.** `Asids::choose` and `take`, which give ASID 1 of
  generation 1, `Space::new` and `Tables::new` on the segment of the root's
  process slot; then the write plan of `clone_kernel_from`; then the write
  plans of `map_page` of the pages of the root plan, in the order and with
  the kinds of step 5 of the first process, the frame of a page of the
  private allocation being the base of the allocation and its offset in
  it; after the acknowledgement of the last plan, the initial context
  `Context::new(root_entry, ROOT_STACK_TOP)` of step 7, which passes
  `validate`, written as the saved context of the root's thread and the
  cursor emptied, in one write set of 2 items; then the result.
- **The round trip at boot.** The boot wiring executes each plan with
  `krepi_arch::mmu::apply` and calls `acknowledge` of the root for the
  next step. It makes step 4, which writes the root's private pages and the
  page of the boot information through the direct map, after it has
  executed the plan of `clone_kernel_from` and before it calls
  `acknowledge` for that plan, so the steps keep their order; no plan of
  steps 3 and 5 reads or writes those pages.
- **The root's private pages.** The pages of the memory of the root's RW
  segments and of its stack count in its item of private pages of loaded
  images, as the private pages of a child count in its own; the page of the
  boot information, like the pages of the boot bundle, counts in no item.
  The root's starting limit of the item is the root's limit of the loading
  part, which the check of the loading part at boot keeps at least these
  pages (planned), so the charge cannot fail. The pages stay with the
  owner identity `OWNER_ROOT_PAGES` for the whole boot, since the root is
  never destroyed ([the root](../lifecycle/contract.md#the-root)).
- **The root's capabilities.** Their slots are fixed: the root's process at
  `PROCESS_SLOT` and its thread at `THREAD_SLOT`, which the boot
  information names by the handles `0@1` and `1@1`, as the
  [determinism](../capabilities/contract.md#determinism) of the
  capabilities component states for the root. The root holds CREATE on
  itself and CONTROL on itself; whoever holds CONTROL on the root can stop
  the system, as the
  [lifecycle](../lifecycle/contract.md#the-root) component states.

## Errors

| Error | Rule broken | Entries | Place in the order of errors |
| --- | --- | --- | --- |
| `RootSlots` | A `capability_slots` below 2, the fixed slots of the root | `boot_root` | At boot, before the root is created |
| `ReservedBits` | A packed register with a bit outside its fields | `spawn_begin` | The form of the register arguments, first |
| `InvalidSlot` of the capabilities component | A slot of the caller's table, the slot of a grant, or a fixed slot whose mask is not 0, not below `capability_slots` | `create_endpoint`, `create_notification`, `spawn_begin`, `spawn_grant` | The form of the register arguments |
| `SameSlot` | The two slots of the creator's table of a `spawn_begin` are the same slot | `spawn_begin` | The form of the register arguments, after the `InvalidSlot` of those slots |
| `InvalidRights` of the capabilities component | A mask of the fixed slot of the thread with bit 4; the rights of a grant that are 0 or have a bit above bit 4 | `spawn_begin`, `spawn_grant` | The form of the register arguments |
| `InvalidClass` | A `class_and_ceiling` with a bit outside its fields, or a field that names no class | `spawn_commit` | The form of the register arguments, first |
| `InvalidConfiguration` of the budget-ledger component | An amount of the class of 0, or an amount above 0 for a class above it | `spawn_commit` | The form of the register arguments, after `InvalidClass` |
| `InvalidHandle`, `NoCapability`, `StaleHandle`, `WrongType` of the capabilities component | A handle that does not name a usable capability of the kind in the caller's table | Every operation that takes a handle | Handle resolution: the range, the empty slot, the generation, the type |
| `StaleReference` of the objects component | A capability whose object has been released | Every operation that takes a handle | Handle resolution: the liveness of the object |
| `NoImage` | An index that names no entry of the directory, or an entry of another kind than Image | `spawn_begin` | Handle resolution, after the lookup of `create` |
| `PermissionDenied` of the capabilities component | A capability without CREATE, a thread capability without CONTROL, or a source without GRANT or a requested right | Every operation that takes a handle | Rights |
| `RevocationPending`, `TransferPending` of the capabilities component | A capability of the subtree of a pending revocation or its target, or the source of a pending move | Every operation that takes a handle | Object state, first |
| `NotOwnProcess` | A capability with CREATE to another process than the caller's | `create_endpoint`, `create_notification`, `spawn_begin`, `spawn_commit` | Object state, after the errors of the lookups |
| `ProcessNotAlive` | A thread to bind whose process is not alive | `create_endpoint` | Object state, after `NotOwnProcess` |
| `Staged` | A `spawn_begin` whose caller has a creation staged | `spawn_begin` | Object state, after `NotOwnProcess` |
| `NotStaged` | A call whose caller has no creation staged | `spawn_segment`, `spawn_grant`, `spawn_commit`, `spawn_abort` | Object state: for `spawn_commit` after `NotOwnProcess`, for the others first after the errors of the lookups |
| `SlotTaken` | The slot of a grant that is a fixed slot or the slot of a staged grant | `spawn_grant` | Object state, after `NotStaged` |
| `SlotOccupied`, `GenerationExhausted` of the capabilities component | A slot of the caller's table that holds a capability or has retired | `create_endpoint`, `create_notification`, `spawn_begin`, `spawn_commit` | Object state, last |
| `QuotaExceeded` of the objects component | A creation or a share beyond what the caller's limit leaves | `create_endpoint`, `create_notification`, `spawn_begin`, `spawn_commit` | The caller's quota, first |
| `ImageShare` | Private pages of the image beyond the share of private pages | `spawn_commit` | The caller's quota, after the limit of the loading part |
| `AdmissionRejected` of the scheduler | A class or a ceiling above the class of the creator's thread | `spawn_commit` | The caller's quota, after `ImageShare` |
| `AdmissionRejected` of the budget-ledger component | An amount beyond the creator's holding of its class | `spawn_commit` | The caller's quota, last |
| `GrantsFull` | A grant beyond `SPAWN_GRANTS` | `spawn_grant` | The caller's quota |
| `PoolExhausted` of the objects component | No free slot of the ordinary class in the endpoint, notification, process or thread pool | `create_endpoint`, `create_notification`, `spawn_commit` | Shared capacity: the process pool, then the thread pool |
| `Exhausted`, `GenerationExhausted` of the address-space component | No ASID that can be taken | `spawn_commit` | Shared capacity, after the pools |
| `OutOfPages` of the vm component | Fewer free frames than the private pages of the image | `spawn_commit` | Shared capacity, after the ASIDs |
| `DepthExceeded` of the capabilities component | A grant whose copy would have a path longer than `MAX_DEPTH` | `spawn_grant`, `spawn_commit` | Shared capacity, last |
| `InvalidState` | An `acknowledge` whose process has no cursor, a call that no composer makes | `acknowledge` | Object state |

The errors of `loader::validate` for a segment and a commit are those of
the loading component (planned), at the places that its order gives, and
`spawn_segment` and `spawn_commit` return them as they are.

- **Order.** Each entry checks in the order of its rule section and
  returns the first error; where an operation composes the checks of
  another component, the error of the earlier place decides, and at the
  same place the order of the rule section. The places of the last column
  are those of the order of errors of the
  [security model](../../../security.md#internal-choices): the operation
  number and version, which the dispatch of the ABI checks with the
  reserved and unused registers; the form of the register arguments;
  handle resolution; rights; the range of user buffers and the form of
  argument structures, which no operation of this page has; object state;
  the caller's quota; shared capacity. `NoImage` takes a place in handle
  resolution, since the index names an object of the boot bundle.
- **No change on failure.** No error changes state: an entry that returns
  an error leaves every field of the kernel state as it was, the copies in
  its write set and the staging record included, gives no plan and writes
  no counter; a composing operation that meets an error discards its
  buffer, so the kernel state after any failed operation equals the state
  before it. There is no exception. The settlements before the operation in
  its transition are transactions of their own and stay. The result
  registers of a failed system call follow the
  [observable outputs](../../../security.md#observable-outputs) of the
  security model, and the errors of shared capacity are outside the output
  sources there.
- **Totality.** `InvalidState` of `acknowledge`, and the errors of the
  entries of other components that the checks of this page exclude before
  the first write, among them `WrongPool` of `init_endpoint`, `OutOfTables`
  and `AlreadyMapped` of `map_page` and `OutOfPages` of `Pool::take`,
  answer calls that no composer makes, and change nothing. A second
  `boot_root`, which the boot wiring never makes, is refused by the checks
  of `start_root` and of `ledger::admit` of the root.
- **Names.** The names are those of this contract; the numeric values of
  the errors that reach EL0 belong to the ABI inventory.

The prototype's execution manager had six errors whose rules are here, and
its spawn controller refused a request in nine ways. Here:

| Prototype error or refusal | Here |
| --- | --- |
| `InvalidLayout` | Moved to the dispatch component: the errors of `loader::validate` for a segment or a commit, and the limits of the loading part (planned) |
| `Quota` | Rewritten: `QuotaExceeded` of the objects component, for the items of the five shares and of the child; `ImageShare`, for private pages beyond their share |
| `GenerationExhausted` | Moved to the page-tables component: the generations of the owner identities of page allocations; a creation takes no page of the page ownership table at run time |
| `Page(_)` | Rewritten: `OutOfPages` of the vm component, a page pool with fewer free frames than the private pages of the image; `OutOfMemory` and `MetadataExhausted` of the page ownership table stop the boot only |
| `Object(_)` | Not kept as a wrapper: the errors of the objects and capabilities components that this page meets are returned as they are |
| `InvalidContext` | Moved to the context component: `context::Error`; the initial context of a creation passes `validate` by the checks of this page |
| A missing right, `PERMISSION_DENIED` | Moved to the capabilities component: `PermissionDenied` of the lookup; CREATE on another process is `NotOwnProcess` |
| An invalid handle or transaction, `INVALID_HANDLE` | Moved to the capabilities component: the errors of the lookup; a creation that is not staged is `NotStaged` |
| An authority that no longer exists, `OBJECT_GONE` | Moved to the objects component: `StaleReference`, a capability whose process has been reaped |
| A version that differs, `UNSUPPORTED_VERSION` | Moved to the dispatch component: its check of the version |
| An unused argument register that is not 0, `INVALID_ARGUMENT` | Moved to the dispatch component: its check of the unused registers |
| An unknown operation of spawning, `UNSUPPORTED_OPERATION` | Moved to the dispatch component: its check of the operation number |
| A transaction already pending, `INVALID_STATE` | Kept and rewritten: `Staged`, a `spawn_begin` whose caller has a creation staged, and `NotStaged`, the other calls of a child whose caller has none |
| The exhaustion of transaction identifiers, `OVERFLOW` | Not applicable: no transaction identifier exists, since a staging record is named by its process |
| A lack of capacity, `NO_CAPACITY` | Rewritten: the shared capacity of a commit, `PoolExhausted` of the process and the thread pool, `Exhausted` and `GenerationExhausted` of the ASIDs and `OutOfPages` of the page pool |

## Check and execute

Every write entry of this page makes all its checks before its first write,
then changes only the copies in the write set of its caller
([write-set transactions](../objects/contract.md#write-set-transactions)),
and its writes outside write sets and its plans follow the write-back. The
items of this page are the process slots, which hold the staging records,
and the items of the entries that it composes. The ASID allocator, the
record of an address space, the lower tables and the table pool, the page
pool with the metadata of its frames, and the bytes of the frames are no
items of a write set: the checks fix their writes, which follow the
write-back in a fixed order and cannot fail. So the write phase of every
entry can meet only `WriteSetFull` of `stage`, which the write sets below
never reach, and the fault-injection points of test builds, each of which
discards the buffer and leaves the state from before the entry, before any
write outside the write set and any plan. `acknowledge` has no
fault-injection point, since it follows a plan that has been executed.

| Entry | Checks before the first write | Write set | Writes after the write-back |
| --- | --- | --- | --- |
| `create_endpoint` | The slot, the two lookups, the process of `create`, whether the process of the thread is alive, the slot of the table, the quota, the pool | 4: the endpoint slot, the counts of the endpoint pool, the caller's process slot, the new entry | None |
| `create_notification` | The slot, the lookup, the process of `create`, the slot of the table, the quota, the pool | 4: the notification slot, the counts of the notification pool, the caller's process slot, the new entry | None |
| `spawn_begin` | The fields, the slots and the masks, the lookup, the image, the process of `create`, the staging record, the slots of the table, the shares | 1: the caller's process slot | None |
| `spawn_segment` | Those of `validate` for a segment, and the staging record | 1: the caller's process slot | None |
| `spawn_grant` | The rights and the slot, the lookup of the source, the staging record, the slot of the child, the number of grants, the depth | 1: the caller's process slot | None |
| `spawn_abort` | The staging record | 1: the caller's process slot | None |
| `spawn_commit` | Those of [the commit](#child-processes), with those of `validate` for a commit, the rechecks of the staging record among them | At most 31, listed below | The take of the ASID, the record of the address space, the table set, the take of each private frame; then the first plan |
| `acknowledge` | A cursor | 1: the process slot that holds the cursor; at the last step 2, with the thread slot of the new thread for its initial context | The next plan, with the table record that `map_page` writes, or nothing |
| `boot_root` | `capability_slots` | 10, below, and the items of the capability to the device directory that the device-authority rules add (planned) | The take of ASID 1, the record of the address space, the table set; then the first plan |

**The write set of a commit.** Its items, each counted once, by the items of
the [objects](../objects/contract.md#write-set-transactions) and of the
composed components:

| Items | Item | Changed by |
| ---: | --- | --- |
| 1 | The process slot of the creator | The five splits and the charges of a child process and of two capability slots in its quota record; its staging record, which becomes the cursor; and its last child, with its first child when it has none, in the chain of its children |
| 1 | The process slot of the child | Its quota record, from the starting state of `occupy` through the splits and the charges of its private pages and of its capability slots; and the state that `lifecycle::init` writes |
| 1 | The thread slot of the child | `occupy`, with the budget record of `ledger::admit` and the scheduling state of `scheduler::admit` |
| 2 | The counts of the process pool and of the thread pool | `occupy` |
| 2 | The entries of the creator's table that receive the capabilities to the child and to its thread | `install`, whose object slots and process slot are the three slots above |
| 2 | The entries `PROCESS_SLOT` and `THREAD_SLOT` of the child's table | `reserve` and `commit`, whose sources are the two entries above, without another child, whose object slots are the slots of the child and of its thread, and whose receiving process slot is that of the child |
| 16 | For each of at most `SPAWN_GRANTS` = 4 grants: the new entry of the child's table, its source, the former last child of its source and the object slot of its object | `reserve` and `commit` of a copy, whose receiving process slot is that of the child ([check and execute](../capabilities/contract.md#check-and-execute)) |
| 1 | The thread slot of the creator | `ledger::admit`, which lowers its holdings |
| 1 | The slot of the last thread of the queue of the class of the new thread | `scheduler::admit`, which links the new thread after it |
| 1 | The scheduler record of the executing CPU | `scheduler::admit` and `scheduler::requeue` |
| 1 | The class ledger of the class of the context of the current dispatch | `scheduler::requeue`, whose other items are the thread slot of the creator and the scheduler record |
| 1 | The process slot of the former last child of the creator | `lifecycle::init`, which makes the child its next sibling |
| 1 | The VM head of the region table of the child | `Regions::new()` |

So a commit writes at most 31 items, within $W$ = 64 of the objects
contract; a commit without a grant, a former last child or a `requeue`
writes fewer.

**The write set of the boot of the root.** The root's process slot and
thread slot, the counts of the process and of the thread pool, the record
of the kernel domain, the entries `PROCESS_SLOT` and `THREAD_SLOT` of the
root's table, the unallocated holdings of the ledger with its root flag,
the scheduler record of the boot CPU, whose queue of control is empty, and
the root's VM head: 10 items, beside those of the capability to the device
directory.

- The fault-injection points of a test build in the write phase of each
  entry but `acknowledge` leave the state from before the entry: the
  staging record, the pools, the tables, the quota records and the records
  of the ledger and of the scheduler as they were, and no ASID, table,
  frame or plan taken.
- A refused operation gives no plan and changes no table, no frame and no
  metadata. So after any failed entry of this page the state equals the
  state before it, the staging record included; there is no exception.

## Work bounds

- `create_endpoint` makes two lookups, each of at most 17 entries and one
  slot of the object table
  ([work bounds](../capabilities/contract.md#work-bounds)), and
  `ObjectTable::choose` scans at most the capacity of the endpoint pool;
  it writes 4 items. `create_notification` makes one lookup and scans at
  most the capacity of the notification pool.
- `spawn_begin` makes one lookup, reads one entry of the directory and
  checks five items; `spawn_segment` makes the checks of `validate`, which
  compares a segment with at most the 8 segments that a plan holds
  (planned); `spawn_grant` makes one lookup and forms a path of at most
  `MAX_DEPTH` references; `spawn_abort` makes a fixed number of steps. Each
  writes 1 item.
- `spawn_commit` makes at most 1 + `SPAWN_GRANTS` = 5 lookups, the checks
  of `validate` for a commit over at most 8 segments, two scans of
  `choose`, at most the capacities of the process and the thread pool, and
  `Asids::choose`, at most 255 ASIDs
  ([work bounds](../../memory/address-space/contract.md#work-bounds)); it
  writes at most 31 items. After the write-back it takes one frame for each
  private page, each in a fixed number of steps, at most the private pages
  of an image that the loading part allows (planned), and gives the plan of
  `clone_kernel_from` over at most the 32 tables of a set, one write plan
  of at most seven steps for each page that it maps
  ([work bounds](../../memory/page-tables/contract.md#work-bounds)), at
  most the pages of the image window that the check of the loading part at
  boot allows, and one frame plan of at most 4096 bytes for each page of
  an RW segment that holds bytes of the file. No creation takes a page of
  the page ownership table or adds an extent to it at run time: the private
  pages of a child are frames of the page pool, and the root's private
  allocation is the boot wiring's.
- `acknowledge` writes 1 or 2 items and gives at most one plan.
- `boot_root` writes 10 items and maps at most the pages of the root block
  and of the bundle window, one `map_page` each, at boot
  ([work bounds](../../memory/address-space/contract.md#work-bounds)).
- **No long operation.** The component has no long operation: a commit and
  the boot of the root run to their result without a preemption point, and
  every other entry to its end, and no progress of theirs is stored between
  two transitions. A commit maps and copies its whole image in one
  transition, the longest work of this page without a preemption point,
  bounded by the image window and the private pages that the loading part
  allows; the tests of the limits of loading measure it (planned).
- The constants are `SPAWN_GRANTS` = 4; `PROCESS_SLOT` = 0 and
  `THREAD_SLOT` = 1; `MAX_DEPTH` = 16 of the capabilities contract; and
  $W$ = 64 of the objects contract.

## Determinism

- **Slots of objects.** A new endpoint, notification, process and thread
  each take the lowest free slot of the ordinary range of their pool, and
  the root's pair that of the control class, by
  [the choice](../objects/contract.md#determinism) of the objects
  component; a new address space takes the lowest free ASID whose
  generation is not exhausted
  ([ASIDs](../../memory/address-space/contract.md#determinism)), the rules
  for slots of the
  [internal choices](../../../security.md#internal-choices).
- **Slots of capabilities.** The caller names the slot of each first
  capability and of each grant; the fixed slots are 0 and 1. The kernel
  chooses no slot of a table.
- **Frames.** The private pages of a child take the frames at the top of
  the free stack of the page pool, in the order of the pages
  ([determinism](../../memory/vm/contract.md#determinism)); the physical
  address of a frame is not an output.
- **Order of steps.** The fixed slots come before the grants, and the grants
  in the order in which they were staged; the plans of a commit follow the
  order of [Child processes](#child-processes): the segments in the order
  in which they were staged, their pages in address order, the copy of a
  page before its mapping, and the stack after the segments.
- **Admission.** A new thread joins the tail of the queue of its class
  ([run queues](../../scheduling/scheduler/contract.md#run-queues)).
- **Children.** The children of a process are linked in the order of their
  creation, which their slots, the lowest free, do not give; the
  destruction of their owner takes them in that order
  ([children](../lifecycle/contract.md#children)).
- **Handles.** A handle that a creation returns names a slot of the
  caller's own table with the generation of that slot for the caller, and
  the handles of the initial capabilities of a child those of its new
  table, so they follow from the history of those tables alone.
- **Time.** The admission takes the time that the architecture crate reads
  once on entry to the transition, [ND-01](../../../security.md#nd-01) of
  the register of
  [permitted nondeterminism](../../../security.md#permitted-nondeterminism),
  and the result of a creation does not depend on it. A creation has no
  preemption point, so the arrival of interrupts,
  [ND-02](../../../security.md#nd-02), changes none of its results.
- **Requests.** Requests that contend for a pool, a quota record, a
  staging record or the page pool take effect in the order in which they
  enter the kernel. With more than one CPU, the order in which CPUs take
  their tokens is the multicore interleaving of
  [ND-03](../../../security.md#nd-03); for each such order, the rules of
  this page fix the result.
- **Boot.** The root's slots, its ASID, its limits and its mappings follow
  from the capacity record, the directory and the constants, so cold boots
  of one image give the same root.

The component leaves no other choice open.

## State fields

| Field | Class | Lock or owner | Linearization point | Publication |
| --- | --- | --- | --- | --- |
| The staging record of each process: the two slots of the creator's table, the masks, the shares, the image, its plan and the grants, and, from the write-back of a commit or of the boot of the root to its result, the cursor | Per-process | The token of the process of the slot; with one CPU, the executing CPU | The write-back of the write set that changes it | Under the token of the process |
| The chain of the children of each process: the first and the last child of each process, and the previous and the next sibling of each child, in their process slots | Shared | The tokens of the process slots that a change of a link joins: a creation holds those of the creator, the child and the former last child, and a reap those of the owner, the child and its siblings | The write-back of the creation that links a child, and of the reap that unlinks it | Under the tokens, by the release of the locks that provide them once CPUs share them |

`lifecycle::init` links a child into the chain in the write set of its
creation, and the reap of the lifecycle component unlinks it; the other
fields of the state of a process are classified in the
[State fields](../lifecycle/contract.md#state-fields) of the lifecycle
contract. The slots, quota records and counts that a creation changes are
fields of the [objects](../objects/contract.md#state-fields) component;
the capability tables of the
[capabilities](../capabilities/contract.md#state-fields) component; the
budget records and run queues of the
[budget-ledger](../../scheduling/budget-ledger/contract.md#state-fields) and
[scheduler](../../scheduling/scheduler/contract.md#state-fields)
components; the address space, its ASID and its lower tables of the
[address-space](../../memory/address-space/contract.md#state-fields)
component; the saved context of the
[context](../../boot-platform/context/contract.md#state-fields) component;
and the page pool, the frames and the VM head of the
[vm](../../memory/vm/contract.md#state-fields) component.

## Testing obligations

- The host tests of the module `creation` (planned) replay every vector of
  [Legacy test vectors](#legacy-test-vectors) whose entry is on this page,
  with its expected output, and write their results for the comparison with
  the specification
  ([host results](../../../formal-verification.md#host-results)).
- Errors: each error of [Errors](#errors) through a call that gives it,
  compared field by field before and after, the staging record included,
  with no plan; for each pair of consecutive checks of an entry whose
  errors differ, a call that breaks both and gets the error of the
  earlier, the errors of `validate` against those of this page among them.
- For each of the three kinds of creation, endpoints, notifications and
  children: a creation that succeeds; one whose capability lacks its right;
  one whose quota is used up; and one that meets each fault-injection point
  of its write phase, after which the state is that from before. The
  endpoints and notifications of three rounds of creation and of the
  deletion of their last capability are released, and the counts of the
  pools and the usages return to those of the start after each round.
- Staging: a `spawn_begin` with a creation staged is `Staged`, and every
  other call of a child without one is `NotStaged`; a `spawn_abort` empties
  the record; a commit after the revocation of its creation right, pending
  and completed, after another creation has used the shares, after a slot
  of the creator's table has been filled, and after the revocation of the
  source of a grant, fails with the error of its recheck and keeps the
  staging record, which a second commit then commits.
- Images: an image that the checks of `validate` refuse and one that they
  accept; after the commit of the second, every page of an RX or R segment
  is the page of the boot bundle that holds it, with its kind; every page
  of an RW segment holds the bytes of the file and 0 beyond them; the stack
  pages read 0 and the guard is unmapped; the plans come in the order of
  [Child processes](#child-processes); and no page of the child is mapped
  writable and executable.
- Initial capabilities: masks of 0, of each bit and of every right for each
  fixed slot; a table with `capability_slots` 1, in which a mask of the
  thread that is not 0 is `InvalidSlot`; four grants with fewer rights than
  their sources and a badge, which the child holds with those rights and
  that badge, and a fifth, `GrantsFull`; the revocation of the creator's
  capability to the child, and of the source of a grant, which removes the
  child's capability; a child without CREATE, whose creation is
  `PermissionDenied`, and one with CREATE, whose objects it owns and pays
  for within its shares.
- Write sets: a commit with four grants, each with a former last child of
  its own source, a former last child of the creator and a creator that
  runs on its own context reaches 31 items, and every entry stays within
  the item counts of [Check and execute](#check-and-execute).
- Quotas: a property test with fixed seeds drives creations, splits,
  charges and the reaping of the lifecycle component over a tree of
  processes and checks after every write-back, against an independent
  model, the [conservation](../objects/contract.md#metadata-quotas) of the
  objects component and that the owner of every child is the process of its
  creator.
- The boot of the root: the record of the kernel domain with a control
  usage of 1; the root's limits for records of several values; the root's
  usage of private pages, the pages of its RW segments and its stack; its
  first capabilities at `0@1` and `1@1` with their rights; and a record
  with `capability_slots` 1, which stops the boot with `RootSlots`.
- QEMU tests on QEMU virt, from EL0, once the operations exist: the root
  creates an endpoint and a notification and a child from an image of the
  boot bundle with a grant of SEND on an endpoint of its own; the child
  runs its entry, calls that endpoint for its start information, reads its
  RW data and its zero stack, and ends; a child from an image whose
  segments are refused is not created. The 8 GB Pi 5 runs the same.
- The tests take their expected values from this page, from the vectors and
  from independent models, never from an earlier run of the code under
  test ([testing](../../../conventions/testing.md#independent-evidence)).

## Open obligations

The module `creation` has no `unsafe` code, no assembly and no MMIO, and
its entries are to be covered by its targets. The effects of a creation on
the state of other components that the specification of this component
does not describe are open obligations: the initialization of an endpoint
by the IPC component and the reading of the state of a process of the
lifecycle component in `create_endpoint`; the admission of the budget
ledger and of the scheduler, the state of the lifecycle component, the VM
head and the page pool of the vm component, the ASID, the address space
and the lower tables of the address-space and page-tables components and
the initial context of the context component, in `spawn_commit`, in
`acknowledge` and in `boot_root`. They are carried by the proof of object
lifetimes, waits and sequential composition, by release 0.2. The plans
that the entries give are executed by `krepi_arch::mmu::apply` and
`krepi_arch::frames::apply`, rows of the
[page-tables](../../memory/page-tables/contract.md#open-obligations) and
[vm](../../memory/vm/contract.md#open-obligations) obligations, and the
entries use the write-set buffer that the adapter of the objects component
lends, a row of the
[objects obligations](../objects/contract.md#open-obligations).

| Obligation | Kind | Verified state | Carrier | Stage |
| --- | --- | --- | --- | --- |
| `kernel/src/creation.rs#create_endpoint` (planned) | `code` | Reads and writes (composes `lifecycle::is_alive` and `ipc::init_endpoint` with the occupation, the charge and the installation of the new endpoint) | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/src/creation.rs#spawn_commit` (planned) | `code` | Reads and writes (composes `ledger::admit`, `scheduler::admit` and `scheduler::requeue`, `lifecycle::init`, `Regions::new`, `Pool::free` and `Pool::take`, `Asids::choose` and `Asids::take`, `Space::new`, `Tables::new` and the plans of the mapping of the image, with the occupation, the splits, the charges, the installations and the reservations of the creation) | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/src/creation.rs#acknowledge` (planned) | `code` | Reads and writes (gives the next plan of a commit or of the boot of the root, and writes the initial context of `Context::new` as the saved context of the new thread) | The proof of object lifetimes, waits and sequential composition | `0.2` |
| `kernel/src/creation.rs#boot_root` (planned) | `code` | Reads and writes (composes `QuotaRecord::start_root`, `ledger::admit`, `scheduler::admit`, `lifecycle::init`, `Regions::new`, `Asids::take`, `Space::new`, `Tables::new` and the plans of the mapping of the root, with the occupation, the charges and the installations of the root's first capabilities) | The proof of object lifetimes, waits and sequential composition | `0.2` |

## Legacy test vectors

The vectors are host tests of the prototype tree at
`prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`, 21 in all. Their
expected outputs are those that the test bodies assert, written in the
rules of this page. The vectors are not yet in a file of the repository,
so the section holds no `vectors` block.

| File | Vectors |
| --- | ---: |
| `src/objects/endpoints/tests/admission.rs` | 6 |
| `src/objects/endpoints/tests/lifetime.rs` | 4 |
| `src/objects/notifications/tests/admission.rs` | 7 |
| `src/objects/notifications/tests/lifetime.rs` | 4 |

- These are all the tests of the prototype's endpoints and notifications
  of its object pool; `src/objects/endpoints/tests.rs` and
  `src/objects/notifications/tests.rs` hold only fixtures and module
  declarations.
- The id of a vector is the path of its file below `src/objects/`, without
  the directories named `tests` and without `.rs`, with a hyphen between
  the parts and in place of each underscore, and the position of the test
  among the tests of its file, from 1.

A vector of this page is one test function. The vector file is to hold one
line for each case of a vector through an entry of this page, with the id
`<vector>.<n>`, `n` counting those cases from 1 in the order of the test; a
case that its row marks not applicable has no line, and a vector whose
Entry column names no entry of this page has none.

**The fixture.** The prototype's fixture keeps an object pool of 4
processes and 8 threads, with a control reserve of one of each, and 8
endpoints and 8 notifications. It creates the root's pair as a control
allocation and an ordinary process P with its thread S, the service or
recipient thread of the tests. Here the fixture is a table of
`processes=4 threads=8 endpoints=8 notifications=8` with
`capability_slots=16 reserved_processes=1 reserved_threads=1`, the other
capacities 1 and the other reserves 0, after the boot of the root R,
whose pair takes the reserved tails, and the commit of a child P of R,
with its thread S, in process slot 0 and thread slot 0, whose shares of
endpoints and notifications are 0. R's limits of endpoints and of
notifications are then 8 each, the ordinary capacities of their pools.

**Notation.** `R[s]` is slot $s$ of the table of R, and a handle is written
`<slot>@<generation>`. R[0] holds R's process with every right, `0@1`, and
R[1] its thread, `1@1`, from the boot; R[2] holds P, `2@1`, and R[3] holds
S, `3@1`, each with every right, from the commit. `count(O)` is the count
of capabilities of object O. The output of a call is `ok`, followed by its
result, or `err=<error>`, with the error by its name on this page or on the
objects and capabilities contracts. "After P has left Alive" is after the
kill of P by R through `2@1`, an operation of the
[lifecycle](../lifecycle/contract.md#kill) component.

**Behaviour changes.** These rules differ from the prototype:

- No creation pins a thread or counts references: the prototype's pin of
  the service or recipient thread, its counts of references with their
  overflow and underflow, and its explicit reap of an endpoint or a
  notification do not apply. An endpoint and a notification are released
  when their last capability is deleted or their owner destroyed.
- The creation of an endpoint needs CONTROL of the thread capability, where
  the prototype needed every right, so a capability with CONTROL alone
  succeeds; its refusal of a dying thread is `ProcessNotAlive`.
- A notification has no recipient, no flag of closure by the user and no
  native variant: the refusals for its recipient do not apply.
- A generation belongs to a slot, which retires after its last occupant,
  where the prototype's pool had one counter for all its slots.
- The caller's quota comes before shared capacity, and the root's limits of
  endpoints and notifications are the ordinary capacities of their pools,
  so the ninth creation of the fixture is `QuotaExceeded`, where the
  prototype's was `PoolExhausted`.
- A handle names only a slot of the caller's own table, so the handles of
  another object table and the attenuated receipts of the prototype have no
  case through the operations of this page.

### `src/objects/endpoints/tests/admission.rs`

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `endpoints-admission-1` | 4 | `creation_pins_owner_and_attenuates_observation` | `create_endpoint(0@1, 3@1, 4)`: `ok 4@1`. The endpoint E is endpoint slot 0 at generation 1, owned by R, with the bound thread S, an empty queue and no receiver; R[4] holds E with SEND, RECEIVE, GRANT and REVOKE, `count(E)=1`, and R's usage of endpoints is 1; the slot of S is unchanged. The prototype's owner record, an observation receipt of S that cannot regain CONTROL, has no case, since the binding is a reference that no output carries; its pin of S and its refusal to reap E (`Busy`) do not apply | `create_endpoint` |
| `endpoints-admission-2` | 29 | `creation_requires_full_live_owner_and_is_atomic` | R derives from `3@1` into R[5] with OBSERVE and into R[6] with CONTROL. `create_endpoint(0@1, 5@1, 4)`: `err=PermissionDenied`; `create_endpoint(0@1, 6@1, 4)`: `ok 4@1`, where the prototype, which needed every right, refused it. After P has left Alive, `create_endpoint(0@1, 3@1, 7)`: `err=ProcessNotAlive`. Each refusal leaves the endpoint pool, R's table and R's usages as before it and writes nothing into the slot of S | `create_endpoint`, with `derive` of the capabilities component |
| `endpoints-admission-3` | 48 | `fixed_capacity_and_slot_reuse_preserve_identity` | Eight `create_endpoint(0@1, 3@1, s)` for $s$ from 4 to 11: `ok <s>@1`, the endpoints in endpoint slots 0 to 7 at generation 1. A ninth into R[12]: `err=QuotaExceeded`, R's limit of 8 being used, where the prototype gave `PoolExhausted`; it changes nothing. The close of `4@1` deletes the last capability of the endpoint of slot 0 and releases it, the slot free at generation 2. `create_endpoint(0@1, 3@1, 4)`: `ok 4@2`, a new endpoint in endpoint slot 0 at generation 2, and the close of `4@1` is then `err=StaleHandle`. After the close of every capability, the endpoint pool has 8 free slots, R's usage of endpoints is 0 and the slot of S is unchanged; the prototype's count of references of S does not apply | `create_endpoint`, with `close` of the capabilities component |
| `endpoints-admission-4` | 76 | `generation_exhaustion_never_consumes_owner_references` | A test sets the generation of every slot of the endpoint pool to $2^{64} - 1$. `create_endpoint(0@1, 3@1, 4)`: `ok 4@1`, an endpoint in endpoint slot 0 at generation 18446744073709551615; the close of `4@1` releases it and retires the slot, leaving the pool `free=7 allocated=0 retired=1`; `create_endpoint(0@1, 3@1, 4)`: `ok 4@2`, in endpoint slot 1. The prototype's counter for the whole pool, which refused every creation once it ran out (`GenerationExhausted`), and its counts of references do not apply | `create_endpoint`, with `ObjectTable::choose` of the objects component |
| `endpoints-admission-5` | 97 | `owner_reference_overflow_does_not_publish_endpoint` | The prototype's count of references of S, set to its largest value, made the creation fail (`CounterOverflow`) without a change. No case: a creation writes no count of references into the bound thread | None |
| `endpoints-admission-6` | 112 | `foreign_pool_and_attenuated_receipts_cannot_mutate` | A handle names a slot of R's own table, whose references are of this object table, so a thread or an endpoint of another table reaches no operation of this page; `ipc::init_endpoint` with the reference of a thread of a table whose pools have other numbers, which a host test passes, is `err=WrongPool` and changes nothing, the case of `ipc-admission-7` of the IPC contract. `create_endpoint(0@1, 3@1, 4)`: `ok 4@1`; a derivation from `4@1` into R[5] with SEND gives `5@1`, a capability to the same endpoint, `count(E)=2`; a lookup of `5@1` for an endpoint with RECEIVE is `err=PermissionDenied`. The prototype's refusals through its attenuated receipt of a retain, a release, a close and a reap, and of a query with CONTROL, do not apply: no references are counted, `close` needs no right and an endpoint has no explicit reap | `create_endpoint`; `init_endpoint` of the IPC component; `derive` and `lookup` of the capabilities component |

### `src/objects/endpoints/tests/lifetime.rs`

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `endpoints-lifetime-1` | 4 | `closure_preserves_obligations_until_explicit_drain` | `create_endpoint(0@1, 3@1, 4)`: `ok 4@1`; a derivation from `4@1` into R[5] with SEND gives `5@1`, `count(E)=2`. The close of `4@1` leaves E allocated, `count(E)=1`; the close of `5@1` deletes its last capability, which releases E: its slot is free at generation 2 and R's usage of endpoints is 0. A later close of `4@1` or of `5@1` is `err=NoCapability`. The prototype's closure is this deletion of the last capability; its references with their underflow (`CounterUnderflow`), its retain after the closure (`InvalidState`) and its reap held back by a reference (`ReferencesOutstanding`) do not apply | `create_endpoint`, with `derive` and `close` of the capabilities component, which releases E |
| `endpoints-lifetime-2` | 36 | `dead_service_remains_pinned_until_endpoint_is_reaped` | `create_endpoint(0@1, 3@1, 4)`: `ok 4@1`. After P has left Alive, E is not served, so a call to it ends at once with `PeerClosed`; the step of the destruction of P that drains the endpoints bound to its thread ends the calls on E and leaves E allocated and owned by R, `count(E)=1`, as the prototype kept it open. No reference of E holds back the reaping of P: once P is dead, R reaps it, and a child that R then creates takes the process slot of P and the thread slot of S at their next generations; the binding of E has gone stale, and E stays until the close of `4@1` releases it. The prototype's retains of references to E (`InvalidState`) and its pin of S, which refused the reaping of S (`ReferencesOutstanding`), do not apply | `create_endpoint`; `drain_step` of the IPC component, and the destruction and reaping of the [lifecycle](../lifecycle/contract.md#destruction) component |
| `endpoints-lifetime-3` | 64 | `individual_and_aggregate_reference_overflow_are_atomic` | The prototype's counts of references of one endpoint and of all, at their largest values, refused a retain (`CounterOverflow`) without a change. No case: no count of references exists | None |
| `endpoints-lifetime-4` | 83 | `invalid_owner_reference_cannot_partially_reap_endpoint` | With the pin of S broken by the test, the prototype's reap of a closed endpoint was `CounterUnderflow` without a change and succeeded once the pin was restored. No case: no count of references exists, and the release of an endpoint whose owner is destroyed is a step of the destruction of the owner, the [lifecycle](../lifecycle/contract.md#destruction) component's | None |

### `src/objects/notifications/tests/admission.rs`

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `notifications-admission-1` | 4 | `creation_pins_owner_and_attenuates_observation` | `create_notification(0@1, 4)`: `ok 4@1`. The notification N is notification slot 0 at generation 1, owned by R, with the word 0 and an empty waiter queue and direct queue; R[4] holds N with SIGNAL, WAIT, GRANT and REVOKE, `count(N)=1`, and R's usage of notifications is 1. The prototype's recipient, an observation receipt of S, its flag of closure by the user, its pin of S and its refusal to reap N (`Busy`) do not apply: a notification has no recipient, and N is released at its last capability | `create_notification` |
| `notifications-admission-2` | 30 | `creation_requires_full_live_owner_and_is_atomic` | `create_notification` takes no thread, so the prototype's refusals of a recipient receipt with OBSERVE or CONTROL alone (`PermissionDenied`) and of a dying recipient (`InvalidState`) do not apply. After P has left Alive, `create_notification(0@1, 4)`: `ok 4@1`, since the state of no other process is a check of the creation of a notification | `create_notification` |
| `notifications-admission-3` | 52 | `fixed_capacity_and_slot_reuse_preserve_identity` | Eight `create_notification(0@1, s)` for $s$ from 4 to 11: `ok <s>@1`, the notifications in notification slots 0 to 7 at generation 1. A ninth into R[12]: `err=QuotaExceeded`, R's limit of 8 being used, where the prototype gave `PoolExhausted`; it changes nothing. The close of `4@1` releases the notification of slot 0, the slot free at generation 2. `create_notification(0@1, 4)`: `ok 4@2`, a new notification in notification slot 0 at generation 2, and the close of `4@1` is then `err=StaleHandle`. After the close of every capability, the notification pool has 8 free slots and R's usage of notifications is 0; the prototype's count of references of its recipient does not apply | `create_notification`, with `close` of the capabilities component |
| `notifications-admission-4` | 89 | `generation_exhaustion_never_consumes_owner_references` | A test sets the generation of every slot of the notification pool to $2^{64} - 1$. `create_notification(0@1, 4)`: `ok 4@1`, a notification in notification slot 0 at generation 18446744073709551615; the close of `4@1` releases it and retires the slot, leaving the pool `free=7 allocated=0 retired=1`; `create_notification(0@1, 4)`: `ok 4@2`, in notification slot 1. The prototype's counter for the whole pool (`GenerationExhausted`) and its counts of references do not apply | `create_notification`, with `ObjectTable::choose` of the objects component |
| `notifications-admission-5` | 110 | `owner_reference_overflow_does_not_publish_notification` | The prototype's count of references of the recipient, set to its largest value, made the creation fail (`CounterOverflow`) without a change. No case: a notification has no recipient, and no count of references exists | None |
| `notifications-admission-6` | 131 | `foreign_pool_and_attenuated_receipts_cannot_mutate` | A handle names a slot of R's own table, and `create_notification` takes no thread, so the prototype's recipient of another pool and its query and close of a notification of another pool (`WrongPool`) have no case. `create_notification(0@1, 4)`: `ok 4@1`; a derivation from `4@1` into R[5] with SIGNAL gives `5@1`, `count(N)=2`; a lookup of `5@1` for a notification with WAIT is `err=PermissionDenied`. The prototype's refusals through its attenuated receipt do not apply, as in `endpoints-admission-6` | `create_notification`, with `derive` and `lookup` of the capabilities component |
| `notifications-admission-7` | 171 | `native_notification_pins_its_recipient_until_explicit_native_reap` | The prototype's native notification, which the user could not close, pinned its recipient until its explicit reap, which it refused before the closure (`Busy`). No case: the notification of an interrupt and its binding belong to the device-authority rules of the devices and DMA domain (planned), and no notification pins a thread | None |

### `src/objects/notifications/tests/lifetime.rs`

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `notifications-lifetime-1` | 4 | `closure_preserves_obligations_until_explicit_drain` | `create_notification(0@1, 4)`: `ok 4@1`; a derivation from `4@1` into R[5] with SIGNAL gives `5@1`, `count(N)=2`. The close of `4@1` leaves N allocated, `count(N)=1`; the close of `5@1` deletes its last capability, which releases N: its slot is free at generation 2 and R's usage of notifications is 0. A later close of `4@1` or of `5@1` is `err=NoCapability`. The prototype's references with their underflow (`CounterUnderflow`), its retain after the closure (`InvalidState`) and its reap held back by a reference (`ReferencesOutstanding`) do not apply | `create_notification`, with `derive` and `close` of the capabilities component, which releases N |
| `notifications-lifetime-2` | 45 | `dead_service_remains_pinned_until_notification_is_reaped` | `create_notification(0@1, 4)`: `ok 4@1`. After P has left Alive, and once P is dead and R has reaped it, N, which has no recipient, stays allocated and owned by R, `count(N)=1`; a child that R then creates takes the process slot of P and the thread slot of S at their next generations; the close of `4@1` releases N. The prototype's recipient S, its retains (`InvalidState`) and its pin, which refused the reaping of S (`ReferencesOutstanding`), do not apply; the release of a notification at the destruction of its owner is a step of the [lifecycle](../lifecycle/contract.md#destruction) component | `create_notification`, with `close` of the capabilities component; the reaping of the [lifecycle](../lifecycle/contract.md#reaping) component |
| `notifications-lifetime-3` | 82 | `individual_and_aggregate_reference_overflow_are_atomic` | The prototype's counts of references of one notification and of all, at their largest values, refused a retain (`CounterOverflow`) without a change. No case: no count of references exists | None |
| `notifications-lifetime-4` | 110 | `invalid_owner_reference_cannot_partially_reap_notification` | With the pin of the recipient broken by the test, the prototype's reap of a closed notification was `CounterUnderflow` without a change and succeeded once the pin was restored. No case: no count of references exists, and the release of a notification whose owner is destroyed is a step of the destruction of the owner, the [lifecycle](../lifecycle/contract.md#destruction) component's | None |

### Vectors of other pages

These vectors are frozen on other pages, whose rows leave their cases of
creation to this page, and the count of 21 leaves them out.

| Vector | Page and file | Line | Test | Here | Entry |
| --- | --- | ---: | --- | --- | --- |
| `as-12` | The [address-space contract](../../memory/address-space/contract.md#legacy-test-vectors), `src/execution/tests/creation.rs` | 142 | `out_of_memory_and_metadata_exhaustion_restore_partial_allocations` | A creation takes no page of the page ownership table at run time: the private pages of a child come from the page pool and its tables from the segment of its process slot. A commit whose page pool holds fewer free frames than the private pages of its image is `err=OutOfPages`, before any write, and leaves every field and the staging record as before; the exhaustion of the page ownership table stops the boot only | `spawn_commit` |
| `as-14` | The address-space contract, `src/execution/tests/creation.rs` | 199 | `owner_generation_exhaustion_never_wraps_or_touches_backing` | No case: a creation takes no page of the page ownership table at run time, so it uses no owner identity of a page allocation | None |
| `as-16` | The address-space contract, `src/execution/tests/layouts.rs` | 64 | `bad_layout_or_insufficient_quota_has_no_allocation_or_object_side_effects` | The layouts of the prototype are the segments of a plan, whose refusals of empty, unaligned and overflowing segments are errors of `loader::validate` (planned) through `spawn_segment`; a share of private pages below the private pages of the image is `err=ImageShare` at the commit; each changes nothing, the next slots of the pools and the staging record included. Threads own no kernel stack, so its parts of the kernel stack do not apply | `spawn_segment`, `spawn_commit` |
| `cx-12` | The [context contract](../../boot-platform/context/contract.md#legacy-test-vectors), `src/execution/tests/context.rs` | 26 | `configuration_is_once_only_and_cannot_observe_or_mutate_active_contexts` | A thread gets its initial context, `Context::new` of its entry and the top of its stack, in the creation that makes it, before it first runs, and no thread exists without one, so the prototype's unconfigured thread and its second configuration (`InvalidState`) have no case; its reads and writes of the context of a running thread (`Busy`) belong to the context component | `spawn_commit` and `acknowledge`; `boot_root`, for the root |
| `ipc-admission-7` | The [IPC contract](../../ipc-waits/ipc/contract.md#legacy-test-vectors), `src/ipc/tests/admission.rs` | 188 | `foreign_pool_receipts_cannot_alias_local_endpoint_or_thread` | `create_endpoint` passes `init_endpoint` the reference that its lookup of the thread capability gives, always a reference of this object table, so the reference of another pool reaches `init_endpoint` only from a host test, as `endpoints-admission-6` states | `create_endpoint` |

## Current deviations

The rules of this page differ from those of the prototype's spawn
controller, execution manager and object pool, which
[References](#references) lists:

- **Staging.** The prototype kept one transaction of spawning for the whole
  system, with a counter of identifiers and operations of its own; here
  each process has its staging record, named by its process, and no
  identifier exists.
- **Authority.** The prototype checked a typed spawn authority at each step
  and bound the transaction to the thread and the capability that began
  it; here the creation right is CREATE on the caller's own process, which
  the commit looks up again through any handle of the caller.
- **The image.** The prototype took segments by their offset in the whole
  boot bundle and fixed two profiles of windows; here a segment is a range
  of one image, which the creator names by its index in the directory, in
  the one image window of the loading component (planned).
- **The first capabilities of a child.** The prototype passed one argument
  register to the child and returned its thread capability; here the
  creator receives the capabilities to the child and to its thread in the
  slots that it names, the child receives derivations of them in its fixed
  slots and up to four grants, and its start information comes through an
  endpoint that it is granted.
- **Pages and tables.** The prototype's execution manager allocated the
  tables, the data, the user stack and a kernel stack of each domain from
  its arena, zeroed and prepared them, and charged them per domain; here
  the private pages of a child are frames of the page pool, zero already
  and charged to its own item, its tables are the segment of its process
  slot, and a thread has no kernel stack of its own.
- **Rollback.** The prototype released every allocation of a creation that
  failed after a preparation callback; here every check precedes the first
  write, and the plans that follow the write-back cannot fail.
- **References.** The prototype's endpoints and notifications pinned their
  thread, counted references and needed an explicit reap; here a creation
  writes no reference, and the vectors and their behaviour changes state
  the consequences ([Legacy test vectors](#legacy-test-vectors)).
- **Endpoints and notifications.** The creation of an endpoint needs
  CONTROL of the thread, where the prototype needed every right; a
  notification has no recipient and no native variant.

## References

- The kernel's own rules, which this page instantiates:
  [Kernel objects and capabilities](../../../architecture.md#kernel-objects-and-capabilities)
  for the creation right, owners, quotas and the split of limits;
  [System calls and the ABI](../../../architecture.md#system-calls-and-the-abi)
  for creation through a capability and entries that run to completion;
  [Processes, POSIX and Linux compatibility](../../../architecture.md#processes-posix-and-linux-compatibility)
  for the creators of processes, the validation of an image again by the
  kernel and the start message of a process; and
  [Address spaces and VM objects](../../../architecture.md#address-spaces-and-vm-objects)
  for executable pages from the boot bundle; the
  [internal choices](../../../security.md#internal-choices),
  [unforgeable authority](../../../security.md#unforgeable-authority),
  [effective revocation](../../../security.md#effective-revocation),
  [observable outputs](../../../security.md#observable-outputs) and
  [integrity policy](../../../security.md#integrity-policy) of the security
  model.
- The rules of this page take, as clauses of their own, the rules of the
  prototype tree at `prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`:
  - `docs/features/services/static-bootstrap.md`, lines 43 to 105: the
    interface and semantics of the prototype's staged spawning, its
    operations to begin, add a segment, commit and abort, the checks of
    the authority at each mutation and at the commit, the abort after a
    revocation and staging that owns no pages, which this page keeps, and
    the transaction identifier, the profiles of windows and the initial
    argument, which it does not carry
    ([Current deviations](#current-deviations));
  - `docs/features/kernel/foundations.md`, lines 113 to 131: a creation
    that checks capacities and quotas first and publishes a process
    together with its first thread, and a failure that consumes no slot;
    its rows on waits, exit and reclamation belong to the waits and
    lifecycle components;
  - `docs/features/kernel/ipc.md`, lines 84 to 90: the endpoint pool and
    the service thread that an endpoint binds, which the prototype retained
    until its reap and which is a reference here;
  - `docs/features/kernel/notifications.md`, lines 116 to 124: the
    notification pool and its retained recipient thread, which does not
    exist here;
  - `docs/features/kernel/user-execution.md`, lines 299 to 344: the
    ownership and lifetimes of the resources of a domain, its creation
    charged by its pages and checked before its publication, and the
    release of every receipt of a creation that fails; its parts on
    destruction belong to the lifecycle component;
  - `docs/features/kernel/quotas.md`, lines 60 to 96: admission that takes
    each budget from what its creator holds of the same class and cannot
    choose a higher class, which this page composes, without the scopes of
    the prototype;
  - `docs/features/kernel/capabilities.md`, lines 163 to 170: the strong
    references of capabilities to their objects, which held back reaping
    and which do not exist here.
