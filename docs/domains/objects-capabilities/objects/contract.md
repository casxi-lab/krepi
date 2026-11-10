# Objects contract

This page governs the code of the `objects` component of the
[kernel objects and capabilities](../README.md) domain: the kinds of kernel
objects with their pools, the identities and generations of the slots of
the pools, the object part of the capacity record and the storage that the
boot carves for it, the metadata quotas of the calling domains, and the
write-set transactions through which the entries of the core change kernel
state. The capability tables, which name objects to EL0, belong to the
module `capabilities` of the core (planned); the creation of objects and the
lifetimes of processes and threads belong to the modules `creation` and
`lifecycle` (planned), which compose the entries of this page. The
observable behaviour that these rules serve, with its evidence, is in the
[requirements](requirements.md), the other document of the component.

## Terms

- **Object.** An instance of one of the eight kinds of
  [Object kinds and pools](#object-kinds-and-pools); the kernel records
  that the same section lists are not objects.
- **Pool.** The fixed array of slots of one kind of object, carved at boot
  ([Storage carved at boot](#storage-carved-at-boot)) and never resized.
- **Pool number.** A nonzero 64-bit value that names a pool for the whole
  boot ([Object kinds and pools](#object-kinds-and-pools)).
- **Slot.** An element of a pool: its slot number, from 0 to the capacity of
  the pool less one; its state, free, allocated or retired; its generation;
  and, while it is allocated, its owner and the fields of its object, which
  the component of that kind of object defines.
- **Generation.** The 64-bit value of a slot that tells its successive
  occupants apart ([Identities and generations](#identities-and-generations)).
  The current generation of a slot is its generation, or $2^{64}$ when the
  slot is retired, which no 64-bit generation equals.
- **Reference.** `objects::ObjectRef` (planned): a pool number, a 32-bit slot
  number and a 64-bit generation. Objects refer to each other inside the
  kernel only by references
  ([rule 3](../../../conventions/provable-subset.md#3-flat-relations-and-one-kernel-root)).
- **Live reference.** A reference whose pool is a pool of the table, whose
  slot number is below the capacity of that pool, and whose slot is
  allocated at exactly the generation of the reference.
- **Calling domain.** The process of the calling thread; and the kernel
  domain, for the objects that the kernel creates at boot.
- **Kernel domain.** The calling domain of the kernel itself. It owns the
  root's process with its thread, which it creates at boot, and the device
  directory; it creates nothing after boot.
- **Owner.** `objects::Owner` (planned): the kernel domain, or the reference
  of a process. Every allocated slot records its owner, which never changes
  while the slot stays allocated.
- **Allocation class.** Ordinary, or control: the allocations of the root's
  process and thread and of the paths that stop processes, notify faults and
  clean up, which their contracts name. Only entries of the kernel pass the
  control class; no EL0 argument selects it.
- **Quota item.** One of the seven items of a quota record
  ([Metadata quotas](#metadata-quotas)).
- **Capacity record.** The typed record of the boot-bundle directory that
  sets the capacities of the pools, the capability slots and VM regions of
  each process, the control reserves and the limits of VM and loading
  ([capacities](../../../architecture.md#kernel-objects-and-capabilities)).
  Its object part is this component's
  ([Capacity record](#capacity-record)); its VM and loading part belongs to
  the VM and loading components; the directory, with the framing of the
  record in it, belongs to the address-space component of the
  [memory and address spaces](../../memory/README.md) domain.
- **Capacities.** `objects::Capacities` (planned): the object part of a
  capacity record once it has passed its checks.
- **Write set.** The items that an entry changes, each once
  ([Write-set transactions](#write-set-transactions)).
- **Write-set buffer.** `objects::WriteSet` (planned): the buffer of one CPU
  into which an entry copies its write set, empty before and after every
  entry.
- **Token.** What an access to state that is not per-CPU holds, as the
  [SMP design rules](../../../conventions/smp.md#s1-state-classes) state for
  shared and per-process state; with one CPU, the executing CPU holds every
  token.
- **Boot wiring.** The code of a board crate that runs on the boot CPU before
  any entry from EL0: it validates the capacity record, carves the storage
  of [Storage carved at boot](#storage-carved-at-boot) from the
  [page ownership table](../../memory/page-tables/contract.md#page-ownership)
  that it builds for the kernel root, zeroes that storage, forms its slices
  and builds the object table on them.

## Entry points

The entries of the core are in the module `objects` of `krepi-kernel`
(planned). No entry of this page is an operation of the ABI inventory: the
operations that create objects, and those that copy, derive, close and
revoke capabilities, belong to the creation and capabilities components,
which compose these entries.

| Entry point | Kind | Called by | ABI operation | Rules |
| --- | --- | --- | --- | --- |
| `objects::validate_capacities`, `Capacities::allocations` and `Capacities::root_limits` (planned) | Read entries, host-testable | `validate_capacities` and `allocations`: the boot wiring, once, before the storage is carved; `root_limits`: the boot of the root by the kernel root (planned) | None | [Capacity record](#capacity-record), [Storage carved at boot](#storage-carved-at-boot), [Metadata quotas](#metadata-quotas) |
| `ObjectTable::new` (planned) | Write entry, host-testable | The boot wiring, once, for the kernel root, on the slices of the carved storage that it forms | None | [Object kinds and pools](#object-kinds-and-pools), [Storage carved at boot](#storage-carved-at-boot) |
| `ObjectTable::resolve` (planned) | Read entry, host-testable | Every module of the core that follows a reference: `capabilities`, `waits`, `ipc`, `vm`, `lifecycle`, `creation` and `dispatch` (planned) | None | [Identities and generations](#identities-and-generations) |
| `ObjectTable::choose` (planned) | Read entry, host-testable | The module `creation` and the boot of the root by the kernel root (planned), in their checks | None | [Identities and generations](#identities-and-generations), [Determinism](#determinism) |
| `ObjectTable::occupy` and `ObjectTable::release` (planned) | Write entries on the copies of a write set, host-testable | `occupy`: the module `creation` and the boot of the root; `release`: the module `lifecycle`, for a process and its thread when they are reaped, and for the endpoints and notifications of an owner that is destroyed, in the steps of its destruction; and the module `capabilities`, for an endpoint or a notification whose last capability of its current generation is deleted (planned) | None | [Identities and generations](#identities-and-generations), [Metadata quotas](#metadata-quotas), [Write-set transactions](#write-set-transactions) |
| `QuotaRecord::check`, `charge`, `credit`, `split`, `merge` and `start_root` (planned) | A read entry and write entries on the copies of a write set, host-testable | `check`, `charge` and `split`: the module `creation`; `credit` and `merge`: the module `lifecycle`; `charge` and `credit` of capability slots: the module `capabilities`; of committed VM pages and of private pages of loaded images: the VM and loading components; `charge` and `start_root`: the boot of the root by the kernel root (planned), `charge` for the root's pair in the control usage of the kernel domain | None | [Metadata quotas](#metadata-quotas) |
| `WriteSet::stage`, `commit` and `discard` (planned) | Write entries on the write-set buffer of the executing CPU, host-testable | Every entry of the core that changes more than one item (planned) | None | [Write-set transactions](#write-set-transactions) |
| `ObjectTable::counts` and `QuotaRecord::usage` (planned) | Read entries, host-testable | The modules `creation` and `lifecycle` (planned), and the tests | None | [Identities and generations](#identities-and-generations), [Metadata quotas](#metadata-quotas) |

## Extractability

The module `objects` of the core (planned), below `kernel/src/` (planned),
follows the [provable Rust subset](../../../conventions/provable-subset.md):
the kinds and pools, the references and generations, the capacity record
and its checks, the quota records and the write sets. Its items are
`pub(crate)` except the rows of the entry table that the boot wiring calls,
`validate_capacities`, `Capacities::allocations` and `ObjectTable::new`,
with the value types that those rows take and return, among them
`Capacities`, the allocations with their owner identities and the error
type ([provable core](../../../architecture.md#the-provable-core)). The
module is in the lowest layer of the
[module order](../../../architecture.md#module-order-in-the-core): it refers
to no other module and not to the kernel root, and works on the parts of
the state that its callers pass it, the object table, the quota records and
the write-set buffer of the executing CPU. Per-CPU state comes in by an
explicit `&mut` argument
([rule 8](../../../conventions/provable-subset.md#8-no-interior-mutability)),
and the module defines no callback.

The module has no adapter of its own. The write-set buffer of each CPU, in
the storage carved at boot, is lent through the per-CPU record of the
architecture crate (planned); finding the record of the executing CPU,
masking interrupts and lending the buffer by `&mut` is an adapter of the
architecture crate, outside the proof target, which
[Open obligations](#open-obligations) lists. The boot wiring, code of the
board crates, zeroes the storage of
[Storage carved at boot](#storage-carved-at-boot) that it takes from the
page ownership table of the kernel root, forms the slices of that storage
through the direct map and hands them, as the storage of the pools, the
capability tables, the VM region tables and the write-set buffers, to
`ObjectTable::new` and to the components of those tables; forming the
slices from physical pages is `unsafe` code of the board crate, outside the
proof target, which [Open obligations](#open-obligations) lists as well.
The contract is written before its code, so this section lists no source
paths; the change that adds the module writes its `paths` block here.

## Object kinds and pools

The kernel provides eight kinds of object. Every kind except VM regions is
held by EL0 through capabilities. Each kind has its storage, a quota item
that counts it, and a creator:

| Kind | Storage | Charged to | Created by |
| --- | --- | --- | --- |
| Process | The process pool | The child-process item of its owner, together with its thread | The kernel at boot for the root, owned by the kernel domain; afterwards the creation component, for a holder of the creation right, owned by that holder's process |
| Thread | The thread pool | With its process, in the same item | Together with its process: a process has one thread, created with it |
| Endpoint | The endpoint pool | The endpoint item of its owner | The creation component, for a holder of the creation right |
| Reply | No pool: the reply record embedded in the slot of the calling thread | No item | The kernel, when a call is received (the IPC component) |
| Notification | The notification pool | The notification item of its owner | The creation component, for a holder of the creation right |
| VM region | No pool: a row of the VM region table of its process; no capability to it is issued | Its committed pages, in the committed-page item of its process | `reserve` (the VM component) |
| Device directory | A pool of one slot, held in the object table itself | No item; owned by the kernel domain | The kernel at boot; only the root holds a capability to it |
| Device grant | The device-grant pool | No item; owned by the root | The root, through its capability to the device directory (the device-authority rules of the devices and DMA domain) |

- **Records that are not objects.** The capability table entries, the wait
  records and wait-set registrations embedded in threads, the ASID records,
  the per-CPU records, the progress of revocation and of destruction, the
  quota records and the capacity record are kernel records: they have no
  pool and no quota item of their own, even where they carry a generation
  or progress.
- **Pools.** The process, thread, endpoint, notification and device-grant
  pools have the capacities of the capacity record. The device directory
  has a pool of exactly one slot, which `ObjectTable::new` allocates at
  generation 1 for the kernel domain and which is never released; its
  contents are those of the device-authority rules, and its storage, of the
  fixed size that those rules give, is part of the object table, so it
  takes none of the allocations below. A reply lives in its thread and a VM
  region in its process, so neither has a pool.
- **Pool numbers.** `ObjectTable::new` takes the number of its first pool.
  The six pools take that number and the five after it, in the order
  process, thread, endpoint, notification, device directory, device grant.
  It refuses a first pool number of 0, or one whose five successors do not
  fit 64 bits (`InvalidConfiguration`).
  The boot wiring passes 1; a host test passes other numbers to build
  tables whose pools differ. The table is built once in a boot, so its pool
  numbers are never reused within the boot.
- **No borrowing.** A pool that has no free slot for an allocation never
  takes a slot of another pool, and a capability table or a VM region table
  never takes rows of another process.
- **Slots.** A slot records its state, its generation and, while allocated,
  its owner; the fields of its object are those of the kind's component. A
  process slot also holds the quota record of the process
  ([Metadata quotas](#metadata-quotas)). The owner of a thread is the owner
  of its process, which the thread records besides the reference of its
  process. The capability table and the VM region table of a process are
  those of its process slot: their storage holds one table of each for every
  slot of the process pool.
- **Threads.** Since a process has one thread, the thread pool holds at most
  as many allocated slots as the process pool; a thread capacity above the
  process capacity leaves the rest of the thread pool unused.

A kind added later gets a pool and a quota item of its own, and references
keep their form.

### Storage carved at boot

No object memory is allocated after boot. The storage of the object table
is carved from the page ownership table once, at boot, before the first
entry from EL0, in eight allocations, and no entry takes or returns pages
afterwards; a full pool or table never takes memory, as the
[provable subset](../../../conventions/provable-subset.md#2-no-allocation-at-run-time)
requires.

| Allocation | Holds | Owner identity |
| --- | --- | --- |
| Processes | The slots of the process pool, with their quota records | `objects::OWNER_PROCESSES` (planned) |
| Threads | The slots of the thread pool, with their embedded wait and reply records | `objects::OWNER_THREADS` (planned) |
| Endpoints | The slots of the endpoint pool | `objects::OWNER_ENDPOINTS` (planned) |
| Notifications | The slots of the notification pool | `objects::OWNER_NOTIFICATIONS` (planned) |
| Device grants | The slots of the device-grant pool | `objects::OWNER_DEVICE_GRANTS` (planned) |
| Capability tables | For every slot of the process pool, one table of `capability_slots` entries | `objects::OWNER_CAPABILITY_TABLES` (planned) |
| VM region tables | For every slot of the process pool, one table of `vm_regions` rows | `objects::OWNER_REGION_TABLES` (planned) |
| Write-set buffers | For every CPU of the CPU topology, one buffer of $W$ items | `objects::OWNER_WRITE_SETS` (planned) |

- Each allocation holds its number of items times the size of an item,
  rounded up to whole pages; the sizes of the items are constants of the
  core that the types of their components give. `Capacities::allocations`
  gives the eight in this order, each with its pages and its owner identity.
- The eight owner identities are nonzero 64-bit constants of the module,
  distinct from each other and from the owner identity of every other
  holder of the page ownership table.
- The boot wiring takes the allocations, once, for the kernel root
  (planned), which does not exist yet: the fields of the root hold the page
  ownership table and the object table, which the boot wiring builds before
  it, and `page_tables` runs at boot before the root, as the
  [module order](../../../architecture.md#module-order-in-the-core)
  states. On the page ownership table that it builds for the kernel root
  with `Ownership::new`, the boot wiring takes the allocations in the order
  of the table, each in one step of
  [zeroing before publication](../../memory/page-tables/contract.md#page-ownership),
  where the caller zeroes: `Ownership::choose` at an alignment of one page
  and a low placement without a window; then it zeroes the chosen range
  through the direct map with `krepi_arch::mmu::zero_frames`; then
  `Ownership::assign` with the owner identity of the allocation. When the
  page ownership table finds no range for one of them, the boot stops with
  `InsufficientMemory`. It then forms the slices of the eight allocations
  and calls `ObjectTable::new` on them. The module `objects` gives the
  allocations as values and calls neither the kernel root nor
  `page_tables`.
- **Extents.** An allocation adds at most two extents to the page ownership
  table, the held range and the rest of the free extent that it splits; a
  low placement at an alignment of one page starts at the start of a free
  extent, so it adds at most one. The eight allocations add at most eight
  extents, whatever the capacities, and at most 16 under any placement. On
  the 8 GB Pi 5, whose table holds four free extents at boot, the storage
  of the object table leaves at least 148 of the 160 extents to the other
  holders, the table pools of the address spaces and the pages of VM
  objects.
- The per-CPU kernel and emergency stacks are part of the image, not of
  these allocations.

## Identities and generations

- **References.** A reference names the object that its slot holds at its
  generation. A reference is never a handle of EL0: handles name slots of
  capability tables, and the capability entry holds the reference of its
  object
  ([handles](../../../architecture.md#kernel-objects-and-capabilities)).
- **Generations.** Every slot of a pool starts free at generation 1. An
  occupation makes a free slot allocated and leaves its generation as it
  is, so the new object's reference carries the generation of the slot. A
  release of an allocated slot at generation $g < 2^{64} - 1$ makes it free
  at $g + 1$; a release at $2^{64} - 1$ retires the slot, which stays
  retired until the next boot. A generation never wraps, never decreases
  and never repeats for a slot, so a reference that has gone stale never
  becomes live again.
- **Counts.** Each pool counts its free, allocated and retired slots, which
  add up to its capacity after every write-back. `counts` gives the three.
- **No dangling reference.** For every reference that kernel state holds,
  its generation is at most the current generation of its slot, and where
  the two are equal the slot is allocated and holds an object of the kind
  of its pool. A reference in a capability entry goes stale lazily: the
  release of its slot raises the current generation above the reference,
  and every lookup compares them. The generations of ASIDs are not
  generations of this page and are not covered by this rule.
- **Resolution.** `resolve(reference, kind)` gives the slot of a live
  reference to an object of the kind. It checks in this order and returns
  the first error: the pool number is the number of the pool of the kind
  (`WrongPool`); the slot number is below the capacity of the pool, the slot
  is allocated and its generation equals that of the reference
  (`StaleReference`). It is total: every representable reference, among
  them one of a pool of no slot, of the largest slot number or of
  generation 0, gives a result or one of these errors, and it writes
  nothing.
- **Choice.** `choose(pool, class)` gives the lowest free slot of the range
  of the allocation class, and writes nothing. The ordinary range of a pool
  of capacity $N$ and control reserve $r$ is the slots 0 to $N - r - 1$, the
  reserved tail the slots $N - r$ to $N - 1$. An ordinary allocation takes
  the lowest free slot of the ordinary range; a control allocation that of
  the reserved tail, and when the tail has none, that of the ordinary
  range. A retired slot is not free, so it is never chosen. It checks the
  pool (`WrongPool`) and then that the range has a free slot
  (`PoolExhausted`).
- **Occupation.** `occupy(pool, slot, owner)` changes the copy of a free
  slot in the write set to allocated with that owner and gives the
  reference of the new object; the caller passes the slot that `choose` gave
  in its checks. For a process slot it also sets the quota record of the
  process to its starting state ([Metadata quotas](#metadata-quotas)). It
  checks the pool (`WrongPool`), then that the slot number is below the
  capacity and the slot is free (`InvalidState`), and on the counts of the
  pool moves one slot from free to allocated.
- **Release.** `release(reference, kind)` changes the copy of the slot of a
  live reference as **Generations** states and moves one slot from
  allocated to free or to retired. It checks the reference as `resolve`
  does, and then, for a process slot, that the quota record of the process
  counts no usage, ordinary or control, of an item other than the
  page-table pages (`InvalidState`): the objects, capability entries and
  pages of a process are released before its process slot. The fields of
  the released object, its owner and its quota record included, are
  cleared.

## Capacity record

The object part of the capacity record is its first 48 bytes: twelve
unsigned 32-bit fields, little-endian, without padding, in this order. The
VM and loading part follows it, from byte 48, and belongs to the VM and
loading components.

| Offset | Field | Content |
| ---: | --- | --- |
| 0 | `processes` | The capacity of the process pool |
| 4 | `threads` | The capacity of the thread pool |
| 8 | `endpoints` | The capacity of the endpoint pool |
| 12 | `notifications` | The capacity of the notification pool |
| 16 | `device_grants` | The capacity of the device-grant pool |
| 20 | `capability_slots` | The slots of the capability table of each process |
| 24 | `vm_regions` | The rows of the VM region table of each process |
| 28 | `reserved_processes` | The control reserve of the process pool |
| 32 | `reserved_threads` | The control reserve of the thread pool |
| 36 | `reserved_endpoints` | The control reserve of the endpoint pool |
| 40 | `reserved_notifications` | The control reserve of the notification pool |
| 44 | `reserved_device_grants` | The control reserve of the device-grant pool |

**Checks.** The boot wiring checks the record once, as untrusted input,
before it carves any storage, and stops the boot at the first check that
fails with the fixed error of that check; the kernel does not fall back to
the defaults. The checks run in this order:

1. The framing of the record in the boot-bundle directory, which is a rule
   of the address-space component, with its error.
2. The record holds the 48 bytes of its object part, and each of the seven
   fields from `processes` to `vm_regions` is at least 1; `capability_slots`
   is at most 65,536, the slots that the 16-bit slot number of a handle
   names, and `vm_regions` at most the rows that a region number of the VM
   component names (`InvalidConfiguration`). A capacity of a pool fits its
   32-bit field and so the slot number of a reference.
3. There are at least as many threads as processes (`InvalidConfiguration`).
4. Each control reserve is at most the capacity of its pool; a reserve may
   be 0 (`InvalidConfiguration`).
5. The pages of the eight allocations of
   [Storage carved at boot](#storage-carved-at-boot), together with the
   pages of the table pools that the address-space component carves for the
   process capacity of the record, are at most the free pages of the page
   ownership table (`InsufficientMemory`). The image, with the per-CPU
   stacks and the pools of the kernel tables, the device tree and the boot
   bundle hold no free page.
6. The process capacity is at most the number of ASIDs, which is a rule of
   the address-space component, with its error.

`validate_capacities` makes checks 2 to 5, in this order, on the bytes of
the record, with the free pages of the page ownership table, the pages of
the table pool of one address space and the number of CPUs, which the boot
wiring passes; check 1 comes before it and check 6 after it. After the
checks the capacities are read-only for the rest of the boot.

**Defaults.** When the directory holds no capacity record, the boot wiring
uses the default record of its board, `DEFAULT_CAPACITIES` (planned) of the
board crate, and checks it in the same way. The default record of every
board provides at least 64 processes and 256 threads; the other default
values are constants of the board crates, named by the fields of the
record.

## Metadata quotas

- **Calling domains and owners.** The calling domain of an operation is the
  process of the calling thread. Every object that a calling domain creates
  records that domain as its owner, and the kernel domain owns the objects
  that the kernel creates at boot: the root's process with its thread, and
  the device directory. The device grants are owned by the root; neither
  they nor the device directory are counted by a quota item.
- **Records.** Each process slot holds the quota record of its process, and
  the object table holds the record of the kernel domain. A record holds,
  for each of the seven items, a limit, an ordinary usage and a control
  usage, each of 64 bits. The ordinary usage counts the ordinary
  allocations, which the limit bounds; the control usage counts the control
  allocations, which no limit bounds and which take the reserved tail of
  their pool first.

| Item | Counts | Owner of what it counts | Limit |
| --- | --- | --- | --- |
| Child processes | The allocated process slots, each with the thread slot of its thread | The owner of the process slot | Split from the creator's limit |
| Endpoints | The allocated endpoint slots | The owner of the slot | Split from the creator's limit |
| Notifications | The allocated notification slots | The owner of the slot | Split from the creator's limit |
| Capability slots | The filled entries of the capability table of a process | The process of the table | `capability_slots`, the size of its table |
| Committed VM pages | The pages committed in the VM regions of a process, as the VM and loading components count them | The process of the address space | Split from the creator's limit |
| Private pages of loaded images | The private pages of the images loaded into a process, as the VM and loading components count them | The process of the address space | Split from the creator's limit |
| Page-table pages | The tables of the table pool of the address space of a process, which the address-space component fixes per process | The process itself | The tables of one table pool |

- **Starting state.** `occupy` of a process slot sets every limit and usage
  of its record to 0, except the capability slots, whose limit is
  `capability_slots`, and the page-table pages, whose limit and ordinary
  usage are the tables of one table pool from the occupation of the slot to
  its release. Neither of these two items is split from the creator or
  returned to it: the process's own fixed structures give them. The check
  of capability slots fails only when the table of the process has no free
  entry, a result of the process itself. The page-table pages are written
  only by `occupy` and `release` of the process slot; no entry checks,
  charges or credits them, and which tables of its pool a process uses is
  a rule of the address-space component.
- **Order.** A creation checks the caller's own quota before the shared
  capacity, and checks the quota and the free slot before its first write;
  it charges the quota and occupies the slot in one write set
  ([rule 2](../../../conventions/provable-subset.md#2-no-allocation-at-run-time)).
  `check(record, item, n)` refuses with `QuotaExceeded` when the ordinary
  usage plus $n$ exceeds the limit; the creation passes as $n$ the charge
  together with the share that it splits from the item.
- **Charges.** `charge(record, item, n, class)` adds $n$ to the ordinary
  usage, refusing with `QuotaExceeded` as `check` does, or to the control
  usage for the control class. `credit(record, item, n, class)` takes $n$
  from the usage of the class and refuses with `InvalidState` when the
  usage is smaller than $n$.
- **Splitting limits.** The limits of a child of the five items child
  processes, endpoints, notifications, committed VM pages and private pages
  of loaded images are carved out of what its creator has left.
  `split(parent, child, item, share)` lowers the parent's limit of the item
  by the share and raises the child's by it; it refuses with
  `QuotaExceeded` when the share exceeds the parent's limit less its
  ordinary usage. A split is a transfer of limit: the share is not a usage
  of the parent.
- **Returning limits.** When a child is reaped, `merge(parent, child)` adds
  the child's limits of the five split items to the parent's, in the write
  set that releases the child's process slot; it refuses with
  `InvalidState` while a usage of the child in one of these items is not 0.
  A parent is reaped only after its children, so their limits return to it
  before its own return to its owner. No ownership and no quota is
  transferred to another owner.
- **Releases.** Endpoints and notifications are released when the last
  capability of their current generation is deleted, or, when their owner
  is destroyed, in the bounded steps of that destruction, before the owner
  becomes dead; processes and threads are released when they are reaped.
  Each release credits its owner in the same write set.
- **The root.** The root's process and thread are a control allocation of
  the kernel domain, charged to the control usage of its child-process item.
  `ObjectTable::new` writes the record of the kernel domain with every limit
  and usage 0. The boot of the root, in one write set, occupies the root's
  process and thread slots, charges the pair to the kernel domain with
  `charge(record of the kernel domain, child processes, 1, control)` and
  writes the root's starting limits with `start_root`. From the write-back
  of that write set on, the record of the kernel domain has every limit and
  usage 0 but this control usage of 1, and the kernel domain creates
  nothing after boot. `root_limits` gives the root's starting limits of the
  five split items: for child processes, the smaller of the ordinary
  capacities of the process and the thread pool, the ordinary capacity of
  a pool being its capacity less its control reserve; for
  endpoints and notifications, the ordinary capacity of their pool; for
  committed VM pages and private pages of loaded images, the values of the
  VM and loading part of the capacity record, which its caller passes.
  `start_root(record, limits)` writes them into the root's record, in the
  write set that occupies the root's process slot, after `occupy` has set
  the starting state; it refuses with `InvalidState` unless the limits and
  usages of the five items of the record are 0. The root's capability
  slots and page-table pages are those of every process. The limits of the
  objects are split from the pools; the limits of pages are not, so the
  page limits of all processes together may exceed the free pages.
- **Consequence.** `start_root` writes the root's starting limits once, and
  afterwards limits move only between a parent and its child. So from the
  write-back of the boot of the root on, for each of the five split items
  the limits of the live calling domains, the kernel domain with its limits
  of 0 among them, add up to the root's starting limit. For child
  processes, endpoints and notifications they therefore never exceed the
  ordinary capacity of the pools that the item counts, and an ordinary
  creation that passes its quota check fails for shared capacity
  (`PoolExhausted`) only when control allocations have taken slots of the
  ordinary range, which they do once the reserved tail of their pool has
  no free slot, or slots have retired. When the control reserve of a pool
  is 0, the root's process or thread in that pool is such a control
  allocation and takes the lowest slot of its ordinary range. When that
  pool is the process pool and the ordinary capacity of the thread pool is
  not less than the capacity of the process pool, the limits of child
  processes add up to one more than the ordinary process slots that are
  left, and the last ordinary creation of a process within them can meet
  `PoolExhausted`. The pages run out as shared capacity, with the error of
  the component that counts them.
- **Shared records.** The quota records are shared state: a release may
  credit an owner that its caller holds no right to, such as the owner of an
  object that the destruction of a process releases.

**Conservation.** For every quota item, from the return of
`ObjectTable::new` on and after every write-back of the entries of the
kernel, also while processes are destroyed:

1. The usages of different calling domains never overlap: every slot,
   entry, page or table that the item counts is counted in the usage of
   exactly one calling domain, its owner.
2. The usages of all calling domains, ordinary and control together, add up
   to what is allocated for the item: the allocated process slots, the
   allocated endpoint slots, the allocated notification slots, the filled
   capability entries of all tables, the committed and the loaded private
   pages as the VM and loading components count them, and the tables of the
   table pools of all allocated process slots.

The entries of the kernel are `ObjectTable::new`, the boot of the root and
the operations that compose the entries of this page. `ObjectTable::new`
leaves every slot of the five carved pools free and every usage 0. An owner
never changes; each of these entries charges or credits the owner of what an
item counts in the write set that occupies or releases it, the boot of the
root the kernel domain for the root's process with its thread; and a process
slot, whose release clears its record, is released only once that record
counts no usage but its page-table pages, which leave with the slot. So both
statements hold in every state that these entries reach, without exception.
The root's own table pool counts for the root. `occupy` and `release` charge
and credit nothing themselves: a host test that calls them without `charge`
and `credit`, as the [Legacy test vectors](#legacy-test-vectors) do, builds
tables that the entries of the kernel do not reach, and Conservation is not
checked on them.

## Write-set transactions

- **Checks first.** An entry of the core that changes kernel state first
  makes all its checks and determines its write set, and writes no state
  while it checks
  ([rule 1](../../../conventions/provable-subset.md#1-check-then-execute)).
  Its write set holds the items that it changes, each once: object slots,
  with the quota records that process slots hold, the counts of pools,
  capability entries, the record of the kernel domain and the queue links
  of other components. An item is keyed by its pool and its slot; the
  counts of a pool are keyed by the pool, a capability entry by its table
  and its slot, and the record of the kernel domain by a key of its own.
  The contract of each entry lists its write set: this page for its own
  entries, the contracts of the composing components for theirs.
- **Execution.** The entry then stages each item of its write set into the
  write-set buffer of its CPU with `stage`, changes the copies with the
  write entries of the components, and writes them back with `commit`. The
  keys of the write-back are distinct, so it stores them in any order with
  the same result, and it cannot fail. `discard` empties the buffer without
  writing. An entry that changes a single item and has no failure point may
  write it in place, without the buffer. No operation copies the whole
  kernel state.
- **Capacity of the buffer.** A buffer holds $W$ = 64 items,
  `objects::WRITE_SET_CAPACITY` (planned): the largest write set of an entry
  of the core, which the contract of every entry that composes these
  entries keeps within it. A contract that needs a larger write set raises
  this constant in the same change. `stage` of a key that the buffer holds
  already keeps the first copy; of a new key in a full buffer it refuses
  with `WriteSetFull`.
- **Failures of the write phase.** After the checks, only the capacity and
  quota failures that the contract of the entry lists can occur, and the
  fault-injection points of test builds: at most ten points, which the
  implementation of the object table names, each stopping the write phase
  with `InjectedFault`. A production build has no injection point. A failure
  discards the buffer, so the state is the state from before the entry. The
  capacity and quota failures of this page are `WriteSetFull` of `stage`
  and `QuotaExceeded` of `charge` and `split`, which an entry that made its
  checks never meets.
- **Tokens.** In the specification, an entry takes, during its checks, the
  tokens of the state in its write set that is not per-CPU, and releases
  them after the write-back
  ([multicore by design](../../../architecture.md#multicore-by-design)).
  With one CPU, the executing CPU holds every token.
- **No failure counter.** A rejected entry and a failed write phase write
  nothing, a counter of failures included. The audit counters of this
  component count committed operations only: for each pool, the slots
  occupied and the slots released, a release that retires a slot included,
  one set for each CPU, increased by `commit` on the CPU that commits.

The write set of each write entry of this page:

| Entry | Write set |
| --- | --- |
| `ObjectTable::new` | Every slot and the counts of every pool, and the record of the kernel domain; it writes them in place, at boot, before any token exists |
| `occupy` | The slot and the counts of its pool |
| `release` | The slot and the counts of its pool |
| `charge`, `credit`, `start_root` | One quota record |
| `split`, `merge` | The two quota records |
| `stage`, `commit`, `discard` | The write-set buffer of the executing CPU, which is per-CPU and in no write set |

## Errors

| Error | Rule broken | Entries | Place in the order of errors |
| --- | --- | --- | --- |
| `InvalidConfiguration` | A record shorter than its object part; a capacity, a capability-slot count or a VM region count of 0, or beyond its width; fewer threads than processes; a control reserve larger than its pool; for `ObjectTable::new`, storage of another size than the capacities give, a first pool number of 0, or one whose five successors do not fit 64 bits | `validate_capacities`, `ObjectTable::new` | Checks 2 to 4 of the capacity record, at boot |
| `InsufficientMemory` | The eight allocations and the table pools of the address spaces do not fit the free pages, or the page ownership table finds no range for one of the allocations | `validate_capacities`; the boot wiring, when it carves at boot | Check 5 of the capacity record, at boot |
| `WrongPool` | A reference or a pool number that is not that of the pool of the kind that the entry needs | `resolve`, `choose`, `occupy`, `release` | Handle resolution: the type |
| `StaleReference` | A reference whose slot number is not below the capacity of its pool, or whose slot is free, retired or of another generation | `resolve`, `release` | Handle resolution: the liveness of the object |
| `QuotaExceeded` | An ordinary charge or check beyond the limit, or a share beyond the limit less the ordinary usage | `check`, `charge`, `split` | The caller's quota |
| `PoolExhausted` | No free slot in the range of the allocation class | `choose` | Shared capacity |
| `InvalidState` | An occupation of a slot that is not free or beyond the capacity; a release of a process slot whose quota record counts a usage other than its page-table pages; a credit beyond the usage; a merge while a usage of the child in a split item is not 0; a `start_root` on a record whose five split items are not 0 | `occupy`, `release`, `credit`, `merge`, `start_root` | Object state |
| `WriteSetFull` | A new key staged into a buffer of $W$ items | `stage` | A capacity failure of the write phase |
| `InjectedFault` | A fault-injection point of a test build | `commit` | The write phase, in test builds only |

- **Order.** Each entry of this page checks in the order of its row in the
  rule sections and returns the first error. An entry that composes them
  applies the order of errors of the
  [security model](../../../security.md#internal-choices) to its operation:
  the errors of this page take the places that the last column gives, so
  the caller's quota comes before shared capacity, and both after handle
  resolution, rights, user buffers and object state.
- **No change on failure.** No error changes state: an entry of this page
  that returns an error leaves every field of the kernel state as it was,
  the copies in the write set included, and writes no counter; a composing
  entry that meets an error discards its buffer, so the kernel state after
  any failed operation equals the state before it. There is no exception.
  The result registers of a failed system call follow the
  [observable outputs](../../../security.md#observable-outputs) of the
  security model; this component writes no register. An error of the boot
  stops the boot before any entry from EL0.
- **Totality.** `WrongPool`, `StaleReference` and `InvalidState` of the
  write entries answer a call whose check phase did not make the check;
  no entry of the core makes such a call, and the answer changes nothing.
- **Names.** The names are those of this contract; the numeric values of
  the errors that reach EL0 through a composing operation belong to the ABI
  inventory.

The prototype's object pool had sixteen errors. Here:

| Prototype error | Here |
| --- | --- |
| `InvalidConfiguration` | Kept, for the checks of the capacity record and of the storage |
| `WrongPool` | Kept, for a reference or pool number of another pool |
| `StaleHandle` | Renamed `StaleReference`: references are not handles |
| `PermissionDenied` | Moved to the capabilities component: rights live in capability entries, and a reference carries none |
| `QuotaExceeded` | Kept, for the caller's quota |
| `PoolExhausted` | Kept, for shared capacity |
| `GenerationExhausted` | Not kept: a slot retires instead of the whole pool, and a range without a free slot is `PoolExhausted` |
| `PreparationFailed` | Renamed `InjectedFault` and kept to test builds: the preparation callback of the prototype is a fault-injection point |
| `InvalidState` | Kept, for the state of an item that a write entry needs; the owner failures of the prototype's activation are `WrongPool` and `StaleReference` of `resolve` |
| `Busy` | Moved to the lifecycle component and the scheduler: the activation and the reaping of a running thread |
| `ReferencesOutstanding` | Moved to the lifecycle component: the gates of reclamation |
| `CounterOverflow` | Not applicable: the counts and usages of this page are bounded by the capacities, and the count of capabilities of an object, which the capabilities component keeps, by the slots of all capability tables |
| `CounterUnderflow` | Not applicable, as `CounterOverflow`; a credit beyond a usage is `InvalidState` |
| `WaitInProgress` | Moved to the waits component |
| `StaleWait` | Moved to the waits component |
| `AlreadyCompleted` | Moved to the waits component |

## Check and execute

- `validate_capacities`, `Capacities::allocations` and `root_limits` write
  nothing; `validate_capacities` returns the capacities or the first error
  of its checks.
- `ObjectTable::new` checks the capacities, the sizes of its storage and the
  first pool number before its first write, then writes every slot free at
  generation 1, the counts, the slot of the device directory and the record
  of the kernel domain, with every limit and usage 0. It runs once at boot
  and cannot fail after its checks.
- `resolve`, `choose`, `counts`, `QuotaRecord::check` and `usage` write
  nothing.
- `occupy`, `release`, `charge`, `credit`, `split`, `merge` and
  `start_root` change only the copies in the write set of their caller.
  Each checks on the copies what its effect needs, as [Errors](#errors)
  lists, before it changes them, and changes nothing when a check fails.
  The composing entry has made the same checks before its first write, with
  `resolve`, `choose`, `check` and `usage`, so its write phase meets none of
  them.
- `stage` checks the room in the buffer before it copies; `commit` writes
  every copy back and cannot fail, except at a fault-injection point of a
  test build, where it discards instead; `discard` cannot fail.
- A composing entry completes all its checks before its first write, and
  its write phase allows only the failures that its contract lists among
  `WriteSetFull`, `QuotaExceeded` and `InjectedFault`, each of which
  discards the buffer and leaves the state from before the entry.

## Work bounds

- `validate_capacities` reads the twelve fields once and makes a fixed number
  of checks; `allocations` computes eight products and roundings;
  `root_limits` makes a fixed number of steps.
- `ObjectTable::new` writes each slot of each pool once: at most the sum of
  the five capacities of the record and one, at boot.
- `resolve`, `occupy`, `release` and `counts` read and write one slot and the
  counts of its pool.
- `choose` scans at most the slots of the range of its class: the ordinary
  range for an ordinary allocation, and the reserved tail and the ordinary
  range for a control one, so at most the capacity of the pool.
- `QuotaRecord::check`, `charge`, `credit`, `split` and `usage` touch one
  item of one or two records; `merge` five items of two records, and
  `start_root` five items of one record.
- `stage` compares its key with at most $W - 1$ staged keys and copies one
  item; `commit` writes at most $W$ items; `discard` makes a fixed number of
  steps.
- The component has no long operation: every entry runs to its end, and no
  progress is stored between two calls. The long operations that use these
  entries, such as the destruction of a process, store their progress in
  their own objects.

## Determinism

- **Slots.** `choose` takes the lowest free slot of the range of its class,
  as [Identities and generations](#identities-and-generations) states,
  which is the rule for slots of the security model's
  [internal choices](../../../security.md#internal-choices); a retired slot
  is never chosen. The slot of a capability is the caller's choice, a rule
  of the capabilities component.
- **Generations.** The generation of a new object is the generation of its
  slot, which follows from the slot's history alone.
- **Quotas.** Charges, credits, splits and merges are fixed arithmetic on
  the records; a share is the caller's argument.
- **Write-back.** The keys of a write set are distinct, so the order of the
  write-back does not change the result.
- **Requests.** Requests that contend for a pool or a record take effect in
  the order in which they enter the kernel. With more than one CPU, the
  order in which CPUs take the token of the same pool or record is the
  multicore interleaving that [ND-03](../../../security.md#nd-03) of the
  register of
  [permitted nondeterminism](../../../security.md#permitted-nondeterminism)
  allows; for each such order, the rules of this page fix the result.
- **Boot.** The capacities, the allocations and the pool numbers follow from
  the bytes of the record and the values that the boot wiring passes.

The component leaves no other choice open.

## State fields

| Field | Class | Lock or owner | Linearization point | Publication |
| --- | --- | --- | --- | --- |
| The state, generation and owner of each slot of the five carved pools | Shared | The token of the pool; with one CPU, the executing CPU | The release of the token after the write-back of the write set that changes the slot | Under the token, by the release of the lock that provides it once CPUs share it |
| The counts of each pool: free, allocated and retired slots | Shared | The token of the pool | The release of the token after the write-back | Under the token |
| The quota record of each process, in its process slot, and the record of the kernel domain | Shared | The token of the record | The release of the token after the write-back | Under the token |
| The capacities, the pool numbers and the slot of the device directory | Shared, read-only after boot | The boot CPU, which builds them before any entry from EL0 | The return of `ObjectTable::new` | Once, before the secondary CPUs start; they never change afterwards |
| The write-set buffer of each CPU | Per-CPU | Its CPU, which lends it to the entry that runs; empty before and after every entry | - | `none`: its single owner never changes |
| The audit counters: for each pool, the slots occupied and released, one set for each CPU | Shared | Its CPU, which alone increases them, in `commit` | The increase in `commit` | By a Release store of the increase, which a reader on another CPU loads with Acquire |

The fields of the objects in the slots, the capability tables, the VM
region tables and the count of capabilities of each object are fields of
the components that define them, which classify them in their contracts.
The page ownership table that holds the storage is a field of the
[page-tables](../../memory/page-tables/contract.md#state-fields) component.

## Testing obligations

- The host tests of the module `objects` (planned) replay every vector of
  [Legacy test vectors](#legacy-test-vectors) whose entry is on this page,
  with its expected output, and write their results for the comparison with
  the specification
  ([host results](../../../formal-verification.md#host-results)); the
  vectors whose entry belongs to another component are replayed by that
  component.
- Each check of the capacity record has a test at its limit and one beyond:
  each of the seven fields from `processes` to `vm_regions` at 1 is
  accepted and at 0 refused; 65,536 capability slots are accepted and
  65,537 refused; as many threads as processes are accepted and one fewer
  refused; a reserve equal to its pool is accepted and one more refused; a
  record of 47 bytes is refused; allocations that fit the free pages
  exactly are accepted and one page more fails with `InsufficientMemory`.
  For each pair of consecutive checks of the order whose errors differ, a
  record that breaks both gives the error of the earlier: checks 4 and 5
  through `validate_capacities`, and checks 1 and 2 and checks 5 and 6
  through the boot wiring, where the errors of the address-space component
  differ from those of checks 2 and 5. Checks 2 to 4 share
  `InvalidConfiguration`, so their order is not observable and has no such
  test.
- The default record of each board passes the checks and provides at least
  64 processes and 256 threads.
- `Capacities::allocations` gives eight allocations with distinct owner
  identities and the pages that this page computes, for the default records
  and for a record at the limits; on the page ownership table of the 8 GB
  Pi 5, the boot wiring's carving of each adds at most one extent.
- Generations: a slot occupied and released $n$ times has generation
  $n + 1$; a slot that a test sets to $2^{64} - 1$ is occupied once and its
  release retires it; the reference of a retired slot fails with
  `StaleReference`; after every step the counts add up to the capacity.
- Conservation: a property test starts from `ObjectTable::new` and the
  boot of the root, drives creations, splits, charges, credits, merges and
  releases over a tree of processes, among them the destruction of a
  parent with children, and checks after every write-back, against an
  independent model of owners, limits and usages, both statements of
  [Conservation](#metadata-quotas) and the sum of the split limits.
- The record of the kernel domain, with every limit and usage 0 after
  `ObjectTable::new` and with a control usage of 1 child process after the
  boot of the root; the root's starting limits, as `start_root` writes
  them, for a record with reserves of 0, with reserves at their pools and
  with a thread pool whose ordinary capacity is below that of the process
  pool; a release of a process slot whose record still counts a capability
  entry is `InvalidState`; and an ordinary creation within the quota that
  meets `PoolExhausted` only after control allocations have taken slots of
  the ordinary range, once with control allocations beyond a full reserved
  tail and once with the root's pair in a process pool whose control
  reserve is 0.
- Write sets: for each fault-injection point of the implementation, an
  operation that fails there leaves every slot, count and quota record as
  before; a write set of $W$ items commits, and one more key fails with
  `WriteSetFull`.
- For each error of [Errors](#errors), a call that gives it leaves every
  field of the table, of the records and of the buffer as before, compared
  field by field.
- The process pool is filled with ordinary processes, each with its thread,
  and emptied again three times, and after each round the counts and
  usages equal those before; the thread pool is filled only as far as the
  processes take it, since a process has one thread.
- QEMU tests boot QEMU virt with the default record, and with a record whose
  allocations do not fit, which stops the boot with `InsufficientMemory`;
  three cold boots give the same counts.
- The tests take their expected values from this page, from the vectors and
  from independent models, never from an earlier run of the code under test
  ([testing](../../../conventions/testing.md#independent-evidence)).

## Open obligations

The module `objects` has no `unsafe` code, no assembly and no MMIO, and its
entries are to be covered by its targets. An entry that a later contract
adds to the object table beyond the entries of this page is an open
obligation of the contract that adds it, carried by the proof of object
lifetimes, waits and sequential composition, by release 0.2. The
obligations of the code around this page are the adapter that lends the
write-set buffer of the executing CPU
([rule 8](../../../conventions/provable-subset.md#8-no-interior-mutability))
and the board's forming of the slices of the storage carved at boot
([Extractability](#extractability)). Each board forms those slices in its
board crate; the row of the Pi 5 board is added with its board crate.

| Obligation | Kind | Verified state | Carrier | Stage |
| --- | --- | --- | --- | --- |
| `kernel/arch/src/percpu.rs#enter_masked` (planned) | `unsafe` | Neither (finds the per-CPU record of the executing CPU, masks its interrupts and lends its write-set buffer by `&mut` for no longer than the token of the CPU lives; it reads and writes none of the buffer's contents) | The proof of the SMP primitives and of the concurrency backend | `0.2` |
| `kernel/boards/qemu-virt/src/main.rs#image::object_storage` (planned) | `unsafe` | Neither (forms, through the direct map, the slices of the eight allocations of [Storage carved at boot](#storage-carved-at-boot) on the pages that the page ownership table holds for their owner identities, after their zeroing, each of the size that `Capacities::allocations` gives; it reads and writes none of their contents) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` |

## Legacy test vectors

The vectors are host tests of the prototype tree at
`prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`, 36 in all. Their
expected outputs are those that the test bodies assert, written in the
rules of this page. The vectors are not yet in a file of the repository, so
the section holds no `vectors` block.

| File | Vectors |
| --- | ---: |
| `src/objects/tests.rs` | 13 |
| `src/objects/tests/activations.rs` | 20 |
| `src/smp/tests.rs` | 3 |

- `src/objects/tests.rs` holds 20 tests. The 13 below are frozen here; the
  other seven test the lifetimes of processes and threads, exit,
  termination, quiescence and the gates of reclamation, and are vectors of
  the lifecycle component of this domain, not of this page.
- The 23 vectors of `src/objects/tests/activations.rs` and
  `src/smp/tests.rs` are the tests in which the prototype's activation
  entries must reject, without a panic and without a change, one of three
  inputs, and that input decides the rejection: an invalid owner identity
  of the thread, that is a missing owner, a slot number beyond the pool, a
  key of another pool or slot, or a generation that does not match; a pool
  of no process slot; and a CPU number outside the activation array.
  `activation-legacy-10`, `activation-parallel-10`, `smp-2` and `smp-3`
  also put that rejection before a later check of the activation. The
  other activation tests of these files are not frozen here: those of a
  dying or a dead owner, whose state is the lifecycle component's; those of
  the activation serial alone, and of the claims, stops and receipts of the
  activation, which are the scheduler's; those in which another check of
  the activation decides the rejection; and those of its successes. The
  activation itself is not an entry of this component, so these vectors
  hold for the resolution of references and the checks of the capacity
  record. The eight tests of `src/smp/tests.rs` from line 13 to line 189
  are not activation tests and are not frozen here either: they test the
  single CPU that owns a thread, the budget ledger of the scheduler, and
  the acknowledgements of stops and TLB invalidations that hold back a
  reclamation.
- Four vectors test rules of other components and are frozen here with the
  component that receives them: `objects-7` the capabilities component,
  `objects-9` and `objects-12` the waits component, and `objects-13` the
  scheduler.

A vector of this page is one test function; a function that a macro expands
in two modules is two vectors. The vector file is to hold one line for each
case of it through an entry, with the id `<vector>.<n>`, `n` counting those
cases from 1 in the order of the test; a case that its row marks not
applicable has no line.

**Notation.** Counts, slot numbers and generations are decimal. A table is
written by the fields of its capacity record that the case sets, the other
capacities being 1 and the other reserves 0, and by the number of its first
pool, 1 unless the row says otherwise. A reference is
`<pool>:<slot>:<generation>`. The output of a call is `ok`, followed by its
fields, or `err=<error>`, with the error by its name on this page; a
structured value is a list of `key=value` fields separated by single
spaces, in the order of the expected output below. The counts of a pool are
`free`, `allocated` and `retired`.

**Owners and charges.** The vectors call `occupy` and `release` without
`charge` and `credit`, for an owner that the test passes, so they charge
no quota record. `objects-1`, `objects-3`, `objects-4`, `objects-5`,
`objects-8` and `objects-11` and the fixture of the owner vectors build
their tables without the root's pair, and `objects-6` and `objects-10`
occupy the root's pair without the charge of the boot of the root. They
hold for the slots, the generations and the counts; the
[Conservation](#metadata-quotas) of usages is not checked on their tables.

**Vectors of a property.** `objects-10` and `smp-1` assert a property over a
generated family of inputs; their rows state the property and the
generation rule. `objects-1` is composite: the prototype's self-test, whose
steps the row assigns to their components.

**Behaviour changes.** These rules differ from the prototype:

- A generation belongs to a slot, from 1, and a slot at $2^{64} - 1$ retires
  when it is released, where the prototype's pool had one counter for all
  its slots and refused every creation once it ran out. The generations of
  `objects-3`, `objects-10` and `objects-11` change.
- A rejected request writes nothing: the prototype's counts of failed
  creations, pool exhaustions, quota failures, failed preparations and
  exhausted generations are not kept, and the assertions of `objects-1`,
  `objects-3`, `objects-4` and `objects-11` on them are dropped. The counts
  of created and reaped objects are the audit counts of occupied and
  released slots.
- The prototype's preparation callback is a fault-injection point of a test
  build.
- References carry no rights; the rights live in capability entries.
- A slot holds no copy of its pool number or slot number, so a damage of
  those copies, as in `activation-legacy-7` and `activation-parallel-7`,
  does not exist, and a reference whose pool and copy were both changed, as
  in `activation-legacy-9`, is a reference of another pool.
- The owner failures that the prototype's activation reported as
  `InvalidState` are `WrongPool` and `StaleReference` of `resolve`, and a
  record of no process slot is `InvalidConfiguration`.
- The allocation class is an argument of the kernel's own entries, not a
  token of a pool.
- A capacity record has at least as many threads as processes, so the
  thread pool of `objects-4` runs out through its control reserve instead
  of its capacity.

### Object table vectors

`src/objects/tests.rs`, 13 vectors.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `objects-1` | 15 | `reusable_self_test_covers_the_same_contracts_without_host_facilities` | Composite. One table `processes=3 threads=4 reserved_processes=1 reserved_threads=1`. A creation of a pair that meets a fault-injection point is `err=InjectedFault` and leaves the counts as before; two ordinary pairs take process slots 0 and 1; a third is `err=PoolExhausted`, the reserved process slot 2 left free; the prototype's limit of threads of a process does not exist, since a process has one thread, and `check` of an item at its limit stands for it, `err=QuotaExceeded`; a control pair takes process slot 2 and thread slot 3, and 3 processes are allocated; after the release of the slots of the two ordinary pairs, a new ordinary pair takes process slot 0 and thread slot 0 with the references `1:0:2` and `2:0:2`, the references `1:0:1` and `2:0:1` of the first pair are then `err=StaleReference`, and the slots of the new pair are released; at the end 1 process and 1 thread are allocated, the control pair, and the audit counts of released process and thread slots are 3 and 3. The prototype's other steps belong to other components: the attenuation of rights to the capabilities component; the single winner of a wait, its result and its stale ticket to the waits component; termination, activation, quiescence, the reference gates of reaping and the exit status to the lifecycle component. The prototype's count of at least 18 checks counts the steps of the test itself and does not apply | `stage`, `commit`, `discard`, `choose`, `occupy`, `release`, `QuotaRecord::check`, `resolve`, `counts` |
| `objects-2` | 28 | `configuration_rejects_missing_capacity_or_invalid_reserve` | In the order of the test: the records `processes=0 threads=1` and `processes=1 threads=0`; `ObjectTable::new` of a table `processes=1 threads=1` with the first pool number 0; and the records `processes=1 threads=1 reserved_processes=2` and `processes=1 threads=1 reserved_threads=2`: each `err=InvalidConfiguration` | `validate_capacities`, `ObjectTable::new` |
| `objects-3` | 52 | `failed_preparation_never_publishes_or_charges_objects` | Table `processes=2 threads=2`: 8 creations of a pair, each meeting a fault-injection point, are each `err=InjectedFault`, and after each the counts are `free=2 allocated=0 retired=0` for both pools and every slot is free; then a pair commits with the references `1:0:1` and `2:0:1`, and the audit count of occupied process slots is 1 | `stage`, `commit`, `discard`, `choose`, `occupy`, `counts` |
| `objects-4` | 72 | `thread_exhaustion_leaves_free_process_slot_unpublished` | Table `processes=2 threads=2 reserved_threads=1`, whose ordinary range of threads has one slot, with one ordinary pair: the checks of a second ordinary pair give `err=PoolExhausted` for the thread pool, before any write and any fault-injection point; the counts are unchanged and process slot 1 stays free. The prototype's table of 2 processes and 1 thread fails check 3 of the capacity record | `choose`, `counts` |
| `objects-5` | 86 | `control_reserve_requires_pool_bound_internal_authority` | Table `processes=2 threads=2 reserved_processes=1 reserved_threads=1` with one ordinary pair: an ordinary thread slot and an ordinary pair are each `err=PoolExhausted`; a control pair takes process slot 1 and thread slot 1, and 2 processes and 2 threads are allocated. The prototype's control token of another pool, `PermissionDenied`, does not apply | `choose`, `occupy`, `counts` |
| `objects-6` | 110 | `bootstrap_is_explicit_and_all_reserved_pool_excludes_ordinary_allocations` | Table `processes=1 threads=1 reserved_processes=1 reserved_threads=1` with the first pool number 13: the root's pair, a control allocation of the kernel domain, gets `13:0:1` and `14:0:1`, references into the process and thread pools of the table; an ordinary pair is `err=PoolExhausted`; the root's process slot resolves. That the root is alive is the lifecycle component's state | `ObjectTable::new`, `choose`, `occupy`, `resolve` |
| `objects-7` | 122 | `attenuated_receipts_cannot_regain_control_or_change_state` | A process and its thread, each named with only the right to observe: both can be queried; widening either to all rights is `PermissionDenied`; creating a thread, terminating the process, beginning a wait, terminating the thread and retaining a resource through them are each `PermissionDenied`; 1 process is allocated and stays alive | The capabilities component, which holds the rights: no entry of this page, since references carry no rights |
| `objects-8` | 159 | `a_receipt_from_another_pool_cannot_name_a_matching_slot` | Two tables, each `processes=1 threads=1` with one pair, the first with the first pool number 1 and the second with 7, so that their pools have no number in common: the process reference `1:0:1` and the thread reference `2:0:1` of the first, resolved in the second, are each `err=WrongPool`. A wait ticket of the first, completed in the second, is `WrongPool` and leaves no pending wait there: a case of the waits component | `resolve`; the waits component, for the ticket |
| `objects-9` | 257 | `all_wait_completion_orders_have_exactly_one_winner` | For each of the four outcomes signalled, timed out, cancelled and peer closed as the winner: during the wait, another begin and a take of the result are `WaitInProgress`; the previous ticket is `StaleWait`; the winner completes and each loser is `AlreadyCompleted`; the take gives the winner, and another take `StaleWait`; 4 completions | The waits component; no entry of this page |
| `objects-10` | 345 | `repeated_command_cycles_retain_the_root_and_never_reuse_generation` | Property. Table `processes=8 threads=16 reserved_processes=1 reserved_threads=2` with the root's pair, a control allocation, in process slot 7 and thread slot 14. Rounds $n$ from 1 to 128: an ordinary pair is occupied and its slots are then released; it gets `1:0:<n>` and `2:0:<n>`, a generation larger than in every earlier round; the process reference of round $n - 1$ is `err=StaleReference`, and in round 1 there is none; after each round the counts equal those before the first and the root's slots are unchanged. At the end the audit counts of occupied and released process slots are 129 and 128. Lines `objects-10.1` to `objects-10.128`, one for each round: `process=<reference> thread=<reference> stale=<output>`, the output `-` in round 1; line `objects-10.129`: `occupied=129 released=128` | `choose`, `occupy`, `release`, `resolve`, `counts` |
| `objects-11` | 373 | `generation_exhaustion_never_wraps_or_commits_half_a_pair` | Table `processes=2 threads=3` whose slots all start at generation $2^{64} - 1$, which a test sets: a pair gets `1:0:18446744073709551615` and `2:0:18446744073709551615`; its release retires both slots, leaving the process pool `free=1 allocated=0 retired=1` and the thread pool `free=2 allocated=0 retired=1`, and its references are `err=StaleReference`; a second pair takes process slot 1 and thread slot 1, and its release retires them; a third pair is `err=PoolExhausted` for the process pool before any write, and the thread pool stays `free=1 allocated=0 retired=2`. The prototype's three refusals with its pool-wide counter do not apply | `choose`, `occupy`, `release`, `resolve`, `counts` |
| `objects-12` | 396 | `wait_generation_exhaustion_does_not_reset_to_an_old_ticket` | A thread whose next wait generation is $2^{64} - 1$: one wait completes and its result is taken; a further begin is `GenerationExhausted`; the thread stays ready with no pending wait | The waits component; no entry of this page |
| `objects-13` | 412 | `activation_is_single_owner_and_never_schedules_a_blocked_or_dead_thread` | With the first of two threads active, activating the second is `Busy`; quiescing the second is `InvalidState`; beginning a wait on the running thread is `InvalidState`; after quiescence the wait can begin; activating the blocked thread and the terminated thread is `InvalidState`; the process stays alive | The scheduler; no entry of this page |

### Owner and capacity vectors

`src/objects/tests/activations.rs`, 20 vectors, and `src/smp/tests.rs`, 3
vectors. The macro `owner_regressions!` of `activations.rs` expands the same
ten frozen functions in the module `activation_migration::legacy`, line 437,
and in `activation_migration::parallel`, line 442; the line of a row is the
line of the function in the macro. The two prototype entries that the
modules call differ only in the activation, which is not part of this
component, so `activation-parallel-<n>` holds the cases of
`activation-legacy-<n>`.

**Fixture.** Table `processes=2 threads=3` with two pairs, with the
generations that the prototype's counter gave them: process slot 0 at 1,
thread slot 0 at 2, process slot 1 at 3, thread slot 1 at 4, a state that
generations of slots reach after earlier releases. The thread of slot 0
holds the reference `1:0:1` of its process. A case damages that reference or
that process slot as its row states and resolves the reference with
`resolve` for a process. Every case returns without a panic, and every
field of the table is unchanged. The prototype's other fields of the
fixture, a completed wait and counts of references, belong to other
components and do not apply.

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `activation-legacy-1`, `activation-parallel-1` | 288 | `missing_owner` | Process slot 0 made free, its generation left at 1: `err=StaleReference` | `resolve` |
| `activation-legacy-2`, `activation-parallel-2` | 292 | `zero_process_capacity_is_an_ordinary_owner_rejection` | The record `processes=0 threads=3`: `err=InvalidConfiguration`, so no table has a process pool of no slot; the reference `1:0:1` resolved against such a pool, which a test builds without `ObjectTable::new`: `err=StaleReference` | `validate_capacities`, `resolve` |
| `activation-legacy-3`, `activation-parallel-3` | 313 | `owner_slot_past_end` | The reference `1:2:1`: `err=StaleReference` | `resolve` |
| `activation-legacy-4`, `activation-parallel-4` | 317 | `owner_slot_maximum` | The reference `1:4294967295:1`, the largest slot number: `err=StaleReference` | `resolve` |
| `activation-legacy-5`, `activation-parallel-5` | 321 | `foreign_owner_pool` | The reference `2:0:1`, its pool number raised by one: `err=WrongPool` | `resolve` |
| `activation-legacy-6`, `activation-parallel-6` | 325 | `owner_generation_mismatch` | The reference `1:0:2`: `err=StaleReference` | `resolve` |
| `activation-legacy-7`, `activation-parallel-7` | 329 | `occupant_key_slot_mismatch` | The slot number kept in process slot 0 changed to 1 | Not applicable: a slot keeps no copy of its slot number |
| `activation-legacy-8`, `activation-parallel-8` | 333 | `another_live_slot_is_not_the_owner` | The reference `1:1:1`, which names process slot 1 at a generation that it does not hold: `err=StaleReference` | `resolve` |
| `activation-legacy-9`, `activation-parallel-9` | 337 | `matching_foreign_owner_keys_are_rejected` | The reference `2:0:1`, with the pool number kept in process slot 0 raised by one as well; a slot keeps no copy of its pool number, so the case is that of `activation-legacy-5`: `err=WrongPool` | `resolve` |
| `activation-legacy-10`, `activation-parallel-10` | 417 | `owner_validation_precedes_exhaustion` | The reference `1:0:2`, with the activation serial exhausted; the serial belongs to the scheduler, so the case is that of `activation-legacy-6`: `err=StaleReference` | `resolve` |
| `smp-1` | 212 | `activation_migration_all_raw_cpu_values_have_total_entry_results` | Property: the raw CPU values 0 to 255 in turn; below 4 the activation succeeds with serial 1, and each of the other 252 is `InvalidState` with the pool unchanged and no panic | Not applicable: no entry of this component takes a CPU number, since per-CPU state comes in by `&mut` |
| `smp-2` | 252 | `activation_migration_invalid_cpu_precedes_nonlegacy_duplicate_busy` | With the thread active on CPU 0, CPU 255 is `InvalidState`, before `Busy`, and the pool is unchanged | Not applicable, as `smp-1` |
| `smp-3` | 299 | `activation_migration_invalid_cpu_precedes_serial_exhaustion` | With the serial exhausted, CPUs 4 and 255 are `InvalidState` and CPU 0 is `GenerationExhausted`, each with the pool unchanged | Not applicable, as `smp-1` |

## References

- The kernel's own rules, which this page instantiates:
  [Kernel objects and capabilities](../../../architecture.md#kernel-objects-and-capabilities)
  for the kinds, capacities, generations, dangling references, quotas and
  transactions, and the execution model under
  [System calls and the ABI](../../../architecture.md#system-calls-and-the-abi)
  for entries that run to completion and long operations that store their
  progress in their objects.
- G. Klein, J. Andronick, K. Elphinstone, T. Murray, T. Sewell, R. Kolanski,
  G. Heiser, "Comprehensive Formal Verification of an OS Microkernel", ACM
  Transactions on Computer Systems 32(1), 2014,
  <https://trustworthy.systems/publications/nicta_full_text/7371.pdf>: the
  checking and executing phases, and the absence of allocation at run time.
- X. Chen, Z. Li, J. Zhang, V. Narayanan, A. Burtsev, "Atmosphere: Practical
  Verified Kernels with Rust and Verus", SOSP 2025,
  <https://mars-research.github.io/doc/2025-sosp-atmo.pdf>: flat tables of
  objects referred to by index.
- The rules of this page take, as clauses of their own, the rules of the
  prototype tree at `prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`:
  - `docs/features/kernel/foundations.md`, lines 98 to 139: object
    ownership, identities and rights, creation, quotas and exhaustion; its
    rows on waits, exit and reclamation belong to the waits and lifecycle
    components;
  - `docs/features/kernel/foundations.md`, lines 140 to 160: activation
    admission, the complete identity of the owner and the raw CPU number;
  - `docs/features/kernel/foundations.md`, lines 186 to 201: the persistent
    pool, its control reserve and its ordinary range;
  - `verification/group-stop/activation-migration.md`, lines 17 to 42: the
    input domain of every representable pool and reference, and the
    rejection that leaves the whole pool unchanged;
  - `verification/group-stop/activation-migration.md`, lines 43 to 86: the
    lookup predicates of a thread and its owner, and the order of
    rejections;
  - `verification/group-stop/activation-migration.md`, lines 139 to 160:
    the counterexamples of the owner and the evidence they require;
  - `docs/kernel-state.md`, lines 43 to 76: the objects of the resource
    managers and the division into per-CPU, per-thread, per-process and
    shared state.
