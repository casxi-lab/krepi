# VM contract

This page governs the code of the `vm` component of the
[memory and address spaces](../README.md) domain: the VM window of every
process and the regions in it, with the region table of each process; the
five operations `reserve`, `commit`, `decommit`, `mprotect` and `release`,
which act on the caller's own address space; the VM part of the capacity
record; the page pool from which committed pages and the private pages of
loaded images come, with the metadata of its frames; the two-phase release,
which the release of a region and the destruction of a process share; and
the plans that the entries of this page give, with their acknowledgement.
The tables themselves are written by the entries of the
[page-tables](../page-tables/contract.md) component; the address space of
each process, with its ASID and its table pool, is the
[address-space](../address-space/contract.md) component's; and the quota
records are the
[objects](../../objects-capabilities/objects/contract.md#metadata-quotas)
component's. The validation of loading requests, with the loading part of
the capacity record, belongs to the
[dispatch](../../runtime-sdk/dispatch/contract.md) component, which
the address-space and objects contracts call the loading component; the
mapping of loaded images to the
[creation](../../objects-capabilities/creation/contract.md) component; and
the destruction of a process, which composes the revocation of this page,
to the [lifecycle](../../objects-capabilities/lifecycle/contract.md)
component. The observable behaviour that these rules serve, with its
evidence, is in the [requirements](requirements.md), the other document of
the component.

## Terms

- **VM window.** The virtual addresses `[VM_START, VM_END)`,
  `[0x4040000000, 0x4080000000)`: the second 1 GiB slot of the EL0 window,
  slot 257 of the lower region, in which every region of every process lies
  ([VM window and regions](#vm-window-and-regions)).
- **Region.** A range of whole pages of the VM window of one process that
  `reserve` establishes, named by its start. It is a row of the VM region
  table of its process, not an object with a pool, and no capability names
  it ([object kinds](../../objects-capabilities/objects/contract.md#object-kinds-and-pools)).
  The memory of a region is a private anonymous object of one thread: each
  of its pages is committed or not.
- **Committed page.** A page of a region that the lower tables of its
  process map, with a frame of the page pool and the kind `UserReadWrite`
  or `UserReadOnly`.
- **Region table.** The table of a process in the storage of the VM region
  tables that the objects component carves
  ([storage carved at boot](../../objects-capabilities/objects/contract.md#storage-carved-at-boot)):
  its VM head and its `vm_regions` rows, `vm_regions` being the field of the
  [capacity record](../../objects-capabilities/objects/contract.md#capacity-record).
- **VM head.** `vm::Regions` (planned): the record at the start of the
  region table of a process: the set of its rows in use, its first row in
  address order, the set of the 2 MiB slots of its VM window that hold a
  level 3 table, and the cursor of the operation in progress.
- **Row.** One row of a region table: the start and the pages of a region,
  its neighbours in address order, the count of its pages that hold a
  frame and its phase, live or pending with the progress of its release. A
  commit raises the count by its pages, and the return of each frame of the
  region to the pool in a decommit or a release lowers it by one; the
  revocation at the destruction of a process frees the rows with the whole
  table instead.
- **Page pool.** `vm::Pool` (planned): the frames that the boot carves in
  one range of RAM, with their free stack and their metadata
  ([Configuration and the page pool](#configuration-and-the-page-pool)).
- **Frame.** A page of the page pool. A frame is free, on the free stack;
  committed, a frame that a commit has taken for a page of one process; or
  loaded, a private page of an image loaded into one process.
- **Committed chain.** The frames that one process holds, committed and
  loaded, linked in both directions through the metadata of the frames,
  with its head in that metadata: a frame joins it at the head and leaves
  it at any place in a fixed number of steps.
- **Plan.** What an entry of this page gives the architecture crate to
  execute: a write plan of the page-tables component, `page_tables::WritePlan`,
  or a frame plan, `vm::FramePlan` (planned), which zeroes one frame or
  copies bytes of the boot bundle into one frame
  ([Acknowledgement and reclamation](#acknowledgement-and-reclamation)).
- **Step.** `vm::Step` (planned): what an operation, `acknowledge` or
  `revoke_step` gives: a plan; `Again`, the end of a step of a long
  operation whose progress is stored and which has no result yet; or the
  result of the operation.
- **Cursor.** The field of the VM head that holds the operation in
  progress with its row, the next page, its end and the frame of the plan
  in flight; it
  is empty between transitions. A plan is in flight from the entry that
  gives it to its `acknowledge`.
- **Pending and completed.** A region is pending from the transaction that
  starts its release to the end of its release, which completes it; a
  completed region no longer exists.
- **Composer.** The module of the core above this one that composes an
  entry of this page: `dispatch`, for the operations and the
  acknowledgement of plans; `creation`, for the VM head of a new process and
  the private pages of its images; and `lifecycle`, for the revocation of a
  process that is destroyed (planned).
- **Boot wiring.** The code of a board crate that runs on the boot CPU
  before the first entry from EL0, as in the
  [objects](../../objects-capabilities/objects/contract.md#terms) and
  [address-space](../address-space/contract.md#terms) contracts.
- **Token.** What an access to state that is not per-CPU holds, as the
  [SMP design rules](../../../conventions/smp.md#s1-state-classes) state;
  with one CPU, the executing CPU holds every token.

## Entry points

The entries of the core are in the module `vm` of `krepi-kernel`
(planned); the adapter that executes frame plans is the module `frames` of
`krepi-arch` (planned). Five entries are operations of the ABI inventory,
in its production range: `reserve`, `commit`, `decommit`, `mprotect` and
`release` (planned). They act only on the address space of the caller's
own process and take no handle. Their operation numbers, the registers of
their arguments and results and the numeric values of their errors belong
to the inventory; this page names the arguments and the results. The other
entries are called by the boot wiring and by the composers. The first row
holds constants, and the last row is the adapter of the architecture
crate. Between them are the 13 entries of the core, which the
specification and the proof of the component (planned) take in two groups:
the five operations and `acknowledge`, 6 entries; and the configuration,
the page pool and the revocation at the destruction of a process,
`check_config`, `Pool::new`, `Pool::free`, `Pool::take`, `Pool::next`,
`Regions::new` and `revoke_step`, 7 entries.

| Entry point | Kind | Called by | ABI operation | Rules |
| --- | --- | --- | --- | --- |
| `vm::VM_START`, `VM_END`, `MAX_REGIONS`, `MAX_CALL_PAGES`, `RELEASE_BATCH`, `MAX_POOL_PAGES`, `OWNER_PAGE_POOL` and `OWNER_PAGE_FRAMES` (planned) | Constants, host-testable | The entries of this page; the boot wiring; the objects component, for `MAX_REGIONS` in its check of the capacity record; the composers, for the layout of the EL0 window (planned) | None | [VM window and regions](#vm-window-and-regions), [Configuration and the page pool](#configuration-and-the-page-pool), [Work bounds](#work-bounds) |
| `vm::check_config` (planned), with the value type `vm::Config` | Function that writes nothing, host-testable | The boot wiring, once, after the last check of the capacity record of the objects and address-space components and before it carves any storage; the boot of the root, `creation::boot_root` (planned), reads the root's limit of committed VM pages from the `Config` that it gives | None | [Configuration and the page pool](#configuration-and-the-page-pool) |
| `Pool::new` (planned), with the value type `vm::Pool` | Write entry, host-testable | The boot wiring, once, after it has carved the page pool and its metadata | None | [Configuration and the page pool](#configuration-and-the-page-pool) |
| `Pool::free` and `Pool::take` (planned) | A read entry and a write entry outside write sets, host-testable | `creation::spawn_commit` (planned): `free` in its checks; `take` after its write-back, once for each private page of the image that it loads | None | [Configuration and the page pool](#configuration-and-the-page-pool), [Quotas](#quotas) |
| `Pool::next` (planned) | Read entry outside write sets, host-testable, that writes nothing | `creation::acknowledge` (planned), in the continuation of a commit of `creation::spawn_commit`, to name the frame of each next private page in turn | None | [Configuration and the page pool](#configuration-and-the-page-pool) |
| `Regions::new` (planned), with the value type `vm::Regions` | Function that writes nothing, host-testable | `creation::spawn_commit` and `creation::boot_root` (planned), for the write set of the creation of a process and of the boot of the root | None | [VM window and regions](#vm-window-and-regions) |
| `vm::reserve` (planned) | Write entry on the copies of a write set, host-testable | `dispatch::entry` (planned), for the operation `reserve` | `reserve` | [VM window and regions](#vm-window-and-regions) |
| `vm::commit` (planned), with the value types `vm::Step` and `vm::FramePlan` | Write entry on the copies of a write set, host-testable; gives write plans | `dispatch::entry` (planned), for the operation `commit` | `commit` | [Commit](#commit), [Quotas](#quotas), [Tables and extents](#tables-and-extents) |
| `vm::decommit` (planned) | Write entry on the copies of a write set, host-testable; gives write plans and frame plans | `dispatch::entry` (planned), for the operation `decommit` | `decommit` | [Decommit](#decommit), [Acknowledgement and reclamation](#acknowledgement-and-reclamation) |
| `vm::mprotect` (planned) | Write entry on the copies of a write set, host-testable; gives write plans | `dispatch::entry` (planned), for the operation `mprotect` | `mprotect` | [Protection and W^X](#protection-and-wx) |
| `vm::release` (planned) | Write entry on the copies of a write set, host-testable; one step of a long operation, which gives write plans and frame plans | `dispatch::entry` (planned), for the operation `release`, also when the call is executed again | `release` | [Two-phase release](#two-phase-release) |
| `vm::acknowledge` (planned) | Write entry on the copies of a write set, host-testable; gives the next step | `dispatch::resume` (planned), after the architecture crate has executed a plan that an entry of this page gave, through `lifecycle::acknowledge` (planned) for the plans of `revoke_step` | None | [Acknowledgement and reclamation](#acknowledgement-and-reclamation) |
| `vm::revoke_step` (planned) | Write entry on the copies of a write set, host-testable; one step of a long operation, which gives frame plans | `lifecycle::destroy_step` (planned), in the destruction of a process, after the invalidation of its ASID and the reset of its lower tables | None | [Revocation at process destruction](#revocation-at-process-destruction) |
| `krepi_arch::frames::apply` (planned) | `unsafe` function | `el0_dispatch` of each kernel image, for a frame plan that `dispatch::entry` or `dispatch::resume` returns (planned) | None | [Acknowledgement and reclamation](#acknowledgement-and-reclamation) |

## Extractability

The module `vm` of the core (planned), in `kernel/src/vm.rs` (planned),
follows the [provable Rust subset](../../../conventions/provable-subset.md):
the window and its constants, the region tables, the five operations with
their checks and steps, the VM part of the capacity record, the page pool
with the metadata of its frames, the revocation at the destruction of a
process and the acknowledgement of plans. It is in layer 5 of the
[module order](../../../architecture.md#module-order-in-the-core). It refers
to `objects`, for write sets, quota records and references, and to
`address_space`, for the EL0 window and the table pool, both of layer 1; to
`page_tables` of layer 2, for the entries of the lower tables of a process
and their write plans; and to the kernel root, which holds the page pool
and the region tables. It refers to no module of its own layer, `waits` and
`scheduler`, or above it: `ipc`, `lifecycle`, `creation` and `dispatch`. It
reads no state of a process beyond its region table, its quota record, its
lower tables and its frames; whether a process is alive is the state of
`lifecycle`, which calls `revoke_step` only for a process whose destruction
has reached it, and the dispatch of the core passes no such state to the
operations, which only the running thread of a live process calls.

Its items are `pub(crate)` except the rows that the boot wiring calls,
`check_config` and `Pool::new`, with the value types that those rows and
the architecture crate take and return, `Config`, `Pool`, `FramePlan` and
the error type, and the constants of the first row that the boot wiring
uses, `MAX_POOL_PAGES`, `OWNER_PAGE_POOL` and `OWNER_PAGE_FRAMES`
([provable core](../../../architecture.md#the-provable-core)). The write
entries receive the one kernel root by `&mut`
([rule 3](../../../conventions/provable-subset.md#3-flat-relations-and-one-kernel-root))
and the write-set buffer of the executing CPU by an explicit `&mut`
argument
([rule 8](../../../conventions/provable-subset.md#8-no-interior-mutability)).
The module touches no register and defines no callback for a hardware
action: every change of a table or of the bytes of a frame is a plan that
the architecture crate executes, and an operation continues through
`acknowledge` once a plan has been executed.

The adapter `frames` of `krepi-arch` (planned), in
`kernel/arch/src/frames.rs` (planned), does not follow the subset: it
zeroes a frame with `krepi_arch::mmu::zero_frames` of the
[page-tables](../page-tables/contract.md#write-plans-and-publication)
component and copies bytes of the boot bundle into a frame. The boot
wiring, code of the board crates, forms the slice of the frame metadata on
the pages that it carves. Both are
[open obligations](#open-obligations). The prototype's VM controller called
its backend for each hardware action, which this page replaces by plans;
its rules are sources of this page ([References](#references)). The
contract is written before its code, so this section lists no source paths;
the change that adds the module writes its `paths` block here.

## VM window and regions

- **The window.** `VM_START` is `0x4040000000` and `VM_END`
  `0x4080000000`: the VM window is the second 1 GiB slot of the
  [EL0 window](../address-space/contract.md#el0-address-layout), 262,144
  pages under one level 2 table. Every region of every process lies in it,
  and so does every page that an entry of this page maps.
- **Its neighbours.** The boot ranges of the root, from `0x4000000000` to
  `0x4020000000`, and the
  [image window](../../runtime-sdk/dispatch/contract.md#the-image-window)
  of the dispatch component,
  which ends at or below `VM_START`, lie in the first 1 GiB slot of the EL0
  window; the windows of device grants, which the device-authority rules of
  the devices and DMA domain place, lie above `VM_END`. So the VM window
  shares no 1 GiB slot, and so no table, with them, and the root's boot
  ranges do not meet its own VM window. These are relations of constants:
  a host test checks them, and the boot checks nothing of them.
- **Regions.** `reserve(address, pages)` establishes a region of `pages`
  pages, at least one, and gives its `start`. The regions of one process
  never overlap, and a pending region keeps its range until it completes.
- **Placement.** An `address` other than 0 is the start, which the caller
  chooses. With the `address` 0, the region starts at the lowest address of
  the VM window at which `pages` pages lie outside every region of the
  process.
- **Checks of a reserve.** In this order, each before the first write:
  1. the form of the arguments: `address` is a multiple of 4096
     (`Alignment`); `pages` is at least 1 (`Length`); with an `address`
     other than 0, the range of `pages` pages from `address`, which ends at
     `address` $+ 4096 \cdot$ `pages`, does not wrap and lies in the VM
     window, and with the `address` 0, `pages` is at most the 262,144 pages
     of the window (`Window`);
  2. object state: no plan is in flight in the VM head (`InvalidState`);
     with an `address` other than 0, the range meets no region of the
     caller, pending ones included (`Overlap`), and with the `address` 0,
     the window holds `pages` pages in a row outside every region of the
     caller (`WindowFull`);
  3. the caller's quota: the region table of the caller has a free row
     (`RegionTableFull`).
- **Write set of a reserve.** At most 4 items: the new row, its neighbours
  in address order and the VM head. A reserve gives no plan, and its result
  is the `start`.
- **Rows.** A region table has `vm_regions` rows. `MAX_REGIONS`, 256, is
  the number of rows that a row number names, and so the bound of
  `vm_regions` in check 2 of the
  [capacity record](../../objects-capabilities/objects/contract.md#capacity-record).
  A new region takes the lowest free row of its table; the rows in use are
  linked in address order, the first one in the VM head. A row number is an
  internal identifier that no output carries: EL0 names a region by its
  start.
- **No generations.** A row has no generation in release 0.1: an address
  names the region that holds it at the time of the call, and a completed
  region leaves no name behind. Region generations come with futexes
  ([region generations](../../../architecture.md#futexes-and-upcalls)).
- **The VM head.** `Regions::new()` gives the empty VM head: no row in use,
  no level 3 table recorded and no operation in progress. The
  [creation of a process](../../objects-capabilities/creation/contract.md#child-processes)
  writes it into the VM head of the region table of its process slot, one
  item of its write set, and the
  [boot of the root](../../objects-capabilities/creation/contract.md#the-boot-of-the-root)
  does so for the root; the last step of the revocation at the destruction
  of a process writes it back.
- **The record of the pages.** A page of a region is committed exactly when
  the lower tables of the process map it, and the kind of its leaf is its
  protection. A row records neither the protection nor which of its pages
  are committed, only the count of its pages that hold a frame; the entries
  read the tables with `Tables::lookup_page` of the
  [page-tables](../page-tables/contract.md#entry-points) component.

## Configuration and the page pool

The VM part of the capacity record is bytes 48 to 63, after the object part
of the
[objects](../../objects-capabilities/objects/contract.md#capacity-record)
component: four unsigned 32-bit fields, little-endian, without padding, in
this order. The
[loading part](../../runtime-sdk/dispatch/contract.md#loading-configuration)
follows from byte 64 and belongs to the dispatch component; its fields are
not part of this page.

| Offset | Field | Unit | Content |
| ---: | --- | --- | --- |
| 48 | `root_vm_pages` | Pages | The root's starting limit of committed VM pages, the value of `root_limits` of the objects component for that item |
| 52 | `vm_page_cap` | Pages | The cap of the committed VM pages of each process, the root included |
| 56 | `pool_pages` | Pages | The frames of the page pool |
| 60 | `vm_reserved` | - | 0 |

**Checks.** `check_config(record, processes)` checks the bytes of the
record, as untrusted input, in this order, and returns the first error:

1. the record holds the 64 bytes up to the end of its VM part
   (`InvalidConfiguration`);
2. `root_vm_pages`, `vm_page_cap` and `pool_pages` are each at least 1, and
   `pool_pages` is at most `MAX_POOL_PAGES`, 4,194,304, the pages that the
   [page ownership table](../page-tables/contract.md#page-ownership)
   manages at most (`InvalidConfiguration`);
3. `vm_reserved` is 0 (`InvalidConfiguration`).

- It gives the `Config`: the three values and the two allocations below,
  for the process capacity `processes` of the object part.
- The boot wiring runs it once, after the last check of the capacity
  record, the process capacity against the ASIDs of the
  [address-space](../address-space/contract.md#address-spaces-and-asids)
  component, and before the
  [check of the loading part](../../runtime-sdk/dispatch/contract.md#loading-configuration)
  and before it carves any storage; it stops the boot at the error, without a
  fallback to the defaults. The three checks share one error, so their
  order is not observable.
- The fields count pages, and no loop of the core is bounded by them at
  run time: the operations are bounded by `MAX_CALL_PAGES` and
  `RELEASE_BATCH`, and `Pool::new` by `MAX_POOL_PAGES` at boot. A change of
  the values of a record changes neither the checks nor the bounds.

**Defaults.** When the directory holds no capacity record, the default
record of the board, `DEFAULT_CAPACITIES` (planned) of the
[objects](../../objects-capabilities/objects/contract.md#capacity-record)
contract, gives the VM part, which is checked in the same way. In the
default record of every board, `root_vm_pages` and `vm_page_cap` are each
at least 256 pages, 1 MiB. The pages that the root may commit are bounded
by the smaller of the two, so by at least 1 MiB, and the cap bounds every
other process by at least 1 MiB as well: the commit limit of each process
of the [capacities](../../../architecture.md#kernel-objects-and-capabilities)
of the default record. The pages that a child may commit are bounded in
addition by the share of the item that its creator splits to it
([Quotas](#quotas)). The default `pool_pages` of each
board, like the other default values, is a constant of its board crate,
named by its field, which the tests of the limits of loading and VM measure
(planned).

**Carving.** The `Config` gives two allocations, each one holder of the
page ownership table:

| Allocation | Pages | Owner identity |
| --- | --- | --- |
| The page pool | `pool_pages` | `OWNER_PAGE_POOL` |
| The frame metadata | $\lceil (16\,f + 8\,P) / 4096 \rceil$, for $f$ = `pool_pages` and $P$ = `processes`: 16 bytes for each frame and 8 for the head of the committed chain of each process slot | `OWNER_PAGE_FRAMES` |

- The boot wiring carves them in this order after the root's private
  allocation, step 2 of
  [the first process](../address-space/contract.md#first-process-and-boot-information),
  and before the module `creation` creates the root's process, step 3; so
  after the eight allocations of the objects component and the table pool
  of the address-space component. Each is one step of
  [zeroing before publication](../page-tables/contract.md#page-ownership):
  `Ownership::choose` at an alignment of one page and a low placement
  without a window, then `krepi_arch::mmu::zero_frames` of the chosen
  range, then `Ownership::assign` with its owner identity. The two owner
  identities are nonzero constants, distinct from each other and from the
  owner identity of every other holder. When the page ownership table finds
  no range, the boot stops with its error, `OutOfMemory` or
  `MetadataExhausted`, without a fallback.
- The page pool is one range in one bank, so the boot needs `pool_pages`
  free pages in a row. The metadata cannot be kept in the frames, since a
  frame of the pool is zero whenever it is free.
- `Pool::new(base, pages, metadata, processes)` gives the pool of the
  frames from `base`, every frame free, the lowest on top of the free
  stack, and every committed chain empty; it writes each entry of the
  metadata once. The boot wiring places the pool in the kernel root
  (planned) before the root's process is created.

**The pool.**

- A free frame is zero: the carving zeroes every frame, and a frame returns
  to the pool only after a zero plan of it has been executed
  ([Acknowledgement and reclamation](#acknowledgement-and-reclamation)).
- A frame that a process takes is the top of the free stack, and a frame
  that returns goes on top of it.
- `Pool::free()` gives the number of free frames. `Pool::take(process)`
  takes the top frame as a loaded frame of the process, links it at the
  head of the committed chain of the process and gives its physical
  address. The
  [creation of a process](../../objects-capabilities/creation/contract.md#child-processes)
  calls it after its write-back and before its first plan, for each private
  page of the image that it loads, having checked `free` and charged the
  pages before its first write, so that no plan in flight needs a free
  frame; `take` of an empty pool is `OutOfPages` and changes nothing, a
  call that no composer makes. A commit takes its frames as committed
  frames ([Commit](#commit)).
- `Pool::next(frame)` gives the frame linked after `frame`, away from the
  head, on the committed chain of the process that holds it, and none at
  the end of the chain; for a free frame, a call that no composer makes, it
  gives none as well. It writes nothing. The acknowledgement of a commit of
  the creation of a process calls it to name the frame of each next private
  page in turn, from the frame of the first, which heads the chain of the
  child after the last take
  ([private pages](../../objects-capabilities/creation/contract.md#child-processes)).
- Every frame has exactly one holder at any time: the pool or one process,
  on whose committed chain it is with its kind. The page ownership table
  records the whole pool as one holder; which process holds a frame is the
  record of this page.
- A frame is mapped at EL0 at most once, by the lower tables of the process
  that holds it, and at EL1 only through the direct map. Its physical
  address is not an output
  ([observable outputs](../../../security.md#observable-outputs)).

## Commit

`commit(address, pages)` commits `pages` pages from `address`, all in one
region of the caller, and gives no result value.

- **Checks.** In this order, each before the first write:
  1. the form of the arguments: `address` is a multiple of 4096
     (`Alignment`); `pages` is at least 1 and at most `MAX_CALL_PAGES`, 512
     (`Length`); the range of `pages` pages from `address`, which ends at
     `address` $+ 4096 \cdot$ `pages`, does not wrap and lies in the VM
     window (`Window`);
  2. the region, which takes the place of handle resolution: the first page
     lies in a region of the caller (`NoRegion`), and the range ends at or
     before its end (`RegionBounds`);
  3. object state: the region is not pending (`Pending`), no plan is in
     flight in the VM head (`InvalidState`, a call that no composer makes),
     and no page of the range is committed (`AlreadyCommitted`);
  4. the caller's quota: `QuotaRecord::check` of the committed VM pages
     with `pages` (`QuotaExceeded` of the objects component); the usage of
     that item plus `pages` is at most `vm_page_cap` (`CommitLimit`); the
     tables that the range needs are free in the table pool of the process
     (`OutOfTables` of the page-tables component,
     [Tables and extents](#tables-and-extents));
  5. shared capacity: the pool has at least `pages` free frames
     (`OutOfPages`).
- **Write set.** 3 items: the process slot of the caller, whose quota
  record is charged `pages` committed VM pages; the row, whose count grows
  by `pages`; and the VM head, with the 2 MiB slots of the range added to
  its set of slots and the cursor of the commit.
- **Steps.** After the write-back, page by page in address order, the
  commit takes the top frame of the free stack as a committed frame of the
  caller and links it at the head of the committed chain, so that the frame
  of each page is linked just before the frame of the page before it. It
  then gives the write plan of `Tables::map_page` of the first page, its
  frame and `UserReadWrite`, and `acknowledge` gives that of each next
  page; after the `acknowledge` of the plan of the last page, the result is
  `ok`. The checks fixed every plan, so each `map_page` passes its checks,
  and the frames of a commit have left the free stack before its first
  plan.
- A committed page reads zero, since its frame came zero from the pool, and
  is writable and never executable at EL0.
- The commit runs to its result in one transition, without a preemption
  point.

## Decommit

`decommit(address, pages)` returns the frames of `pages` committed pages
from `address`, all in one region of the caller, and keeps the region;
it gives no result value.

- **Checks.** The form of `address`, `pages` and the range, as for a
  commit (`Alignment`, `Length`, `Window`); the region (`NoRegion`,
  `RegionBounds`); then object state: the region is not pending
  (`Pending`), no plan is in flight in the VM head (`InvalidState`), and
  every page of the range is committed (`NotCommitted`).
- **Write set.** 1 item: the VM head, with the cursor of the decommit.
- **Steps.** After the write-back, page by page in address order: the
  write plan of `Tables::unmap_page` of the page, `Store` and then
  `Invalidate`
  ([unmapping](../page-tables/contract.md#write-plans-and-publication)),
  which gives the frame; after its `acknowledge`, the frame plan that zeroes
  the frame; and after the `acknowledge` of that plan, the return of the
  frame to the pool with the credit of one committed VM page to the caller
  and the count of the row lowered by one
  ([Acknowledgement and reclamation](#acknowledgement-and-reclamation)).
  After the last page, the result is `ok`.
- The range stays a region of the caller, and its pages are not mapped
  until they are committed again; an access at EL0 takes a translation
  fault.
- The decommit runs to its result in one transition, without a preemption
  point.

## Protection and W^X

`mprotect(address, pages, protection)` changes the access of `pages`
committed pages from `address`, all in one region of the caller, and gives
no result value. `protection` is a mask: bit 0, value 1, read; bit 1, value
2, write; bit 2, value 4, execute. The value 1 gives `UserReadOnly` and the
value 3 `UserReadWrite`.

- **Checks.** The form of `address`, `pages` and the range, as for a commit
  (`Alignment`, `Length`, `Window`), and of `protection`: no bit above
  bit 2, and bit 0 set (`Protection`); the region (`NoRegion`,
  `RegionBounds`); rights: bit 2 clear (`ExecuteDenied`), since no memory
  object of release 0.1 carries the execute right, and a later release
  refuses the bit in the same place for an object without that right
  ([address spaces and VM objects](../../../architecture.md#address-spaces-and-vm-objects));
  then object state: the region is not pending (`Pending`), no plan is in
  flight in the VM head (`InvalidState`), and every page of the range is
  committed (`NotCommitted`).
- **Write set.** 1 item: the VM head, with the cursor of the `mprotect`.
- **Steps.** After the write-back, page by page in address order, for each
  page whose kind differs from the one requested: the write plan of
  `Tables::unmap_page`, which gives its frame, and after its `acknowledge`
  the write plan of `Tables::map_page` of the page, the same frame and the
  new kind: two plans, break-before-make, since no entry replaces a valid
  entry ([no remapping](../page-tables/contract.md#write-plans-and-publication)).
  A page that has the requested kind gets no plan. After the last page, the
  result is `ok`.
- The protection is kept in the leaf, so an `mprotect` of a part of a
  region splits no row and needs no free row. A page that is reserved and
  not committed is the only inaccessible page: `mprotect` makes no page
  inaccessible.
- The `mprotect` runs to its result in one transition, without a
  preemption point.

**W^X.** No frame of the pool is ever writable and executable:

- The entries of this page map a frame only with `UserReadWrite` or
  `UserReadOnly`, neither of them executable
  ([descriptors and attributes](../page-tables/contract.md#descriptors-and-attributes)),
  and never with `UserReadExecute` or a device kind; the
  [creation](../../objects-capabilities/creation/contract.md#child-processes)
  component maps a loaded frame with `UserReadWrite` as well.
- A frame has at most one mapping at EL0, of the process that holds it, and
  its alias in the direct map is read-write and execute-never at EL1 only.
  A frame returns to the pool only after the entry that maps it is gone, so
  its next holder never finds a second mapping of it.
- So executable pages come only from the boot bundle, as the page-tables
  component states for release 0.1.
- The writable and the executable mappings of each memory object, which the
  [architecture](../../../architecture.md#address-spaces-and-vm-objects)
  counts to keep W^X, are quantities that follow from the state, not fields
  of it: the object of a region has no executable mapping, and its writable
  mappings are its committed pages of the kind `UserReadWrite`.

## Two-phase release

`release(address)` removes the region that starts at `address`, with every
committed page of it, in two phases, and gives no result value.

- **Checks.** `address` is a multiple of 4096 (`Alignment`) and lies in the
  VM window (`Window`); a region starts at `address` (`NoRegion`); no plan
  is in flight in the VM head (`InvalidState`). A region that is pending
  passes: the call continues its release.
- **Pending.** The call that finds the region live marks it pending, with
  its progress at its start, in the write set of its first step. From that
  write-back on, `commit`, `decommit` and `mprotect` in the region are
  refused with `Pending`, and a `reserve` that meets its range with
  `Overlap`, or with `InvalidState` while a plan of the release is in
  flight, so new accesses are refused at once.
- **Steps.** Each call of `release` takes one step: it examines the next
  pages of the region from its progress, at most `RELEASE_BATCH`, 64, and,
  for each committed page among them in address order, gives the plans of a
  decommit: the write plan of `Tables::unmap_page`, the zero plan of the
  frame and, at the `acknowledge` of that plan, the return of the frame
  with the credit of one committed VM page and the count of the row
  lowered by one. The write set of a step is 2 items, the row with its
  phase and progress and the VM head with the cursor; a step that completes
  the region without a committed page among its pages also holds the
  neighbours of the row in address order, at most 4 items. A step ends:
  - with the completion of the region, when its progress has reached its
    end or its count is 0: the row leaves the region table and the result
    of the call is `ok`;
  - otherwise with `Again`, at a preemption point: the progress stays in
    the row, the call writes no result, and the
    [dispatch of the core](../../runtime-sdk/dispatch/contract.md#execution-again)
    executes the call again from the saved user registers, at
    once or, when an interrupt is pending, once the thread runs again
    ([execution again](../address-space/contract.md#kernel-stacks-and-blocking)),
    and the call continues from the progress.
- **Completion.** A page completes when its frame returns to the pool,
  after the execution of its unmap plan, the acknowledgement of its
  invalidation and the zeroing of its frame; its frame and its quota return
  only then
  ([reclamation barriers](../README.md#reclamation-barriers)). The
  completion of the region follows the last page in one step of a fixed
  number of writes.
- **References.** In release 0.1 the only references to the frame of a page
  that may outlive its unmap are translations in a TLB: no DMA region is
  mapped at EL0, and buffers shared with the kernel, futexes and user-copy
  points belong to later releases
  ([address spaces and VM objects](../../../architecture.md#address-spaces-and-vm-objects)).
  The `Invalidate` of the unmap plan is the broadcast `TLBI VAAE1IS`, which
  `DSB ISH` completes, and
  [S3](../../../conventions/smp.md#s3-reclamation-after-acknowledgement)
  makes the completion of that invalidation on the executing CPU the
  acknowledgement of every CPU that may hold the translation; so the
  execution of the unmap plan is the acknowledgement of its invalidation.
  The other references that several CPUs may hold belong to the multicore
  components (planned).
- **Who meets a pending region.** A process has one thread, which executes
  a release that stopped at a preemption point again before it runs any
  other code, so no thread at EL0 meets a pending region in release 0.1.
  `Pending` is reached by host tests, which call the entries directly, and
  a host test that holds a plan without its `acknowledge` shows a release
  whose completion is deferred.

## Revocation at process destruction

The destruction of a process is the second trigger of the same two phases,
for all its regions and its loaded frames at once.

- **Pending.** Once the process has left Alive, its thread is removed and
  no operation of this page runs on its address space again
  ([destruction](../../objects-capabilities/lifecycle/contract.md#destruction));
  its regions stay as they are until the revocation.
- **Premises.** The lifecycle component calls `revoke_step(process)` only
  once the address space of the process is loaded on no CPU, its ASID has
  been invalidated by the execution of its release plan, whose
  `TLBI ASIDE1` removes every non-global translation of the ASID, and the
  plan of `Tables::reset` of its lower tables has been executed
  ([release of an ASID](../address-space/contract.md#address-spaces-and-asids)).
  So no TLB entry and no table entry names a frame of the process, and the
  ASID invalidation is the acknowledgement of every page at once.
- **Steps.** Each call takes one step: for at most `RELEASE_BATCH` frames
  from the head of the committed chain of the process, committed and loaded
  alike, the frame plan that zeroes the frame and, at its `acknowledge`,
  the return of the frame to the pool with the credit of one page to the
  item of its kind, committed VM pages or private pages of loaded images.
  It gives no write plan and reads no table. A step ends:
  - with completion, when the chain is empty: the call writes `Regions::new()`
    into the VM head of the process, which frees every row, pending ones
    included, and gives its result;
  - otherwise with `Again`, at a preemption point of the destruction, whose
    progress is the chain itself.
- After the completion the process holds no frame, and its usages of
  committed VM pages and of private pages of loaded images are 0, which the
  [reaping](../../objects-capabilities/lifecycle/contract.md#reaping) of
  the process requires.
- A frame returns to the pool only after the reset that removed the entry
  that mapped it, so a frame has at most one mapping, and every page one
  holder, during the destruction as well.
- The order of these steps among the other steps of the destruction, after
  the invalidation and the reset and before the release of the ASID and of
  the segment of the table pool, is the
  [lifecycle](../../objects-capabilities/lifecycle/contract.md#destruction)
  component's.

## Acknowledgement and reclamation

**The round trip of plans.**

- An entry of this page fixes in its checks every plan that it and its
  steps give: which pages, which frames, which kinds and in which order
  follow from the state and the arguments by the rules of this page. Every
  plan comes after the write-back of the write set of the entry, and no
  plan fails ([write plans](../page-tables/contract.md#write-plans-and-publication)),
  so an operation has no error after its first plan.
- The core sets no callback and never writes a frame. An entry gives a
  step; the
  [dispatch of the core](../../runtime-sdk/dispatch/contract.md#the-round-trip-of-plans)
  hands a plan to `el0_dispatch`
  as one of the results of a transition: the return to EL0, a write plan,
  the release plan of an ASID, a frame plan or the halt of the system.
  `el0_dispatch` executes a write plan with `krepi_arch::mmu::apply` and a
  frame plan with `krepi_arch::frames::apply`, and then enters the dispatch
  of the core again, which calls `acknowledge` of the process
  whose VM head holds the cursor.
- One plan is executed before the next is given, and no other entry runs
  on the lower tables or the VM head of the process in between
  ([write plans](../page-tables/contract.md#write-plans-and-publication)):
  an operation of the process and `revoke_step` refuse with `InvalidState`
  while a plan is in flight in its VM head, a call that no composer makes.
  The entries of other processes may take and return frames in between,
  since no plan in flight needs a free frame: the frames of a commit leave
  the free stack before its first plan, and a frame that a zero plan names
  stays on the committed chain until the `acknowledge` of that plan.
- The cursor is empty between transitions: a commit, a decommit and an
  `mprotect` run to their result in one transition, and a step of a release
  or of a revocation ends with its cursor empty and its progress in the row
  or in the chain. So no cursor of a multi-page operation crosses a
  transition.

**Frame plans.** `vm::FramePlan` is one of two forms, and neither fails:

- `Zero(frame)`: write 0 into the 4096 bytes of a frame through the direct
  map, which `krepi_arch::frames::apply` executes with
  `krepi_arch::mmu::zero_frames`;
- `Copy(source, frame, bytes)`: copy `bytes` bytes, at most 4096, from the
  offset `source` of the boot bundle, read through the kernel's read-only
  mapping of the image, to the start of a frame, through the direct map.
  The
  [creation](../../objects-capabilities/creation/contract.md#child-processes)
  component gives it for the file bytes of the RW segments of an image that
  it loads, and continues its own operation after the plan; `acknowledge`
  continues only the plans of the entries of this page.

**Acknowledgement.** `acknowledge(process)` records that the plan in
flight of the cursor of the VM head of `process` has been executed and
gives the next step:

- after the write plan of a page of a commit: the write plan of the next
  page, with the frame that the commit took for it, which the chain links
  just before the frame of the page, or the result;
- after the first write plan of a page of an `mprotect`, its second; after
  the second: the first plan of the next page whose kind differs from the
  one requested, or the result;
- after the unmap plan of a decommit or of a release: the zero plan of the
  frame that `unmap_page` gave;
- after a zero plan: the frame leaves the committed chain and goes on top
  of the free stack, and one page of the item of its kind is credited to
  the process, in one write set of at most 5 items, the process slot and
  the VM head and, for a decommit or a release, the row, whose count falls
  by one, and, at the completion of a release, the neighbours of the row in
  address order; then the plan of the next page, the end of the step, or
  the result;
- with no plan in flight: `InvalidState`, a call that no composer makes,
  which changes nothing.

**Reclamation.** A frame returns to the pool, and its page to the quota of
its holder, only after the unmap of its page with the acknowledgement of
its invalidation, or the invalidation of the ASID and the reset of the
tables of a destroyed process, and after its zeroing; the frame and its
quota return together, in one write set. So a free frame is zero, no frame
is reused while a translation of it may remain in a TLB, and a quota is
never credited for a frame that is not back. A plan that has been given and
is not acknowledged keeps its frame off the pool and its page in the quota
of its holder.

## Tables and extents

- **Tables.** The tables of the VM window of a process come from the 32
  tables of its own segment of the table pool
  ([table pools](../address-space/contract.md#table-pools)). The VM window
  needs one level 2 table, and one level 3 table for each of its 2 MiB
  slots in which a page has been committed since the process was created:
  a table returns to the pool only through `reset` at the destruction of
  the process ([table pool](../page-tables/contract.md#table-pool)), and a
  level 3 table that a decommit or a release empties stays.
- **The count.** A commit counts the tables that it needs from the VM head
  without walking the tables: a level 3 table for each 2 MiB slot of its
  range that the set of slots of the VM head does not hold, and the level 2
  table of the VM window when that set is empty. When `Tables::used` plus
  that count exceeds 32, the commit is refused with `OutOfTables` before
  any write. The page-table pages are an item of the caller alone, so the
  error is of the caller's quota and depends only on its own state.
- **The bound.** With $t$ tables of its segment free before its first
  commit, a process commits pages in at most $t - 1$ slots of 2 MiB of its
  VM window, $2\,(t - 1)$ MiB, and no entry of this page uses a block. The
  [check of the loading part](../../runtime-sdk/dispatch/contract.md#loading-configuration)
  at boot leaves a child at least the
  level 2 table and one level 3 table of the VM window. The root takes the
  tables of its boot ranges first, and with the largest boot bundle that
  the address-space component admits none is left for its VM window, so
  every commit of the root is then `OutOfTables`
  ([table pools](../address-space/contract.md#table-pools)).
- **Extents.** The page pool and the frame metadata are the only pages that
  this component takes from the page ownership table, at boot; no entry
  takes or returns pages of the table afterwards, so the count of its
  extents does not grow at run time. On the 8 GB Pi 5 the holders take at
  most these extents of the 160 of the table
  ([capacity](../page-tables/contract.md#page-ownership)), counting at
  most two for each allocation:

| Holder | Allocations | Extents |
| --- | ---: | ---: |
| The free extents at boot | - | 4 |
| The storage of the objects component | 8 | At most 16 |
| The table pool of the address spaces | 1 | At most 2 |
| The root's private allocation | 1 | At most 2 |
| The page pool | 1 | At most 2 |
| The frame metadata | 1 | At most 2 |
| At run time | 0 | 0 |
| In all | 12 | At most 28 |

- An allocation adds at most two extents, the held range and the rest of
  the free extent that it splits, as the rows above count. At a low
  placement and an alignment of one page, as all these are carved, an
  allocation starts at the start of a free extent and adds at most one, so
  the twelve allocations add at most 12, and the count, with the 4 free
  extents at boot, stays at most 16, within the 28 of the rows above.

## Quotas

- **Committed VM pages.** A commit checks the item of its caller with
  `QuotaRecord::check` and charges `pages` in its write set; each frame
  that returns from a decommit, a release or a revocation is credited, one
  page, in the write set that returns it. Every charge and credit of this
  component, of committed VM pages and of private pages of loaded images, is
  of the ordinary class. The root's limit of the item is
  `root_vm_pages`, which the boot of the root passes to `root_limits`; a
  child's limit is the share that its creator splits to it from its own
  limit (planned)
  ([splitting limits](../../objects-capabilities/objects/contract.md#metadata-quotas)).
- **The cap.** A commit is refused with `CommitLimit` when the usage of
  committed VM pages of the caller plus `pages` exceeds `vm_page_cap`, after
  the check of the item. So the pages that a process may commit are the
  smaller of what its limit and what the cap leave. The cap is a check of
  this page beside the item; it changes neither the item nor its checks,
  charges and splits.
- **Pages are not split from the pool.** The limits of pages are not carved
  out of the frames: the limits and caps of all processes together may
  exceed the pool, and when the frames run out a commit fails for shared
  capacity, `OutOfPages`.
- **Private pages of loaded images.** The
  [creation](../../objects-capabilities/creation/contract.md#quotas-and-admission)
  component charges the private pages of an image that it loads to the item
  of the child, before its first write, and takes their frames with
  `Pool::take`; each returns, with the credit of one page of the item, in
  the revocation at the destruction of the child.
- **Rows.** The region table of a process has its fixed `vm_regions` rows,
  counted by no item; a `reserve` without a free row is refused with
  `RegionTableFull`, which depends only on the caller.
- **Counting.** For the
  [conservation](../../objects-capabilities/objects/contract.md#metadata-quotas)
  of the objects component, this component counts as the committed VM
  pages of a process the committed frames of its chain, together with the
  pages that a commit of the process has charged at its write-back and not
  yet taken; and as its private pages of loaded images the loaded frames of
  its chain, together with the pages that the creation of the process in
  progress has charged and not yet taken, and, for the root, the pages of
  the memory of its RW segments and of its stack in its private allocation
  at boot, which the
  [boot of the root](../../objects-capabilities/creation/contract.md#the-boot-of-the-root)
  charges to the item and which are not frames of the pool. Every charge
  and credit of these items is in the write set that changes these
  counts, so both statements of conservation hold after every write-back.

## Errors

| Error | Rule broken | Entries | Place in the order of errors |
| --- | --- | --- | --- |
| `InvalidConfiguration` | A record shorter than the end of its VM part; `root_vm_pages`, `vm_page_cap` or `pool_pages` of 0, or `pool_pages` above `MAX_POOL_PAGES`; a `vm_reserved` other than 0 | `check_config` | At boot, after the checks of the objects and address-space components |
| `Alignment` | An address that is not a multiple of 4096 | `reserve`, `commit`, `decommit`, `mprotect`, `release` | The form of the register arguments |
| `Length` | A count of pages of 0; for `commit`, `decommit` and `mprotect`, above `MAX_CALL_PAGES` | `reserve`, `commit`, `decommit`, `mprotect` | The form of the register arguments, after `Alignment` |
| `Window` | A range that wraps or does not lie in the VM window; for `reserve` with the address 0, more pages than the window holds; for `release`, an address outside the window | `reserve`, `commit`, `decommit`, `mprotect`, `release` | The form of the register arguments, after `Length` |
| `Protection` | A protection with a bit above bit 2, or without bit 0 | `mprotect` | The form of the register arguments, after `Window` |
| `NoRegion` | An address in no region of the caller; for `release`, one at which no region starts | `commit`, `decommit`, `mprotect`, `release` | Handle resolution: the region that the address names |
| `RegionBounds` | A range that goes beyond the end of the region of its first page | `commit`, `decommit`, `mprotect` | Handle resolution, after `NoRegion` |
| `ExecuteDenied` | A protection with the execute bit | `mprotect` | Rights |
| `Overlap` | A range that meets a region of the caller, pending ones included | `reserve` | Object state, after `InvalidState` |
| `WindowFull` | With the address 0, no range of the pages in the window outside the regions of the caller | `reserve` | Object state, after `InvalidState` |
| `Pending` | A region whose release is pending | `commit`, `decommit`, `mprotect` | Object state, first |
| `AlreadyCommitted` | A committed page in the range | `commit` | Object state, after `InvalidState` |
| `NotCommitted` | A page of the range that is not committed | `decommit`, `mprotect` | Object state, after `InvalidState` |
| `QuotaExceeded` of the objects component | The committed VM pages of the caller beyond its limit | `commit` | The caller's quota, first |
| `CommitLimit` | The committed VM pages of the caller beyond `vm_page_cap` | `commit` | The caller's quota, after `QuotaExceeded` |
| `OutOfTables` of the page-tables component | More tables than the segment of the caller has free | `commit` | The caller's quota, after `CommitLimit` |
| `RegionTableFull` | No free row in the region table of the caller | `reserve` | The caller's quota |
| `OutOfPages` | Fewer free frames than the pages; for `Pool::take`, an empty pool | `commit`, `Pool::take` | Shared capacity |
| `InvalidState` | A call that no composer makes: an operation or `revoke_step` while a plan is in flight in the VM head of the process; `acknowledge` with no plan in flight | `reserve`, `commit`, `decommit`, `mprotect`, `release`, `acknowledge`, `revoke_step` | Object state: after `Pending` for `commit`, `decommit` and `mprotect`; first for the other entries |

- **Order.** Each entry checks in the order of its rule section and
  returns the first error. The places of the last column are those of the
  order of errors of the
  [security model](../../../security.md#internal-choices): the operation
  number and version, which the dispatch of the ABI checks; the form of the
  register arguments; handle resolution; rights; the range of user buffers,
  which no operation of this page has; object state; the caller's quota;
  shared capacity. An operation of this page takes no handle: the region
  that its address names takes the place of handle resolution, and only the
  execute bit of `mprotect` has a place among the rights.
- **No change on failure.** No error changes state: an entry that returns
  an error leaves every field of the kernel state as it was, the copies in
  its write set included, gives no plan and writes no counter; a composing
  operation that meets an error discards its buffer, so the kernel state
  after any failed operation equals the state before it. There is no
  exception. The settlements before the operation in its transition are
  transactions of their own and stay. The result registers of a failed
  system call follow the
  [observable outputs](../../../security.md#observable-outputs) of the
  security model, and `OutOfPages`, an error of shared capacity, is outside
  the output sources there.
- **States are not errors.** A pending region and a plan that has not been
  acknowledged are states: the operations that meet a pending region are
  refused with `Pending`, and nothing reports a failed release, which does
  not exist.
- **Totality.** `AlreadyMapped` and `NotMapped` of the page-tables
  component do not reach the operations: the checks of this page find
  every page free or mapped as its plan needs before the first write.
  `InvalidState` and `OutOfPages` of `Pool::take` answer calls that no
  composer makes.
- **Names.** The names are those of this contract; the numeric values of
  the errors that reach EL0 belong to the ABI inventory. `ExecuteDenied` is
  the refusal at the place of rights: no capability is resolved, so it is
  not `PermissionDenied` of the
  [capabilities](../../objects-capabilities/capabilities/contract.md#errors)
  component, which names a right that an entry of a table lacks.

The prototype's VM registry had fourteen errors. Here:

| Prototype error | Here |
| --- | --- |
| `Configuration` | Rewritten: `InvalidConfiguration`, the checks of the VM part of the capacity record at boot, which stop the boot |
| `Argument` | Split by the rule broken: `Alignment`, `Length`, `Window` and `Protection`, in the form of the register arguments |
| `Authority` | Not applicable: no capability names a region or an address space, and the operations act only on the caller's own address space |
| `Stale` | Rewritten: `NoRegion`, an address that names no region; a region has no identifier to go stale |
| `Overlap` | Kept for `reserve`; the case of a committed page in a commit is `AlreadyCommitted` |
| `Quota` | Moved to the objects component: `QuotaExceeded` of the committed VM pages, with `CommitLimit` of the cap beside it; the prototype's aggregate limit of its registry is the page pool, `OutOfPages` |
| `Capacity` | Rewritten: `RegionTableFull`, a region table of the caller without a free row |
| `GenerationExhausted` | Not applicable: a region has no generation in release 0.1 |
| `Busy` | Rewritten: `Pending`, an operation in a region whose release is pending |
| `Backend` | Not applicable: no plan fails, and the checks precede every write |
| `Retirement` | Rewritten as a state, not an error: a release whose plans are not yet acknowledged is pending, and new operations in it get `Pending` |
| `ReferencesOutstanding` | Moved to the lifecycle component: the gates of reclamation, which do not count references |
| `Execution(_)` | Not kept as a wrapper: the errors of the objects, address-space and page-tables components that this page meets are returned as they are, and the busy execution manager does not exist |
| `Object(_)` | Not kept as a wrapper, as `Execution(_)` |

## Check and execute

Every write entry of the core on this page makes all its checks before its
first write, then changes only the copies in the write set of its caller
([write-set transactions](../../objects-capabilities/objects/contract.md#write-set-transactions)),
and its plans and the writes outside write sets follow the write-back. The
items of this page are the VM head and the rows of each region table, keyed
by the region table of the process slot and by the head or the row
number, and the process slots, for their quota records. The page pool, the
frame metadata, the lower tables and the bytes of the frames are no items
of a write set: their writes are fixed by the checks and executed after the
write-back in a fixed order, and none of them fails. So the write phase of
an operation can meet only `WriteSetFull` of `stage`, which a write set of
at most 5 items never meets, and the fault-injection points of test builds,
which discard the buffer and leave the state from before the operation;
then no plan has been given and no write outside the write set made.
`acknowledge` and `revoke_step` have no fault-injection point, since they
follow plans that have been executed: the plans of an operation, and for
`revoke_step` the invalidation and the reset of the destruction.

| Entry | Checks before the first write | Write set of this page | Writes after the write-back |
| --- | --- | --- | --- |
| `check_config` | The three checks of the VM part | Nothing: a value | Nothing |
| `Pool::new` | None; the boot wiring passes the carved range and its metadata | Not in a write set: at boot, before any token exists | Every entry of the metadata once |
| `Pool::free` | None | Nothing: a read entry | Nothing |
| `Pool::take` | A free frame | Nothing | The metadata of the frame, the top of the free stack and the head of the chain of the process |
| `Pool::next` | None; it reads the metadata of the frame | Nothing: a read entry | Nothing |
| `Regions::new` | None | Nothing: a value | Nothing |
| `reserve` | The form, a plan in flight, the overlap or the free range in the window, a free row | At most 4: the new row, its neighbours in address order and the VM head | Nothing |
| `commit` | The form, the region, its phase, a plan in flight and its pages, the item, the cap, the tables and the free frames | 3: the process slot, the row and the VM head | For each page, the take of its frame, with the metadata of the frame, the free stack and the head of the chain; then the write plan of the first page |
| `decommit` | The form, the region, its phase, a plan in flight and its pages | 1: the VM head | The write plan of the first page |
| `mprotect` | The form and the protection, the region, the execute bit, its phase, a plan in flight and its pages | 1: the VM head | The first write plan of the first page whose kind changes, if there is one |
| `release` | The form, the region, a plan in flight, and the pages of the step | 2: the row and the VM head; at a completion without a committed page in the step, at most 4: the row, its neighbours and the VM head | The write plan of the first committed page of the step, if there is one |
| `acknowledge` | A plan in flight | At most 5: the VM head, and with a returned frame the process slot, and for a decommit or a release the row and at the completion of a release its neighbours | With a returned frame, its metadata, the free stack and the chain; then the next plan |
| `revoke_step` | No plan in flight; the chain | 1: the VM head, with the cursor, or with `Regions::new()` at the completion | The zero plan of the first frame of the step, if there is one |

- `check_config`, `Pool::free`, `Pool::next` and `Regions::new` write
  nothing; the other entries cannot fail after their checks.
- The composed write sets stay within $W$ = 64 items: an operation of this
  page is composed by the
  [dispatch of the core](../../runtime-sdk/dispatch/contract.md#operations)
  with the settlements of its
  transition, which are transactions of their own, and a revocation step by
  the lifecycle component, whose
  [contract](../../objects-capabilities/lifecycle/contract.md#destruction)
  counts its write set.
- A refused operation gives no plan and changes no table, no frame and no
  metadata.

## Work bounds

- `check_config` reads the four fields once and makes a fixed number of
  checks. `Pool::new` writes each entry of the metadata once, at most
  `MAX_POOL_PAGES` frames and the heads of at most the process capacity,
  at boot. `Pool::free`, `Pool::take`, `Pool::next` and `Regions::new` take
  a fixed number of steps; `Regions::new` gives two bit sets, of
  `MAX_REGIONS` bits and of 512 bits.
- `reserve` walks the rows in use once in address order, at most
  `vm_regions`, at most `MAX_REGIONS`, and the set of rows in use once for
  the lowest free row.
- `commit` walks the rows to find its region, at most `vm_regions`; reads
  at most `MAX_CALL_PAGES` leaves with `lookup_page`, each at most three
  entries; counts at most two 2 MiB slots, since a range of at most 2 MiB
  meets at most two; takes at most `MAX_CALL_PAGES` frames, each in a fixed
  number of steps; and gives at most `MAX_CALL_PAGES` write plans of at
  most seven steps each
  ([work bounds](../page-tables/contract.md#work-bounds)).
- `decommit` reads at most `MAX_CALL_PAGES` leaves and gives at most
  `MAX_CALL_PAGES` write plans of two steps and as many zero plans of 4096
  bytes; `mprotect` reads at most `MAX_CALL_PAGES` leaves and gives at most
  twice as many write plans.
- `release` walks the rows to find its region and, in one step, reads at
  most `RELEASE_BATCH` leaves and gives at most `RELEASE_BATCH` write plans
  and zero plans. A release of a region of $n$ pages takes at most
  $\lceil n / \mathtt{RELEASE\_BATCH} \rceil$ steps, the last of which
  completes it.
- `revoke_step` gives at most `RELEASE_BATCH` zero plans in one step; the
  revocation of a process with $m$ frames takes at most
  $\lceil m / \mathtt{RELEASE\_BATCH} \rceil + 1$ steps.
- `acknowledge` reads at most `MAX_CALL_PAGES` leaves, for an `mprotect`,
  which passes over the pages that have the requested kind, or
  `RELEASE_BATCH`, for a release, which passes over the pages of its step
  that are not committed, each at most three entries; it writes a fixed
  number of fields, since a frame leaves the committed chain, which is
  linked in both directions, in a fixed number of steps; and it gives at
  most one plan. `krepi_arch::frames::apply` writes or copies at most 4096
  bytes.
- **Long operations.** The release of a region and the revocation at the
  destruction of a process are the long operations of this page. A step
  ends at a preemption point; the progress of a release is in its row, and
  that of a revocation is the committed chain of the process, whose
  destruction stores its own progress in the process slot
  ([destruction](../../objects-capabilities/lifecycle/contract.md#destruction)).
  The other entries run to their end, and no progress of theirs is stored
  between two transitions.
- **Without a preemption point.** A commit, a decommit and an `mprotect`
  run in one transition, with at most `MAX_CALL_PAGES` plans and, for a
  decommit, the zeroing of at most 2 MiB, the longest work of this page
  without a preemption point; a step of a release or of a revocation zeroes
  at most 256 KiB. Their write sets do not grow with the pages, so $W$ does
  not bound `MAX_CALL_PAGES`; the time between two preemption points does.
- The constants are `MAX_CALL_PAGES` = 512, 2 MiB; `RELEASE_BATCH` = 64;
  `MAX_REGIONS` = 256; `MAX_POOL_PAGES` = 4,194,304; and $W$ = 64 of the
  objects contract.

## Determinism

- **Requests.** Requests that contend for a region table, a row or the page
  pool take effect in the order in which they enter the kernel.
- **Placement.** A region with the address 0 takes the lowest address of
  the window at which its pages fit; any other start is the caller's. A new
  region takes the lowest free row, and the row number is an internal
  identifier that no output carries.
- **Frames.** A frame is taken from the top of the free stack, which at
  boot holds the frames in address order with the lowest on top, and a
  returned frame goes on top; a taken frame is linked at the head of the
  committed chain of its process, and a revocation returns the frames from
  the head. The physical address of a frame is not an output
  ([observable outputs](../../../security.md#observable-outputs)), so the
  outputs of a process do not depend on which frames it holds.
- **Order of pages and plans.** The operations take the pages of their
  range, and a release step its pages, in address order; the plans of a
  page follow the order of its rule section; an `mprotect` gives no plan
  for a page that has its kind.
- **Preemption.** Where a release or a revocation stops at a preemption
  point depends on when an interrupt is pending, which the arrival of the
  timer interrupt, [ND-01](../../../security.md#nd-01), and of device
  interrupts, [ND-02](../../../security.md#nd-02), of the register of
  [permitted nondeterminism](../../../security.md#permitted-nondeterminism)
  decide; for each, the rules of this page fix the result, and the result
  of the operation does not depend on it.
- **Several CPUs.** With more than one CPU, the order in which CPUs take
  the tokens of the same process or of the page pool is the multicore
  interleaving of [ND-03](../../../security.md#nd-03); for each such order,
  the rules of this page fix the result.
- **Boot.** The `Config`, the allocations and the initial order of the
  free stack follow from the bytes of the record and the range that the
  carving gives, so cold boots of one image give the same pool.

The component leaves no other choice open.

## State fields

| Field | Class | Lock or owner | Linearization point | Publication |
| --- | --- | --- | --- | --- |
| The VM head of each process: its set of rows in use, its first row, its set of 2 MiB slots with a level 3 table and its cursor | Per-process | The token of the process; with one CPU, the executing CPU | The write-back of the write set that changes it | Under the token of the process |
| The rows of the region table of each process | Per-process | The token of the process | The write-back of the write set that changes it | Under the token of the process |
| The page pool: its base and its frames, its free stack with its count, and the metadata of its free frames | Shared | The token of the page pool, a field of the kernel root; with one CPU, the executing CPU | The end of the write of a frame that `Pool::take` or a commit takes, or that `acknowledge` returns | Under the token, by the release of the lock that provides it once CPUs share it |
| The metadata of each frame that a process holds, and the head of its committed chain | Per-process | The token of its process, to which a frame passes when it is taken and from which it passes back to the pool token when it returns; `Pool::next` reads it under that token, which the creation of the process holds | As the page pool | At the handover: under the token of the page pool |
| The VM part of the capacity record, the `Config` | Shared, read-only after boot | The boot CPU, which checks it before the first entry from EL0 | The return of `check_config` | Once, before the secondary CPUs start; it never changes afterwards |

The bytes of a frame are the memory of its holder, not a field of the
kernel, and a frame plan writes them only while no EL0 mapping names the
frame or before the creation component maps it. The storage of the region
tables is carved by the
[objects](../../objects-capabilities/objects/contract.md#storage-carved-at-boot)
component, whose state fields hold the slots and quota records; the page
ownership table that holds the pool and its metadata, and the lower tables
of a process, are fields of the
[page-tables](../page-tables/contract.md#state-fields) and
[address-space](../address-space/contract.md#state-fields) components.

## Testing obligations

- The host tests of the module `vm` (planned) replay every vector of
  [Legacy test vectors](#legacy-test-vectors) whose entry is on this page,
  with its expected output, and write their results for the comparison with
  the specification
  ([host results](../../../formal-verification.md#host-results)); the
  cases whose entries belong to the lifecycle component are replayed by the
  tests of that component with the entries of this page.
- Configuration: each check of [Configuration and the page pool](#configuration-and-the-page-pool)
  at its limit and one beyond: a record of 64 and of 63 bytes; each of the
  three fields at 1 and at 0; `pool_pages` at `MAX_POOL_PAGES` and one
  above; `vm_reserved` at 0 and 1; and the default record of each board,
  which passes and has `root_vm_pages` and `vm_page_cap` of at least 256.
- The pool: the carving of the pool and its metadata on the page ownership
  table of the 8 GB Pi 5 after the other allocations at boot adds at most
  one extent each, with the metadata pages of the formula; a pool that
  finds no range stops the boot with the error of the page ownership
  table; `Pool::new` gives the frames in address order from the top; after
  several takes for one process, `Pool::next` from the head of its chain
  gives its frames in the reverse of the order of their takes and then
  none, and none for a free frame.
- Operations: a property test with fixed seeds drives `reserve`, `commit`,
  `decommit`, `mprotect`, `release` and `revoke_step` with `acknowledge` of
  every plan on several processes and checks after every step, against an
  independent model of regions, pages, kinds, frames and usages: that the
  regions of a process are disjoint and in its window; that a page is
  committed exactly when it is mapped, with its kind; that every frame has
  one holder and at most one mapping; that a free frame is zero and a
  committed page reads zero when committed; that the usages of committed VM
  pages and of private pages of loaded images equal the counts of
  [Quotas](#quotas); and that the plans come in the order of the rule
  sections, written from this page.
- Each error of [Errors](#errors) through a call that gives it, compared
  field by field before and after, with no plan; for each pair of
  consecutive checks of an operation whose errors differ, a call that
  breaks both and gets the error of the earlier; a commit at
  `MAX_CALL_PAGES` and one beyond; a commit that needs exactly the free
  tables and one that needs one more; a commit at the limit of the item, at
  the cap and one beyond each; a commit of exactly the free frames and one
  more.
- Release: a release of a region larger than `RELEASE_BATCH` pages that
  stops at each preemption point, during which `commit`, `decommit` and
  `mprotect` in it are `Pending` and `reserve` over it `Overlap`, and that
  is executed again to its completion; a host test that holds an unmap plan
  and then a zero plan without `acknowledge`, during which the frame is off
  the pool and its page in the usage of the process, an operation of the
  process on a range outside the region and `revoke_step` of the process
  are `InvalidState`, and a commit of another process takes its frames
  from the pool.
- Revocation: a process with committed and loaded frames and a pending
  release, revoked after the invalidation and the reset in steps of
  `RELEASE_BATCH`, after which it holds no frame, its usages are 0 and its
  VM head is empty, while the frames of another process keep their bytes.
- W^X: no sequence of operations maps a frame of the pool with an
  executable kind, and an `mprotect` with the execute bit is
  `ExecuteDenied`.
- QEMU tests on QEMU virt, from EL0, once the operations exist: a commit
  whose pages read zero and take a write; an `mprotect` to read-only whose
  write takes a permission fault, `DataPermission`; an execution from a
  committed page, which takes `InstructionPermission`; an access after a
  decommit and after a release, which takes `DataTranslation`; and a
  release of a large region that a timer interrupt preempts. The 8 GB Pi 5
  runs the same with the caches on.
- No test bounds the time that a step takes, and the tests take their
  expected values from this page, from the vectors and from independent
  models, never from an earlier run of the code under test
  ([testing](../../../conventions/testing.md#independent-evidence)).

## Open obligations

The module `vm` has no `unsafe` code, no assembly and no MMIO, and its
entries are to be covered by its targets. The composition of its entries
into a transition by the dispatch of the core, with the round trip of
plans, into the creation of a process by the creation component, and into
the destruction of a process by the lifecycle component are effects across
components, open obligations of the
[dispatch](../../runtime-sdk/dispatch/contract.md#open-obligations),
[creation](../../objects-capabilities/creation/contract.md#open-obligations)
and [lifecycle](../../objects-capabilities/lifecycle/contract.md#open-obligations)
contracts, carried by the proof of object lifetimes, waits and sequential
composition, by release 0.2. The write plans that the entries
give are executed by `krepi_arch::mmu::apply` and the zeroing of a frame
by `krepi_arch::mmu::zero_frames`, rows of the
[page-tables obligations](../page-tables/contract.md#open-obligations); the
entries use the write-set buffer that the adapter of the objects component
lends, a row of the
[objects obligations](../../objects-capabilities/objects/contract.md#open-obligations).
The rows below are the adapter that executes the frame plans of this page
and the board's forming of the slice of the frame metadata; each board
forms that slice in its board crate, and the row of the Pi 5 board is added
with its board crate.

| Obligation | Kind | Verified state | Carrier | Stage |
| --- | --- | --- | --- | --- |
| `kernel/arch/src/frames.rs` (planned) | `code` | Neither | The proof of contexts, user copies and the private VM | `0.2` |
| `kernel/arch/src/frames.rs#apply` (planned) | `unsafe` | Neither (executes one frame plan: zeroes one frame of the page pool through `krepi_arch::mmu::zero_frames`, or copies at most 4096 bytes of the boot bundle, read through the kernel's read-only mapping of the image, to the start of one frame of the page pool through the direct map; it changes the bytes of frames, which no proof describes, and no table, metadata or quota) | The proof of contexts, user copies and the private VM | `0.2` |
| `kernel/boards/qemu-virt/src/main.rs#image::frame_metadata` (planned) | `unsafe` | Neither (forms, through the direct map, the slice of the frame metadata on the pages that the page ownership table holds for `OWNER_PAGE_FRAMES`, after their zeroing, of the size that `Config` gives; it reads and writes none of its contents) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` |

## Legacy test vectors

The vectors are host tests of the prototype tree at
`prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`, 15 in all. Their
expected outputs are those that the test bodies assert, written in the
rules of this page. The vectors are not yet in a file of the repository,
so the section holds no `vectors` block.

| File | Vectors |
| --- | ---: |
| `src/vm/tests.rs` | 4 |
| `src/vm/tests/authority.rs` | 5 |
| `src/vm/tests/failures.rs` | 6 |

- These are all the tests of the prototype's `src/vm`; its other files hold
  no test.
- The id of a vector is the path of its file below `src/`, without the
  directories and files named `tests` and without `.rs`, with a hyphen
  between the parts and in place of each underscore, and the position of
  the test among the tests of its file, from 1.

A vector of this page is one test function. The vector file is to hold one
line for each case of a vector through an entry of this page, with the id
`<vector>.<n>`, `n` counting those cases from 1 in the order of the test; a
case that its row marks not applicable has no line, and a vector whose
Entry column names no entry of this page has no line.

**The prototype's registry.** The fixture of the three files keeps an
object pool of 8 processes and 8 threads, an execution manager of 4
domains over a page allocator of 128 pages from `0x1000`, each domain
taking 4 pages for its layout, and a registry of 4 grants and 10 regions
with an aggregate of 20 pages, of which 4 pages, 2 regions and 1 grant are
reserved for the control class. A test admits a grant for a domain, a
window of 32 pages at `0x34000000` with a page quota, and seeds a Memory
capability to it. Its `map(offset, pages)` maps a new region at the offset
of the window and gives a region identifier, and `unmap(id)` removes the
region; its backend records the events `zero`, `map`, `unmap`,
`invalidate` and `scrub`, and can be made to fail.

**Correspondence.** A `map` of the prototype is a `reserve` of the range at
the same offset from `VM_START` with the `commit` of all its pages, and an
`unmap` is a `release` of the region; a case at or beyond the end of the
prototype's window of 32 pages takes the end of the VM window, `VM_END`, in
place of that end. The quota of a grant is the limit of committed VM pages
of the process, and the aggregate of the registry is the page pool. A
backend event of `zero` has no counterpart, since the frames of the pool
are zero; `map` is the write plan of `map_page`, `unmap` and `invalidate`
the write plan of `unmap_page`, whose `Store` and `Invalidate` they are,
and `scrub` the zero plan of the frame. The prototype recorded one event of
each kind for a region, where each page here has its own plans, so the
numbers of events and of plans differ.

**Notation.** Addresses and byte values are written as `0x` and lowercase
hexadecimal digits, counts in decimal. The output of a call is `ok`,
followed by its result, or `err=<error>`, with the errors of this page.

**Behaviour changes.** The rules of
[Current deviations](#current-deviations) change these vectors: the cases
of capabilities, grants, region identifiers and generations, control
reserves, failing backends and a busy execution manager have no line; the
cases of limits take the limits of this page; the case of the start 0,
which the prototype refused, is a placement by the kernel and succeeds; and
the events of a region become the plans of each of its pages.

### `src/vm/tests.rs`

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `vm-1` | 215 | `isolated_zeroed_regions_reuse_only_after_scrub_and_invalidation` | Two owners with a quota of 8 each map 2 pages at the start of their windows: their physical ranges do not overlap, and the first's pages read 0; with the first's pages filled with `0xa5` and the second's with `0xb6`, the unmap of the first gives the events `unmap`, `invalidate` and `scrub`, in this order, and its pages read 0; a new map of 2 pages gives another region identifier and the same physical range, which is then filled with `0xf9`; the old identifier is `err=Stale`; a release of the old allocation receipt is `err=InvalidAllocation` and scrubs nothing, so the range keeps `0xf9`; the second's pages keep `0xb6`; after both are closed, the registry is empty, the charged pages and the free bytes are those of the start, and the authorities and the capability references are 0 | `reserve` and `commit` of 2 pages at `VM_START` in each of two processes: `ok`, with four distinct frames, which read 0; with the first process's pages filled with `0xa5` and the second's with `0xb6`, `release` of the first region: for each page in address order, the write plan of `unmap_page` and then the zero plan of its frame, the frame returning at the `acknowledge` of the zero plan, and its two frames read 0; `reserve` and `commit` of 2 pages at `VM_START` again take the same two frames, which read 0; the second process's frames keep `0xb6`; after the revocation of both processes, the number of free frames and the usages are those of the start. The region identifier, its staleness and the receipt have no case: a region is named by its address alone, and a frame carries no receipt |
| `vm-2` | 266 | `bounds_overlap_and_per_owner_quota_fail_before_touching_backing` | With a quota of 3, maps at the byte offsets and with the pages (0, 0), (0, 17), (1, 1), (`0x20000`, 1) and (`0x1f000`, 2) of the window of 32 pages are each `err=Argument`, with no event; a map of 2 pages at offset 0 succeeds; a map of 1 page at offset `0x1000` is `err=Overlap`, and one of 2 pages at offset `0x2000` `err=Quota`; the state is unchanged and the backend has no event | With a limit of 3 committed VM pages and no region: `reserve` of 0 pages at `VM_START`, `err=Length`; `commit` of `MAX_CALL_PAGES` + 1 pages at `VM_START`, `err=Length`, which precedes the lookup of the region, the prototype's 17 pages beyond its 16; `reserve` of 1 page at `VM_START` + 1, `err=Alignment`; `reserve` of 1 page at `VM_END` and of 2 pages at `VM_END` - `0x1000`, each `err=Window`; none gives a plan or changes a field. `reserve` and `commit` of 2 pages at `VM_START`: `ok`; `reserve` of 1 page at `VM_START` + `0x1000`: `err=Overlap`; `reserve` of 2 pages at `VM_START` + `0x2000`: `ok`, and its `commit`: `err=QuotaExceeded`, with no plan and every field as after the `reserve` |
| `vm-3` | 285 | `ordinary_exhaustion_preserves_control_page_and_metadata_reserves` | Owners a and b with a quota of 16 and a control owner c with a quota of 4: a maps 16 pages; b's map of 1 page is `err=Quota`; c maps 4 pages, and 20 pages are mapped; after all three are closed, a maps 8 regions of 1 page, its ninth map is `err=Capacity`, and c maps 1 page | With a pool of 16 frames: `reserve` and `commit` of 16 pages in one process, `ok`; `reserve` of 1 page in another and its `commit`, `err=OutOfPages`. With `vm_regions` 8: eight `reserve` of 1 page in one process, `ok`, and a ninth, `err=RegionTableFull`. The control class of pages, rows and grants has no case: the pool and the region tables have no control reserve |
| `vm-4` | 309 | `physical_exhaustion_and_zero_failure_preserve_existing_regions` | With a page allocator of 6 pages, of which the domain takes 4: a map of 1 page whose zeroing fails is `err=Execution(Page(ZeroFailed))`, and the process still holds 1 mapping obligation; a map of 2 pages succeeds, and its pages are filled with `0x5a`; a map of 1 more page is `err=Execution(Page(OutOfMemory))`; the pages keep `0x5a`, and 2 pages are mapped | With a pool of 2 frames: `reserve` and `commit` of 2 pages, `ok`; `reserve` of 1 page and its `commit`, `err=OutOfPages`, with no plan; the committed pages keep `0x5a`, and the usage of committed VM pages is 2. The failed zeroing has no case: a commit zeroes nothing, since its frames come zero from the pool, and a zero plan does not fail |

### `src/vm/tests/authority.rs`

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `vm-authority-1` | 3 | `capabilities_are_typed_live_and_bound_to_the_captured_owner` | A map through another owner's capability, through a capability to another process's grant in the caller's space, through a capability with only the right to observe, through a capability of another type and through a closed capability is each `err=Authority`, with no event | No case: no capability names a region or an address space, and the operations act only on the caller's own address space, so there is no authority to name, attenuate or close |
| `vm-authority-2` | 45 | `closing_grant_drains_mappings_but_waits_for_outward_capability_references` | With 2 pages mapped and a capability to the grant in another process's space: after the owner's space is closed, the close of the grant is `err=ReferencesOutstanding`, its pages are 0 and its external references 2; a map through the other process's capability is `err=Authority`; after that capability is closed, the close of the grant and the destruction of the domain succeed | No case: there is no grant and no capability to one, and whether a process may be reclaimed is a gate of the [lifecycle](../../objects-capabilities/lifecycle/contract.md#reaping) component, which counts no references |
| `vm-authority-3` | 74 | `supplemental_mapping_reference_is_independent_of_authority_retention` | After a map of 1 page the process holds 2 mapping obligations; with a DMA resource retained and the grant closed, it holds 1; its destruction is `err=ReferencesOutstanding` until the DMA resource is released, and then succeeds | No case: no DMA region is mapped at EL0 in release 0.1, and the gate of reclamation is the [lifecycle](../../objects-capabilities/lifecycle/contract.md#reaping) component's |
| `vm-authority-4` | 111 | `revoking_a_derived_grant_denies_new_work_but_preserves_existing_mappings` | A capability derived with CONTROL maps 1 page, filled with `0x76`; the revocation of the original's descendants counts 1; afterwards a map and an unmap through the derived capability are `err=Authority`, an unmap by another owner is `err=Stale`, the page keeps `0x76`, and the unmap through the original succeeds | No case: no capability names a region, so there is no derived capability to revoke |
| `vm-authority-5` | 136 | `invalid_admission_bounds_and_request_overflow_create_no_ownership` | Admissions of a grant at the start, pages and quota (0, 1, 1), (`0x34000001`, 1, 1), (`0x34000000`, 0, 1), (`0x34000000`, 1, 0), (`0x34000000`, 1, 2), (`0x34000000`, `0xffffffffffffffff`, 1) and (`0x1000000000000`, 1, 1) are each `err=Argument`, and the external references of the thread are unchanged and the count of authorities is 0; then a map at `0xfffffffffffff000` is `err=Argument`, with no event | `reserve` of 1 page at `VM_START` + 1, `err=Alignment`; of 0 pages at `VM_START`, `err=Length`; of `0xffffffffffffffff` pages at `VM_START`, `err=Window`; of 1 page at `0x1000000000000` and at `0xfffffffffffff000`, `err=Window`; each changes no field. The start 0 is a placement by the kernel, so `reserve` of 1 page at 0 is `ok` with the start `VM_START`; the quota of a grant, 0 or larger than its pages, has no case, since the limit of committed VM pages is an item of the quota record |

### `src/vm/tests/failures.rs`

| Vector | Line | Test | Expected output | Entry |
| --- | ---: | --- | --- | --- |
| `vm-failures-1` | 3 | `partial_mapping_failure_retires_the_prefix_and_releases_exact_charge` | A map of 2 pages whose backend maps a prefix and fails is `err=Backend`; the events are `zero`, `map`, `unmap`, `invalidate` and `scrub`; no mapping remains, and the charged pages, the free bytes and the regions are those from before | No case: a commit makes all its checks before its first write and none of its plans fails, so there is no partial map to retire |
| `vm-failures-2` | 20 | `failed_map_retirement_is_retained_even_without_a_published_receipt` | A map of 2 pages whose backend fails to map and then to invalidate is `err=Retirement`: 2 pages and 1 retiring region remain, with 6 charged pages and 2 mapping obligations; a further map is `err=Busy`; nothing has been scrubbed; a retry with a working backend leaves no region | `release` of a region of 2 committed pages whose first unmap plan a host test holds without `acknowledge`: the region is pending, no zero plan has been given, the frames are off the pool and the usage of committed VM pages stays 2; the prototype's further map lies after the region: here a `reserve` there while the plan is held is `err=InvalidState`, and a `commit` in the region `err=Pending`; after the `acknowledge` of every plan and the calls that continue the release, the region is gone, `ok`, and the frames are in the pool. A failed retirement has no case: a held plan is one not yet acknowledged, and no plan fails |
| `vm-failures-3` | 45 | `failed_unmap_or_invalidation_keeps_pages_and_prevents_process_reaping` | For a failing invalidation and then a failing unmap: the unmap of a region of 2 pages filled with `0xde` is `err=Retirement`, nothing is scrubbed, the pages keep `0xde` and 2 pages stay mapped, and the destruction of the domain is `err=ReferencesOutstanding`; with a working backend the unmap and the close succeed | `release` of a region of 2 pages filled with `0xde`, with its first unmap plan executed and held before its `acknowledge`, and then with it held before its execution: in both, no zero plan has been given, the frames keep `0xde` and stay off the pool, and the usage of committed VM pages stays 2; after the `acknowledge` of every plan the release completes, `ok`. That the process does not reach Dead before its frames return is a gate of the [lifecycle](../../objects-capabilities/lifecycle/contract.md#reaping) component |
| `vm-failures-4` | 70 | `owner_fault_closes_authority_but_keeps_retirement_and_peer_independent` | Domain a maps 2 pages and domain b 1 page, filled with `0xf3`; a's execution ends by a fault and its space is closed; with a failing invalidation, the close of a's grant is `err=Retirement`, the grant is no longer open, 3 pages are mapped and the destruction of a is `err=ReferencesOutstanding`; with a working backend, the close and the destruction succeed, and b's page keeps `0xf3` | After the fault of process a, whose destruction is the [lifecycle](../../objects-capabilities/lifecycle/contract.md#destruction) component's, `revoke_step` of a after the invalidation of its ASID and the reset of its tables, with its first zero plan held: a's 2 frames stay off the pool and its usage of committed VM pages stays 2; after the `acknowledge` of every plan, the revocation completes, a holds no frame, and b's frame keeps `0xf3`. The grant and its close have no case |
| `vm-failures-5` | 102 | `active_cpu_blocks_mapping_and_closure_without_callback_or_state_change` | While domain a runs on the execution manager, a map and the close of the grant of domain b are each `err=Execution(Busy)`; b's grant stays open, the backend has no event and the registry is unchanged | No case: an operation acts only on the address space of the calling thread, the one thread of its process, and an entry runs to completion, so no operation meets another address space or one that runs |
| `vm-failures-6` | 126 | `generation_exhaustion_never_reissues_a_region_identifier` | With the next region identifier at `0xffffffffffffffff`, a map gives that identifier and its unmap succeeds; the next map is `err=GenerationExhausted` | No case: a region has no identifier and no generation in release 0.1 ([VM window and regions](#vm-window-and-regions)) |

## Current deviations

The rules of this page differ from those of the prototype's private user
memory, which [References](#references) lists:

- **No capability.** The prototype bound a grant to a stopped domain by a
  trusted admission and authorized each request through a typed Memory
  capability, pinned by references; here the operations act on the
  caller's own address space without a handle, and no grant, Memory
  capability or reference count exists.
- **Names.** A region is named by its start address, without an identifier
  or a generation; the prototype gave each region an identifier from a
  counter and refused a stale one.
- **Placement.** A `reserve` at the address 0 places the region at the
  lowest address of the window at which its pages fit; the prototype
  refused a grant that started at 0.
- **Two operations of a map.** The prototype's map reserved and committed a
  region at once, and its unmap removed it; here `reserve` and `commit`,
  and `decommit` and `release`, are separate, and `mprotect` changes the
  access of committed pages.
- **Pages per call.** A call commits, decommits or protects at most
  `MAX_CALL_PAGES` = 512 pages, where the prototype mapped at most 16
  contiguous pages per request; a region has no limit of pages but the
  window.
- **The pages.** Frames come from a page pool that the boot carves and that
  holds them zero, so a commit zeroes nothing and cannot fail to zero; the
  prototype took each region from the allocator of its execution manager
  and zeroed it at the map.
- **Limits.** The limit of a process is its item of committed VM pages with
  the cap of the capacity record, and the shared capacity is the page pool;
  the prototype's registry had an aggregate of pages, regions and grants
  with reserves for a control class, which do not exist here.
- **Release.** The release takes two phases whose plans cannot fail; the
  prototype's failed retirement, which kept its record and charge for a
  retry, is a plan that has not been acknowledged.
- **Plans per page.** Each committed page has its own unmap plan, with the
  invalidation of its address, and its own zero plan; the prototype
  unmapped a region, invalidated the translations of its address space and
  scrubbed its pages once for the whole region.
- **Window.** The VM window is the second 1 GiB slot of the EL0 window for
  every process; the prototype's native profile restricted requests to
  `[0x34000000, 0x34100000)` with eight live pages for each child.

## References

- Arm Limited, *Arm Architecture Reference Manual for A-profile
  architecture*, DDI 0487, version M.d, 2026,
  <https://documentation-service.arm.com/static/6abbec2a6db85c5e6614a4a1>:
  the TLB maintenance after a change of the permissions of a page;
  `TLBI VAAE1IS` and `TLBI ASIDE1` with the completion of TLB maintenance
  by `DSB`; the permission and translation faults of EL0.
- The kernel's own rules, which this page instantiates:
  [Address spaces and VM objects](../../../architecture.md#address-spaces-and-vm-objects)
  for the private anonymous objects of one thread, the two phases of
  `release`, the counts of W^X and the execute right;
  [Kernel objects and capabilities](../../../architecture.md#kernel-objects-and-capabilities)
  for VM regions, the capacity record and the commit limit of each process;
  and [System calls and the ABI](../../../architecture.md#system-calls-and-the-abi)
  for entries that run to completion and long operations that store their
  progress; the
  [internal choices](../../../security.md#internal-choices),
  [effective revocation](../../../security.md#effective-revocation) and
  [observable outputs](../../../security.md#observable-outputs) of the
  security model.
- The rules of this page take, as clauses of their own, the rules of the
  prototype tree at `prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`:
  - `docs/private-memory.md`, lines 9 to 35: authority and limits, the
    limit of 16 pages per request, the checks before any backing is taken,
    the control reserves and the native profile, which are not carried
    ([Current deviations](#current-deviations)), and the zero bytes before
    EL0 runs;
  - `docs/private-memory.md`, lines 37 to 62: the scalar ABI of the
    prototype's map and unmap, with zero unused arguments and a stale
    region identifier that cannot free a new region; the operations of this
    page replace them;
  - `docs/private-memory.md`, lines 64 to 85: publication and retirement,
    from the record before the tables are changed to the unmap, the
    completed invalidation, the scrub and the release of the charge, which
    the order of [Acknowledgement and reclamation](#acknowledgement-and-reclamation)
    keeps without a callback;
  - `docs/private-memory.md`, lines 87 to 107: verification and limits,
    the host tests of authority, bounds, quotas, exhaustion, zeroing,
    reuse and failed retirement, and the QEMU consumer of the C runtime;
  - `docs/records/kernel/concurrency-vm-review/README.md`, lines 111 to
    193: admission and ownership, and publication, protection and reclaim,
    whose order of unmap, completed invalidation, receipt, scrub and free,
    and whose break-before-make, this page keeps, while its shared sealing
    and queues of frames belong to later releases;
  - `docs/components.md`, line 26: the place of the VM controller among the
    components, on the sole allocator of the execution manager;
  - `docs/kernel-state.md`, lines 173 to 178: the state of the VM registry,
    owned by one controller, with the retained receipt of each region.
