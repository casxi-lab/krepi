---
specifications:
  - Krepi.Spec.PageTables.Basic
  - Krepi.Spec.PageTables.Descriptor
  - Krepi.Spec.PageTables.Tables
  - Krepi.Spec.PageTables.Plan
  - Krepi.Spec.PageTables.Map
  - Krepi.Spec.PageTables.Boot
  - Krepi.Spec.PageTables.Ownership
  - Krepi.Spec.PageTables.Tokens
  - Krepi.Spec.PageTables.Witnesses.TableSets
  - Krepi.Spec.PageTables.Witnesses.PageOwnership
---

# Page-tables specification

The Lean specification of the `page-tables` component, written from its
[requirements](requirements.md) and [contract](contract.md) and never from an
implementation. It is an executable model: every entry is a computable
definition whose body is public (`@[expose]`), none is `noncomputable` or
chooses with `Classical.choice`, and every loop is structural recursion on a
list whose length the contract bounds or on fuel from the contract's
[work bounds](contract.md#work-bounds). The modules lie below
[`verification/Krepi/Spec/PageTables/`](../../../../verification/Krepi/Spec/PageTables/)
and import Lean core, the earlier modules of the component and, for the boot
memory map, the modules of the fdt specification. The
[proof path](proof.md) plans the proof of the code against this
specification, as the planned target `page-tables`.

This page describes the modules of the state machine: the descriptors and
kinds, the physical ranges, the pools with the record of their tables in use,
the walk, the write plans, the kernel mappings, the direct map and the page
ownership table, the entries of rows 107 to 117 of the
[entry table](contract.md#entry-points), and the shared fields of the
[state fields](contract.md#state-fields) as transactions that hold a token.
The invariants and the properties of the component are stated in two
modules below
[`verification/Krepi/SpecProperties/PageTables/`](../../../../verification/Krepi/SpecProperties/PageTables/),
`Invariants` and `Properties`, which import Lean core and the specifications
alone and lie on the statement side ([Invariants](#invariants),
[Properties](#properties)). Each proposition that a theorem is to prove is a
definition there, registered in
[`verification/statements.json`](../../../../verification/statements.json)
with its theorem below
[`verification/Krepi/Proofs/PageTables/`](../../../../verification/Krepi/Proofs/PageTables/),
whose proof is planned: it is `sorry` until a proof pull request proves it
([statements and proofs](../../../formal-verification.md#statements-and-proofs)).
The specification tests, for each requirement one input that the
specification must accept and one that it must reject, are stated the same
way in `Stp` below
[`verification/Krepi/SpecTests/PageTables/`](../../../../verification/Krepi/SpecTests/PageTables/),
with their planned theorems in `Krepi.Proofs.PageTables.Stp`
([Specification tests](#specification-tests)). The witnesses that the
specification is not vacuous are two further modules below
[`verification/Krepi/Spec/PageTables/Witnesses/`](../../../../verification/Krepi/Spec/PageTables/Witnesses/),
split along the seam of the entry table: `TableSets` for the table sets,
rows 107 to 112, and `PageOwnership` for the page ownership table,
rows 113 to 117 ([Witnesses](#witnesses)).
[`Krepi.SpecTests.PageTables.Replay`](../../../../verification/Krepi/SpecTests/PageTables/Replay.lean)
replays the cases of the
[vector file](../../../../verification/vectors/memory/page-tables.vectors)
through the specification ([vector notation](#vector-notation)).

## Widths and quantifiers

The state of a table set is its pool and the record of its tables in use.
An entry that writes a set returns, on success, the set after its write phase,
whose record holds the tables that its plan takes, and the plan; the plan's
execution on the pool (`Tables.apply`) gives the set that the
[abstract mapping](contract.md#abstract-mapping) describes. A failure returns
one error and nothing else, since a result is an `Except TableError α`, so
a refused call changes no table and takes no table. The modification set of
each entry:

| Entry | Writes |
| --- | --- |
| `Tables.new` | The record, set to 1 |
| `Tables.reset` | The record, set to 1; the plan zeroes the tables in use |
| `Tables.mapPage`, `Tables.mapBlock` | The record, raised by the new tables; the plan writes them and the entry of the leaf |
| `Tables.unmapPage` | Nothing; the plan writes the entry of the leaf |
| `Tables.cloneKernelFrom` | The record of the target, set to that of the source; the plan zeroes the target's tables in use and writes its tables of the indices that the source uses; the source is an argument and is not written |
| `Tables.kernelMap`, `Tables.directMap` | The record, raised by the new tables; the plan writes them and the entries of the leaves; the layout and the boot memory map are arguments and are not written |
| `Tables.lookupPage`, `Tables.lookupBlock`, `Tables.usedTables`, `descriptor`, `directAddress`, the functions of `PhysRange`, `Plan.counts` | Nothing |

The state of the page ownership table is `Ownership E X`: the arena, the
managed banks, the extents, the exclusion records and the generation counter.
An entry that writes it returns, on success, the table after its write phase
and its value, a receipt or a reservation; a failure returns one error, with
the packet or the reservation that `publish` and `cancel` hand back, and no
table, so a refused request writes nothing and the table keeps no count of
failures. The modification set of each entry:

| Entry | Writes |
| --- | --- |
| `Ownership.new` | The table, built: the banks in address order, a free extent for each run of pages that no exclusion touches, a record for each exclusion, and the counter at 1 |
| `Ownership.assign`, `Ownership.reserve` | The free extent that holds the choice, replaced by the choice, held published or reserved with the generation of the counter, and the free parts before and after it; the counter, advanced |
| `Ownership.publish` | The state of the extent of the packet, from reserved to published |
| `Ownership.cancel`, `Ownership.release` | The extent of the reservation or of the receipt, free, merged with the free extents next to it in its bank |
| `Reservation.initialized` | No table; it consumes the reservation and gives the packet or the reservation, marked as attempted with one more failure |
| `Ownership.choose`, `Ownership.owner`, `Ownership.ownerOf`, `Ownership.validate`, `Ownership.stats` | Nothing |
| The transactions of `Shared` | The field of the token that each takes ([Tokens](#tokens)) |

Each entry is stated for all of its inputs at their machine widths:

| Value | Lean type | Range |
| --- | --- | --- |
| A virtual address, a physical address, an output address, a descriptor, `base` and `source_base` | `UInt64` | $[0, 2^{64})$ |
| The physical width `bits` | `UInt8` | $[0, 2^{8})$; the entries refuse those outside 32 to 48 |
| The start and the length of a physical range | `UInt64` | A range whose length is not 0 and whose end is below $2^{64}$, the invariant of `PhysRange` |
| A kind | `Kind`, nine constructors | Each kind |
| A table set | `Tables r N` of a region `r` and a capacity `N` | Every pool of `N` tables and every record, also a set that no entry built |
| The capacity `N`, the record of the tables in use, a table index and an entry index of a plan step | `Nat` | Every natural number |
| A write plan | `Plan`, a list of `Step` | Every list |
| A layout of `kernel_map` | `Layout`: a list of `LayoutRange`, each a `PhysRange` with a kind of `layoutKinds`, and a list of guard addresses of `UInt64` | At most 16 ranges, each of one of the four kinds of a layout; every list of guard addresses |
| The boot memory map of `direct_map` | `Krepi.Spec.Fdt.MemoryPlan` of the fdt specification | Every value, also one that no entry of the fdt specification built |
| The arena, an owner identity and a generation | `UInt64` | $[0, 2^{64})$; `Ownership.new` refuses the arena 0 |
| The pages and the alignment of a request | `UInt64`, counts of 4 KiB pages | $[0, 2^{64})$; `choose` and `reserve` refuse those whose bytes are $2^{64}$ or more |
| The count of failures of a reservation or a packet | `UInt64` | $[0, 2^{64})$ |
| A bank, an exclusion, a window and the range of a value | `PhysRange` | Every physical range; `Ownership.new` refuses a bank off page boundaries |
| The owner of an exclusion | `Excluder`: firmware, image, boot storage | Each |
| The generation counter | `Counter`: `next g` or `exhausted` | Each |
| A page ownership table | `Ownership E X` of an extent capacity `E` and an exclusion capacity `X` | Every value, also one that no entry built |
| The capacities `E` and `X`, the bank of an extent and the fields of `Stats` | `Nat` | Every natural number |

Inside a definition arithmetic is on `Nat`, which does not wrap. The rules
that compare with a power of two compare the exact value: the end of a pool,
$\mathtt{base} + 4096 N \le 2^{\mathrm{bits}}$, in `poolFits`; a physical
address against $2^{\mathrm{bits}}$ in `checkPhysical` and `copyableLeaf`;
the end of a range against $2^{64}$ in `PhysRange.new` and against $2^{39}$ in
`directAddress`. The capacities of the core are constants of at most 80
tables, so the counts fit any width; they are `Nat` here so that no count
wraps on a set written by hand. A table address `base + 4096 t` is taken at
64 bits (`tableAddress`) only for a table `t` below `N` of a pool that the
first checks accepted, which ends at or below $2^{48}$.

The page ownership table compares with $2^{64}$ exactly: the bytes of a
request and of its alignment in `Ownership.choose`, the rounded start and the
end of a range in `fit` and `rangeOf?`, and the counter after $2^{64} - 1$ in
`Counter.after`. The fields of `Stats` are `Nat`: on a table that the entries
built the bytes are those of disjoint ranges below $2^{64}$ and the counts at
most the capacity, and `Nat` states them for every table without a wrap.

The functions are total, so "for every input the entry returns" holds of the
specification by construction. A set that no entry built, such as one whose
storage a test wrote, is still an input of every entry, and the walk reads it
by the rules of [the walk](#readings-of-the-contract); the results that the
contract fixes are those on sets that `Tables.new` built on zero storage and
the write entries then changed.

## Model

### Basic

[`Basic.lean`](../../../../verification/Krepi/Spec/PageTables/Basic.lean): the
shared values.

- **Sizes and indices.** `PAGE_SIZE` 4 KiB, `BLOCK_SIZE` 2 MiB, `GIB_SIZE`
  1 GiB and `ENTRIES` 512; `index1`, `index2` and `index3`, the bits 30 to
  38, 21 to 29 and 12 to 20 of a virtual address ([Terms](contract.md#terms));
  `blk` and `gib`, the address rounded down to 2 MiB and to 1 GiB
  ([Abstract mapping](contract.md#abstract-mapping)).
- **Regions and widths.** `Region` with `lower` and `upper`, and
  `Region.holds`: below $2^{39}$ (`VA_LIMIT`), or at or above `DIRECT_BASE`,
  $2^{64} - 2^{39}$; `widthOk`, a physical width of 32 to 48.
- **Errors.** `TableError` with the 7 variants of
  [errors of table sets](contract.md#errors-of-table-sets) and
  `OwnershipError` with the 12 of [page ownership](contract.md#page-ownership),
  each in the order of its table, with the name of each variant as the
  contract and the vector notation write it.
- **Physical ranges.** `PhysRange` holds `start` and `len` with the invariant
  of the term: the length is not 0 and the end fits in 64 bits.
  `PhysRange.new` is `PhysRange::new`, `InvalidRange` for a length of 0 and
  `AddressOverflow` for an end of $2^{64}$ or more; `PhysRange.endAddr`,
  `PhysRange.contains` and `PhysRange.overlaps` are `end`, `contains` and
  `overlaps`, compared at the exact ends.

### Descriptor

[`Descriptor.lean`](../../../../verification/Krepi/Spec/PageTables/Descriptor.lean):
the [descriptors and attributes](contract.md#descriptors-and-attributes).

- **Kinds.** `Kind` with the nine kinds of the kind table, in its order.
  `Kind.attributes` gives each kind's row, the AP[2:1], PXN, UXN, AttrIndx,
  SH, nG and AF of the table, and `Attributes.bits` places them at bits 7 and
  6, 53, 54, 2 to 4, 8 and 9, 11 and 10. `KernelPrivateReadWrite` is one of
  the nine: no mapping of release 0.1 uses it, since the lower tables of a
  process hold no kernel page private to one address space
  ([address spaces and ASIDs](../address-space/contract.md#address-spaces-and-asids)),
  and its bits, and the refusal of the copy to take it, are specified as for
  every kind.
- **Permissions.** `Attributes.readOnly` is AP[2] (RO),
  `Attributes.writable` its negation, `executableEl1` and `executableEl0` are
  PXN and UXN clear (NX), `isDevice` is AttrIndx 0 and `isGlobal` is nG
  clear. They read the bits of a row, so that W^X of the kinds, the first
  rule of [W^X](contract.md#descriptors-and-attributes), is a statement on
  the bits.
- **Descriptors.** `descriptor k a` is `page_tables::descriptor`: the address
  in bits 12 to 47, the bits of the kind and `0b11` in bits 1 and 0.
  `blockDescriptor a` is the page descriptor of `ReadWrite` at `a` rounded to
  bits 21 to 47, with bit 1 clear. `tableDescriptor a` holds the address and
  `0b11`, with no attribute. `INVALID` is 0, the invalid entry that the
  component writes.
- **Decoding.** `typeBits` and `isValid` read bits 1 and 0;
  `outputAddress` and `blockAddress` read bits 12 to 47 and 21 to 47;
  `isPlainTableDescriptor` is a table descriptor without an attribute bit;
  `Kind.ofPage` gives the kind whose page descriptor a descriptor is, and
  `isReadWriteBlock` whether it is the block descriptor of `ReadWrite`.
- **The direct address.** `directAddress r` is `page_tables::direct_address`:
  `DIRECT_BASE | start` when the end of the range is at most $2^{39}$, and
  none otherwise ([kernel direct map](contract.md#kernel-direct-map)).

### Tables

[`Tables.lean`](../../../../verification/Krepi/Spec/PageTables/Tables.lean):
table sets, the walk and the abstract mapping.

- **Pools and sets.** `Table` is a vector of 512 descriptors and `Pool N`
  one of `N` tables; `Tables r N` holds the pool and `used`, the record of
  the tables in use, which are the tables of the indices below it. The
  region and the capacity are parameters of the type. `Tables.table` and
  `Tables.entry` read the pool, 0 where it has no table or entry;
  `tableAddress base t` is the address of table `t`, `base` $+ 4096 t$.
- **The first checks.** `checkEntry` makes the first checks of an entry that
  takes a virtual address: `Alignment` for the address, at 4 KiB for a page
  and 2 MiB for a block, or `base`; then `AddressWidth` for an address
  outside the region or `bits` outside 32 to 48; then `TableBacking` for a
  pool of no table or one that does not end at or below $2^{\mathrm{bits}}$
  (`poolFits`). `checkPool` makes the same checks without an address, for
  the two pools of the copy; `checkPhysical` checks a physical address,
  `Alignment` and then `AddressWidth`.
- **The walk.** `Tables.child?` gives the table in use that a table
  descriptor points at. `Tables.walk2` reads the root entry of an address and
  gives its level 2 table and entry; `Tables.walk` goes on to the level 3
  entry, and `Reach` says where it ends: an invalid root or level 2 entry, a
  block, or a level 3 entry. A valid entry that does not point at a table in
  use is `TableBacking`. `Tables.pageLeaf` gives the page leaf of an address,
  `NotMapped` without one, a page of a block included.
- **Entries that write nothing.** `Tables.lookupPage` and
  `Tables.lookupBlock` are `lookup_page` and `lookup_block`: the first checks
  for a page or a block, the walk, and the descriptor or `NotMapped`.
  `Tables.usedTables` is `used`, the record.
- **The abstract mapping.** `Tables.M`, `Tables.G` and `Tables.P` are the
  $M$, $G$ and $P$ of the contract for the set at `base`, as propositions:
  $M(v) = l$ when the walk of a 4 KiB-aligned address of the region reaches a
  page descriptor of a kind, or the block descriptor of `ReadWrite` whose
  block holds the page of `v` at the same offset; $g \in G$ when the root
  entry of a 1 GiB slot points at a table in use; $b \in P$ when the walk of
  a 2 MiB slot reaches a level 3 table. No entry computes them: they state
  what the pool means.

### Plan

[`Plan.lean`](../../../../verification/Krepi/Spec/PageTables/Plan.lean): the
[write plans](contract.md#write-plans-and-publication).

- **Steps.** `Step` with `zero t`, `store t i d`, `fence`, `sync` and
  `invalidate v`, the five steps of the contract's table; `Plan` is a list of
  steps in the order of their execution; `Step.storesValid` says whether a
  step makes an entry valid.
- **Execution.** `Step.exec` is the effect of a step on the pool: `Zero`
  writes 0 into the 512 entries of a table (`Pool.zeroTable`) and `Store` a
  descriptor into an entry (`Pool.store`); `Fence`, `Sync` and `Invalidate`
  leave the pool as it is. A step outside the pool or the table leaves it as
  it is too, which no plan of an entry holds. `Plan.exec` runs the steps in
  order and `Tables.apply` gives the set once its plan has run.
- **Hardware.** What `DMB ISHST`, `DSB ISH`, `ISB` and the invalidation do
  for the walks and the TLBs of the CPUs is not modelled. The adapter that
  executes the steps is excluded from the specification as an
  [open obligation](contract.md#open-obligations): the stores, the zeroing
  and the barriers of `kernel/arch/src/mmu.rs`, with the TLB maintenance of
  the boot component. The specification states the order of the steps, which
  the requirements fix.

### Map

[`Map.lean`](../../../../verification/Krepi/Spec/PageTables/Map.lean): the
write entries of a set.

- **`Tables.new`** takes the storage of the pool and sets the record to 1. It
  checks nothing; on storage that is zero in all its tables the set is empty.
- **`Tables.reset`** sets the record to 1, and its plan is a `Zero` of every
  table in use, in index order. It checks nothing.
- **`Tables.mapPage`** makes the first checks for a page, checks the physical
  address, walks the address and, last, compares the new tables that the page
  needs with the free tables of the pool. Its plan is that of
  [new tables](contract.md#write-plans-and-publication) and
  [new entries](contract.md#write-plans-and-publication): a new level 3 table
  and a new level 2 table are written before the table descriptors that make
  them reachable, with one `Fence` before the store into the root or the
  existing level 2 table, and the plan ends with `Sync`.
- **`Tables.mapBlock`** makes the first checks for a block, checks the
  physical address at 2 MiB, reads the root entry and the level 2 entry, and
  refuses a level 2 entry that is valid, a block or a level 3 table, with
  `AlreadyMapped`. Its plan writes one level 2 descriptor, after a new level 2
  table when the root entry was invalid.
- **`Tables.unmapPage`** makes the first checks for a page and finds the page
  leaf; its plan is `Store(t, i, 0)` and `Invalidate(v)`, and it gives the
  output address of the leaf. The tables under the leaf stay in use.
- **`Tables.cloneKernelFrom`** checks the two pools, their overlap and the
  record of the source, then walks the source from its root
  (`Tables.walkRoot`, `Tables.walkLevel2`, `Tables.reach`, `checkLeaves`)
  and checks that the walk reached every table in use. Its plan zeroes the
  tables in use of the target, stores every valid entry of every table in use
  of the source into the target's table of the same index (`copyStores`),
  the table descriptors pointing into the target's pool, and ends with
  `Sync`; the record of the target becomes that of the source.

### Boot

[`Boot.lean`](../../../../verification/Krepi/Spec/PageTables/Boot.lean): the
[kernel mappings](contract.md#kernel-mappings) and the
[kernel direct map](contract.md#kernel-direct-map), the entries of row 112.
It imports the boot memory map, `MemoryPlan`, from the
[fdt specification](../../boot-platform/fdt/specification.md) and reads its
usable ranges through `MemoryPlan.availableRanges`.

- **Leaves.** A mapping writes leaves, `MapLeaf`: a virtual address, an
  output address, a descriptor and a form, page or block. `Tables.place`
  walks the set for one leaf with the rules of `map_page` and `map_block`:
  `TableBacking` for a bad table descriptor, `AlreadyMapped` for a slot that
  is not free, and otherwise the place of the leaf, `Place`: under an invalid
  root entry, in a level 2 table of the set, or in a level 3 table of the
  set. `Tables.checkLeaf` adds the rule of the map itself: a leaf that the
  map already covers is `AlreadyMapped`.
- **New tables.** `assignTables` gives the leaves, in address order, their
  tables: a leaf under an invalid root entry takes the new level 2 table of
  its 1 GiB slot, the one that an earlier leaf of the slot took or else the
  next free index, and then a page whose level 2 entry is free takes the new
  level 3 table of its 2 MiB slot in the same way (`Alloc.add`). The next
  free index after the map less the record is the number of new tables.
- **The plan.** `mapPlan` writes the leaves one 1 GiB slot after the other,
  in address order (`runsBy`): under a level 2 table of the set, each 2 MiB
  slot is a `Store` of its block, the `Store` of each of its pages into a
  level 3 table of the set, or `Zero(t3)`, the `Store` of each page, `Fence`
  and the `Store` of the table descriptor of the new level 3 table
  (`heldLevel2Steps`); under a new level 2 table, every new level 3 table
  under it first, `Zero(t3)` and its pages, then `Zero(t2)`, the `Store` of
  each of its entries in index order, `Fence` and the `Store` of its table
  descriptor into the root (`newLevel2Steps`). `Sync` ends the plan. Each new
  table is complete before the one store that makes it reachable from a
  table of the set, and on one leaf the plan is that of `Tables.mapPage` or
  `Tables.mapBlock` for it. `Tables.mapLeaves` refuses with `OutOfTables` a
  map that needs more tables than the pool has free, and otherwise returns
  the set whose record holds the new tables and the plan.
- **`Tables.kernelMap`** takes the lower kernel set and a `Layout`: at most
  16 ranges, `LayoutRange`, each a `PhysRange` with one of the four kinds of
  `layoutKinds`, and the guard pages, each named by an address in it. It
  makes the first checks of a pool (`checkPool`), then checks the ranges
  sorted by their start (`sortByKey`), each with `Tables.checkLayoutRange`:
  its ends on page boundaries, `Alignment`; its end at most $2^{39}$ and
  $2^{\mathrm{bits}}$, `AddressWidth`; then its pages in address order
  (`layoutPages`), each mapped at its physical address with the kind of the
  range, the walk of each and then `AlreadyMapped` for a page that an earlier
  range holds or that holds a guard address. Last the tables, with
  `Tables.mapLeaves`.
- **`Tables.directMap`** takes the direct map's set and a boot memory map. It
  makes the first checks of a pool, then checks the usable ranges sorted by
  their start, each with `Tables.checkUsableRange`: its ends on page
  boundaries, `Alignment`; its end at most $2^{39}$ and $2^{\mathrm{bits}}$,
  `AddressWidth`; then its leaves in address order (`directLeaves`), a block
  of `ReadWrite` at each multiple of 2 MiB with 2 MiB of the range left and a
  page of `ReadWrite` elsewhere, each at `DIRECT_BASE | pa`, with the walk of
  each and then `AlreadyMapped` for a leaf that shares an address with an
  earlier range. Last the tables, with `Tables.mapLeaves`.
- **Counts.** `Plan.counts` gives the bytes, the blocks and the pages of the
  map that a plan writes: one block for each `Store` of a block descriptor
  (`Step.storesBlock`) and one page for each `Store` of the page descriptor of
  a kind (`Step.storesPage`), 2 MiB and 4 KiB each.
- **Capacities.** `DIRECT_MAP_TABLES`, 80, and `KERNEL_TABLES`, 32, are the
  pools of the kernel tables ([table pool](contract.md#table-pool)). The
  entries are stated for every capacity.
- **Bounds.** Every loop is structural recursion on a list or on fuel: the
  pages of a range of a layout are its length over 4 KiB (`layoutPages`),
  and the steps of the walk of a usable range of length $L$ are at most
  $L / 2\,\mathrm{MiB} + 2 \cdot 511$ (`directFuel`), the bound of
  [work bounds](contract.md#work-bounds): a block for each 2 MiB and at most
  511 pages at each end.

### Ownership

[`Ownership.lean`](../../../../verification/Krepi/Spec/PageTables/Ownership.lean):
the [page ownership](contract.md#page-ownership) table, the entries of rows
113 to 117, modelled at the level of its extents. It imports `Basic.lean`
only: the table takes its banks, exclusions, windows and receipts as physical
ranges, which the boot wiring converts from the boot memory map.

- **Values.** `HoldState` with reserved and published; `Excluder` with
  firmware, image and boot storage; `Owner`, a row of the owner table: free,
  an excluder, or a holder $\mathrm{held}(o, n, s)$; `Allocation`, the
  receipt, with the arena, the owner identity, the generation and the range;
  `Reservation`, with whether a zeroing was attempted and the count of
  failures; `Initialized`, the packet; `Placement`, low or high with an
  optional window; `Choice`, the owner identity and the range of `choose`.
- **State.** `Ownership E X` holds the arena, the managed banks in address
  order, the extents in address order, each an `Extent`: a range of pages of
  one bank, free or held (`Holding`), the exclusion records, each an
  `Exclusion` with its owner, and the generation counter, `Counter`, the
  generation of the next allocation or reservation or `exhausted`.
  `EXTENTS`, 160, and `EXCLUSION_RECORDS`, 132, are the capacities of the
  core; the entries are stated for every `E` and `X`.
- **The owner function.** `Ownership.ownerOf` is $O$: a page in an extent
  has the owner of the extent; a page of a managed bank in no extent has the
  first owner, in the order firmware, image, boot storage, of the exclusion
  records that touch it (`firstExcluder`). `Ownership.owner` is the entry
  `owner`, $O$ of the page that holds an address. The generation counter $g$
  is `Ownership.counter`.
- **`Ownership.new`** checks the banks on page boundaries
  (`PhysRange.onPages`), the arena, the number of banks against none and
  against `E`, the overlap of two banks (`anyOverlap`), the number of
  exclusions against `X`, and last the extents of the banks split by the
  exclusions against `E`. The extents of a bank (`bankExtents`) are the runs
  of its pages that no exclusion touches: each exclusion cuts out the pages
  that it touches, its start rounded down and its end rounded up to a page
  within the bank (`Exclusion.cut`, `cutRuns`). The banks are sorted by
  their start (`sortByKey`), each extent names its bank by its index in that
  order, and the counter starts at 1.
- **`Ownership.choose`** checks the bytes of the request and of its
  alignment, `pages` and `alignment` times 4 KiB, against $2^{64}$, then 0
  pages, an alignment that is not a power of two (`isPowerOfTwo`) and the
  counter. `scan` then visits the extents in address order, from the lowest
  for a low placement and from the highest for a high one, passes the held
  ones, and in a free extent takes the part inside the window
  (`Placement.part`) and there the range of the request (`fit`): the lowest
  start rounded up to the alignment that ends inside the part, or for a high
  placement the start of the last range that fits, rounded down. A range
  that would need more extents than the capacity has free (`Extent.extra`)
  is passed over and remembered; the first range that fits gives the choice.
  At the end of the scan `MetadataExhausted` when a range was passed over for
  capacity, and `OutOfMemory` otherwise.
- **`Ownership.assign`** gives `ZeroFailed` when the zeroing failed and
  otherwise makes the write of `Ownership.take`: the free extent that holds
  the range of the choice becomes the range, held published by the owner
  identity with the generation of the counter, between its free parts
  (`Extent.take`), and the counter advances (`Counter.after`). `take` repeats
  the checks of `choose` that its write needs, so a choice of `choose` on
  the same table passes them.
- **`Ownership.reserve`** is `choose` and the write of `take`, reserved; it
  returns a `Reservation` that is not attempted and has no failure.
  **`Reservation.initialized`** gives an `Initialization`: the packet with
  the count of failures when the zeroing completed, or the reservation
  marked as attempted with one more failure.
- **Receipts.** `Ownership.findHeld` makes the checks of a value that names a
  held range: the arena, the owner identity, and an extent that is exactly its
  range held by that owner identity with its generation in its state.
  `Ownership.release` and `Ownership.cancel` free that extent and merge it
  with the free extents next to it in the same bank (`mergeFreed`,
  `Extent.join`); `cancel` refuses first a reservation whose zeroing was
  attempted. `Ownership.publish` turns the reserved extent of a packet into a
  published one and returns the receipt. `Ownership.validate` makes the
  checks of `release` without a write, with the state that the value names.
  A refused packet or reservation is returned with the error.
- **`Ownership.stats`** folds over the extents: the managed bytes, those of
  the free and the held extents, the free and the allocated bytes, the
  number of held extents, of free extents and the largest, the extents in use
  and `E`, as `Stats`.
- **Bounds.** Every loop is structural recursion on a list: the banks, the
  exclusions and the runs at initialization, the extents in a scan, a search
  and a merge, the exclusion records in `firstExcluder`. A table of at most
  `E` extents and `X` records makes each a pass over at most 160 extents or
  132 records, the bounds of [work bounds](contract.md#work-bounds).

### Tokens

[`Tokens.lean`](../../../../verification/Krepi/Spec/PageTables/Tokens.lean):
the four shared fields of the [state fields](contract.md#state-fields) as
transactions that hold a token. It imports `Boot.lean`, for the kernel
mappings, the direct map and the capacities of the kernel tables, and
`Ownership.lean`.

- **State.** `Shared E X` holds the lower kernel set and the direct map's
  set, each a `Tables` value with its descriptors and its record of tables in
  use, in the pools of `KERNEL_TABLES` and `DIRECT_MAP_TABLES` tables; the
  page ownership table, none until it is built; and whether the MMU is on.
- **Tokens.** `BootCpu` is the boot CPU before the MMU is on;
  `KernelTablesToken` the token of the kernel tables; `OwnershipToken` the
  token of the page ownership table. Each is a value without fields that a
  transaction takes as an argument, so that no transaction runs without the
  evidence of its owner; with one CPU the executing CPU holds each,
  `BootCpu.boot`, `KernelTablesToken.executing` and
  `OwnershipToken.executing`.
- **Transactions.** `Shared.boot` makes both kernel sets with `Tables::new`
  on their pools. While the MMU is off, the boot CPU runs
  `Shared.buildKernelMap` and `Shared.buildDirectMap`, `kernel_map` and
  `direct_map` with the execution of their plans, and `Shared.enable` ends
  the boot; no transaction writes the direct map's set after it. Then
  `Shared.fillKernel` runs `map_page` on the lower kernel set and executes its
  plan under the token of the kernel tables, and `Shared.withKernelSource`
  lends the set as the source of a copy under the same token. Under the
  token of the page ownership table, `Shared.newOwnership` builds the table
  once, `Shared.withOwnership` runs a write entry and `Shared.readOwnership`
  a read entry, and `Shared.allocate` runs `choose`, the caller's zeroing and
  `assign` as one transaction. A transaction that is not enabled gives none,
  and one whose entry fails gives its error with the state unchanged.

### Invariants

[`Invariants.lean`](../../../../verification/Krepi/SpecProperties/PageTables/Invariants.lean):
the invariants of the state of the component, a check that decides each,
and the statements of their establishment, of their preservation and of
the well-formedness of each operation. It imports `Tokens.lean` and the
invariants of the fdt specification, for the well-formedness of the boot
memory map.

The state is a table set, its pool with the record of its tables in use; a
page ownership table; and the shared state of `Tokens.lean`. A structural
invariant is quantified over a whole table of the state; a functional
invariant states what the state means beyond the shape of its tables. Every
invariant is decidable: a computable check, `check...`, decides it, on every
value or, for a functional invariant that reads the extents, on every value
that keeps the invariants that it names, and a statement states that
agreement, so that a check at boot can use it. Lines are those of the
contract.

| Invariant | Kind | States | Established by | Preserved by | Read by | Decidable |
| --- | --- | --- | --- | --- | --- | --- |
| `Tables.WellFormed` | Structural: the descriptors of every table of a set and its tables in use; the well-formedness of the page tables | At `base` and `bits`: a pool that the contract admits (lines 36 to 41, 669 and 670); a record of the root and at most $N$ tables (lines 29 to 35); every table not in use zero (line 679); the root holds only 0 and table descriptors with no attribute of tables in use, a level 2 table also block descriptors of `ReadWrite`, a level 3 table only 0 and page descriptors of a kind, every output address below $2^{\mathrm{bits}}$ (lines 150 to 159, 173 and 174); the table descriptors reach every table in use but the root exactly once and the root never (lines 270 and 271, 302 and 303) | `Tables::new` on zero storage (`NewWellFormed`); `reset` and `clone_kernel_from`, from any record, when the tables not in use are zero (`ResetWellFormed`, `CloneKernelFromWellFormed`); the kernel tables of `kernel_map` and `direct_map` on such sets (`BootKernelMapWellFormed`, `BootDirectMapWellFormed`) | `map_page`, `map_block`, `unmap_page`, `kernel_map`, `direct_map`, once the plan has run | The walk of every entry, which finds no bad table descriptor on such a set; the abstract mapping and the properties `AfterEveryWrite`, `TablesInUseCounted`, `PlansPublishInOrder` and `KernelTablesOnlyFilled`; `clone_kernel_from`, whose checks of its source are these rules | Yes: `Tables.checkWellFormed` |
| `Ownership.WellFormed` | Structural: the banks, the extents and the exclusion records | The arena not 0 (line 87); at least one bank, each on page boundaries, in address order and disjoint (lines 550 to 552); at most `E` extents (lines 639 and 640), each a range of whole pages in the bank that it names (lines 88 and 89), in address order and disjoint (line 808); at most `X` exclusion records (lines 645 to 649); a counter that has given no generation 0 (line 621) | `Ownership::new` (`NewOwnershipWellFormed`) | `assign` of a choice of `choose`, `reserve`, `publish`, `cancel`, `release` | `choose`, whose scan in address order it makes the order of the contract, `owner` and `stats`; the functional invariants and their checks | Yes: `Ownership.checkWellFormed` |
| `Shared.WellFormed` | Structural: the shared fields (lines 825 to 828) | Both kernel sets well-formed in their pools at a `Config`, and the page ownership table, once built, well-formed | The shared state of the boot (`BootWellFormed`) | Each transaction of `Tokens.lean`: `buildKernelMap`, `buildDirectMap`, `enable`, `fillKernel`, `newOwnership`, `withOwnership` with an entry that keeps a table well-formed, `allocate` | `KernelTablesOnlyFilled`; the transactions | Yes: `Shared.checkWellFormed` |
| `Ownership.OneOwner` | Functional: the uniqueness of page ownership | "Every managed page has exactly one owner" (line 535): the table records exactly one owner for each managed page, the holding of one extent or, for a page in no extent, that of the exclusion records that touch it | `Ownership::new` (`NewOneOwner`) | `assign`, `reserve`, `publish`, `cancel`, `release` | `owner` and the owner function $O$, on which the rows of `AfterEveryWrite` and `BootOwnersMatchDirectMap` are stated; the zeroing through the direct map, which reaches a page of one holder | Yes, on a well-formed table: `Ownership.checkOneOwner` |
| `Ownership.HolderRanges` | Functional | "The pages of one holder generation form one range in one bank, the range of one extent, and two holders never share a generation" (lines 536 and 537): the pages whose owner has the generation of a held extent are exactly the pages of that extent | `Ownership::new` (`NewHolderRanges`) | The same five entries | `release`, `publish`, `cancel` and `validate`, whose check of one extent is then the requirement "exactly for the pages $q$ of $x$" (lines 343 to 345) | Yes, on a well-formed table with one owner: `Ownership.checkHolderRanges` |
| `Ownership.GenerationsBelowCounter` | Functional | Every generation of a holder is at least 1 and below the counter: it "starts at 1, grows by one with each allocation and reservation, and is never reused" (lines 621 to 623, 816) | `Ownership::new` (`NewGenerationsBelowCounter`) | The same five entries | `assign` and `reserve`, whose generation no holder has; the preservation of `Ownership.HolderRanges` | Yes, on a well-formed table: `Ownership.checkGenerationsBelowCounter` |
| `Ownership.FreeExtentsMaximal` | Functional | No free extent ends where a free extent of its bank starts: a released extent merges with the free extents next to it (lines 620 and 621), one extent for each free run (lines 642 and 643) | `Ownership::new` (`NewFreeExtentsMaximal`) | The same five entries | `stats`, whose free extents and largest one are the free runs; the count of the extents against the capacity in `choose` and in [PGT-R11](requirements.md#pgt-r11) | Yes: `Ownership.checkFreeExtentsMaximal` |
| `Ownership.FreeOrHeldUsable` | Functional, of the table of the kernel root and its boot memory map | "The pages that are free or held are exactly the pages of its usable ranges, so exactly the pages of the direct map" (lines 538 to 540) | `Ownership::new` on the managed banks and the exclusions of a well-formed boot memory map (`NewFreeOrHeldUsable`, with `BootTableRanges`) | The same five entries | The direct map, which maps those pages (`BootOwnersMatchDirectMap`; W^X, line 213) | Yes, on a well-formed table with one owner: `Ownership.checkFreeOrHeldUsable` |
| `Shared.DirectMapOffset` | Functional, of the direct map's set | Every page of the set maps `DIRECT_BASE \| pa` to a page `pa` below $2^{39}$ as `ReadWrite` (lines 55 and 56, 482 to 484, 503) | The shared state of the boot (`BootDirectMapOffset`) | `buildDirectMap` (`BuildDirectMapOffset`); no other transaction writes the field | `direct_address` and the zeroing of pages through the direct map; W^X | Yes: `Shared.checkDirectMapOffset` |

The fourth invariant of the page ownership table in the contract, that the
firmware, image and boot storage pages never change owner (line 541), is a
statement of two states, not of one: the rows of `AfterEveryWrite` give it,
since each changes $O$ only on pages that are free or held. The table sets
have no functional invariant of one state: what a set means is its abstract
mapping, and how each entry changes it is `AfterEveryWrite`.

`Ownership.Invariant` is the conjunction of the invariants of one page
ownership table but `Ownership.FreeOrHeldUsable`, the hypothesis of the
preservation statements; `Ownership.Chose` states that a choice is one of
`choose` on the same table, the requirement of `assign` (line 341).

The statements of the module, 65 in all, are in four groups:

- **Checks**, 9: `CheckTablesWellFormed`, `CheckOwnershipWellFormed`,
  `CheckSharedWellFormed`, `CheckFreeExtentsMaximal` and
  `CheckDirectMapOffset` on every value; `CheckOneOwner`,
  `CheckGenerationsBelowCounter`, `CheckHolderRanges` and
  `CheckFreeOrHeldUsable` on the values that keep the invariants that they
  name.
- **Establishment**, 11: `NewWellFormed`, `BootKernelMapWellFormed` and
  `BootDirectMapWellFormed` of the table sets; `BootWellFormed` and
  `BootDirectMapOffset` of the shared state of the boot; and
  `NewOwnershipWellFormed`, `NewOneOwner`, `NewHolderRanges`,
  `NewGenerationsBelowCounter`, `NewFreeExtentsMaximal` and
  `NewFreeOrHeldUsable` of `Ownership::new`.
- **Preservation**, 26: each of `assign`, `reserve`, `publish`, `cancel`
  and `release` preserves each of `Ownership.OneOwner`,
  `Ownership.HolderRanges`, `Ownership.GenerationsBelowCounter`,
  `Ownership.FreeExtentsMaximal` and `Ownership.FreeOrHeldUsable`, named
  `<Entry><Invariant>` such as `AssignOneOwner`, on a table that keeps
  `Ownership.Invariant`, for `assign` with a choice of `choose`; and
  `BuildDirectMapOffset`.
- **Well-formedness**, 19: one lemma for each operation, apart from the
  functional statements, that on a well-formed value the value that it
  returns is well-formed: `ResetWellFormed`, `CloneKernelFromWellFormed`,
  `MapPageWellFormed`, `MapBlockWellFormed`, `UnmapPageWellFormed`,
  `KernelMapWellFormed` and `DirectMapWellFormed` of the write entries of a
  set, once the plan has run, the first two from the zero storage of the
  tables not in use alone, so that they also establish the invariant;
  `AssignWellFormed`, `ReserveWellFormed`, `PublishWellFormed`,
  `CancelWellFormed` and `ReleaseWellFormed` of the page ownership table;
  and `BuildKernelMapWellFormed`, `BuildDirectMapWellFormed`,
  `EnableWellFormed`, `FillKernelWellFormed`,
  `NewOwnershipSharedWellFormed`, `WithOwnershipWellFormed` and
  `AllocateWellFormed` of the transactions. `Reservation::initialized`
  changes no table and the read entries return values, so they have no
  lemma.

### Properties

[`Properties.lean`](../../../../verification/Krepi/SpecProperties/PageTables/Properties.lean):
the cross-cutting properties of the component, each a registered statement,
with the definitions that they need: the transactions of `Tokens.lean` as
values, `Txn`, run in order from the shared state of the boot by `runAll`;
the sets that W^X counts together; the checks of the order of a plan,
`Plan.publishesInOrder`, and of a plan that only fills,
`Plan.fillsOnly`; the slots of $G$ and $P$; and the ranges that a free
extent holds and gives a request.

| Property | States | Requirements | Contract |
| --- | --- | --- | --- |
| `NoWritableExecutable` | No kind is writable and executable; on every shared state that the transactions reach from the boot, under the rules of the boot wiring and of the fills (`WxPremises`), no frame is mapped writable by the lower kernel set or the direct map's set and executable by one of them, counting also a copy of the lower kernel set | [PGT-R01](requirements.md#pgt-r01), [PGT-R05](requirements.md#pgt-r05), [PGT-R06](requirements.md#pgt-r06) | "At no time is a frame mapped writable and executable, counting every alias in every table set together" (lines 201 to 203), with its three reasons (lines 205 to 230) |
| `AfterEveryWrite` | For each of the 14 write entries, on a valid state, a success establishes the `Requires` column of its row and the `After` column between the state before and the state once the plan has run; the two failures that the rows name, a failed zeroing of `assign` and the cancel of an attempted reservation | [PGT-R02](requirements.md#pgt-r02) to [PGT-R06](requirements.md#pgt-r06), [PGT-R08](requirements.md#pgt-r08) to [PGT-R10](requirements.md#pgt-r10), [PGT-R12](requirements.md#pgt-r12) | "Each write entry of a set changes $M$ as its row states once its write plan has been executed" (lines 316 and 317) and "each write entry of the page ownership table changes $O$ and $g$ as its row states" (lines 333 and 334), the rows of lines 322 to 329 and 340 to 345 |
| `DirectMapUnchangedAfterBoot` | From any shared state with the MMU on, every list of transactions leaves the direct map's set as it was, and the MMU on | [PGT-R05](requirements.md#pgt-r05) | "The boot wiring writes the direct map once, before the MMU is on, and no entry changes it afterwards" (lines 505 and 506); "the field never changes after it" (line 826) |
| `KernelTablesOnlyFilled` | On a well-formed shared state, every transaction keeps every valid entry of both kernel sets, and its plan for a kernel set writes only entries that are invalid when it writes them and holds no `Invalidate` | [PGT-R04](requirements.md#pgt-r04), [PGT-R07](requirements.md#pgt-r07) | "A plan for one of the kernel tables writes only invalid entries and holds no `Invalidate`; no entry of this page removes or changes a valid entry of the kernel tables" (lines 426 to 429) |
| `PlansPublishInOrder` | On a well-formed set, the plans of `map_page`, `map_block`, `kernel_map` and `direct_map` build each new table, under it first, before the one store that makes it reachable, with a `Fence` before that store, fill only invalid entries of reached tables and end with `Sync`; the plan of `unmap_page` is the store of 0 into the leaf and `Invalidate`; the plan of a copy is `Zero` steps, `Store` steps and `Sync` | [PGT-R07](requirements.md#pgt-r07), [PGT-R04](requirements.md#pgt-r04), [PGT-R12](requirements.md#pgt-r12) | The rules of new tables, new entries, unmapping and the copy (lines 406 to 425, 430 to 432, 440 to 451) |
| `TablesInUseCounted` | On a well-formed set, the record of the tables in use is 1 and the numbers of the elements of $G$ and of $P$, which `Tables.gSlots` and `Tables.pSlots` list once each | [PGT-R03](requirements.md#pgt-r03), [PGT-R05](requirements.md#pgt-r05), [PGT-R11](requirements.md#pgt-r11) | "$\mathrm{used} = 1 + \|G\| + \|P\|$" (lines 302 and 303); the count of a mapping (lines 687 to 689) |
| `PlacementFirstFit` | On a well-formed table, a choice is the range that an extent of the scan of its placement gives, the lowest or highest aligned range inside the window, within the capacity, and every earlier extent gives none or one beyond the capacity; `OutOfMemory` means that no extent holds the request, `MetadataExhausted` that every range given needs more extents than the capacity has free | [PGT-R09](requirements.md#pgt-r09), [PGT-R10](requirements.md#pgt-r10) | The placement (lines 574 to 580) and the end of the scan (lines 588 to 590) |
| `BootOwnersMatchDirectMap` | For every well-formed boot memory map, the table of `Ownership::new` on its managed banks and exclusions has one owner for every managed page, and once `direct_map` of the same map has run on a new set, a page is free exactly when the direct map maps it | [PGT-R08](requirements.md#pgt-r08), [PGT-R05](requirements.md#pgt-r05) | The criterion of [PGT-R08](requirements.md#pgt-r08); "the direct map maps only pages whose owner is free or a holder" (lines 212 and 213); lines 538 to 540 |

`WxPremises` states the rules that W^X rests on and that no entry of the
component checks: `kernel_map` and `direct_map` run at most once each (line
112); the boot memory map is well-formed and each `ReadExecute` range of the
layout lies in a span of its boot storage, the image (lines 209 to 218 and
525); and a fill of the lower kernel set maps an executable kind only at a
page of the text and a page of the text only with `ReadExecute` (lines 219
to 230). The mappings of the address spaces of processes beyond the copy,
among them `UserReadExecute` for the boot bundle, are those of the
address-space component.

### Specification tests

[`Stp.lean`](../../../../verification/Krepi/SpecTests/PageTables/Stp.lean):
for each requirement, one input that the specification must accept, with the
result that it must give, and one that it must reject, with the error that it
must give. Each test is a proposition, registered in `statements.json` with
its theorem in `Krepi.Proofs.PageTables.Stp`, the name of the test with a
lower-case first letter, whose proof is planned. Each instantiates the
criterion of its requirement, the sentence that begins "The criterion:", and
quotes the words that it instantiates, which the last column gives. The
expected results are literals written from the requirements and the
contract, never computed by the specification: descriptors from the rows of
the kind table, plans from the rules of
[write plans and publication](contract.md#write-plans-and-publication),
counts from the table of [Table pool](contract.md#table-pool) and outputs of
the rows of the frozen vectors. Where the criterion is that the frozen
vectors hold, a test takes the input of a vector of the requirement's
evidence and states the outputs of its row, with the state that the row
reads. The module imports `Tokens.lean` alone; its helpers make a set with
`Tables::new` on zero storage, map a page or a block with the plan executed,
and write a physical range whose bounds `decide` checks, and the inputs of
the capacities are made with `PhysRange::new`.

Three requirements rule out an outcome rather than an input, and their
rejecting tests take that outcome: [PGT-R01](requirements.md#pgt-r01), whose
descriptor is a function of every kind and address, keeps no bit of an
address with every bit set outside bits 12 to 47;
[PGT-R05](requirements.md#pgt-r05) maps no excluded page, so `lookup_page`
refuses each with `NotMapped` on a direct map that succeeds with the counts
of the usable pages; and [PGT-R07](requirements.md#pgt-r07), whose plans have
no failure, writes no valid entry of the kernel tables, so the fill of a page
that `kernel_map` mapped is refused. Each of the three fails for a
specification that gave the outcome, as every other rejecting test fails for
one that always succeeds and every accepting test for one that always
rejects.

The sets of the tests hold at most 10 tables, the kernel sets the 32 and 80
tables of their pools, and the tables of page ownership a few extents, except
where the criterion names a size: the 4,096 blocks of 8 GiB in 9 tables of
[PGT-R03](requirements.md#pgt-r03); the RAM of the five Pi 5 models, up to
16 GiB, of the accepting test of [PGT-R05](requirements.md#pgt-r05); and the
direct maps of 80 and 81 tables and the table of 160 extents and 132
exclusions of [PGT-R11](requirements.md#pgt-r11).

| Requirement | Test | Input | Result | Criterion |
| --- | --- | --- | --- | --- |
| [PGT-R01](requirements.md#pgt-r01) | Accepted: `DescriptorsFollowKindRows` | The nine kinds at the output address `0x10_0800_0000` of `pt-01`; the block of `ReadWrite` at `0x1_0000_0000`; the page of `pt-01` and the block of `pt-15` in new sets | The descriptor of each kind, the bits of its row with the address in bits 12 to 47, and the block descriptor; `lookup_page` and `lookup_block` give those descriptors | "the descriptor of every kind equals the bits of its row, written from the Arm Architecture Reference Manual, and the frozen vectors that read descriptor bits hold" |
| [PGT-R01](requirements.md#pgt-r01) | Rejected: `DescriptorKeepsOnlyItsBits` | The nine kinds and the block at the output address `0xffff_ffff_ffff_ffff` | The bits of each row and bits 12 to 47 of the address, bits 21 to 47 for the block, and no other bit | "the descriptor of every kind equals the bits of its row", with "every other bit 0" |
| [PGT-R02](requirements.md#pgt-r02) | Accepted: `MapPageThenLookup` | `pt-03`: `0x4000_0000` to itself as `ReadWrite` in a lower set of 3 tables; `pt-14`: `0xffff_ff80_0000_0000` to `0x1_0000_0000` in an upper set of 3 | 3 tables in use and the descriptor of each page | "the frozen vectors hold" |
| [PGT-R02](requirements.md#pgt-r02) | Rejected: `MapPageRefusesMappedPage` | `pt-03`: the same address to `0x4000_1000` as `Device` | `AlreadyMapped`; the set keeps its descriptor and 3 tables | "with the tables and the count of tables in use unchanged after every refusal" |
| [PGT-R03](requirements.md#pgt-r03) | Accepted: `EightGibOfBlocksInNineTables` | `pt-17`: 4,096 blocks from 0 in an upper set of 9 tables | 9 tables in use; `lookup_block` at five blocks across 1 GiB and 4 GiB gives the block at its own address | "4,096 blocks in a pool of 9 tables" |
| [PGT-R03](requirements.md#pgt-r03) | Rejected: `BlockBeyondNineTablesRefused` | `pt-17`: the block of `0x2_0000_0000` on that set | `OutOfTables` | "the refusal of one more with `OutOfTables`" |
| [PGT-R04](requirements.md#pgt-r04) | Accepted: `UnmapAndResetFollowContract` | `pt-09`: two pages in a lower set of 4 tables; `unmap_page` of one, `reset`, then a new page | The page and the plan `Store(2, 0, 0)`, `Invalidate(0x0)`, 4 tables in use; the plan of `reset` a `Zero` of each of 4 tables, then 1 table in use and every entry 0; then 3 tables and the new descriptor | "the frozen vectors hold, and the plan of `unmap_page` equals the order of the contract" |
| [PGT-R04](requirements.md#pgt-r04) | Rejected: `UnmapRefusesUnmappedPage` | `pt-05`: a second `unmap_page` of `0x0` | `NotMapped` | "the frozen vectors hold" |
| [PGT-R05](requirements.md#pgt-r05) | Accepted: `DirectMapCountsOfPi5Models` | The boot memory maps of the 1, 2, 4, 8 and 16 GB models with the exclusions of `Table pool`, in sets of 80 tables | The tables, blocks and pages of each row of `Table pool`: 4, 508, 581 to 19, 8,188, 581 | "the four other Pi 5 models give the counts of tables, blocks and pages of the contract" |
| [PGT-R05](requirements.md#pgt-r05) | Rejected: `DirectMapOmitsExcludedPages` | A managed window with an image, a device tree, a boot bundle, a `no-map` and a `reusable` reservation, a hole and a bank outside the window | 4 blocks and 506 pages, and `NotMapped` at a page of each exclusion, the hole and the unmanaged bank | "every page below 8 GiB is mapped to itself or absent exactly as an independent page model says" |
| [PGT-R06](requirements.md#pgt-r06) | Accepted: `KernelMapGivesKindsAndGuard` | An image on QEMU virt with text, read-only data, data and a stack with its guard page, the device tree, the interrupt controller and the console, in a lower set of 32 tables | 7 tables in use; the descriptor of each page's kind, the read-only pages with AP[2] set, the data and the stack execute-never, the devices `Device`; the guard `NotMapped` | "a write to a `ReadOnly` page, an execution from an execute-never page and an access to the guard each take the fault of the contract, and a `Device` page of the console is written" |
| [PGT-R06](requirements.md#pgt-r06) | Rejected: `KernelMapRefusesSharedPage` | A text and a data range that share the page `0x4020_1000` | `AlreadyMapped` | "on the host, a layout whose text and data share a page is refused" |
| [PGT-R07](requirements.md#pgt-r07) | Accepted: `PlansFollowContractOrder` | `map_page` with two new tables, `map_block` of `pt-15`, `unmap_page` of `pt-09`, a copy of one page, `kernel_map` of three pages and `direct_map` of two pages and a block, on new sets | The plan of each, step by step, as the contract writes it | "the plans of `map_page`, `map_block`, `unmap_page`, `clone_kernel_from`, `kernel_map` and `direct_map` equal the order of the contract, written from it" |
| [PGT-R07](requirements.md#pgt-r07) | Rejected: `KernelFillRefusesValidEntry` | After the boot, the fill under the token of the kernel tables of a page that `kernel_map` mapped | `AlreadyMapped` and no plan | "the plans ... equal the order of the contract", with "a plan for the kernel tables writes only invalid entries" |
| [PGT-R08](requirements.md#pgt-r08) | Accepted: `OwnershipOfBoardShapes` | QEMU virt and the five Pi 5 models: their boot memory maps and `Ownership::new` of their managed banks and exclusions | The managed banks and usable ranges; the table with one free extent for each usable range, the exclusion records and the counter at 1; the owners of pages of each kind | "for the boot memory map of every board shape, every managed page has exactly one owner, the free pages are exactly the pages of the direct map" |
| [PGT-R08](requirements.md#pgt-r08) | Rejected: `OwnershipRefusesOverlappingBanks` | `own-17`: banks that share the page `0x1000` | `InvalidRange` | "every managed page has exactly one owner", with the refusal of overlapping banks |
| [PGT-R09](requirements.md#pgt-r09) | Accepted: `AllocationTakesWindowAndGeneration` | `own-20`: 2 pages at an alignment of 4, high, in a window off its pages; a failed zeroing, then another owner's allocation and its release | The highest aligned range in the window; `ZeroFailed`; the same range with generation 1 and its receipt, the extents after it; one free extent after the release | "the frozen vectors hold" |
| [PGT-R09](requirements.md#pgt-r09) | Rejected: `ReleaseRefusesStaleReceipt` | `own-10`: the release of a receipt of generation 1 after the page was released and taken again | The new receipt of generation 2, and `InvalidAllocation` | "the frozen vectors hold" |
| [PGT-R10](requirements.md#pgt-r10) | Accepted: `ReservationPublishesAfterZeroing` | `own-23`: a reservation, an allocation outside it, the zeroing, the validation and the publication, both releases | The reservation held at once, not zeroed; the packet; the receipt; all bytes free at the end | "the frozen vectors hold" |
| [PGT-R10](requirements.md#pgt-r10) | Rejected: `CancelRefusesAttemptedReservation` | `own-24`: the cancel of a reservation after a failed zeroing | The reservation attempted with 1 failure, and `ZeroFailed` with the reservation returned | "the frozen vectors hold" |
| [PGT-R11](requirements.md#pgt-r11) | Accepted: `CapacitiesAtTheirLimits` | A direct map that needs exactly 80 tables; a table of 28 banks with 132 exclusions; an allocation of 1 page at its 160 extents | 80 tables in use; the statistics of 160 extents; the page of an extent of exactly one page | "a direct map that needs exactly 80 tables succeeds", "a page ownership table at exactly 160 extents works", "an initialization with 132 exclusions succeeds" |
| [PGT-R11](requirements.md#pgt-r11) | Rejected: `CapacitiesRefuseOneMore` | A direct map that needs 81 tables; a reservation that needs a 161st extent; a 133rd exclusion | `OutOfTables`, `MetadataExhausted` and `MetadataExhausted` | "one that needs 81 is refused", "one more extent is refused", "one with 133 is refused" |
| [PGT-R12](requirements.md#pgt-r12) | Accepted: `CopyIsPrivateAndOrdered` | `pt-07`: a source of three pages and a target with a page of its own | The plan of the copy, step by step; 6 tables in use and the source's descriptors; later writes to either set leave the other unchanged | "the frozen vectors hold, and the plan of the copy equals the order of the contract" |
| [PGT-R12](requirements.md#pgt-r12) | Rejected: `CopyRefusesPrivateLeaf` | `pt-12`: a source with a `KernelPrivateReadWrite` leaf | `InvalidDescriptor` | "the frozen vectors hold" |

### Witnesses

[`Witnesses/TableSets.lean`](../../../../verification/Krepi/Spec/PageTables/Witnesses/TableSets.lean)
and
[`Witnesses/PageOwnership.lean`](../../../../verification/Krepi/Spec/PageTables/Witnesses/PageOwnership.lean):
the theorems that witness that the specification is not vacuous
([specifications](../../../formal-verification.md#specifications)), split
into two modules along the seam of the entry table. For each frozen function
of rows 107 to 117, one input on which it succeeds, with the value that it
gives; for each error that the contract gives that function, one input on
which it fails with that error. The functions are counted, not the rows: 28,
of which 17 can fail. The value type `Kind` of row 107 is read through
`descriptor`, whose witness takes every kind, and has no witness of its own;
the adapter of row 118 is excluded. The expected values are literals worked
out from the contract, never computed by the specification. Where the
contract gives one error for several rules, the witness of that error is a
conjunction with one input for each rule, for instance the eight rules of
`TableBacking` of `clone_kernel_from`.

The modules import the specification alone, `TableSets` the module `Boot`
and `PageOwnership` the module `Ownership`, so they write their inputs
themselves: the pools of the sets entry by entry, as the tests of the
prototype write storage directly; the layouts by their ranges; the tables of
page ownership as literals of their state; and the boot memory maps as the
values that `MemoryPlan::all_ram` of the fdt specification gives, which
`plansBuilt` states. A set or a table of page ownership is an input as its
type admits it, any pool with any record and any counter, as `pt-08`,
`pt-13` and `own-01` write them; the boot memory map of `direct_map` is an
input as the fdt entries build it, since the fdt contract gives it no other
constructor. A success of a write entry on a set is stated as its record of the
tables in use and its plan (`outcome`): the write phase changes no table of
the pool ([widths and quantifiers](#widths-and-quantifiers)), and the
kernel compares two pools of 512 entries a table too slowly for a witness.

Each witness is an equation, `f x = .ok v` or `f x = .error e`, or for a set
`outcome (f x) = .ok v`, and the module proves it by `decide +kernel`, with
a local instance that decides the equality of `Except` values and that no
statement mentions; `Tables::new` is stated for every storage and proved by
`rfl`. The modules use no `native_decide`, `sorry` or axiom. `TableSets`
builds in 5 to 11 s and `PageOwnership` in about 3 s, no declaration of
either above 1 s.

| Line | Functions | Success | Rejection | Priority pairs | Unreachable branches |
| --- | ---: | ---: | ---: | ---: | ---: |
| 107 | 9 | 9 | 10 | 8 | 0 |
| 108 | 3 | 3 | 4 | 10 | 1 |
| 109 | 1 | 1 | 5 | 6 | 0 |
| 110 | 1 | 1 | 5 | 6 | 0 |
| 111 | 1 | 1 | 4 | 4 | 0 |
| 112 | 2 | 2 | 10 | 15 | 2 |
| 113 | 1 | 1 | 4 | 5 | 0 |
| 114 | 2 | 2 | 7 | 5 | 2 |
| 115 | 3 | 3 | 9 | 7 | 2 |
| 116 | 2 | 2 | 7 | 5 | 0 |
| 117 | 3 | 3 | 3 | 2 | 0 |
| Total | 28 | 28 | 68 | 73 | 5 statements, all planned |

The two statements of the page ownership table each cover a branch of
rows 114 and 115, so the column counts them at both lines.

**Error priority.** For each step of the error orders of the contract, one
more witness gives an input that breaks a rule of that step and a later
rule of the same entry, and states the error of the step; each is a
conjunction over the entries that have both rules, so the 73 pairs are 33
theorems. The orders are those of
[errors of table sets](contract.md#errors-of-table-sets) for the entries on
one address, `priorityStep1` to `priorityStep6`, and for `kernel_map` and
`direct_map`, `priorityMapStep1` to `priorityMapStep8`; that of
[copying the kernel tables](contract.md#copying-the-kernel-tables),
`priorityCloneStep1` to `priorityCloneStep7`; and those of
[page ownership](contract.md#page-ownership) for `Ownership::new`,
`priorityNewStep1` to `priorityNewStep4`, for `choose` and `reserve`,
`priorityChooseStep1` to `priorityChooseStep5`, and for the receipts of
`publish`, `cancel`, `release` and `validate`, `priorityReceiptStep1` to
`priorityReceiptStep3`. Two rules of one error are not told apart, so a step
is paired with the next rule of another error: the pool of an entry on one
address with its physical address, or with `NotMapped` where it has none;
the walk with `OutOfTables` or `NotMapped`. `priorityMapStep6` and
`priorityMapStep8` take the leaves and the ranges in address order, a range
of `kernel_map` given later in its layout but lower in address being checked
first; `priorityCloneStep6` takes the walk of the copy entry by entry, each
table under its entry before the next entry. The last check of each order,
`OutOfTables`, the record of tables not reached, the capacity of the
extents of `Ownership::new`, `MetadataExhausted` and `OutOfMemory` of the
scan and `InvalidAllocation`, has no later rule; the two rules of
`PhysRange::new` cannot be broken by one input, since a range of length 0
ends at its start. With the earlier rule repaired, each of these inputs
fails with the error of the later rule, so each witness tells the order of
the contract from the reverse one.

`assignRechecks` gives `assign` choices that `choose` does not give on the
table, outside the requirement of its row, and states the three refusals of
the checks that `assign` makes after the zeroing, in the order of those of
`choose` ([check and execute](contract.md#check-and-execute)). The table
counts the one error that the row of `assign` gives it, `ZeroFailed`; the
three refusals are those of choices outside its requirement, which a choice
of `choose` on the same table never meets (`TakeAcceptsChoice`).

An error branch that no input of its entry reaches has no witness. For each,
a planned proposition states the fact that keeps the entry from it, and a
theorem of the same name with a lower-case first letter below
`Krepi.Proofs.PageTables.Witnesses` proves it; the error of the branch is
witnessed through another branch of the same entry.

| Statement | Branch | Reason |
| --- | --- | --- |
| `DirectMapRangesOnPages` | `direct_map`: a usable range off a page, `Alignment` | The managed banks and the reservations of a boot memory map that the fdt entries build are whole pages, so are its usable ranges; the `Alignment` of `direct_map` is that of `base` |
| `DirectMapRangesApart` | `direct_map`: a leaf that an earlier usable range shares, `AlreadyMapped` | Those usable ranges are disjoint parts of disjoint banks; the `AlreadyMapped` of `direct_map` is that of the walk |
| `CloneTargetWidthChecked` | `clone_kernel_from`: the width at the check of the target pool, `AddressWidth` | It is the width that the check of the source pool accepted |
| `TakeAcceptsChoice` | `assign` and `reserve`: the checks of the taking of a choice of `choose` on the same table, `GenerationExhausted`, `OutOfMemory` and `MetadataExhausted` | On a table that the entries build the free extents are disjoint, so the extent that holds the chosen range and its room are those that `choose` found, and the counter is unchanged (`Built`) |
| `HighPlacementNoOverflow` | `choose` and `reserve`: the rounding of a high placement, `AddressOverflow` | Its start is the end of a part less the request, rounded down, so its range ends inside an extent; the rounding overflows only for a low placement |

The two variants of the specification that reject every input or accept
every input are refuted in each module by two theorems, each a conjunction
over the functions of its rows that can fail, 9 of the table sets and 8 of
the page ownership table: `notAlwaysRejecting` gives an input on which each
succeeds, from the success witnesses, and `notAlwaysSucceeding` an input on
which each fails, from the rejection witnesses. The other 11 functions
return a value for every input and have no error. Every success, rejection
and priority witness is proved in its module; none is planned.

## Design decisions

### Readings of the contract

Where the contract leaves a rule open, the specification takes the reading
below and states it. Lines are those of the contract at commit `6a15f41`,
before it stated any of these readings; a row whose reading the contract now
states names the section that states it, and the other rows remain readings
of the specification. Where the contract defers to the prototype tree, which
it does for the arguments of the entries ("as the prototype does", lines 613
and 614), the reading follows the prototype and names the place.

| Reading | Contract | Basis |
| --- | --- | --- |
| The first checks give `Alignment` for a virtual address or a `base` off its boundary, then `AddressWidth` for an address outside the region or `bits` outside 32 to 48, then `TableBacking` for the pool: the three errors in the stated order, each with the rules of its row of the error table | [Errors of table sets](contract.md#errors-of-table-sets), lines 341 to 343 and 349 to 351; now stated in [Errors of table sets](contract.md#errors-of-table-sets) | The order lists the three errors "in this order" and the error table gives each rule its error |
| `base` and `source_base` are 64-bit and `bits` is 8-bit | [Table pool](contract.md#table-pool), lines 612 to 614; now stated in [Table pool](contract.md#table-pool) | "as the prototype does": the prototype takes `base: u64` and `pa_bits: u8` (`src/arch/aarch64/paging.rs:248-255` at the prototype commit) |
| The record of the tables in use is their number, and the tables in use are those of the indices below it | [Terms](contract.md#terms), lines 28 to 30; [Table pool](contract.md#table-pool), lines 616 to 619; [Determinism](contract.md#determinism), lines 732 to 734; the rows of `pt-08` and `pt-13`, lines 942 and 947; now stated in [Terms](contract.md#terms) | A new table is the one of the lowest free index, a table returns to the pool only through `reset` and through the copy, which gives the target the indices of the source, so the tables in use stay a prefix; `pt-08` counts one more table in use and `pt-13` has a record of 0 |
| The region and the capacity are parameters of the type of a set | [Terms](contract.md#terms), lines 28 to 30; [Copying the kernel tables](contract.md#copying-the-kernel-tables), lines 250 to 252 | A set never holds addresses of the other region, and the copy takes two sets of one region and one capacity with no error for others |
| `Tables::new` takes the storage as it is and sets the record to 1, and `reset` accepts any record, also 0, its plan zeroing the tables below both the record and `N` | [After mapping](contract.md#after-mapping), lines 302 and 303; [Check and execute](contract.md#check-and-execute), lines 684 to 686; the row of `pt-13`, line 947; now stated in [Check and execute](contract.md#check-and-execute) | Both check nothing and rely on their caller; `pt-13` resets a set whose storage and record are all 0 |
| When a page needs a new level 2 and a new level 3 table, the level 2 table takes the lower free index | [Table pool](contract.md#table-pool), line 616; [Determinism](contract.md#determinism), lines 732 and 733; now stated in [Determinism](contract.md#determinism) | "in the order in which its plans first need them": the walk needs the level 2 table first; the table descriptors of `pt-07` depend on it |
| The plan of `map_page` with one new table is `Zero(t3)`, `Store(t3, ...)`, `Fence`, `Store(t2, ...)`, `Sync`; that of `map_block` with a new table `Zero(t2)`, `Store(t2, ...)`, `Fence`, `Store(root, ...)`, `Sync`; without a new table, a `Store` and `Sync` | [Write plans and publication](contract.md#write-plans-and-publication), lines 380 to 389 | The rule of new tables and of new entries, with the plan of two new tables as the contract writes it |
| The plan of `reset` zeroes the tables in index order; that of the copy zeroes the target's tables in use in index order and then stores the valid entries of the source by table index and, in each table, by entry index, with no `Fence`, and `Sync` last | [Write plans and publication](contract.md#write-plans-and-publication), lines 402 to 413; now stated in [Write plans and publication](contract.md#write-plans-and-publication) | The contract fixes the `Zero` steps before the stores and `Sync` last, and that no CPU walks the target before its root is installed, so the order among the stores is not observable; index order is the order of the contract's wording |
| The walk of `map_page`, `unmap_page`, `lookup_page` and `lookup_block` reads an entry by its bits 1 and 0 and its address bits 12 to 47: an entry with bits 1 and 0 `0b00` is free; a valid root entry, and a valid level 2 entry other than a block (`0b01`), is a table descriptor, `TableBacking` when its address is not that of a table in use; at level 3, a valid entry takes the slot and is a page leaf when bits 1 and 0 are `0b11` | [Descriptors and attributes](contract.md#descriptors-and-attributes), lines 145 to 153; [Errors of table sets](contract.md#errors-of-table-sets), lines 343 and 345 to 346 | The contract gives the forms that the component writes; a set that the entries built holds no other entry, and the walk must still return for a set whose storage a test wrote |
| `lookup_block` takes a block slot, so a virtual address off 2 MiB is `Alignment`, and it reads the root entry and the level 2 entry only: a level 2 entry that is not a block is `NotMapped`, also a table descriptor | [Errors of table sets](contract.md#errors-of-table-sets), lines 341 and 346; [Work bounds](contract.md#work-bounds), lines 702 to 704; now stated in [Errors of table sets](contract.md#errors-of-table-sets) and [Work bounds](contract.md#work-bounds) | "for a block, `v` or `p` not of 2 MiB" and "`lookup_block` at a block slot without a block" |
| `map_block` refuses any valid level 2 entry with `AlreadyMapped`, without reading a level 3 table under it | [After mapping](contract.md#after-mapping), line 305; [Errors of table sets](contract.md#errors-of-table-sets), line 345 | A valid level 2 entry is a block, so a page of the block is in $\mathrm{dom}\,M$, or a table, so $v \in P$: the slot is not free of tables |
| `descriptor(kind, address)` takes the address in bits 12 to 47 and drops its other bits | [Descriptors and attributes](contract.md#descriptors-and-attributes), lines 150, 151, 167 and 168; now stated in [Descriptors and attributes](contract.md#descriptors-and-attributes) | "every other bit of a leaf is 0", and the function has no error; the entries check the address before they build a descriptor |
| In the copy, a valid entry of the source at level 1 or 2 that is not a table descriptor without an attribute bit is `InvalidDescriptor`: one with an attribute bit, a block, or bits 1 and 0 `0b10`; the root is reached when the walk starts, so a table descriptor that points at it points at a table already reached | [Copying the kernel tables](contract.md#copying-the-kernel-tables), lines 268 to 279; now stated in [Copying the kernel tables](contract.md#copying-the-kernel-tables) | The order names "a table descriptor with an attribute bit, or a block in its place", and the walk is "from its root" |
| In the copy, an entry of the source with bits 1 and 0 `0b00` is skipped and not copied, also when its other bits are not 0, so the target's entry stays 0 | [Descriptors and attributes](contract.md#descriptors-and-attributes), lines 145 and 146; [Write plans and publication](contract.md#write-plans-and-publication), lines 404 to 411 | An invalid descriptor is one whose bits 1 and 0 are `0b00`, and the copy stores "every valid entry" |
| The checks of `base` and `bits` of the source come before those of the target, so a `bits` outside 32 to 48 is reported with the source's checks, after its `Alignment` | [Copying the kernel tables](contract.md#copying-the-kernel-tables), lines 268 to 270; now stated in [Copying the kernel tables](contract.md#copying-the-kernel-tables) | `bits` is the width of both pools |
| `PhysRange::new` gives `InvalidRange` for a length of 0 before it adds; the order of its two rules is not observable | [Terms](contract.md#terms), lines 67 to 71; the row of `own-02`, line 890 | A range of length 0 ends at its start, which fits in 64 bits |
| `PhysRange::contains` and `overlaps` take a range, and compare the address sets | [Terms](contract.md#terms), lines 67 to 71; the row of `own-02`, line 890 | The row asks whether a range contains and overlaps ranges |
| $M$ holds a page of a set where the walk reaches a page descriptor whose bits are those of a kind, or the block descriptor of `ReadWrite`; a page of a block maps to the physical page at its offset in the block | [Terms](contract.md#terms), lines 39 to 43; [After mapping](contract.md#after-mapping), line 305 | The contract defines $M$ on the pages of the region; the block row maps $v + i$ to $p + i$ |
| `kernel_map` takes the lower kernel set and `direct_map` the direct map's set, as sets of the lower and the upper region | [Terms](contract.md#terms), lines 47 to 51; [Kernel mappings](contract.md#kernel-mappings), lines 222, 223 and 225 to 228 | The kernel tables are a lower set, which maps the image at its physical addresses, and the direct map's set in the upper region |
| A range of a layout is a physical range, `PhysRange`, mapped at its physical address; the at most 16 ranges and the four kinds of a layout are rules of its type, with no error | [Kernel mappings](contract.md#kernel-mappings), lines 222, 223, 225 to 228, 236 and 237; [Terms](contract.md#terms), lines 67 to 71; [Work bounds](contract.md#work-bounds), line 710; now stated in [Kernel mappings](contract.md#kernel-mappings) | The contract states both rules of the layout that the board gives and gives no error for them; the image runs at its load address, so a range is one of physical addresses |
| A guard page is named by an address in it, and a range covers it when the range holds that address; `kernel_map` checks the guards against the ranges and not against the set, and writes no entry of a guard page | [Kernel mappings](contract.md#kernel-mappings), lines 233 to 235; [After mapping](contract.md#after-mapping), line 308; [Errors of table sets](contract.md#errors-of-table-sets), line 345; now stated in [Kernel mappings](contract.md#kernel-mappings) and [After mapping](contract.md#after-mapping) | A range on page boundaries holds an address of a page exactly when it holds the page; "every guard page of $L$ stays outside $\mathrm{dom}\,M'$" is a rule of what the plan writes, since the error table refuses only a range that covers a guard |
| `kernel_map` and `direct_map` check their ranges sorted by the start, ranges of one start in the order of their input, and for each the alignment of its ends, then its width, then the free slots of its leaves one by one in address order: the walk of the leaf, `TableBacking` and then `AlreadyMapped`, and then `AlreadyMapped` for a leaf that an earlier range covers, for `kernel_map` also for a guard page; then `OutOfTables` for the whole plan | [Errors of table sets](contract.md#errors-of-table-sets), lines 341, 342, 345 and 349 to 355; [Kernel direct map](contract.md#kernel-direct-map), lines 447, 457 and 458; [Check and execute](contract.md#check-and-execute), lines 681 to 683; now stated in [Errors of table sets](contract.md#errors-of-table-sets) | The order gives alignment, width and the free slots for each range in address order, the walk's `TableBacking` before `AlreadyMapped`, and the tables last; a page of an earlier range is not free once the plan maps it, which makes two ranges that share a page `AlreadyMapped` |
| The width of a range is its end against $2^{39}$ and against $2^{\mathrm{bits}}$, one `AddressWidth` before any leaf of the range | [Errors of table sets](contract.md#errors-of-table-sets), line 342; [Kernel direct map](contract.md#kernel-direct-map), lines 440 to 443, 457 and 458; now stated in [Errors of table sets](contract.md#errors-of-table-sets) | A usable range that ends above $2^{39}$ has no direct address, and a range on page boundaries holds a page at or above $2^{\mathrm{bits}}$ exactly when it ends above it |
| The new tables of `kernel_map` and `direct_map` take the lowest free indices in the order in which the walk of the leaves, in address order, first needs them, a level 2 table before the level 3 tables under it | [Table pool](contract.md#table-pool), line 616; [Determinism](contract.md#determinism), lines 732 and 733; now stated in [Determinism](contract.md#determinism) | As for `map_page`: the walk needs the level 2 table first |
| The plan of `kernel_map` and `direct_map` builds the tables bottom up: under a new level 2 table, each new level 3 table with its pages, then the level 2 table with its entries in index order, then one `Fence` and the store into the root; a new level 3 table under a level 2 table of the set is followed by one `Fence` and the store of its table descriptor; `Sync` ends the plan. "One `Fence` for each table descriptor" of the work bounds is read as a bound: a `Fence` comes before each store that makes new tables reachable from a table of the set, so there is at most one for each table descriptor | [Write plans and publication](contract.md#write-plans-and-publication), lines 372 to 377, 380 to 389 and 414 to 416; [Work bounds](contract.md#work-bounds), lines 710 to 718; [Determinism](contract.md#determinism), lines 735 to 737; now stated in [Write plans and publication](contract.md#write-plans-and-publication) and [Work bounds](contract.md#work-bounds) | The rule of new tables writes a table completely before the store that makes it reachable, a table under another new table first, and the plan of two new tables, lines 384 to 386, has one `Fence` for two table descriptors; with that rule the plan of one leaf is that of `map_page` or `map_block` |
| `Sync` ends every plan of `kernel_map` and `direct_map`, also that of a map with no leaf | [Write plans and publication](contract.md#write-plans-and-publication), lines 387 to 389; now stated in [Write plans and publication](contract.md#write-plans-and-publication) | A plan whose last store makes an entry valid ends with `Sync`; the copy ends with `Sync` in the same way, and with no store the `Sync` is harmless |
| `direct_map` takes the boot memory map as a value of the fdt specification, any value of its type, and maps its usable ranges, `MemoryPlan.availableRanges` | [Terms](contract.md#terms), lines 52 to 57 and 64 to 66; [Kernel direct map](contract.md#kernel-direct-map), lines 444 to 456 | The contract takes the map as a value that it reads and never changes, and the usable ranges hold no reservation, hole or unmanaged RAM |
| The counts of a direct map, its bytes, blocks and pages, are those of its plan: a block for each `Store` of a block descriptor and a page for each `Store` of a page descriptor | [Entry points](contract.md#entry-points), line 107; [Work bounds](contract.md#work-bounds), lines 714 to 718; the rows of `dm-01` and `dm-02`, lines 966 and 967; now stated in [Legacy test vectors](contract.md#legacy-test-vectors) | The entry returns a plan; the vectors assert the counts of the map that it writes, and the plan has one `Store` for each block and page |
| The capacities of the kernel tables, 80 and 32, are constants, and the entries are stated for every capacity `N` | [Table pool](contract.md#table-pool), lines 632 to 634 and 646 to 648 | The vectors build direct maps in pools of 2 to 16 tables |
| The state of the page ownership table holds the managed banks in address order beside its extents, exclusion records, generation counter and arena, and each extent names its bank | [Terms](contract.md#terms), lines 58, 83 and 84; [Page ownership](contract.md#page-ownership), lines 530 and 566 to 573; [State fields](contract.md#state-fields), line 758; its banks now stated in [State fields](contract.md#state-fields) | An extent is a range of one bank, a released extent merges only within its bank, and `owner` tells a page of a managed bank in no extent, so the table knows its banks; they never change after the initialization |
| The capacities of the table, 160 extents and 132 exclusion records, are constants, `EXTENTS` and `EXCLUSION_RECORDS`, and the entries are stated for every extent capacity `E` and exclusion capacity `X` | [Page ownership](contract.md#page-ownership), lines 581 to 592; the rows of `own-01`, `own-03`, `own-05`, `own-08`, `own-16`, `own-17`, `own-21` and `own-22`, lines 884, 891, 893, 896, 904, 910, 914 and 915 | The vectors build tables of 0 to 128 extents |
| `Ownership::new` checks no bound of 32 banks or of 16 GiB: the boot memory map gives at most 32 banks of at most 16 GiB together, and the entry is stated for every list of banks | [Page ownership](contract.md#page-ownership), lines 500 to 516, 581 and 582; [Work bounds](contract.md#work-bounds), lines 719 to 721; now stated in [Page ownership](contract.md#page-ownership) | The checks of the initialization name no error for either bound, which the capacity paragraph gives as what the boot memory map admits, and the [boot memory map](../../boot-platform/fdt/contract.md#boot-memory-map) of the fdt component refuses more |
| The extents that the banks, split by the exclusions, need are counted once, after every exclusion: the maximal runs of the pages of each bank that no exclusion touches | [Page ownership](contract.md#page-ownership), lines 503 to 516 | The rule compares the extents that the split banks need with the capacity; an exclusion that removes a whole run lowers the count |
| `owner` takes an address and gives the owner of the page that holds it, and none for a page of no managed bank | [Page ownership](contract.md#page-ownership), lines 570 to 573; [Terms](contract.md#terms), line 58; [Abstract mapping](contract.md#abstract-mapping), lines 290 to 292; now stated in [Page ownership](contract.md#page-ownership) | $O$ is defined on the managed pages, and the entry has no error |
| `choose` compares the bytes of the request and those of its alignment, `pages` and `alignment` times 4 KiB, each with $2^{64}$ (`AddressOverflow`); in the scan, a free extent whose start rounded up, or the end of whose range, is $2^{64}$ or more gives `AddressOverflow` when the scan reaches it, so an extent earlier in the scan that holds the range gives it first; a high placement rounds down and does not overflow | [Page ownership](contract.md#page-ownership), lines 524 to 538; now stated in [Page ownership](contract.md#page-ownership) | The order puts the rounding after the generation and before the outcome of the scan, and the first broken rule wins; a range never ends beyond 64 bits ([Terms](contract.md#terms), lines 67 to 71) |
| Taking a range from a free extent needs one more extent for each part of the extent before and after the range, 0 to 2, and the capacity has `E` less the extents in use free | [Page ownership](contract.md#page-ownership), lines 527 to 529, 510 and 583 to 585 | The table records free and held extents together, and the excluded pages take no extent |
| `assign` checks the outcome of the zeroing first (`ZeroFailed`), then the requirement that the choice is one of `choose` under the same token, with the checks of `choose` that its write repeats: the counter exhausted (`GenerationExhausted`), the range not inside one free extent (`OutOfMemory`), the extents (`MetadataExhausted`); a choice of `choose` on the same table passes them | [After ownership](contract.md#after-ownership), line 321; [Page ownership](contract.md#page-ownership), lines 543 to 546; [Check and execute](contract.md#check-and-execute), lines 689 to 694; now stated in [Check and execute](contract.md#check-and-execute) | The entry counts the extents in its checks before its write; the contract fixes no result for a choice that breaks the requirement, so the specification refuses it and writes nothing, and a refinement takes the requirement as a premise |
| The generation counter is the generation of the next allocation or reservation, or exhausted: `assign` and `reserve` give it and advance it, the one that gives $2^{64} - 1$ leaves it exhausted, and `choose` and `reserve` then refuse with `GenerationExhausted` | [After ownership](contract.md#after-ownership), lines 321 and 322; [Page ownership](contract.md#page-ownership), lines 535 and 567 to 569; the row of `own-01`, line 884 | "$g' = g + 1$, or exhausted after $2^{64} - 1$": the allocation of `own-01` gets the generation `0xffffffffffffffff` and the next request is refused |
| `Reservation::initialized` gives the packet with the count of failures of the reservation, or the reservation marked as attempted with its count increased by one; the count is 64-bit and stays at $2^{64} - 1$ once there | [Page ownership](contract.md#page-ownership), lines 547 to 552; [After ownership](contract.md#after-ownership), lines 331 and 332; now stated in [Page ownership](contract.md#page-ownership) | The function has no error and changes only the value that it consumes; the count reaches $2^{64} - 1$ only after as many failed zeroings |
| `validate` takes a receipt or an initialized packet and makes the checks of `release` with the state that the value names, published for a receipt and reserved for a packet | [Page ownership](contract.md#page-ownership), line 570; the rows of `own-23` and `own-25`, lines 921 and 923; now stated in [Page ownership](contract.md#page-ownership) | `own-23` validates a packet, whose pages are reserved, and expects it to pass; `own-25` validates one at another arena |
| A value names a held range of exactly its generation and state when one extent is its range, held by the owner identity with its generation in that state | [After ownership](contract.md#after-ownership), lines 323 to 325; [Page ownership](contract.md#page-ownership), lines 490 and 558 to 566 | The pages of one holder generation form one range in one bank, so one extent, which no merge joins since only free extents merge |
| `cancel` merges the pages that it frees with the free extents next to them in the same bank, as `release` does | [Page ownership](contract.md#page-ownership), lines 553 to 556 and 566 and 567; the row of `own-28`, line 926; now stated in [Page ownership](contract.md#page-ownership) | After the two cancels of `own-28` the free extents are those from before |
| A refused packet or reservation is returned with the error, unchanged | [After ownership](contract.md#after-ownership), line 324; [Page ownership](contract.md#page-ownership), lines 558 to 566 | "a refused packet is returned to its caller" |
| The shared fields are written only by transactions that take the evidence of their owner: the boot CPU while the MMU is off, for both kernel sets; then the token of the kernel tables, to fill an invalid entry of the lower kernel set with `map_page` and to read the set as the source of a copy; the token of the page ownership table for every entry on the table, its read entries and `Ownership::new` included; no transaction writes the direct map's set once the MMU is on | [State fields](contract.md#state-fields), lines 755 to 758; [Terms](contract.md#terms), lines 90 to 93; the [state fields](../address-space/contract.md#state-fields) of the address-space contract | The rows name these owners; a token is held from the first check of an entry to the end of the execution of its plan, and a copy holds the token of the kernel tables for its source |
| The allocation of one step, `choose`, the caller's zeroing and `assign`, is one transaction under the token of the page ownership table | [After ownership](contract.md#after-ownership), line 321; [Page ownership](contract.md#page-ownership), lines 543 to 546 | "taken under the same token" |
| The well-formedness of the page tables is the conjunction of the formats of the entries that the component writes, the zero storage of the tables not in use and the reach of every table in use by exactly one table descriptor | [Descriptors and attributes](contract.md#descriptors-and-attributes), lines 145 to 153, 167 and 168; [Copying the kernel tables](contract.md#copying-the-kernel-tables), lines 255 and 256; [Abstract mapping](contract.md#abstract-mapping), lines 284 and 285; [Table pool](contract.md#table-pool), lines 611, 612 and 620; the reach of the tables in use now stated in [Abstract mapping](contract.md#abstract-mapping) | The contract names no rule of well-formedness; these are the rules of the tables that its entries write, and the copy checks the same of its source |
| "Exactly one owner" is stated on the extents: the owners that the table records for a managed page, the holding of each extent that holds it and the first owner of the exclusion records that touch it, are one | [Page ownership](contract.md#page-ownership), lines 489, 503 to 510 and 570 to 573 | The owner function $O$ is the extent that holds a page or, for a page in no extent, its exclusion records; one owner means that a page is in one extent and touched by no exclusion, or in none and touched |
| The pages of one holder generation are the pages of one held extent: the invariant states that the pages whose owner has the generation of a held extent are exactly its pages | [Page ownership](contract.md#page-ownership), lines 490, 491 and 558 to 566; [After ownership](contract.md#after-ownership), lines 323 to 325; now stated in [Page ownership](contract.md#page-ownership) | A receipt names a held range of exactly its generation, and the checks of `release`, `publish` and `cancel` find one extent; one extent is one range in one bank |
| The generations of the holders are at least 1 and below the counter | [Page ownership](contract.md#page-ownership), lines 567 to 569; [Determinism](contract.md#determinism), line 746; now stated in [Page ownership](contract.md#page-ownership) | "Never reused": the counter gives the next generation, which no holder may have |
| One free extent for each free run is stated on the extents: no free extent ends where a free extent of its bank starts | [Page ownership](contract.md#page-ownership), lines 566, 567, 585 and 586; now stated in [Page ownership](contract.md#page-ownership) | With one owner for every managed page, this makes each free extent a maximal run of free pages, and the free extents of `stats` the free runs |
| The free and held pages of the table of the kernel root are compared with the usable ranges of the boot memory map that it was built from, a parameter of the invariant; the boot wiring gives `Ownership::new` the managed banks of that map and one exclusion for each span of its boot storage and each firmware reservation | [Page ownership](contract.md#page-ownership), lines 492 to 495, 497 and 498; [Terms](contract.md#terms), lines 67 to 71 | The table does not hold the boot memory map; "the boot wiring converts the spans of the boot memory map into them" |
| The direct map's set maps `DIRECT_BASE \| pa` to `pa` below $2^{39}$ as `ReadWrite`, an invariant of the shared state that only `direct_map` writes | [Terms](contract.md#terms), lines 50 and 51; [Kernel direct map](contract.md#kernel-direct-map), lines 444 to 446 and 457 | The definition of the direct map |
| "The firmware, image and boot storage pages never change owner" is a statement of two states, which the rows of `After ownership` give | [Page ownership](contract.md#page-ownership), line 495; [After ownership](contract.md#after-ownership), lines 313 to 316 and 318 to 325 | Each row changes $O$ only on pages that are free or held |
| In the row of `direct_map`, "$G'$ and $P'$ add the slots of those pages" is read as $G'$ adding the 1 GiB slots of the pages and $P'$ the 2 MiB slots of the pages mapped as pages | [After mapping](contract.md#after-mapping), lines 305 and 309; now stated in [After mapping](contract.md#after-mapping) | A block takes no level 3 table, as the row of `map_block` states with $P' = P$ |
| A row of `After mapping` or `After ownership` is stated for a success of its entry on a state that keeps the invariants: the success establishes its `Requires` column and its `After` column; a requirement that the entry does not check, the zero storage of `Tables::new`, is a hypothesis, and one of the hardware, no `TTBR` or TLB holding a set, is not modelled; a failure carries no state and no plan, by the type of the result | [After mapping](contract.md#after-mapping), lines 296 to 298 and 300 to 309; [After ownership](contract.md#after-ownership), lines 313 to 316 and 318 to 325 | "A failed entry returns an error, changes nothing and returns no plan" |
| The statements of `assign` take its requirement, a choice of `choose` on the same table, as a hypothesis | [After ownership](contract.md#after-ownership), line 321 | The checks of `assign` repeat those of `choose` that its write needs, not that the range lies on page boundaries, which every choice of `choose` does |
| W^X counts the lower kernel set, the direct map's set and a copy of the lower kernel set, on the states that the transactions reach from the boot under three rules that no entry checks: `kernel_map` and `direct_map` run once each; the `ReadExecute` ranges of the layout lie in a span of the boot storage of a well-formed boot memory map; a fill of the lower kernel set maps an executable kind only at a page of the text and the text only with `ReadExecute` | [Descriptors and attributes](contract.md#descriptors-and-attributes), lines 193 to 195 and 197 to 213; [Entry points](contract.md#entry-points), line 107; [State fields](contract.md#state-fields), line 755; its second and third rules now stated in [Descriptors and attributes](contract.md#descriptors-and-attributes) | The three reasons of W^X rest on the layout and the fills, which the contract states for the image and its text; it gives no rule for the frame and kind of a fill |
| A guard page is not part of the state of a set: `kernel_map` writes no entry of a guard page of its layout, and a later fill of the lower kernel set does not see the guards | [Descriptors and attributes](contract.md#descriptors-and-attributes), lines 181 to 184; [After mapping](contract.md#after-mapping), line 308; now stated in [Descriptors and attributes](contract.md#descriptors-and-attributes) | "No entry of this page writes a valid descriptor where a guard is": `map_page` takes no guard, so the rule binds its caller |

### Vector notation

The vector file holds the cases of
[legacy test vectors](contract.md#legacy-test-vectors), one line for each
call of an entry that a test makes with the output that it asserts, in the
order of the test. The entries of a table set are calls on state that earlier
calls built, so an input holds the whole test up to the case:

| Field | Meaning |
| --- | --- |
| `sets=` | The sets of the test, `-` for none, `<name>:<region>:<N>` joined by `,`: a set that `Tables::new` makes on zero storage, of region `lower` or `upper` and capacity `N`; `<name>:<region>:<N>:<record>` is zero storage with that record of tables in use |
| `memory=` | Only in a test of the direct map: the boot memory map that the test builds, `MemoryPlan::new` with the fields `window=`, `ram=`, `boot=` and `firmware=` after it, or `MemoryPlan::all_ram` with the last three, which the fdt specification builds from them. A span is `<start>+<size>`, a list of spans is joined by `,`, `-` for none, and a firmware reservation is its span, `/` and its flag, `no-map`, `reusable` or `none`, as in the [notation](../../boot-platform/fdt/contract.md#notation) of the fdt contract |
| `do=` | The earlier calls and writes of the test, `-` for none, joined by `;`; a write entry that succeeds has its plan executed |
| `call=` | The call of the case: `map_page(set,v,p,kind,base,bits)`, `map_block(set,v,p,base,bits)`, `unmap_page(set,v,base,bits)`, `lookup_page(set,v,base,bits)`, `lookup_block(set,v,base,bits)`, `used(set)`, `reset(set)`, `clone_kernel_from(target,source,source_base,base,bits)`, `descriptor(kind,address)` or `direct_map(set,base,bits)`, the direct map of the boot memory map of `memory=` in an upper set |
| `ask=` | What the test asserts of the state after the call, `-` for nothing, joined by `;`: `unchanged(set)`, whether the set, its pool and its record, is the one from before the call; `zero(set)`, whether every entry of its pool is 0; `entry(set,table,index)`, an entry |

The two writes of a test, which are not entries, are
`set_entry(set,table,index,descriptor)`, which writes an entry of the
storage, and `set_used(set,record)`, which writes the record; `pt-08` uses
them as its test writes the source directly. The output of a call is `ok`,
followed by its fields, or `err=<error>`: `unmap_page` gives `page=`,
`lookup_page`, `lookup_block` and `descriptor` give `descriptor=`, `used`
gives `used=`, and `direct_map` gives `bytes=`, `blocks=` and `pages=`, the
counts of its plan (`Plan.counts`); then each item of `ask=` gives
`<item>=<value>`.

These forms stand for calls of a test that the vector file does not write
one by one:

| Form | Meaning | Vectors |
| --- | --- | --- |
| `map_blocks(set,v,p,count,base,bits)` | The first `count` calls of the loop of `pt-17`: `map_block(set,v+0x200000*i,p+0x200000*i,base,bits)` for `i` from 0 to `count - 1`, in this order, each on the set that the calls before it left; in `call=`, `ok` when every call succeeds and the first error otherwise | `pt-17` |
| `mixed_steps(t,l,count)` | The first `count` steps of the loop of the row of `own-22`, from step 0, on the page ownership table `t`, with `l` the receipts that are live after them, in the order of their allocation: when $s \bmod 3 \neq 0$ and an allocation is live, the release by its owner of the live one at position $7s \bmod n$ of the $n$ live ones; otherwise `choose` by owner 7 of $s \bmod 5 + 1$ pages at an alignment of $2^{s \bmod 4}$ pages, high when $s$ is even and low when it is odd, and `assign` of its choice with the zeroing complete; the loop of the test, `src/memory/tests/banks.rs:148-195` at the prototype tree | `own-22` |
| `mixed_step(t,l,s)` | Step `s` of that loop on the table and the live receipts that the steps before it left; it gives `start=<address>` of the receipt, `released` or `err=<error>`, then `free=<bytes>`, the free bytes of `stats` after it | `own-22` |
| `release_all(t,l)` | The release by its owner of every live receipt of `l`, in the order of their allocation, after the loop, `src/memory/tests/banks.rs:196-198` | `own-22` |
| `translate_block(set,pa,base,bits)` | The check of `dm-04` of the 2 MiB block at the physical address `pa` of a direct map, as its test reads every page of it: when `lookup_block` of `DIRECT_BASE \| pa` gives a block descriptor whose output address is `pa`, `map=block`; otherwise `lookup_page` of each of its 512 pages, `map=pages absent=<addresses>` when each gives a page descriptor whose output address is its own address or `NotMapped`, with the addresses of the latter joined by `,` or `-` for none, and `map=none` when every page is `NotMapped`. Each descriptor has AP[2], AP[1] and nG 0 and PXN and UXN 1; any other translation is `map=wrong page=<address>`, of the first such page | `dm-04` |

A call followed by `.` and the name of a field of its output,
`direct_map(s,0x80000,40).bytes`, gives that field alone, `bytes=<bytes>`,
as the last line of `dm-04` writes it.

- A call that the test unwraps asserts that it succeeds, so it is a case,
  with `ok` or `ok page=...`.
- Where a test asserts some bits of a descriptor, the case gives the whole
  descriptor, written from the row of its kind in the kind table; where it
  asserts that a lookup succeeds, the case gives the descriptor too.
- `Kind::bits()` of the prototype, which the tests of `pt-02` and `pt-06`
  call, is `descriptor(kind, 0x0)`.
- What a test asserts of the storage after a call, the tables of a set
  unchanged, every entry 0 or one entry, is an item of the case of that call;
  the count of tables in use is a call of `used` and a case of its own.
- `pt-08` replaces the source's root entry 0 by `0x100000003`, by
  `0x100005003` and by the valid entry with bit 6 set, where the row of the
  contract says only that the copy fails. The file gives, as the rule of
  [legacy test vectors](contract.md#legacy-test-vectors) for such a row
  says, the errors of the order of
  [copying the kernel tables](contract.md#copying-the-kernel-tables):
  the first points at the root, a table already reached, and the second at
  table 5, outside the three tables in use, both `TableBacking`; the third is
  a table descriptor with an attribute bit, `InvalidDescriptor`. Its row says
  that the target is unchanged after each failure, so each failing copy asks
  `unchanged(target)`.
- `pt-07` asks the table descriptors of the target at the indices of the
  source's tables: the source takes level 2 table 1 and level 3 table 2 for
  `0x4000`, level 3 table 3 for `0x9000000` and level 2 table 4 and level 3
  table 5 for `0x40000000`, by the lowest free index with the level 2 table
  first.
- A call whose result the test only checks with `is_ok` succeeds, so the
  case gives `ok` and the descriptor that it gives, as for an unwrapped call;
  `dm-01` checks three lookups so.
- A call whose output the test does not assert, such as the `reset` of
  `pt-13`, whose test asserts only the count of tables in use after it, is an
  item of `do=` and not a case.
- The counts of a direct map are written in the order `bytes`, `blocks`,
  `pages` of the row of `dm-01`, also for `dm-02`, whose row lists the pages
  before the blocks, so that one form serves both.
- The earlier calls of a case of `pt-17` are the calls of its loop that come
  before it, `map_blocks(s,0xffffff8000000000,0x0,<n>,0x100000000,40)` with
  `<n>` the number of them, and the calls after the loop; writing each of
  them would give the file about 0.5 GB.
- The lines of `dm-04` are those of its row: lines `dm-04.1` to
  `dm-04.4096`, one for each 2 MiB block from `0x0` in address order, are the
  `direct_map` of the row and the `translate_block` of the block, and line
  `dm-04.4097` is the bytes of the `direct_map`.

A case of the page ownership table has `sets=-` and no `memory=`. Its tables
and values are named by the calls that make them, and a later call of the case
takes them by name; a call that fails names nothing, and a refused packet or
reservation keeps its name, as the test keeps the value that it gets back.

| Call | Meaning | Output |
| --- | --- | --- |
| `Ownership::new(t,arena,capacity,[banks],[exclusions])` | The table `t` of the extent capacity `capacity` and the 132 exclusion records of the core; ranges `<start>+<length>` joined by `,` in brackets, `[]` for none, and an exclusion as its range, `/` and its owner, `firmware`, `image` or `boot` | `ok` |
| `set_generation(t,g)` | The test's write of the generation counter of `own-01`, not an entry | `ok` |
| `choose(t,c,owner,pages,alignment,placement,window)` | The choice `c`, with the placement `low` or `high` and the window a range or `-` | `ok range=<range>` |
| `assign(t,a,c,zeroed)` | The receipt `a` of the choice `c`, with `zeroed` `true` or `false` | `ok arena=<arena> owner=<owner> generation=<generation> range=<range>` |
| `reserve(t,r,owner,pages,alignment,placement,window)` | The reservation `r` | The fields of a receipt, then `attempted=<Boolean> failures=<count>` |
| `Reservation::initialized(x,r,zeroed)` | The packet `x` of the reservation `r`, or after a failed zeroing the reservation `r` again | `ok value=packet`, the fields of a receipt and `failures=`; or `ok value=reservation` and the fields of a reservation |
| `publish(t,a,owner,x)` | The receipt `a` of the packet `x` | The fields of a receipt |
| `cancel(t,owner,r)`, `release(t,owner,a)`, `validate(t,owner,x)` | The reservation `r`, the receipt `a`, and a receipt or a packet `x` | `ok` |
| `stats(t)` | The statistics | `ok managed=<bytes> free=<bytes> allocated=<bytes> allocations=<count> free_extents=<count> largest_free=<bytes> extents=<count> capacity=<count>` |
| `PhysRange::new(start,len)`, `end(r)`, `contains(r,o)`, `overlaps(r,o)` | The functions of physical ranges, on ranges written `<start>+<length>` | `ok range=<range>`, `ok end=<address>`, `ok contains=<Boolean>`, `ok overlaps=<Boolean>` |

- The prototype's allocation with a zeroing callback is two cases, `choose`
  and `assign`: the chosen range is the range that the callback zeroes, which
  the tests check through their backing bytes or in the callback, and the
  receipt is the output of `assign`, with `true` when the callback succeeds
  and `false` when it fails; a request that `choose` refuses asks for no
  zeroing and has no `assign` ([behaviour changes](contract.md#legacy-test-vectors),
  lines 1006 to 1009). The staged `initialize` with its callback is
  `Reservation::initialized` with the outcome of the callback.
- The assertions of `own-07`, `own-11` and `own-24` on the counts of failed
  requests and of failed zeroings of the table have no case (lines 1010 to
  1012); the count of failures of a reservation is the reservation's and has
  its cases.
- A table that the test unwraps is a case, `ok`, as every unwrapped call. The
  tests' helper `range(start, bytes)`, which unwraps `PhysRange::new`, writes
  a range of the input, `<start>+<length>`, and is not a case; the calls of
  `PhysRange::new` and of the functions of ranges whose outputs a test
  asserts are cases, also the `overlaps` of `own-23`.
- Where a test asserts one field of the statistics, the case is that field,
  `stats(t).<field>`; where it compares the statistics with earlier ones,
  the case is `stats(t)` whole, and the earlier `stats` is an item of `do=`.
- A receipt, a reservation and a packet are written whole, with the
  generation that the counter gives, where the test asserts some of their
  fields.
- Arenas, owner identities and generations are hexadecimal, as the row of
  `own-01` writes its generation; pages, alignments, capacities and failures,
  which are counts, are decimal.
- The capacity of a table is that of the test, the `N` of `PageAllocator`
  or `Extents` in the prototype tree, also where the row names none.
- An exclusion of a test is a firmware reservation (`/firmware`), the
  reserved memory that the tests pass to the table; no output depends on its
  owner.
- The lines of `own-22` are those of its row: line `own-22.<n>` for `n` from
  1 to 800 is `mixed_step(t,l,<n - 1>)` after the table of the row and
  `mixed_steps(t,l,<n - 1>)`, and line `own-22.801` is `stats(t).free` after
  `mixed_steps(t,l,800)` and `release_all(t,l)`. Writing the earlier steps of
  each line one by one would give the file about 320,000 earlier calls.

### Vector disposition

Of the 53 vectors of [legacy test vectors](contract.md#legacy-test-vectors),
these modules answer 47, in 9,382 cases; 6 do not apply.

| Disposition | Vectors | Reason |
| --- | --- | --- |
| Replayed, 44 | `pt-01` to `pt-16`, `pt-18`, `pt-21`, `dm-01` to `dm-03`, `own-01` to `own-11`, `own-16` to `own-21` and `own-23` to `own-28` | Every case is a line of the vector file; the 7 GiB of `own-21` are two extents, so its cases take no more than the others |
| Replayed with a large input, 3 | `pt-17`, `dm-04`, `own-22` | `pt-17`: 4,103 cases, the 4,096 calls of its loop each a case whose earlier calls are a `map_blocks` item. `dm-04`: the property vector of its row, 4,097 lines by the rule of the row. `own-22`: the property vector of its row, 801 lines, whose earlier steps are a `mixed_steps` item. The generator of the file takes the expected outputs of the three from models of the rules of the contract that do not use the specification, for `own-22` a model of each page of each bank as busy or free, and checks them against the literals of the rows |
| Not applicable, 6 | `pt-19`, `pt-20`, `own-12` to `own-15` | `pt-19` and `pt-20`: the direct map never changes after boot, so the sealing of a page, with the split and merge of its block, is not carried ([behaviour changes](contract.md#legacy-test-vectors), lines 1016 to 1018). `own-12` to `own-15`: the kernel has no byte heap (line 1019); the failure of a page request of `own-15` is in `own-07` and `own-28` |

The comments of the vector file name the vectors that are not applicable.
The replay module checks one representative case of each vector of the file,
two of `dm-04` and two of `own-22`, and the whole file is replayed through the
same `replay` by the driver of `cargo xtask formal vectors`.

## Contract correspondence

Each row of the [entry table](contract.md#entry-points) that these modules
state, and the Lean definitions that state its entries, below
`Krepi.Spec.PageTables`:

| Line | Entries | Lean |
| --- | --- | --- |
| 107 | `page_tables::Kind`, `page_tables::descriptor`, `page_tables::direct_address`, `PhysRange::new`, `end`, `contains` and `overlaps`, and `Tables::lookup_page`, `lookup_block` and `used` | `Kind` with `Kind.attributes` and `Attributes.bits`; `descriptor`; `directAddress`; `PhysRange.new`, `PhysRange.endAddr`, `PhysRange.contains`, `PhysRange.overlaps`; `Tables.lookupPage` with `checkEntry` and `Tables.pageLeaf`, `Tables.lookupBlock` with `Tables.walk2`, `Tables.usedTables` |
| 108 | `Tables::new`, `Tables::reset` and `Tables::clone_kernel_from` | `Tables.new`; `Tables.reset`; `Tables.cloneKernelFrom`, with `checkPool`, `Tables.walkRoot`, `Tables.walkLevel2`, `Tables.reach`, `checkLeaves`, `copyableLeaf` and `copyStores` |
| 109 | `Tables::map_page` | `Tables.mapPage`, with `checkEntry`, `checkPhysical` and `Tables.walk2` |
| 110 | `Tables::map_block` | `Tables.mapBlock`, with `checkEntry`, `checkPhysical`, `Tables.walk2` and `blockDescriptor` |
| 111 | `Tables::unmap_page` | `Tables.unmapPage`, with `checkEntry` and `Tables.pageLeaf` |
| 112 | `page_tables::kernel_map` and `page_tables::direct_map` | `Tables.kernelMap` with `Layout`, `LayoutRange`, `layoutKinds`, `sortByKey`, `layoutPages` and `Tables.checkLayoutRange`; `Tables.directMap` with `directLeaves`, `directFuel` and `Tables.checkUsableRange`; both with `Tables.place`, `Tables.checkLeaf`, `assignTables`, `mapPlan` and `Tables.mapLeaves`; `Plan.counts` |
| 113 | `Ownership::new` | `Ownership.new`, with `PhysRange.onPages`, `anyOverlap`, `sortByKey`, `initialExtents`, `bankExtents`, `Exclusion.cut` and `cutRuns` |
| 114 | `Ownership::choose` and `Ownership::assign` | `Ownership.choose` with `isPowerOfTwo`, `scan`, `Placement.part`, `fit` and `Extent.extra`; `Ownership.assign` with `Ownership.take`, `Extent.take` and `Counter.after` |
| 115 | `Ownership::reserve`, `Reservation::initialized` and `Ownership::publish` | `Ownership.reserve` with `Ownership.choose` and `Ownership.take`; `Reservation.initialized` with `Initialization`; `Ownership.publish` with `Ownership.findHeld` |
| 116 | `Ownership::cancel` and `Ownership::release` | `Ownership.cancel` and `Ownership.release`, with `Ownership.findHeld`, `mergeFreed` and `Extent.join` |
| 117 | `Ownership::owner`, `Ownership::validate` and `Ownership::stats` | `Ownership.owner` with `Ownership.ownerOf` and `firstExcluder`; `Ownership.validate` with `Ownership.findHeld`; `Ownership.stats` with `Stats` |

The rules of the contract and the definitions that state them:

| Contract | Lean, below `Krepi.Spec.PageTables` |
| --- | --- |
| [Terms](contract.md#terms): region, table, table set, pool, physical width, kind, abstract mapping, write plan, physical range | `Region` with `Region.holds`; `Table`, `index1`, `index2`, `index3`; `Tables` with `Pool`; `tableAddress`; `widthOk`; `Kind`; `Tables.M`, `Tables.G`, `Tables.P`; `Plan`; `PhysRange` |
| [Descriptors and attributes](contract.md#descriptors-and-attributes): the formats and the kind table | `descriptor`, `blockDescriptor`, `tableDescriptor`, `INVALID`, `typeBits`, `isValid`, `outputAddress`, `blockAddress`, `Kind.attributes`, `Attributes.bits` |
| RO, NX, Device and kernel and user | `Attributes.readOnly`, `writable`, `el0Access`, `executableEl1`, `executableEl0`, `isDevice`, `isGlobal` |
| [Copying the kernel tables](contract.md#copying-the-kernel-tables) | `Tables.cloneKernelFrom` and the definitions of line 108 above |
| [Abstract mapping](contract.md#abstract-mapping): the state of a set | `Tables`, `Tables.M`, `Tables.G`, `Tables.P` |
| [After mapping](contract.md#after-mapping): the rows of `Tables::new`, `reset`, `map_page`, `map_block`, `unmap_page`, `clone_kernel_from`, `kernel_map` and `direct_map` | `Tables.new`, `Tables.reset`, `Tables.mapPage`, `Tables.mapBlock`, `Tables.unmapPage`, `Tables.cloneKernelFrom`, `Tables.kernelMap`, `Tables.directMap`, each with `Tables.apply` of its plan |
| [Errors of table sets](contract.md#errors-of-table-sets): the error table and the order | `TableError`; `checkEntry`, `checkPool` and `checkPhysical`, then the walk (`Tables.walk2`, `Tables.walk`, `Tables.child?`), then the free tables, in each entry; for the maps, `checkPool`, then `Tables.checkLayoutRange` or `Tables.checkUsableRange` for each range in address order with `Tables.place` and `Tables.checkLeaf` for each leaf, then `Tables.mapLeaves` |
| [Write plans and publication](contract.md#write-plans-and-publication): the steps and their order | `Step`, `Plan`, `Step.exec`, `Plan.exec`, `Tables.apply`; the plans of `Tables.mapPage`, `Tables.mapBlock`, `Tables.unmapPage`, `Tables.reset` and `Tables.cloneKernelFrom`; `mapPlan`, with `newLevel2Steps`, `heldLevel2Steps` and `level2Entry`, for `Tables.kernelMap` and `Tables.directMap` |
| [Kernel mappings](contract.md#kernel-mappings): the layout, the identity map of its ranges, their kinds and the guard pages | `Layout`, `LayoutRange`, `layoutKinds`, `MAX_LAYOUT_RANGES`, `layoutPages`, `MapLeaf.isGuard`, `Tables.checkLayoutRange`, `Tables.kernelMap` |
| [Kernel direct map](contract.md#kernel-direct-map): `DIRECT_BASE` and `direct_address` | `DIRECT_BASE`, `directAddress` |
| [Kernel direct map](contract.md#kernel-direct-map): the usable ranges in address order, the block where 2 MiB fit and pages elsewhere, nothing else, the width of $2^{39}$ | `Tables.directMap` with `MemoryPlan.availableRanges` of the fdt specification, `sortByKey`, `directLeaves`, `Tables.checkUsableRange` |
| [Table pool](contract.md#table-pool): the pool and its first checks, the lowest free index, zero storage, the count, the capacities of the kernel tables | `poolFits`, `checkEntry`, `checkPool`; the new tables of `Tables.mapPage` and `Tables.mapBlock` at the record, and of the maps by `assignTables`; `Tables.new` on the storage that its caller gives; `DIRECT_MAP_TABLES`, `KERNEL_TABLES` |
| [Check and execute](contract.md#check-and-execute), for these entries | Each write entry checks every rule before it returns its set and plan, and a failure returns only the error; `Tables.kernelMap` and `Tables.directMap` check every range and the tables of the whole plan first; `Tables.new` and `Tables.reset` have no error; the lookups, `used`, `descriptor` and `directAddress` return values only; the write entries of the page ownership table count the extents that they need in their checks and return the table only on success, so a refused request writes nothing, a counter of failures included; `Ownership.choose`, `Ownership.owner`, `Ownership.validate` and `Ownership.stats` return values only |
| [Work bounds](contract.md#work-bounds), for these entries | The walk reads one entry at each level; the plans of `map_page`, `map_block` and `unmap_page` have at most seven steps, two of them `Zero`; the walk of the copy folds over the 512 entries of each table that it reaches, at most once each since a table is reached once, and its stores fold over the tables below the record, at most `N`; `Tables.kernelMap` folds over at most 16 ranges and over each page of each once (`layoutPages`), and `Tables.directMap` over each usable range once, in at most $L / 2\,\mathrm{MiB} + 2 \cdot 511$ steps of a block or a page (`directFuel`); the plan of each map has one `Store` for each leaf and table descriptor and one `Zero` for each new table; `Ownership.new` compares each bank with the later ones and cuts each bank with each exclusion, and the entries of the page ownership table pass once over the extents, `Ownership.ownerOf` then over the exclusion records |
| [Determinism](contract.md#determinism), for these entries | Every definition is a function; a new table is the one at the record, the lowest free index; the maps walk their ranges in address order, the direct map with a block wherever the rule allows one; `Ownership.choose` scans the extents in address order, from the lowest or the highest by the caller's placement, and takes the first fit in the caller's window; the generation of an allocation is the counter |
| [Abstract mapping](contract.md#abstract-mapping): the state of the page ownership table | `Ownership`, `Ownership.ownerOf` for $O$, `Ownership.counter` for $g$ |
| [After ownership](contract.md#after-ownership): the rows of `Ownership::new`, `assign`, `reserve`, `publish`, `cancel` and `release`, and `Reservation::initialized` | `Ownership.new`, `Ownership.assign`, `Ownership.reserve`, `Ownership.publish`, `Ownership.cancel`, `Ownership.release`, `Reservation.initialized` |
| [Page ownership](contract.md#page-ownership): the owners, initialization, placement, zeroing before publication, receipts, statistics and capacity | `Owner`, `Excluder`, `HoldState`, `Holding`, `Extent`, `Exclusion`, `Counter`; the entries of rows 113 to 117 above; `EXTENTS`, `EXCLUSION_RECORDS` |
| [Page ownership](contract.md#page-ownership): the error table | `OwnershipError` |
| [Terms](contract.md#terms): managed page, extent, receipt, reservation and initialized packet, token | `PhysRange.holdsPage` on the banks; `Extent`; `Allocation`; `Reservation`, `Initialized`; `BootCpu`, `KernelTablesToken`, `OwnershipToken` |
| [State fields](contract.md#state-fields): the four shared fields | `Shared` with the transactions of `Tokens.lean` |

## Requirement correspondence

Each requirement that these modules serve, the definitions that state it, and
the cases of the
[vector file](../../../../verification/vectors/memory/page-tables.vectors)
that
[`Krepi.SpecTests.PageTables.Replay`](../../../../verification/Krepi/SpecTests/PageTables/Replay.lean)
answers through them, and the [specification tests](#specification-tests),
one input that the specification must accept and one that it must reject,
whose theorems in `Krepi.Proofs.PageTables.Stp` are planned. The parts of
[PGT-R05](requirements.md#pgt-r05) to
[PGT-R07](requirements.md#pgt-r07) that a CPU shows, the translation with
the MMU on and the effect of the barriers, belong to the adapter, an
[open obligation](contract.md#open-obligations), and to the QEMU and board
tests of the requirements; these modules state the tables and the plans.
The zeroing of pages in [PGT-R09](requirements.md#pgt-r09) and
[PGT-R10](requirements.md#pgt-r10), `krepi_arch::mmu::zero_frames`, belongs
to the adapter in the same way; the page ownership table states its outcome,
which the caller passes to `assign` and `Reservation::initialized`. The
criteria of [PGT-R08](requirements.md#pgt-r08) for the boot memory map of
every board shape, one owner for every managed page and the free pages equal
to those of the direct map, are `NewOneOwner` and
`BootOwnersMatchDirectMap`, for every well-formed boot memory map, and the
specification test `OwnershipOfBoardShapes` on the boot memory maps of QEMU
virt and the five Pi 5 models. The registered statements of
[invariants](#invariants) and
[properties](#properties), whose theorems are planned, are listed for each
requirement; the statements of the shared state serve the
[state fields](contract.md#state-fields), which no requirement observes. The
last row is the section of liveness, time and performance of the
requirements, which has no ID.

| Requirement | Stated by | Registered statements | Specification tests | Vectors | Not stated by the specification |
| --- | --- | --- | --- | --- | --- |
| [PGT-R01](requirements.md#pgt-r01) | `Kind`, `Kind.attributes`, `Attributes.bits`, `descriptor`, `blockDescriptor`, the permissions of `Attributes`; `Tables.lookupPage`, `Tables.lookupBlock` | `NoWritableExecutable`; `CheckTablesWellFormed` and the well-formedness lemmas of the write entries, `MapPageWellFormed`, `MapBlockWellFormed`, `KernelMapWellFormed`, `DirectMapWellFormed` and `CloneKernelFromWellFormed`, by which every leaf of a set is the descriptor of a kind | `DescriptorsFollowKindRows`, `DescriptorKeepsOnlyItsBits` | `pt-01`, `pt-02`, `pt-06`, `pt-11`, `pt-15`, `pt-21` | That a CPU translates and checks the permissions as the bits say, and `SCTLR_EL1.WXN`, which the QEMU tests of PGT-R05 and PGT-R06 and the adapter cover |
| [PGT-R02](requirements.md#pgt-r02) | `Tables.new`, `Tables.mapPage`, `Tables.lookupPage`, `Tables.usedTables`, `Region.holds` | `AfterEveryWrite` (the rows of `Tables::new` and `map_page`), `NewWellFormed`, `MapPageWellFormed`, `TablesInUseCounted` | `MapPageThenLookup`, `MapPageRefusesMappedPage` | `pt-01`, `pt-03`, `pt-04`, `pt-05`, `pt-13`, `pt-14` | A CPU walking the tables |
| [PGT-R03](requirements.md#pgt-r03) | `Tables.mapBlock`, `Tables.lookupBlock`, `blockDescriptor`; `Tables.unmapPage` and `Tables.mapPage` on a page of a block | `AfterEveryWrite` (the rows of `map_block`, `map_page` and `unmap_page`), `MapBlockWellFormed`, `TablesInUseCounted` | `EightGibOfBlocksInNineTables`, `BlockBeyondNineTablesRefused` | `pt-15`, `pt-16`, `pt-17` | - |
| [PGT-R04](requirements.md#pgt-r04) | `Tables.unmapPage`, `Tables.reset` | `AfterEveryWrite` (the rows of `unmap_page` and `reset`), `UnmapPageWellFormed`, `ResetWellFormed`, `PlansPublishInOrder`, `KernelTablesOnlyFilled` | `UnmapAndResetFollowContract`, `UnmapRefusesUnmappedPage` | `pt-05`, `pt-09`, `pt-11` | The invalidation on a CPU, which the case of break-before-make of the boot component shows |
| [PGT-R05](requirements.md#pgt-r05) | `Tables.directMap` with `directLeaves` and `MemoryPlan.availableRanges`; `directAddress`; `Plan.counts`; `Tables.lookupPage`, `Tables.lookupBlock`, `Tables.usedTables` | `AfterEveryWrite` (the row of `direct_map`), `DirectMapUnchangedAfterBoot`, `BootDirectMapWellFormed`, `DirectMapWellFormed`, `BootDirectMapOffset`, `BuildDirectMapOffset`, `CheckDirectMapOffset`, `TablesInUseCounted`, `BootOwnersMatchDirectMap`, `NoWritableExecutable` | `DirectMapCountsOfPi5Models`, `DirectMapOmitsExcludedPages` | `dm-01` to `dm-04` | The translation with the MMU on at the edges of the ranges, the three cold boots and the board runs; the bank shapes of the four other Pi 5 models, which the fdt contract infers |
| [PGT-R06](requirements.md#pgt-r06) | `Tables.kernelMap` with `Layout`, `layoutKinds` and `Tables.checkLayoutRange` | `AfterEveryWrite` (the row of `kernel_map`), `BootKernelMapWellFormed`, `KernelMapWellFormed`, `NoWritableExecutable` | `KernelMapGivesKindsAndGuard`, `KernelMapRefusesSharedPage` | - | The faults on QEMU virt |
| [PGT-R07](requirements.md#pgt-r07) | `Step`, `Plan`, `Step.exec`; the plans of `Tables.mapPage`, `Tables.mapBlock`, `Tables.unmapPage` and `Tables.cloneKernelFrom`, and `mapPlan` for `Tables.kernelMap` and `Tables.directMap` | `PlansPublishInOrder`, `KernelTablesOnlyFilled` | `PlansFollowContractOrder`, `KernelFillRefusesValidEntry` | - | The stores, barriers and register writes of the adapter, [open obligations](contract.md#open-obligations), and the order that the barriers give on several CPUs |
| [PGT-R08](requirements.md#pgt-r08) | `Ownership.new` with `initialExtents` and `bankExtents`; `Ownership.ownerOf` and `Ownership.owner`; `Ownership.stats`; the merge of `mergeFreed` within a bank | `AfterEveryWrite` (the row of `Ownership::new`), `NewOwnershipWellFormed`, `NewOneOwner`, `NewHolderRanges`, `NewFreeOrHeldUsable`, the preservation of `Ownership.OneOwner` and `Ownership.FreeOrHeldUsable` by the five write entries, `CheckOneOwner`, `CheckFreeOrHeldUsable`, `BootOwnersMatchDirectMap` | `OwnershipOfBoardShapes`, `OwnershipRefusesOverlappingBanks` | `own-03`, `own-04`, `own-05`, `own-17`, `own-18`, `own-19`, `own-21`, `own-22` | The contents of RAM |
| [PGT-R09](requirements.md#pgt-r09) | `Ownership.choose` with `scan` and `fit`; `Ownership.assign` with `Ownership.take` and `Counter.after`; `Ownership.release` and `Ownership.validate` with `Ownership.findHeld`; `Ownership.stats` | `AfterEveryWrite` (the rows of `assign` and `release`), `PlacementFirstFit`, `AssignWellFormed`, `ReleaseWellFormed`, the preservation by `assign` and `release`, `NewGenerationsBelowCounter`, `CheckHolderRanges`, `CheckGenerationsBelowCounter` | `AllocationTakesWindowAndGeneration`, `ReleaseRefusesStaleReceipt` | `own-01`, `own-06` to `own-11`, `own-16`, `own-18`, `own-20`, `own-21`, `own-22` | The zeroing, `krepi_arch::mmu::zero_frames`, the adapter's |
| [PGT-R10](requirements.md#pgt-r10) | `Ownership.reserve`, `Reservation.initialized`, `Ownership.publish`, `Ownership.cancel`, `Ownership.validate`, `Ownership.release`, `Ownership.stats` | `AfterEveryWrite` (the rows of `reserve`, `publish` and `cancel`), `PlacementFirstFit`, `ReserveWellFormed`, `PublishWellFormed`, `CancelWellFormed`, the preservation by `reserve`, `publish` and `cancel` | `ReservationPublishesAfterZeroing`, `CancelRefusesAttemptedReservation` | `own-23` to `own-28` | The zeroing on a CPU |
| [PGT-R11](requirements.md#pgt-r11) | `DIRECT_MAP_TABLES`, `KERNEL_TABLES`; `OutOfTables` of `Tables.mapLeaves` before any write; `EXTENTS`, `EXCLUSION_RECORDS`; `MetadataExhausted` of `Ownership.new`, `Ownership.choose` and `Ownership.reserve` before any write | `TablesInUseCounted`, `NewOwnershipWellFormed` and the well-formedness lemmas of the page ownership table, which bound its extents and exclusion records by their capacities, `NewFreeExtentsMaximal`, `CheckFreeExtentsMaximal`, `PlacementFirstFit` | `CapacitiesAtTheirLimits`, `CapacitiesRefuseOneMore` | `dm-03`, `own-05`, `own-08` | - |
| [PGT-R12](requirements.md#pgt-r12) | `Tables.cloneKernelFrom` | `AfterEveryWrite` (the row of `clone_kernel_from`), `CloneKernelFromWellFormed`, `PlansPublishInOrder`, `NoWritableExecutable`, which counts the copy | `CopyIsPrivateAndOrdered`, `CopyRefusesPrivateLeaf` | `pt-07`, `pt-08`, `pt-10`, `pt-12`, `pt-18` | A process running on the copy, which the tables of address spaces show |
| [Liveness, time and performance](requirements.md#liveness-time-and-performance) | Every definition is total and ends by structural recursion on a measure that the contract bounds: the walk reads one entry at each of three levels; the copy folds over the 512 entries of each table that it reaches and over the tables below the record; `kernel_map` over at most 16 ranges and over the pages of each (`layoutPages`); `direct_map` over the usable ranges and, in each, on fuel $L / 2\,\mathrm{MiB} + 2 \cdot 511$ (`directFuel`, from the work bounds, lines 781 to 783); the plans fold over their leaves and their steps; the page ownership table folds over its banks, its exclusions and its at most `E` extents (`cutRuns`, `scan`, `splitFirst`, `Ownership.stats`); the transactions of the shared state are single steps. No definition waits or takes a lock | None: every definition is total by structural recursion, which Lean checks, so termination needs no statement | None | Every case returns | The time of an entry, which no test bounds |

### PGT-R01

[PGT-R01](requirements.md#pgt-r01), the descriptor kinds, is `Kind` with the
rows of `Kind.attributes`, placed by `Attributes.bits`: `descriptor` gives the
page descriptor of each kind, its address in bits 12 to 47 and every other
bit 0 or a bit of the row, and `blockDescriptor` the block form of
`ReadWrite`. The permissions of `Attributes` read the rows, so that the rules
of the requirement are statements on the bits: no kind is writable and
executable; the kernel kinds give EL0 no access and are global except
`KernelPrivateReadWrite`; the user kinds are not global and do not execute at
EL1; `Device` and `UserDevice` have AttrIndx 0. The replay answers the
descriptors of `pt-02`, `pt-06` and `pt-21` through `descriptor`, those that
`pt-01`, `pt-06` and `pt-11` read back through `Tables.lookupPage`, and the
block of `pt-15` through `Tables.lookupBlock`. The specification test
`DescriptorsFollowKindRows` states the descriptors of the nine kinds and the
block at one address, and those that the sets of `pt-01` and `pt-15` read
back; `DescriptorKeepsOnlyItsBits` the same at an address with every bit
set, of which only bits 12 to 47 reach a descriptor.

### PGT-R02

[PGT-R02](requirements.md#pgt-r02), mapping and looking up a page, is
`Tables.mapPage` and `Tables.lookupPage` on a set of `Tables.new`: the first
checks, the physical address, the walk and the free tables, each with the
error of the contract in its order, and a refused call returns its error
alone, so no table changes and the record stays. `Region.holds` in the first
checks makes a lower set refuse the addresses of the upper region and the
other way round. The replay answers `pt-01`, `pt-03`, `pt-04`, `pt-05`,
`pt-13` and `pt-14`, whose cases of `used` after each refusal give the count
unchanged; `pt-14` refuses the addresses of each region in a set of the
other. The specification tests `MapPageThenLookup` and
`MapPageRefusesMappedPage` take `pt-03` and `pt-14`: a page of each region
mapped and looked up, and the refusal of a second page at the same address.

`AfterEveryWrite` states the row of `map_page` for every success on a
well-formed set: $v$ was not mapped, $M$ gains $v \mapsto (p, k,
\mathrm{page})$ and nothing else, and $G$ and $P$ gain the slots of $v$.

### PGT-R03

[PGT-R03](requirements.md#pgt-r03), blocks, is `Tables.mapBlock`: one level 2
descriptor of `ReadWrite` at a 2 MiB-aligned address, refused with
`AlreadyMapped` where the level 2 entry is valid, so a level 3 table never
becomes a block; `Tables.lookupPage` and `Tables.unmapPage` give `NotMapped`
for a page of a block and `Tables.mapPage` gives `AlreadyMapped`, so a block
never becomes pages. The replay answers `pt-15` and `pt-16`, and `pt-17`, the
4,096 blocks of 8 GiB from `DIRECT_BASE` in an upper set of 9 tables, across
the 1 GiB and 4 GiB boundaries, and the refusal of one more with
`OutOfTables`.

`AfterEveryWrite` states the row of `map_block`, and
`TablesInUseCounted` that the tables in use of a well-formed set are the
root and one table for each element of $G$ and $P$, so that 8 GiB of blocks
use the root and 8 level 2 tables. The specification tests
`EightGibOfBlocksInNineTables` and `BlockBeyondNineTablesRefused` take the
4,096 blocks of `pt-17` and the refusal of one more.

### PGT-R04

[PGT-R04](requirements.md#pgt-r04), unmapping and reset, is
`Tables.unmapPage`, whose plan is `Store(t, i, 0)` and then `Invalidate(v)`
and which leaves the record, so the tables under the leaf stay in the pool,
and `Tables.reset`, which leaves the root alone in use and zeroes every table
in use. The replay answers `pt-05`, `pt-09` and `pt-11`, among them the reset
of `pt-09` with every entry 0 after it. The specification test
`UnmapAndResetFollowContract` states the plans of `unmap_page` and of
`reset` of `pt-09` step by step, and `UnmapRefusesUnmappedPage` the second
unmap of `pt-05`.

`AfterEveryWrite` states the rows of `unmap_page` and `reset`,
`PlansPublishInOrder` that the plan of `unmap_page` is the store of 0 into
the leaf and then `Invalidate`, and `KernelTablesOnlyFilled` that no
transaction removes or changes a valid entry of the kernel tables.

### PGT-R05

[PGT-R05](requirements.md#pgt-r05), the kernel direct map, is
`Tables.directMap` on the direct map's set and the boot memory map of the fdt
specification: it maps every page of every usable range,
`MemoryPlan.availableRanges`, at `DIRECT_BASE | pa` as `ReadWrite`, with a
block at each multiple of 2 MiB that has 2 MiB of its range left and pages
elsewhere (`directLeaves`), and nothing else, since the usable ranges hold no
reservation, hole between banks or RAM outside the managed banks. It checks
the whole map before it writes: a range that ends above $2^{39}$ is
`AddressWidth`, and a map that needs more tables than the pool has free is
`OutOfTables`, with no plan. `Plan.counts` gives the bytes, blocks and pages
of the plan. The replay answers `dm-01` to `dm-03`, and `dm-04`, every 2 MiB
block below 8 GiB of the 8 GB layout of the prototype against the model of
its row, with `0x1ffbfe000` bytes. The specification test
`DirectMapCountsOfPi5Models` states the tables, blocks and pages of the five
Pi 5 models of the table of [Table pool](contract.md#table-pool), and
`DirectMapOmitsExcludedPages` that a page of each kind of exclusion, a hole
and a bank outside the managed window have no direct address. The criterion
names the four other models; the test states the 8 GB model too, whose
counts the prototype measured on the board and the board runs check
([testing obligations](contract.md#testing-obligations)). The
translation on QEMU virt is evidence of the QEMU tests.

`AfterEveryWrite` states the row of `direct_map`,
`Shared.DirectMapOffset` that the direct map's set maps only
`DIRECT_BASE | pa` to `pa` as `ReadWrite`, `DirectMapUnchangedAfterBoot` that no
transaction changes the set once the MMU is on, and `BootOwnersMatchDirectMap`
that its pages are exactly the free pages of the table of the kernel root.

### PGT-R06

[PGT-R06](requirements.md#pgt-r06), the kernel mappings of the image, is
`Tables.kernelMap` on the lower kernel set: every page of every range of the
layout at its physical address with the kind of its range, one of
`ReadExecute`, `ReadOnly`, `ReadWrite` and `Device` by the type of the
layout, and no entry of a guard page. It refuses a range off page boundaries
with `Alignment`, and a page that two ranges share or a range that covers a
guard with `AlreadyMapped`, before any write, so no page has two kinds and,
since no kind of a layout is writable and executable, no page of the image
is mapped writable and executable. No vector covers it; the contract's host
test of a shared page and the QEMU tests are its evidence. The specification
test `KernelMapGivesKindsAndGuard` states the descriptors of an image on QEMU
virt that give the faults of the criterion, with its guard unmapped, and
`KernelMapRefusesSharedPage` the refusal of a text and a data range that
share a page.

`AfterEveryWrite` states the row of `kernel_map`, and
`NoWritableExecutable` that no frame is mapped writable and executable,
counting the lower kernel set, the direct map's set and a copy.

### PGT-R07

[PGT-R07](requirements.md#pgt-r07), write plans, is `Plan` with the plans of
the entries: each new table is zeroed and written before the one store of
the table descriptor that makes it reachable, with a `Fence` before that
store; a plan that makes an entry valid ends with `Sync`; the plan of an
unmap stores the invalid entry and then invalidates the address; no step
fails, since `Step.exec` is total. The plans of the kernel mappings and the
direct map are `mapPlan`: under a new level 2 table its level 3 tables
first, then the level 2 table, one `Fence` and the store into the root, and
`Sync` last; they write only entries that the checks found free. The
execution of the steps on hardware is the adapter's, an
[open obligation](contract.md#open-obligations). The specification test
`PlansFollowContractOrder` states the plan of each of the six entries of the
criterion step by step, and `KernelFillRefusesValidEntry` that the fill of
a valid entry of the lower kernel set after the boot gives no plan.

`PlansPublishInOrder` states the order of every plan of `map_page`,
`map_block`, `kernel_map` and `direct_map` on a well-formed set, of
`unmap_page` and of the copy, and `KernelTablesOnlyFilled` that a plan for
the kernel tables writes only invalid entries and holds no `Invalidate`.

### PGT-R08

[PGT-R08](requirements.md#pgt-r08), one owner for every page, is
`Ownership.new` and the owner function `Ownership.ownerOf`: a managed page in
an extent has the owner of the extent, and a page that an exclusion touches,
rounded out to whole pages within each bank, is in no extent and has the
first of the owners of the exclusion records that touch it. That every
managed page of a table that the entries built has exactly one owner is the
invariant `Ownership.OneOwner`, which `Ownership::new` establishes
(`NewOneOwner`) and every write entry preserves; that the free and held pages
of the table of the kernel root are those of the usable ranges is
`Ownership.FreeOrHeldUsable`; and that, for every well-formed boot memory map,
the free pages are exactly the pages of the direct map is
`BootOwnersMatchDirectMap`. The extents of a bank
are the runs of its pages that no exclusion touches, free at the
initialization; a range is taken inside one free extent and a freed extent
merges only within its bank, so the banks never merge and no range of a
holder spans two. `Ownership.new` refuses no bank and overlapping banks with
`InvalidRange`, a bank off page boundaries with `InvalidAlignment`, the arena
0 with `InvalidArena`, and more banks, exclusions or extents than the
capacities with `MetadataExhausted`. The replay answers `own-03`, `own-04`,
`own-05`, `own-17`, `own-18`, `own-19` and `own-21`, and `own-22`, 800 steps
of mixed placement on three banks against a model of each page. The
specification test `OwnershipOfBoardShapes` states the table of each board
shape, and `OwnershipRefusesOverlappingBanks` the refusal of `own-17` of two
banks that share a page.

### PGT-R09

[PGT-R09](requirements.md#pgt-r09), allocation and release, is
`Ownership.choose`, which gives the lowest or the highest aligned range of
free pages in one free extent of one bank, inside the caller's window, and
`Ownership.assign`, which holds it for its owner identity with the generation
of the counter only when the zeroing completed: a failed zeroing is
`ZeroFailed` and leaves the pages free and the counter where it was. The
counter gives each generation once and is exhausted after $2^{64} - 1$.
`Ownership.release` frees the pages only for a receipt of the table's arena,
the caller's owner identity and a held range of exactly its generation,
published; another owner, another arena, a second release and a stale receipt
are refused with `WrongOwner`, `WrongArena` and `InvalidAllocation`, and a
refused request writes nothing. `Ownership.validate` makes the same checks
without a write. The replay answers `own-01`, `own-06` to `own-11`,
`own-16`, `own-18`, `own-20`, `own-21` and `own-22`. The specification tests
`AllocationTakesWindowAndGeneration` and `ReleaseRefusesStaleReceipt` take
`own-20` and `own-10`.

`AfterEveryWrite` states the rows of `assign` and `release`,
`PlacementFirstFit` the placement and the end of the scan of `choose`, and
the invariants `Ownership.HolderRanges` and
`Ownership.GenerationsBelowCounter` that a receipt names one holder's range
and that no generation is reused.

### PGT-R10

[PGT-R10](requirements.md#pgt-r10), the staged reservation, is
`Ownership.reserve`, which holds the range of `choose` at once, reserved;
`Reservation.initialized`, which gives the packet once the holder's zeroing
completed, or after a failure the reservation, marked as attempted with one
more failure; and `Ownership.publish`, which turns the packet into a receipt,
published. `Ownership.cancel` frees an unused reservation and refuses one
whose zeroing was attempted with `ZeroFailed`; publication and cancel by
another owner identity or at another arena are refused, and the packet or
the reservation is returned. A reservation or a packet that its holder drops
is never passed to an entry again, so its pages stay held. The replay
answers `own-23` to `own-28`. The specification tests
`ReservationPublishesAfterZeroing` and `CancelRefusesAttemptedReservation`
take `own-23` and `own-24`.

`AfterEveryWrite` states the rows of `reserve`, `publish` and
`cancel`, the last with the refusal of an attempted reservation.

### PGT-R11

[PGT-R11](requirements.md#pgt-r11), the capacities, is the constants
`DIRECT_MAP_TABLES`, 80, and `KERNEL_TABLES`, 32, of the kernel tables, with
the refusal of a map that needs more tables than its pool has free with
`OutOfTables`, before any write (`Tables.mapLeaves`); and `EXTENTS`, 160, and
`EXCLUSION_RECORDS`, 132, of the page ownership table, with the refusal with
`MetadataExhausted` of an initialization of more banks, exclusions or
extents than they allow and of a request whose range would need more extents
than the capacity has free, before any write. The 16 GiB and 32 banks that
the table manages at most are those that the boot memory map admits. The
replay answers `dm-03`, `own-05` and `own-08`, and `own-03`, `own-16` and
`own-17` refuse at the capacity too. The specification tests
`CapacitiesAtTheirLimits` and `CapacitiesRefuseOneMore` take the three
limits of the criterion: a direct map of exactly 80 tables and one of 81, a
table of exactly 160 extents and a request for one more, and an
initialization with 132 exclusions and one with 133.

`TablesInUseCounted` relates the record of the tables in use to the
slots that a map touches, and the well-formedness lemmas bound the extents
and the exclusion records by their capacities.

### PGT-R12

[PGT-R12](requirements.md#pgt-r12), copying the kernel tables, is
`Tables.cloneKernelFrom`: the checks of the two pools, their overlap and the
record of the source, then the walk of the source in its order, before any
write; the plan zeroes the target's tables in use and stores every valid
entry of the source into the target's table of the same index, the leaves as
they are, global ones included, and the table descriptors pointing into the
target's pool. The tables of the copy are the target's own, so a later plan
on either set writes only its own pool. The replay answers `pt-07`, `pt-08`,
`pt-10`, `pt-12` and `pt-18`, with the target unchanged after each refusal.
The specification tests `CopyIsPrivateAndOrdered` and
`CopyRefusesPrivateLeaf` take `pt-07`, with the plan of its copy step by
step, and `pt-12`.

`AfterEveryWrite` states the row of `clone_kernel_from`: the copy has
the abstract mapping, $G$, $P$ and the record of the source;
`PlansPublishInOrder` the form of its plan.

## Dependencies

- The specification of the [fdt](../../boot-platform/fdt/specification.md)
  component, whose boot memory map, `MemoryPlan` with its usable ranges, the
  direct map reads: `Boot.lean` imports `Krepi.Spec.Fdt.Plan`.
- Lean core. No module of the specification imports Mathlib, the Aeneas
  library or a generated module. `Ownership.lean` imports `Basic.lean` only,
  and `Tokens.lean` imports `Boot.lean` and `Ownership.lean`. The witness
  modules import `Boot.lean` and `Ownership.lean` and no module of
  `SpecProperties` or `SpecTests`.
