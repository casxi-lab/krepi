---
specifications:
  - Krepi.Spec.PageTables.Basic
  - Krepi.Spec.PageTables.Descriptor
  - Krepi.Spec.PageTables.Tables
  - Krepi.Spec.PageTables.Plan
  - Krepi.Spec.PageTables.Map
  - Krepi.Spec.PageTables.Boot
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
memory map, the modules of the fdt specification.

This page describes the modules of the table sets: the descriptors and kinds,
the physical ranges, the pools with the record of their tables in use, the
walk, the write plans, the kernel mappings and the direct map, the entries of
rows 102 to 107 of the [entry table](contract.md#entry-points). The page
ownership table and the tokens of the
[state fields](contract.md#state-fields) are specified by further modules,
which this page will describe with the invariants, the properties, the
specification tests and the witnesses.
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
[kernel direct map](contract.md#kernel-direct-map), the entries of row 107.
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

## Design decisions

### Readings of the contract

Where the contract leaves a rule open, the specification takes the reading
below and states it. Lines are those of the contract at commit `6a15f41`.
Where the contract defers to the prototype tree, which it does for the
arguments of the entries ("as the prototype does", lines 613 and 614), the reading
follows the prototype and names the place.

| Reading | Contract | Basis |
| --- | --- | --- |
| The first checks give `Alignment` for a virtual address or a `base` off its boundary, then `AddressWidth` for an address outside the region or `bits` outside 32 to 48, then `TableBacking` for the pool: the three errors in the stated order, each with the rules of its row of the error table | [Errors of table sets](contract.md#errors-of-table-sets), lines 341 to 343 and 349 to 351 | The order lists the three errors "in this order" and the error table gives each rule its error |
| `base` and `source_base` are 64-bit and `bits` is 8-bit | [Table pool](contract.md#table-pool), lines 612 to 614 | "as the prototype does": the prototype takes `base: u64` and `pa_bits: u8` (`src/arch/aarch64/paging.rs:248-255` at the prototype commit) |
| The record of the tables in use is their number, and the tables in use are those of the indices below it | [Terms](contract.md#terms), lines 28 to 30; [Table pool](contract.md#table-pool), lines 616 to 619; [Determinism](contract.md#determinism), lines 732 to 734; the rows of `pt-08` and `pt-13`, lines 942 and 947 | A new table is the one of the lowest free index, a table returns to the pool only through `reset` and through the copy, which gives the target the indices of the source, so the tables in use stay a prefix; `pt-08` counts one more table in use and `pt-13` has a record of 0 |
| The region and the capacity are parameters of the type of a set | [Terms](contract.md#terms), lines 28 to 30; [Copying the kernel tables](contract.md#copying-the-kernel-tables), lines 250 to 252 | A set never holds addresses of the other region, and the copy takes two sets of one region and one capacity with no error for others |
| `Tables::new` takes the storage as it is and sets the record to 1, and `reset` accepts any record, also 0, its plan zeroing the tables below both the record and `N` | [After mapping](contract.md#after-mapping), lines 302 and 303; [Check and execute](contract.md#check-and-execute), lines 684 to 686; the row of `pt-13`, line 947 | Both check nothing and rely on their caller; `pt-13` resets a set whose storage and record are all 0 |
| When a page needs a new level 2 and a new level 3 table, the level 2 table takes the lower free index | [Table pool](contract.md#table-pool), line 616; [Determinism](contract.md#determinism), lines 732 and 733 | "in the order in which its plans first need them": the walk needs the level 2 table first; the table descriptors of `pt-07` depend on it |
| The plan of `map_page` with one new table is `Zero(t3)`, `Store(t3, ...)`, `Fence`, `Store(t2, ...)`, `Sync`; that of `map_block` with a new table `Zero(t2)`, `Store(t2, ...)`, `Fence`, `Store(root, ...)`, `Sync`; without a new table, a `Store` and `Sync` | [Write plans and publication](contract.md#write-plans-and-publication), lines 380 to 389 | The rule of new tables and of new entries, with the plan of two new tables as the contract writes it |
| The plan of `reset` zeroes the tables in index order; that of the copy zeroes the target's tables in use in index order and then stores the valid entries of the source by table index and, in each table, by entry index, with no `Fence`, and `Sync` last | [Write plans and publication](contract.md#write-plans-and-publication), lines 402 to 413 | The contract fixes the `Zero` steps before the stores and `Sync` last, and that no CPU walks the target before its root is installed, so the order among the stores is not observable; index order is the order of the contract's wording |
| The walk of `map_page`, `unmap_page`, `lookup_page` and `lookup_block` reads an entry by its bits 1 and 0 and its address bits 12 to 47: an entry with bits 1 and 0 `0b00` is free; a valid root entry, and a valid level 2 entry other than a block (`0b01`), is a table descriptor, `TableBacking` when its address is not that of a table in use; at level 3, a valid entry takes the slot and is a page leaf when bits 1 and 0 are `0b11` | [Descriptors and attributes](contract.md#descriptors-and-attributes), lines 145 to 153; [Errors of table sets](contract.md#errors-of-table-sets), lines 343 and 345 to 346 | The contract gives the forms that the component writes; a set that the entries built holds no other entry, and the walk must still return for a set whose storage a test wrote |
| `lookup_block` takes a block slot, so a virtual address off 2 MiB is `Alignment`, and it reads the root entry and the level 2 entry only: a level 2 entry that is not a block is `NotMapped`, also a table descriptor | [Errors of table sets](contract.md#errors-of-table-sets), lines 341 and 346; [Work bounds](contract.md#work-bounds), lines 702 to 704 | "for a block, `v` or `p` not of 2 MiB" and "`lookup_block` at a block slot without a block" |
| `map_block` refuses any valid level 2 entry with `AlreadyMapped`, without reading a level 3 table under it | [After mapping](contract.md#after-mapping), line 305; [Errors of table sets](contract.md#errors-of-table-sets), line 345 | A valid level 2 entry is a block, so a page of the block is in $\mathrm{dom}\,M$, or a table, so $v \in P$: the slot is not free of tables |
| `descriptor(kind, address)` takes the address in bits 12 to 47 and drops its other bits | [Descriptors and attributes](contract.md#descriptors-and-attributes), lines 150, 151, 167 and 168 | "every other bit of a leaf is 0", and the function has no error; the entries check the address before they build a descriptor |
| In the copy, a valid entry of the source at level 1 or 2 that is not a table descriptor without an attribute bit is `InvalidDescriptor`: one with an attribute bit, a block, or bits 1 and 0 `0b10`; the root is reached when the walk starts, so a table descriptor that points at it points at a table already reached | [Copying the kernel tables](contract.md#copying-the-kernel-tables), lines 268 to 279 | The order names "a table descriptor with an attribute bit, or a block in its place", and the walk is "from its root" |
| In the copy, an entry of the source with bits 1 and 0 `0b00` is skipped and not copied, also when its other bits are not 0, so the target's entry stays 0 | [Descriptors and attributes](contract.md#descriptors-and-attributes), lines 145 and 146; [Write plans and publication](contract.md#write-plans-and-publication), lines 404 to 411 | An invalid descriptor is one whose bits 1 and 0 are `0b00`, and the copy stores "every valid entry" |
| The checks of `base` and `bits` of the source come before those of the target, so a `bits` outside 32 to 48 is reported with the source's checks, after its `Alignment` | [Copying the kernel tables](contract.md#copying-the-kernel-tables), lines 268 to 270 | `bits` is the width of both pools |
| `PhysRange::new` gives `InvalidRange` for a length of 0 before it adds; the order of its two rules is not observable | [Terms](contract.md#terms), lines 67 to 71; the row of `own-02`, line 890 | A range of length 0 ends at its start, which fits in 64 bits |
| `PhysRange::contains` and `overlaps` take a range, and compare the address sets | [Terms](contract.md#terms), lines 67 to 71; the row of `own-02`, line 890 | The row asks whether a range contains and overlaps ranges |
| $M$ holds a page of a set where the walk reaches a page descriptor whose bits are those of a kind, or the block descriptor of `ReadWrite`; a page of a block maps to the physical page at its offset in the block | [Terms](contract.md#terms), lines 39 to 43; [After mapping](contract.md#after-mapping), line 305 | The contract defines $M$ on the pages of the region; the block row maps $v + i$ to $p + i$ |
| `kernel_map` takes the lower kernel set and `direct_map` the direct map's set, as sets of the lower and the upper region | [Terms](contract.md#terms), lines 47 to 51; [Kernel mappings](contract.md#kernel-mappings), lines 222, 223 and 225 to 228 | The kernel tables are a lower set, which maps the image at its physical addresses, and the direct map's set in the upper region |
| A range of a layout is a physical range, `PhysRange`, mapped at its physical address; the at most 16 ranges and the four kinds of a layout are rules of its type, with no error | [Kernel mappings](contract.md#kernel-mappings), lines 222, 223, 225 to 228, 236 and 237; [Terms](contract.md#terms), lines 67 to 71; [Work bounds](contract.md#work-bounds), line 710 | The contract states both rules of the layout that the board gives and gives no error for them; the image runs at its load address, so a range is one of physical addresses |
| A guard page is named by an address in it, and a range covers it when the range holds that address; `kernel_map` checks the guards against the ranges and not against the set, and writes no entry of a guard page | [Kernel mappings](contract.md#kernel-mappings), lines 233 to 235; [After mapping](contract.md#after-mapping), line 308; [Errors of table sets](contract.md#errors-of-table-sets), line 345 | A range on page boundaries holds an address of a page exactly when it holds the page; "every guard page of $L$ stays outside $\mathrm{dom}\,M'$" is a rule of what the plan writes, since the error table refuses only a range that covers a guard |
| `kernel_map` and `direct_map` check their ranges sorted by the start, ranges of one start in the order of their input, and for each the alignment of its ends, then its width, then the free slots of its leaves one by one in address order: the walk of the leaf, `TableBacking` and then `AlreadyMapped`, and then `AlreadyMapped` for a leaf that an earlier range covers, for `kernel_map` also for a guard page; then `OutOfTables` for the whole plan | [Errors of table sets](contract.md#errors-of-table-sets), lines 341, 342, 345 and 349 to 355; [Kernel direct map](contract.md#kernel-direct-map), lines 447, 457 and 458; [Check and execute](contract.md#check-and-execute), lines 681 to 683 | The order gives alignment, width and the free slots for each range in address order, the walk's `TableBacking` before `AlreadyMapped`, and the tables last; a page of an earlier range is not free once the plan maps it, which makes two ranges that share a page `AlreadyMapped` |
| The width of a range is its end against $2^{39}$ and against $2^{\mathrm{bits}}$, one `AddressWidth` before any leaf of the range | [Errors of table sets](contract.md#errors-of-table-sets), line 342; [Kernel direct map](contract.md#kernel-direct-map), lines 440 to 443, 457 and 458 | A usable range that ends above $2^{39}$ has no direct address, and a range on page boundaries holds a page at or above $2^{\mathrm{bits}}$ exactly when it ends above it |
| The new tables of `kernel_map` and `direct_map` take the lowest free indices in the order in which the walk of the leaves, in address order, first needs them, a level 2 table before the level 3 tables under it | [Table pool](contract.md#table-pool), line 616; [Determinism](contract.md#determinism), lines 732 and 733 | As for `map_page`: the walk needs the level 2 table first |
| The plan of `kernel_map` and `direct_map` builds the tables bottom up: under a new level 2 table, each new level 3 table with its pages, then the level 2 table with its entries in index order, then one `Fence` and the store into the root; a new level 3 table under a level 2 table of the set is followed by one `Fence` and the store of its table descriptor; `Sync` ends the plan. "One `Fence` for each table descriptor" of the work bounds is read as a bound: a `Fence` comes before each store that makes new tables reachable from a table of the set, so there is at most one for each table descriptor | [Write plans and publication](contract.md#write-plans-and-publication), lines 372 to 377, 380 to 389 and 414 to 416; [Work bounds](contract.md#work-bounds), lines 710 to 718; [Determinism](contract.md#determinism), lines 735 to 737 | The rule of new tables writes a table completely before the store that makes it reachable, a table under another new table first, and the plan of two new tables, lines 384 to 386, has one `Fence` for two table descriptors; with that rule the plan of one leaf is that of `map_page` or `map_block` |
| `Sync` ends every plan of `kernel_map` and `direct_map`, also that of a map with no leaf | [Write plans and publication](contract.md#write-plans-and-publication), lines 387 to 389 | A plan whose last store makes an entry valid ends with `Sync`; the copy ends with `Sync` in the same way, and with no store the `Sync` is harmless |
| `direct_map` takes the boot memory map as a value of the fdt specification, any value of its type, and maps its usable ranges, `MemoryPlan.availableRanges` | [Terms](contract.md#terms), lines 52 to 57 and 64 to 66; [Kernel direct map](contract.md#kernel-direct-map), lines 444 to 456 | The contract takes the map as a value that it reads and never changes, and the usable ranges hold no reservation, hole or unmanaged RAM |
| The counts of a direct map, its bytes, blocks and pages, are those of its plan: a block for each `Store` of a block descriptor and a page for each `Store` of a page descriptor | [Entry points](contract.md#entry-points), line 107; [Work bounds](contract.md#work-bounds), lines 714 to 718; the rows of `dm-01` and `dm-02`, lines 966 and 967 | The entry returns a plan; the vectors assert the counts of the map that it writes, and the plan has one `Store` for each block and page |
| The capacities of the kernel tables, 80 and 32, are constants, and the entries are stated for every capacity `N` | [Table pool](contract.md#table-pool), lines 632 to 634 and 646 to 648 | The vectors build direct maps in pools of 2 to 16 tables |

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

Two forms stand for calls of a test that the vector file does not write one
by one:

| Form | Meaning | Vectors |
| --- | --- | --- |
| `map_blocks(set,v,p,count,base,bits)` | The first `count` calls of the loop of `pt-17`: `map_block(set,v+0x200000*i,p+0x200000*i,base,bits)` for `i` from 0 to `count - 1`, in this order, each on the set that the calls before it left; in `call=`, `ok` when every call succeeds and the first error otherwise | `pt-17` |
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
  contract says only that the copy fails. The file gives the errors of the
  order of [copying the kernel tables](contract.md#copying-the-kernel-tables):
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

### Vector disposition

Of the 53 vectors of [legacy test vectors](contract.md#legacy-test-vectors),
these modules answer the 25 of the table sets and of the direct map; the 28
of the page ownership table have no line in the vector file yet.

| Disposition | Vectors | Reason |
| --- | --- | --- |
| Replayed, 21 | `pt-01` to `pt-16`, `pt-18`, `pt-21` and `dm-01` to `dm-03` | Every case is a line of the vector file |
| Replayed with a large input, 2 | `pt-17`, `dm-04` | `pt-17`: 4,103 cases, the 4,096 calls of its loop each a case whose earlier calls are a `map_blocks` item. `dm-04`: the property vector of its row, 4,097 lines by the rule of the row. The generator of the file takes the expected outputs of both from models of the rules of the contract that do not use the specification, and checks them against the literals of the rows |
| Not applicable, 2 | `pt-19`, `pt-20` | The direct map never changes after boot, so the sealing of a page, with the split and merge of its block, is not carried ([behaviour changes](contract.md#legacy-test-vectors), lines 871 to 873) |

The comments of the vector file name the vectors that are not applicable.
The replay module checks one representative case of each vector of the file,
two of `dm-04`, and the whole file is replayed through the same `replay` by
the driver of `cargo xtask formal vectors`.

## Contract correspondence

Each row of the [entry table](contract.md#entry-points) that these modules
state, and the Lean definitions that state its entries, below
`Krepi.Spec.PageTables`:

| Line | Entries | Lean |
| --- | --- | --- |
| 102 | `page_tables::Kind`, `page_tables::descriptor`, `page_tables::direct_address`, `PhysRange::new`, `end`, `contains` and `overlaps`, and `Tables::lookup_page`, `lookup_block` and `used` | `Kind` with `Kind.attributes` and `Attributes.bits`; `descriptor`; `directAddress`; `PhysRange.new`, `PhysRange.endAddr`, `PhysRange.contains`, `PhysRange.overlaps`; `Tables.lookupPage` with `checkEntry` and `Tables.pageLeaf`, `Tables.lookupBlock` with `Tables.walk2`, `Tables.usedTables` |
| 103 | `Tables::new`, `Tables::reset` and `Tables::clone_kernel_from` | `Tables.new`; `Tables.reset`; `Tables.cloneKernelFrom`, with `checkPool`, `Tables.walkRoot`, `Tables.walkLevel2`, `Tables.reach`, `checkLeaves`, `copyableLeaf` and `copyStores` |
| 104 | `Tables::map_page` | `Tables.mapPage`, with `checkEntry`, `checkPhysical` and `Tables.walk2` |
| 105 | `Tables::map_block` | `Tables.mapBlock`, with `checkEntry`, `checkPhysical`, `Tables.walk2` and `blockDescriptor` |
| 106 | `Tables::unmap_page` | `Tables.unmapPage`, with `checkEntry` and `Tables.pageLeaf` |
| 107 | `page_tables::kernel_map` and `page_tables::direct_map` | `Tables.kernelMap` with `Layout`, `LayoutRange`, `layoutKinds`, `sortByKey`, `layoutPages` and `Tables.checkLayoutRange`; `Tables.directMap` with `directLeaves`, `directFuel` and `Tables.checkUsableRange`; both with `Tables.place`, `Tables.checkLeaf`, `assignTables`, `mapPlan` and `Tables.mapLeaves`; `Plan.counts` |

The rules of the contract and the definitions that state them:

| Contract | Lean, below `Krepi.Spec.PageTables` |
| --- | --- |
| [Terms](contract.md#terms): region, table, table set, pool, physical width, kind, abstract mapping, write plan, physical range | `Region` with `Region.holds`; `Table`, `index1`, `index2`, `index3`; `Tables` with `Pool`; `tableAddress`; `widthOk`; `Kind`; `Tables.M`, `Tables.G`, `Tables.P`; `Plan`; `PhysRange` |
| [Descriptors and attributes](contract.md#descriptors-and-attributes): the formats and the kind table | `descriptor`, `blockDescriptor`, `tableDescriptor`, `INVALID`, `typeBits`, `isValid`, `outputAddress`, `blockAddress`, `Kind.attributes`, `Attributes.bits` |
| RO, NX, Device and kernel and user | `Attributes.readOnly`, `writable`, `el0Access`, `executableEl1`, `executableEl0`, `isDevice`, `isGlobal` |
| [Copying the kernel tables](contract.md#copying-the-kernel-tables) | `Tables.cloneKernelFrom` and the definitions of line 103 above |
| [Abstract mapping](contract.md#abstract-mapping): the state of a set | `Tables`, `Tables.M`, `Tables.G`, `Tables.P` |
| [After mapping](contract.md#after-mapping): the rows of `Tables::new`, `reset`, `map_page`, `map_block`, `unmap_page`, `clone_kernel_from`, `kernel_map` and `direct_map` | `Tables.new`, `Tables.reset`, `Tables.mapPage`, `Tables.mapBlock`, `Tables.unmapPage`, `Tables.cloneKernelFrom`, `Tables.kernelMap`, `Tables.directMap`, each with `Tables.apply` of its plan |
| [Errors of table sets](contract.md#errors-of-table-sets): the error table and the order | `TableError`; `checkEntry`, `checkPool` and `checkPhysical`, then the walk (`Tables.walk2`, `Tables.walk`, `Tables.child?`), then the free tables, in each entry; for the maps, `checkPool`, then `Tables.checkLayoutRange` or `Tables.checkUsableRange` for each range in address order with `Tables.place` and `Tables.checkLeaf` for each leaf, then `Tables.mapLeaves` |
| [Write plans and publication](contract.md#write-plans-and-publication): the steps and their order | `Step`, `Plan`, `Step.exec`, `Plan.exec`, `Tables.apply`; the plans of `Tables.mapPage`, `Tables.mapBlock`, `Tables.unmapPage`, `Tables.reset` and `Tables.cloneKernelFrom`; `mapPlan`, with `newLevel2Steps`, `heldLevel2Steps` and `level2Entry`, for `Tables.kernelMap` and `Tables.directMap` |
| [Kernel mappings](contract.md#kernel-mappings): the layout, the identity map of its ranges, their kinds and the guard pages | `Layout`, `LayoutRange`, `layoutKinds`, `MAX_LAYOUT_RANGES`, `layoutPages`, `MapLeaf.isGuard`, `Tables.checkLayoutRange`, `Tables.kernelMap` |
| [Kernel direct map](contract.md#kernel-direct-map): `DIRECT_BASE` and `direct_address` | `DIRECT_BASE`, `directAddress` |
| [Kernel direct map](contract.md#kernel-direct-map): the usable ranges in address order, the block where 2 MiB fit and pages elsewhere, nothing else, the width of $2^{39}$ | `Tables.directMap` with `MemoryPlan.availableRanges` of the fdt specification, `sortByKey`, `directLeaves`, `Tables.checkUsableRange` |
| [Table pool](contract.md#table-pool): the pool and its first checks, the lowest free index, zero storage, the count, the capacities of the kernel tables | `poolFits`, `checkEntry`, `checkPool`; the new tables of `Tables.mapPage` and `Tables.mapBlock` at the record, and of the maps by `assignTables`; `Tables.new` on the storage that its caller gives; `DIRECT_MAP_TABLES`, `KERNEL_TABLES` |
| [Check and execute](contract.md#check-and-execute), for these entries | Each write entry checks every rule before it returns its set and plan, and a failure returns only the error; `Tables.kernelMap` and `Tables.directMap` check every range and the tables of the whole plan first; `Tables.new` and `Tables.reset` have no error; the lookups, `used`, `descriptor` and `directAddress` return values only |
| [Work bounds](contract.md#work-bounds), for these entries | The walk reads one entry at each level; the plans of `map_page`, `map_block` and `unmap_page` have at most seven steps, two of them `Zero`; the walk of the copy folds over the 512 entries of each table that it reaches, at most once each since a table is reached once, and its stores fold over the tables below the record, at most `N`; `Tables.kernelMap` folds over at most 16 ranges and over each page of each once (`layoutPages`), and `Tables.directMap` over each usable range once, in at most $L / 2\,\mathrm{MiB} + 2 \cdot 511$ steps of a block or a page (`directFuel`); the plan of each map has one `Store` for each leaf and table descriptor and one `Zero` for each new table |
| [Determinism](contract.md#determinism), for these entries | Every definition is a function; a new table is the one at the record, the lowest free index; the maps walk their ranges in address order, the direct map with a block wherever the rule allows one |
| [Page ownership](contract.md#page-ownership): the error table | `OwnershipError` |

## Requirement correspondence

Each requirement that these modules serve, the definitions that state it, and
the cases of the
[vector file](../../../../verification/vectors/memory/page-tables.vectors)
that
[`Krepi.SpecTests.PageTables.Replay`](../../../../verification/Krepi/SpecTests/PageTables/Replay.lean)
answers through them. The page ownership table of
[PGT-R08](requirements.md#pgt-r08) to [PGT-R10](requirements.md#pgt-r10),
and its capacities in [PGT-R11](requirements.md#pgt-r11), are specified by
further modules. The parts of [PGT-R05](requirements.md#pgt-r05) to
[PGT-R07](requirements.md#pgt-r07) that a CPU shows, the translation with
the MMU on and the effect of the barriers, belong to the adapter, an
[open obligation](contract.md#open-obligations), and to the QEMU and board
tests of the requirements; these modules state the tables and the plans.

| Requirement | Stated by | Vectors |
| --- | --- | --- |
| [PGT-R01](requirements.md#pgt-r01) | `Kind`, `Kind.attributes`, `Attributes.bits`, `descriptor`, `blockDescriptor`, the permissions of `Attributes`; `Tables.lookupPage`, `Tables.lookupBlock` | `pt-01`, `pt-02`, `pt-06`, `pt-11`, `pt-15`, `pt-21` |
| [PGT-R02](requirements.md#pgt-r02) | `Tables.new`, `Tables.mapPage`, `Tables.lookupPage`, `Tables.usedTables`, `Region.holds` | `pt-01`, `pt-03`, `pt-04`, `pt-05`, `pt-13`, `pt-14` |
| [PGT-R03](requirements.md#pgt-r03) | `Tables.mapBlock`, `Tables.lookupBlock`, `blockDescriptor`; `Tables.unmapPage` and `Tables.mapPage` on a page of a block | `pt-15`, `pt-16`, `pt-17` |
| [PGT-R04](requirements.md#pgt-r04) | `Tables.unmapPage`, `Tables.reset` | `pt-05`, `pt-09`, `pt-11` |
| [PGT-R05](requirements.md#pgt-r05) | `Tables.directMap` with `directLeaves` and `MemoryPlan.availableRanges`; `directAddress`; `Plan.counts`; `Tables.lookupPage`, `Tables.lookupBlock`, `Tables.usedTables` | `dm-01` to `dm-04` |
| [PGT-R06](requirements.md#pgt-r06) | `Tables.kernelMap` with `Layout`, `layoutKinds` and `Tables.checkLayoutRange` | - |
| [PGT-R07](requirements.md#pgt-r07) | `Step`, `Plan`, `Step.exec`; the plans of `Tables.mapPage`, `Tables.mapBlock`, `Tables.unmapPage` and `Tables.cloneKernelFrom`, and `mapPlan` for `Tables.kernelMap` and `Tables.directMap` | - |
| [PGT-R11](requirements.md#pgt-r11), the tables of the direct map | `DIRECT_MAP_TABLES`, `KERNEL_TABLES`; `OutOfTables` of `Tables.mapLeaves` before any write | `dm-03` |
| [PGT-R12](requirements.md#pgt-r12) | `Tables.cloneKernelFrom` | `pt-07`, `pt-08`, `pt-10`, `pt-12`, `pt-18` |

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
block of `pt-15` through `Tables.lookupBlock`.

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
other.

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

### PGT-R04

[PGT-R04](requirements.md#pgt-r04), unmapping and reset, is
`Tables.unmapPage`, whose plan is `Store(t, i, 0)` and then `Invalidate(v)`
and which leaves the record, so the tables under the leaf stay in the pool,
and `Tables.reset`, which leaves the root alone in use and zeroes every table
in use. The replay answers `pt-05`, `pt-09` and `pt-11`, among them the reset
of `pt-09` with every entry 0 after it.

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
its row, with `0x1ffbfe000` bytes. The counts of the four other Pi 5 models
and the translation on QEMU virt are evidence of the host and QEMU tests.

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
test of a shared page and the QEMU tests are its evidence.

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
[open obligation](contract.md#open-obligations).

### PGT-R11

[PGT-R11](requirements.md#pgt-r11), the capacities, is served here for the
tables of the kernel: `DIRECT_MAP_TABLES`, 80, and `KERNEL_TABLES`, 32, and
the refusal of a map that needs more tables than its pool has free with
`OutOfTables`, before any write (`Tables.mapLeaves`). The replay answers
`dm-03`. The capacities of the page ownership table are specified with it.

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

## Dependencies

- The specification of the [fdt](../../boot-platform/fdt/specification.md)
  component, whose boot memory map, `MemoryPlan` with its usable ranges, the
  direct map reads: `Boot.lean` imports `Krepi.Spec.Fdt.Plan`.
- Lean core. No module of the specification imports Mathlib, the Aeneas
  library or a generated module.
