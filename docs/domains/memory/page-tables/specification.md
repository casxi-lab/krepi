---
specifications:
  - Krepi.Spec.PageTables.Basic
  - Krepi.Spec.PageTables.Descriptor
  - Krepi.Spec.PageTables.Tables
  - Krepi.Spec.PageTables.Plan
  - Krepi.Spec.PageTables.Map
---

# Page-tables specification

The Lean specification of the `page-tables` component, written from its
[requirements](requirements.md) and [contract](contract.md) and never from an
implementation. It is an executable model: every entry is a computable
definition whose body is public (`@[expose]`), none is `noncomputable` or
chooses with `Classical.choice`, and every loop is structural recursion on a
list whose length the contract bounds. The modules lie below
[`verification/Krepi/Spec/PageTables/`](../../../../verification/Krepi/Spec/PageTables/)
and import Lean core and the earlier modules of the component alone.

This page describes the modules of the table sets: the descriptors and kinds,
the physical ranges, the pools with the record of their tables in use, the
walk, the write plans and the entries of rows 102 to 106 of the
[entry table](contract.md#entry-points). The kernel mappings, the direct map,
the page ownership table and the tokens of the
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
| `Tables.lookupPage`, `Tables.lookupBlock`, `Tables.usedTables`, `descriptor`, `directAddress`, the functions of `PhysRange` | Nothing |

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

### Vector notation

The vector file holds the cases of
[legacy test vectors](contract.md#legacy-test-vectors), one line for each
call of an entry that a test makes with the output that it asserts, in the
order of the test. The entries of a table set are calls on state that earlier
calls built, so an input holds the whole test up to the case:

| Field | Meaning |
| --- | --- |
| `sets=` | The sets of the test, `-` for none, `<name>:<region>:<N>` joined by `,`: a set that `Tables::new` makes on zero storage, of region `lower` or `upper` and capacity `N`; `<name>:<region>:<N>:<record>` is zero storage with that record of tables in use |
| `do=` | The earlier calls and writes of the test, `-` for none, joined by `;`; a write entry that succeeds has its plan executed |
| `call=` | The call of the case: `map_page(set,v,p,kind,base,bits)`, `map_block(set,v,p,base,bits)`, `unmap_page(set,v,base,bits)`, `lookup_page(set,v,base,bits)`, `lookup_block(set,v,base,bits)`, `used(set)`, `reset(set)`, `clone_kernel_from(target,source,source_base,base,bits)` or `descriptor(kind,address)` |
| `ask=` | What the test asserts of the state after the call, `-` for nothing, joined by `;`: `unchanged(set)`, whether the set, its pool and its record, is the one from before the call; `zero(set)`, whether every entry of its pool is 0; `entry(set,table,index)`, an entry |

The two writes of a test, which are not entries, are
`set_entry(set,table,index,descriptor)`, which writes an entry of the
storage, and `set_used(set,record)`, which writes the record; `pt-08` uses
them as its test writes the source directly. The output of a call is `ok`,
followed by its fields, or `err=<error>`: `unmap_page` gives `page=`,
`lookup_page`, `lookup_block` and `descriptor` give `descriptor=`, and `used`
gives `used=`; then each item of `ask=` gives `<item>=<value>`.

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

### Vector disposition

The vectors `pt-01` to `pt-10` are replayed: every case of each is a line of
the vector file, 99 cases, and the replay module checks one representative
case of each. The other vectors of
[legacy test vectors](contract.md#legacy-test-vectors) have no line in the
vector file yet.

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

The rules of the contract and the definitions that state them:

| Contract | Lean, below `Krepi.Spec.PageTables` |
| --- | --- |
| [Terms](contract.md#terms): region, table, table set, pool, physical width, kind, abstract mapping, write plan, physical range | `Region` with `Region.holds`; `Table`, `index1`, `index2`, `index3`; `Tables` with `Pool`; `tableAddress`; `widthOk`; `Kind`; `Tables.M`, `Tables.G`, `Tables.P`; `Plan`; `PhysRange` |
| [Descriptors and attributes](contract.md#descriptors-and-attributes): the formats and the kind table | `descriptor`, `blockDescriptor`, `tableDescriptor`, `INVALID`, `typeBits`, `isValid`, `outputAddress`, `blockAddress`, `Kind.attributes`, `Attributes.bits` |
| RO, NX, Device and kernel and user | `Attributes.readOnly`, `writable`, `el0Access`, `executableEl1`, `executableEl0`, `isDevice`, `isGlobal` |
| [Copying the kernel tables](contract.md#copying-the-kernel-tables) | `Tables.cloneKernelFrom` and the definitions of line 103 above |
| [Abstract mapping](contract.md#abstract-mapping): the state of a set | `Tables`, `Tables.M`, `Tables.G`, `Tables.P` |
| [After mapping](contract.md#after-mapping): the rows of `Tables::new`, `reset`, `map_page`, `map_block`, `unmap_page` and `clone_kernel_from` | `Tables.new`, `Tables.reset`, `Tables.mapPage`, `Tables.mapBlock`, `Tables.unmapPage`, `Tables.cloneKernelFrom`, each with `Tables.apply` of its plan |
| [Errors of table sets](contract.md#errors-of-table-sets): the error table and the order | `TableError`; `checkEntry`, `checkPool` and `checkPhysical`, then the walk (`Tables.walk2`, `Tables.walk`, `Tables.child?`), then the free tables, in each entry |
| [Write plans and publication](contract.md#write-plans-and-publication): the steps and their order | `Step`, `Plan`, `Step.exec`, `Plan.exec`, `Tables.apply`; the plans of `Tables.mapPage`, `Tables.mapBlock`, `Tables.unmapPage`, `Tables.reset` and `Tables.cloneKernelFrom` |
| [Kernel direct map](contract.md#kernel-direct-map): `DIRECT_BASE` and `direct_address` | `DIRECT_BASE`, `directAddress` |
| [Table pool](contract.md#table-pool): the pool and its first checks, the lowest free index, zero storage | `poolFits`, `checkEntry`, `checkPool`; the new tables of `Tables.mapPage` and `Tables.mapBlock` at the record; `Tables.new` on the storage that its caller gives |
| [Check and execute](contract.md#check-and-execute), for these entries | Each write entry checks every rule before it returns its set and plan, and a failure returns only the error; `Tables.new` and `Tables.reset` have no error; the lookups, `used`, `descriptor` and `directAddress` return values only |
| [Work bounds](contract.md#work-bounds), for these entries | The walk reads one entry at each level; the plans of `map_page`, `map_block` and `unmap_page` have at most seven steps, two of them `Zero`; the walk of the copy folds over the 512 entries of each table that it reaches, at most once each since a table is reached once, and its stores fold over the tables below the record, at most `N` |
| [Determinism](contract.md#determinism), for these entries | Every definition is a function; a new table is the one at the record, the lowest free index |
| [Page ownership](contract.md#page-ownership): the error table | `OwnershipError` |

## Requirement correspondence

Each requirement that these modules serve, the definitions that state it, and
the cases of the
[vector file](../../../../verification/vectors/memory/page-tables.vectors)
that
[`Krepi.SpecTests.PageTables.Replay`](../../../../verification/Krepi/SpecTests/PageTables/Replay.lean)
answers through them. The kernel direct map, the kernel mappings and the page
ownership table of
[PGT-R05](requirements.md#pgt-r05), [PGT-R06](requirements.md#pgt-r06) and
[PGT-R08](requirements.md#pgt-r08) to [PGT-R11](requirements.md#pgt-r11) are
specified by further modules.

| Requirement | Stated by | Vectors |
| --- | --- | --- |
| [PGT-R01](requirements.md#pgt-r01) | `Kind`, `Kind.attributes`, `Attributes.bits`, `descriptor`, `blockDescriptor`, the permissions of `Attributes`; `Tables.lookupPage`, `Tables.lookupBlock` | `pt-01`, `pt-02`, `pt-06` |
| [PGT-R02](requirements.md#pgt-r02) | `Tables.new`, `Tables.mapPage`, `Tables.lookupPage`, `Tables.usedTables`, `Region.holds` | `pt-01`, `pt-03`, `pt-04`, `pt-05` |
| [PGT-R03](requirements.md#pgt-r03) | `Tables.mapBlock`, `Tables.lookupBlock`, `blockDescriptor`; `Tables.unmapPage` and `Tables.mapPage` on a page of a block | - |
| [PGT-R04](requirements.md#pgt-r04) | `Tables.unmapPage`, `Tables.reset` | `pt-05`, `pt-09` |
| [PGT-R07](requirements.md#pgt-r07) | `Step`, `Plan`, `Step.exec`; the plans of `Tables.mapPage`, `Tables.mapBlock`, `Tables.unmapPage` and `Tables.cloneKernelFrom` | - |
| [PGT-R12](requirements.md#pgt-r12) | `Tables.cloneKernelFrom` | `pt-07`, `pt-08`, `pt-10` |

### PGT-R01

[PGT-R01](requirements.md#pgt-r01), the descriptor kinds, is `Kind` with the
rows of `Kind.attributes`, placed by `Attributes.bits`: `descriptor` gives the
page descriptor of each kind, its address in bits 12 to 47 and every other
bit 0 or a bit of the row, and `blockDescriptor` the block form of
`ReadWrite`. The permissions of `Attributes` read the rows, so that the rules
of the requirement are statements on the bits: no kind is writable and
executable; the kernel kinds give EL0 no access and are global except
`KernelPrivateReadWrite`; the user kinds are not global and do not execute at
EL1; `Device` and `UserDevice` have AttrIndx 0. The replay answers the descriptors of `pt-02` and
`pt-06` through `descriptor`, and those that `pt-01` and `pt-06` read back
through `Tables.lookupPage`.

### PGT-R02

[PGT-R02](requirements.md#pgt-r02), mapping and looking up a page, is
`Tables.mapPage` and `Tables.lookupPage` on a set of `Tables.new`: the first
checks, the physical address, the walk and the free tables, each with the
error of the contract in its order, and a refused call returns its error
alone, so no table changes and the record stays. `Region.holds` in the first
checks makes a lower set refuse the addresses of the upper region and the
other way round. The replay answers `pt-01`, `pt-03`, `pt-04` and `pt-05`,
whose cases of `used` after each refusal give the count unchanged.

### PGT-R03

[PGT-R03](requirements.md#pgt-r03), blocks, is `Tables.mapBlock`: one level 2
descriptor of `ReadWrite` at a 2 MiB-aligned address, refused with
`AlreadyMapped` where the level 2 entry is valid, so a level 3 table never
becomes a block; `Tables.lookupPage` and `Tables.unmapPage` give `NotMapped`
for a page of a block and `Tables.mapPage` gives `AlreadyMapped`, so a block
never becomes pages. Its vectors, `pt-15` to `pt-17`, have no line in the
vector file yet.

### PGT-R04

[PGT-R04](requirements.md#pgt-r04), unmapping and reset, is
`Tables.unmapPage`, whose plan is `Store(t, i, 0)` and then `Invalidate(v)`
and which leaves the record, so the tables under the leaf stay in the pool,
and `Tables.reset`, which leaves the root alone in use and zeroes every table
in use. The replay answers `pt-05` and `pt-09`, among them the reset of
`pt-09` with every entry 0 after it.

### PGT-R07

[PGT-R07](requirements.md#pgt-r07), write plans, is `Plan` with the plans of
the entries: each new table is zeroed and written before the one store of
the table descriptor that makes it reachable, with a `Fence` before that
store; a plan that makes an entry valid ends with `Sync`; the plan of an
unmap stores the invalid entry and then invalidates the address; no step
fails, since `Step.exec` is total. The plans of the kernel mappings and the
direct map are specified with their entries. The execution of the steps on
hardware is the adapter's, an [open obligation](contract.md#open-obligations).

### PGT-R12

[PGT-R12](requirements.md#pgt-r12), copying the kernel tables, is
`Tables.cloneKernelFrom`: the checks of the two pools, their overlap and the
record of the source, then the walk of the source in its order, before any
write; the plan zeroes the target's tables in use and stores every valid
entry of the source into the target's table of the same index, the leaves as
they are, global ones included, and the table descriptors pointing into the
target's pool. The tables of the copy are the target's own, so a later plan
on either set writes only its own pool. The replay answers `pt-07`, `pt-08`
and `pt-10`, with the target unchanged after each refusal.

## Dependencies

- The specification of the [fdt](../../boot-platform/fdt/specification.md)
  component, whose boot memory map the direct map reads, by the modules of
  the direct map.
- Lean core. No module of the specification imports Mathlib, the Aeneas
  library or a generated module.
