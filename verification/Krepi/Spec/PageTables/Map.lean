module

public import Krepi.Spec.PageTables.Plan

/-!
# Page tables: the write entries of a set

The write entries of a set in the contract's entry table, `Tables::new`,
`reset` and `clone_kernel_from`, `map_page`, `map_block` and `unmap_page`,
with the rules of `Abstract mapping`, `Copying the kernel tables`,
`Table pool`, `Write plans and publication` and `Check and execute`.

Each write entry checks every rule before it writes, in the order of
`Errors of table sets`, so that the first broken rule decides the error, and
a failure returns that error and nothing else: no plan, and no change of the
record of the tables in use. A success returns the set after the write phase,
whose record holds the tables that the plan takes from the pool, and the plan;
the caller executes the plan (`Tables.apply`) before anything else runs on the
set. `Tables::new` and `reset` check nothing and do not fail.

A new table is the one of the lowest free index. When a page needs a new
level 2 and a new level 3 table, the walk needs the level 2 table first, so it
takes the lower index.
-/

@[expose] public section

namespace Krepi.Spec.PageTables

/-! ## Creation and reset -/

/-- `Tables::new(storage)`: the set of the storage, with the root alone in
use. It checks nothing: it relies on its caller for storage that is zero in all
its `N` tables, and then $M = \emptyset$ and $G = P = \emptyset$. -/
def Tables.new (storage : Pool N) : Tables r N := ⟨storage, 1⟩

/-- `Tables::reset`: the record leaves the root alone in use, and the plan is
a `Zero` of every table in use, in the order of their indices. It checks
nothing: it relies on its caller for a set that no CPU holds in a `TTBR` and
no TLB translates. -/
def Tables.reset (s : Tables r N) : Tables r N × Plan :=
  ({ s with used := 1 }, (List.range (min s.used N)).map Step.zero)

/-! ## Pages and blocks -/

/-- `Tables::map_page(v, p, k, base, bits)`: maps the page `v` of the region to
the physical page `p` with kind `k`, or the error of the first broken rule:
the first checks for a page (`checkEntry`); `p` (`checkPhysical`); the walk,
`TableBacking` for a bad table descriptor, then `AlreadyMapped` for a page or
a block that covers `v`; and last `OutOfTables` when the pool has fewer free
tables than the new ones that the page needs.

The plan writes each new table before the store of the table descriptor that
makes it reachable, with a `Fence` before that store, and ends with `Sync`:

- a new level 2 table `t2` and level 3 table `t3`: `Zero(t3)`, `Store(t3, ...)`
  of the page, `Zero(t2)`, `Store(t2, ...)` of the table descriptor of `t3`,
  `Fence`, `Store(root, ...)` of the table descriptor of `t2`, `Sync`;
- a new level 3 table `t3`: `Zero(t3)`, `Store(t3, ...)` of the page, `Fence`,
  `Store(t2, ...)` of the table descriptor of `t3`, `Sync`;
- no new table: `Store(t3, ...)` of the page, `Sync`. -/
def Tables.mapPage (s : Tables r N) (v p : UInt64) (k : Kind) (base : UInt64) (bits : UInt8) :
    Except TableError (Tables r N × Plan) := do
  checkEntry r N v PAGE_SIZE base bits
  checkPhysical p PAGE_SIZE bits
  let page := descriptor k p
  match ← s.walk2 base v with
  | none =>
    if N - s.used < 2 then throw .outOfTables
    let t2 := s.used
    let t3 := s.used + 1
    pure ({ s with used := s.used + 2 },
      [.zero t3, .store t3 (index3 v) page,
        .zero t2, .store t2 (index2 v) (tableDescriptor (tableAddress base t3)),
        .fence, .store 0 (index1 v) (tableDescriptor (tableAddress base t2)), .sync])
  | some (t2, e2) =>
    if !isValid e2 then
      if N - s.used < 1 then throw .outOfTables
      let t3 := s.used
      pure ({ s with used := s.used + 1 },
        [.zero t3, .store t3 (index3 v) page,
          .fence, .store t2 (index2 v) (tableDescriptor (tableAddress base t3)), .sync])
    else if typeBits e2 == BLOCK then throw .alreadyMapped
    else
      let some t3 := s.child? base e2 | throw .tableBacking
      if isValid (s.entry t3 (index3 v)) then throw .alreadyMapped
      pure (s, [.store t3 (index3 v) page, .sync])

/-- `Tables::map_block(v, p, base, bits)`: maps the block slot `v` to the
physical block `p` as `ReadWrite` with one level 2 descriptor, or the error of
the first broken rule: the first checks for a block (`checkEntry`), so `v` a
multiple of 2 MiB; `p` (`checkPhysical`), a multiple of 2 MiB below
$2^{\mathrm{bits}}$; the root entry, `TableBacking` when it does not point at a
table in use; `AlreadyMapped` when the level 2 entry of `v` is valid, a block
or a level 3 table, so the slot is not free of tables; and last `OutOfTables`
when the pool has no free table for a new level 2 table. It never turns a
level 3 table into a block.

The plan of a new level 2 table `t2` is `Zero(t2)`, `Store(t2, ...)` of the
block, `Fence`, `Store(root, ...)` of the table descriptor of `t2`, `Sync`;
without a new table, `Store(t2, ...)` of the block, `Sync`. -/
def Tables.mapBlock (s : Tables r N) (v p base : UInt64) (bits : UInt8) :
    Except TableError (Tables r N × Plan) := do
  checkEntry r N v BLOCK_SIZE base bits
  checkPhysical p BLOCK_SIZE bits
  let block := blockDescriptor p
  match ← s.walk2 base v with
  | none =>
    if N - s.used < 1 then throw .outOfTables
    let t2 := s.used
    pure ({ s with used := s.used + 1 },
      [.zero t2, .store t2 (index2 v) block,
        .fence, .store 0 (index1 v) (tableDescriptor (tableAddress base t2)), .sync])
  | some (t2, e2) =>
    if isValid e2 then throw .alreadyMapped
    pure (s, [.store t2 (index2 v) block, .sync])

/-- `Tables::unmap_page(v, base, bits)`: removes the page leaf of `v` and gives
its physical page, or the error of the first broken rule: the first checks for
a page (`checkEntry`); the walk, `TableBacking` for a bad table descriptor, then
`NotMapped` without a page leaf, among them a page of a block. The plan is
`Store(t, i, 0)` of the leaf and then `Invalidate(v)`; the tables under the
leaf stay in use, so the record does not change. -/
def Tables.unmapPage (s : Tables r N) (v base : UInt64) (bits : UInt8) :
    Except TableError (Plan × UInt64) := do
  checkEntry r N v PAGE_SIZE base bits
  let (t3, d) ← s.pageLeaf base v
  pure ([.store t3 (index3 v) INVALID, .invalidate v], outputAddress d)

/-! ## Copying the kernel tables -/

/-- The kinds that a leaf of the source of a copy may have. -/
def copyKinds : List Kind := [.readExecute, .readOnly, .readWrite, .device]

/-- Whether a leaf of the source may be copied: the page descriptor of one of
`ReadExecute`, `ReadOnly`, `ReadWrite` and `Device`, with an output address
below $2^{\mathrm{bits}}$. -/
def copyableLeaf (bits : UInt8) (d : UInt64) : Bool :=
  copyKinds.any (fun k => descriptor k (outputAddress d) == d) &&
    (outputAddress d).toNat < 2 ^ bits.toNat

/-- The tables that the walk of the source has reached, the root first, and
those of them at level 3. -/
structure Visit where
  reached : List Nat
  leaves : List Nat
  deriving DecidableEq, Repr

/-- One valid entry `d` of the source at level 1 or 2: a table descriptor with
an attribute bit, a block in its place, or another valid entry that is not a
table descriptor, `InvalidDescriptor`; one that points at a table outside the
tables in use or at a table already reached, `TableBacking`. Otherwise the
table that it reaches, now reached. -/
def Tables.reach (source : Tables r N) (sourceBase d : UInt64) (st : Visit) :
    Except TableError (Nat × Visit) := do
  if !isPlainTableDescriptor d then throw .invalidDescriptor
  let some t := source.child? sourceBase d | throw .tableBacking
  if st.reached.contains t then throw .tableBacking
  pure (t, { st with reached := st.reached ++ [t] })

/-- The leaves of a level 3 table of the source, in index order: a valid entry
that is not the page descriptor of a kind of `copyKinds` below
$2^{\mathrm{bits}}$, `InvalidDescriptor`. -/
def checkLeaves (bits : UInt8) : List UInt64 → Except TableError Unit
  | [] => pure ()
  | d :: rest =>
    if isValid d && !copyableLeaf bits d then throw .invalidDescriptor
    else checkLeaves bits rest

/-- The entries of a level 2 table of the source, in index order, each table
under its entry before the next entry. -/
def Tables.walkLevel2 (source : Tables r N) (sourceBase : UInt64) (bits : UInt8) :
    List UInt64 → Visit → Except TableError Visit
  | [], st => pure st
  | d :: rest, st =>
    if !isValid d then source.walkLevel2 sourceBase bits rest st
    else do
      let (t3, st) ← source.reach sourceBase d st
      checkLeaves bits (source.table t3).toList
      source.walkLevel2 sourceBase bits rest { st with leaves := st.leaves ++ [t3] }

/-- The entries of the root of the source, in index order, each table under
its entry before the next entry. -/
def Tables.walkRoot (source : Tables r N) (sourceBase : UInt64) (bits : UInt8) :
    List UInt64 → Visit → Except TableError Visit
  | [], st => pure st
  | d :: rest, st =>
    if !isValid d then source.walkRoot sourceBase bits rest st
    else do
      let (t2, st) ← source.reach sourceBase d st
      let st ← source.walkLevel2 sourceBase bits (source.table t2).toList st
      source.walkRoot sourceBase bits rest st

/-- The stores of the copy for the entries `ds` of table `t` of the source,
from entry `i`: a `Store` of every valid entry into the target's table of the
same index, a leaf as it is and a table descriptor pointing at the target's
table of the index that it points at in the source. -/
def copyStores (sourceBase base : UInt64) (leaf : Bool) (t : Nat) : List UInt64 → Nat → Plan
  | [], _ => []
  | d :: rest, i =>
    let more := copyStores sourceBase base leaf t rest (i + 1)
    if !isValid d then more
    else
      let stored :=
        if leaf then d
        else tableDescriptor (tableAddress base (((outputAddress d).toNat - sourceBase.toNat) / PAGE_SIZE))
      .store t i stored :: more

/-- `Tables::clone_kernel_from(source, source_base, base, bits)` on the target:
fills the target with a private copy of the source, or the error of the first
broken rule, checked in this order:

1. `source_base` and `bits` of the source and then `base` of the target, each
   with the first checks of a pool (`checkPool`);
2. the two pools overlap, `TableBacking`; the record of the source holds no
   table or more than `N`, `TableBacking`;
3. the walk of the source from its root, entry by entry in index order and
   each table under its entry before the next entry (`Tables.walkRoot`): a
   table descriptor with an attribute bit or a block in its place,
   `InvalidDescriptor`; one that points outside the tables in use or at a table
   already reached, `TableBacking`; a leaf of another kind or at or above
   $2^{\mathrm{bits}}$, `InvalidDescriptor`;
4. a table in use of the source that the walk did not reach, `TableBacking`.

The record of the target becomes that of the source. The plan is a `Zero` of
every table in use of the target, in index order; then a `Store` of every
valid entry of every table in use of the source into the target's table of
the same index, the tables in index order and the entries of each in index
order, the table descriptors pointing into the target's pool; and `Sync` last.
The entry does not check that no CPU and no TLB holds the target, and the
caller holds the token of the source. -/
def Tables.cloneKernelFrom (target source : Tables r N) (sourceBase base : UInt64) (bits : UInt8) :
    Except TableError (Tables r N × Plan) := do
  checkPool N sourceBase bits
  checkPool N base bits
  if sourceBase.toNat < base.toNat + PAGE_SIZE * N && base.toNat < sourceBase.toNat + PAGE_SIZE * N then
    throw .tableBacking
  if source.used == 0 || N < source.used then throw .tableBacking
  let st ← source.walkRoot sourceBase bits (source.table 0).toList ⟨[0], []⟩
  if (List.range source.used).any (fun t => !st.reached.contains t) then throw .tableBacking
  let stores := (List.range source.used).flatMap fun t =>
    copyStores sourceBase base (st.leaves.contains t) t (source.table t).toList 0
  pure ({ target with used := source.used },
    (List.range (min target.used N)).map Step.zero ++ stores ++ [.sync])

end Krepi.Spec.PageTables
