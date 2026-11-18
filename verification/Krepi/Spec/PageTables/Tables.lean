module

public import Krepi.Spec.PageTables.Descriptor

/-!
# Page tables: table sets, the walk and the abstract mapping

The state of a table set of the contract's `Terms` and `Abstract mapping`:
the pool, `N` tables of 512 descriptors, with the root at index 0, and the
record of the tables in use. The region and the capacity `N` are parameters
of the type of a set, since a set never holds addresses of the other region
and the copy of the kernel tables takes two sets of one region and one
capacity. `base` and `bits` are arguments of the entries, as `Table pool`
states, so a set does not hold them.

This module states the entries that write nothing, `Tables::lookup_page`,
`lookup_block` and `used`, with the first checks that every entry on a set
makes (`Errors of table sets`) and the walk of a virtual address through the
three levels. The record of the tables in use is the number of tables in use:
a new table is the one of the lowest free index, and a table returns to the
pool only through `reset` and through `clone_kernel_from`, which gives the
target the indices of the source, so the tables in use of every set that the
entries build are those below the record.

The abstract mapping $M$, with $G$ and $P$, is stated only as propositions
(`Tables.M`, `Tables.G`, `Tables.P`): it is the meaning of the pool, read
through the walk, and no entry computes it.
-/

@[expose] public section

namespace Krepi.Spec.PageTables

/-! ## Pools and sets -/

/-- A table: 512 descriptors of 64 bits, indexed from 0. -/
abbrev Table := Vector UInt64 ENTRIES

/-- The table whose 512 descriptors are 0. -/
def Table.zero : Table := Vector.replicate ENTRIES 0

/-- A pool of `N` tables: the storage of a set, table `i` at
`base` $+ 4096 i$. -/
abbrev Pool (N : Nat) := Vector Table N

/-- The pool of `N` tables that are all zero. -/
def Pool.zero (N : Nat) : Pool N := Vector.replicate N Table.zero

/-- `page_tables::Tables` of a region and a capacity: the pool and the record
of the tables in use, the number of tables in use, which are the tables of
the indices below it. A set that the entries build has its record between 1
and `N`; the type admits any record, as a set whose storage the test or the
caller wrote directly may hold. -/
structure Tables (r : Region) (N : Nat) where
  pool : Pool N
  used : Nat
  deriving DecidableEq

/-- Table `t` of the pool, or the zero table where the pool has none. -/
def Tables.table (s : Tables r N) (t : Nat) : Table :=
  if h : t < N then s.pool[t] else Table.zero

/-- Entry `i` of table `t` of the pool, or 0 where there is none. -/
def Tables.entry (s : Tables r N) (t i : Nat) : UInt64 :=
  if h : i < ENTRIES then (s.table t)[i] else 0

/-- The physical address of table `t` of the pool at `base`. -/
def tableAddress (base : UInt64) (t : Nat) : UInt64 :=
  UInt64.ofNat (base.toNat + PAGE_SIZE * t)

/-- `Tables::used`: the number of tables in use. -/
def Tables.usedTables (s : Tables r N) : Nat := s.used

/-- Whether a pool of `N` tables at `base` holds a table and ends at or below
$2^{\mathrm{bits}}$. -/
def poolFits (N : Nat) (base : UInt64) (bits : UInt8) : Bool :=
  N != 0 && base.toNat + PAGE_SIZE * N ≤ 2 ^ bits.toNat

/-! ## The first checks -/

/-- The first checks of every entry on a set of region `r` and capacity `N`
that takes a virtual address `v`, in the order of the contract, the first
broken rule deciding the error: `v` not a multiple of `align`, 4 KiB for a
page and 2 MiB for a block, or `base` not a multiple of 4 KiB, `Alignment`;
`v` outside the region, or `bits` outside 32 to 48, `AddressWidth`; a pool of
no table, or one that does not end at or below $2^{\mathrm{bits}}$,
`TableBacking`. -/
def checkEntry (r : Region) (N : Nat) (v : UInt64) (align : Nat) (base : UInt64)
    (bits : UInt8) : Except TableError Unit := do
  if v.toNat % align != 0 || base.toNat % PAGE_SIZE != 0 then throw .alignment
  if !r.holds v || !widthOk bits then throw .addressWidth
  if !poolFits N base bits then throw .tableBacking

/-- The first checks of an entry on a pool of `N` tables without a virtual
address: `base` not a multiple of 4 KiB, `Alignment`; `bits` outside 32 to
48, `AddressWidth`; the pool, `TableBacking`. -/
def checkPool (N : Nat) (base : UInt64) (bits : UInt8) : Except TableError Unit := do
  if base.toNat % PAGE_SIZE != 0 then throw .alignment
  if !widthOk bits then throw .addressWidth
  if !poolFits N base bits then throw .tableBacking

/-- The checks of a physical address, after those of the set: not a multiple
of `align`, 4 KiB for a page and 2 MiB for a block, `Alignment`; at or above
$2^{\mathrm{bits}}$, `AddressWidth`. -/
def checkPhysical (p : UInt64) (align : Nat) (bits : UInt8) : Except TableError Unit := do
  if p.toNat % align != 0 then throw .alignment
  if 2 ^ bits.toNat ≤ p.toNat then throw .addressWidth

/-! ## The walk -/

/-- The table in use that a table descriptor `d` of the pool at `base` points
at, when its address, bits 12 to 47, is that of a table in use; none when it
points outside the tables in use. The walk reads a table descriptor by its
bits 1 and 0 and this address alone. -/
def Tables.child? (s : Tables r N) (base d : UInt64) : Option Nat :=
  let a := (outputAddress d).toNat
  if base.toNat ≤ a && (a - base.toNat) / PAGE_SIZE < min s.used N then
    some ((a - base.toNat) / PAGE_SIZE)
  else none

/-- The level 2 table of a virtual address `v`, with its level 2 entry: none
when the root entry of `v` is invalid; `TableBacking` when the root entry is
valid and does not point at a table in use. Every valid root entry is read as
a table descriptor, since the component writes no other valid entry into a
root. -/
def Tables.walk2 (s : Tables r N) (base v : UInt64) : Except TableError (Option (Nat × UInt64)) := do
  let e1 := s.entry 0 (index1 v)
  if !isValid e1 then return none
  let some t2 := s.child? base e1 | throw .tableBacking
  return some (t2, s.entry t2 (index2 v))

/-- Where the walk of a virtual address for a page ends. -/
inductive Reach where
  /-- The root entry of the address is invalid. -/
  | root
  /-- The level 2 entry of the address, in table `t2`, is invalid. -/
  | level2 (t2 : Nat)
  /-- The level 2 entry of the address, in table `t2`, is the block
  descriptor `d`: bits 1 and 0 are `0b01`. -/
  | block (t2 : Nat) (d : UInt64)
  /-- The walk reaches the level 3 entry `d` of the address, in table `t3`
  under table `t2`. -/
  | level3 (t2 t3 : Nat) (d : UInt64)
  deriving DecidableEq, Repr

/-- The walk of a virtual address `v` through the pool at `base`, one entry at
each level: `TableBacking` for a valid root entry, or a valid level 2 entry
other than a block, that does not point at a table in use. -/
def Tables.walk (s : Tables r N) (base v : UInt64) : Except TableError Reach := do
  match ← s.walk2 base v with
  | none => return .root
  | some (t2, e2) =>
    if !isValid e2 then return .level2 t2
    if typeBits e2 == BLOCK then return .block t2 e2
    let some t3 := s.child? base e2 | throw .tableBacking
    return .level3 t2 t3 (s.entry t3 (index3 v))

/-- The page leaf of `v`: the table and the descriptor of its level 3 entry,
when the walk reaches one whose bits 1 and 0 are `0b11`; `NotMapped` for an
address without a page leaf, among them a page of a block. -/
def Tables.pageLeaf (s : Tables r N) (base v : UInt64) : Except TableError (Nat × UInt64) := do
  match ← s.walk base v with
  | .level3 _ t3 d => if typeBits d == TABLE_OR_PAGE then pure (t3, d) else throw .notMapped
  | _ => throw .notMapped

/-! ## Entries that write nothing -/

/-- `Tables::lookup_page(v, base, bits)`: the page descriptor of `v`, or the
error of the first broken rule: the first checks for a page; the walk,
`TableBacking` for a bad table descriptor; `NotMapped` without a page leaf. -/
def Tables.lookupPage (s : Tables r N) (v base : UInt64) (bits : UInt8) : Except TableError UInt64 := do
  checkEntry r N v PAGE_SIZE base bits
  let (_, d) ← s.pageLeaf base v
  pure d

/-- `Tables::lookup_block(v, base, bits)`: the block descriptor at the block
slot `v`, or the error of the first broken rule: the first checks for a block,
so `v` a multiple of 2 MiB; the root entry, `TableBacking` when it does not
point at a table in use; `NotMapped` when the level 2 entry of `v` is not a
block. The walk reads the root entry and the level 2 entry only. -/
def Tables.lookupBlock (s : Tables r N) (v base : UInt64) (bits : UInt8) : Except TableError UInt64 := do
  checkEntry r N v BLOCK_SIZE base bits
  match ← s.walk2 base v with
  | some (_, e2) => if typeBits e2 == BLOCK then pure e2 else throw .notMapped
  | none => throw .notMapped

/-! ## The abstract mapping -/

/-- The form of a leaf of the abstract mapping. -/
inductive Form where
  | page
  | block
  deriving DecidableEq, Repr

/-- The triple of the abstract mapping at a page: a physical page, a kind and a
leaf form. -/
structure Leaf where
  pa : UInt64
  kind : Kind
  form : Form
  deriving DecidableEq, Repr

/-- $M(v) = l$ for the set at `base`: `v` is a 4 KiB-aligned address of the
region, and either the walk of `v` reaches a page descriptor of the kind of
`l` with the output address of `l`, or it reaches a block descriptor of
`ReadWrite` whose block holds `l`, the page of `v` in the block. A page of a
block maps to the page at the same offset in the physical block. -/
def Tables.M (s : Tables r N) (base v : UInt64) (l : Leaf) : Prop :=
  r.holds v = true ∧ v.toNat % PAGE_SIZE = 0 ∧
    ((∃ t2 t3 d, s.walk base v = .ok (.level3 t2 t3 d) ∧ typeBits d = TABLE_OR_PAGE ∧
        Kind.ofPage d = some l.kind ∧ l.pa = outputAddress d ∧ l.form = .page) ∨
      (∃ t2 d, s.walk base v = .ok (.block t2 d) ∧ isReadWriteBlock d = true ∧
        l.kind = .readWrite ∧ l.form = .block ∧
        l.pa.toNat = (blockAddress d).toNat + v.toNat % BLOCK_SIZE))

/-- $g \in G$ for the set at `base`: `g` is a 1 GiB-aligned address of the
region whose root entry points at a table in use, so the set holds a level 2
table under the slot. -/
def Tables.G (s : Tables r N) (base g : UInt64) : Prop :=
  r.holds g = true ∧ g.toNat % GIB_SIZE = 0 ∧ ∃ t2 e2, s.walk2 base g = .ok (some (t2, e2))

/-- $b \in P$ for the set at `base`: `b` is a 2 MiB-aligned address of the
region whose level 2 entry points at a table in use, so the set holds a level
3 table under the slot. -/
def Tables.P (s : Tables r N) (base b : UInt64) : Prop :=
  r.holds b = true ∧ b.toNat % BLOCK_SIZE = 0 ∧
    ∃ t2 t3 d, s.walk base b = .ok (.level3 t2 t3 d)

end Krepi.Spec.PageTables
