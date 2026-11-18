module

public import Krepi.Spec.PageTables.Tokens
public import Krepi.SpecProperties.Fdt.Invariants

/-!
# Page tables: invariants

The invariants of the state of the `page-tables` component and the
statements that its entries establish and preserve them. The state is a
table set, its pool with the record of its tables in use; a page ownership
table, its banks, extents, exclusion records, generation counter and arena;
and the shared fields of the contract's `State fields`, the two kernel sets
and the page ownership table with whether the MMU is on, which the
transactions of `Krepi.Spec.PageTables.Tokens` write under their tokens.

The invariants are of two kinds:

- **Structural**, each quantified over a whole table of the state: the
  descriptors of every table of a set and its tables in use
  (`Tables.WellFormed`, the well-formedness of the page tables); the banks,
  the extents and the exclusion records of a page ownership table
  (`Ownership.WellFormed`); and the fields of the shared state
  (`Shared.WellFormed`).
- **Functional**, what the state means beyond the shape of its tables: one
  owner for every managed page (`Ownership.OneOwner`, the uniqueness of page
  ownership); the pages of one holder generation (`Ownership.HolderRanges`);
  the generations below the counter (`Ownership.GenerationsBelowCounter`);
  one free extent for each free run (`Ownership.FreeExtentsMaximal`); the
  free and held pages of the table of the kernel root against the boot
  memory map (`Ownership.FreeOrHeldUsable`); and the offset of the direct
  map (`Shared.DirectMapOffset`).

Each invariant is a proposition with a computable check, `check...`, whose
agreement with it is a statement below, on every value or, for a functional
invariant that reads the extents, on every value that keeps the structural
invariant. The statements are propositions that theorems below
`Krepi.Proofs.PageTables` prove; they are of four groups: the checks; the
establishment of the invariants by the entries that build their values;
the preservation of each functional invariant by each operation that
changes it; and one lemma for each operation that it preserves
well-formedness, apart from the functional statements. Lines are those of
the contract, `docs/domains/memory/page-tables/contract.md`. The
definitions extend the namespace of the specification, so that they read
as fields of its values.
-/

@[expose] public section

namespace Krepi.Spec.PageTables

/-! ## Pools -/

/-- A pool of `N` tables at `base` that the contract admits at the width
`bits`: `base` a multiple of 4 KiB, `bits` from 32 to 48, and at least one
table, the last ending at or below $2^{\mathrm{bits}}$ (lines 35 to 40 and
654 and 655). These are the first checks of `checkPool`. -/
def PoolOk (N : Nat) (base : UInt64) (bits : UInt8) : Prop :=
  base.toNat % PAGE_SIZE = 0 ∧ widthOk bits = true ∧ poolFits N base bits = true

/-- The check of `PoolOk`. -/
def poolOk (N : Nat) (base : UInt64) (bits : UInt8) : Bool :=
  base.toNat % PAGE_SIZE == 0 && widthOk bits && poolFits N base bits

/-- Entry `i` of table `t` of a pool, or 0 where there is none. -/
def Pool.get (p : Pool N) (t i : Nat) : UInt64 :=
  if h : t < N then (if hi : i < ENTRIES then p[t][i] else 0) else 0

/-! ## Table sets -/

/-- Entry `i` of table `t` of the set at `base` points at table `c`: the
entry is a table descriptor with no attribute whose address is that of
table `c`, a table in use (`Tables.child?`). -/
def Tables.PointsAt (s : Tables r N) (base : UInt64) (t i c : Nat) : Prop :=
  i < ENTRIES ∧ isPlainTableDescriptor (s.entry t i) = true ∧ s.child? base (s.entry t i) = some c

/-- Table `t` is a level 2 table of the set at `base`: an entry of the root
points at it. -/
def Tables.IsLevel2 (s : Tables r N) (base : UInt64) (t : Nat) : Prop :=
  ∃ i, s.PointsAt base 0 i t

/-- Table `t` is a level 3 table of the set at `base`: an entry of a level 2
table points at it. -/
def Tables.IsLevel3 (s : Tables r N) (base : UInt64) (t : Nat) : Prop :=
  ∃ t2 i, s.IsLevel2 base t2 ∧ s.PointsAt base t2 i t

/-- Table `t` holds the table descriptors of a walk: the root or a level 2
table. -/
def Tables.IsParent (s : Tables r N) (base : UInt64) (t : Nat) : Prop :=
  t = 0 ∨ s.IsLevel2 base t

/-- **Structural invariant of a table set: the page tables are
well-formed.** At `base` and the width `bits`:

- the pool is one that the contract admits (`PoolOk`), and its record
  holds the root and at most `N` tables (lines 28 to 37 and 654 and 655);
- every table that is not in use is zero (line 664);
- every entry of the root is invalid, and so 0, or a table descriptor with
  no attribute of a table in use (lines 149 to 152);
- every entry of a level 2 table is 0, such a table descriptor, or the
  block descriptor of `ReadWrite` at an output address below
  $2^{\mathrm{bits}}$ (lines 149 to 158);
- every entry of a level 3 table is 0 or the page descriptor of a kind at an
  output address below $2^{\mathrm{bits}}$, every other bit 0 (lines 149 to
  158, 172 and 173);
- the table descriptors of the root and of the level 2 tables reach every
  table in use but the root exactly once, and the root never (lines 265 and
  266), so that the tables in use are the root and one table for each
  element of $G$ and of $P$ (lines 297 and 298).

These are the rules of the tables that the entries of the contract write,
and those that `clone_kernel_from` checks of its source. -/
def Tables.WellFormed (s : Tables r N) (base : UInt64) (bits : UInt8) : Prop :=
  PoolOk N base bits ∧
  1 ≤ s.used ∧ s.used ≤ N ∧
  (∀ t, s.used ≤ t → t < N → s.table t = Table.zero) ∧
  (∀ i, i < ENTRIES → s.entry 0 i = 0 ∨ ∃ c, s.PointsAt base 0 i c) ∧
  (∀ t, s.IsLevel2 base t → ∀ i, i < ENTRIES →
    s.entry t i = 0 ∨ (∃ c, s.PointsAt base t i c) ∨
      (isReadWriteBlock (s.entry t i) = true ∧
        (blockAddress (s.entry t i)).toNat < 2 ^ bits.toNat)) ∧
  (∀ t, s.IsLevel3 base t → ∀ i, i < ENTRIES →
    s.entry t i = 0 ∨
      ((∃ k, s.entry t i = descriptor k (outputAddress (s.entry t i))) ∧
        (outputAddress (s.entry t i)).toNat < 2 ^ bits.toNat)) ∧
  (∀ t i, s.IsParent base t → ¬ s.PointsAt base t i 0) ∧
  (∀ c, 1 ≤ c → c < s.used → ∃ t i, s.IsParent base t ∧ s.PointsAt base t i c) ∧
  (∀ t i t' i' c, s.IsParent base t → s.IsParent base t' →
    s.PointsAt base t i c → s.PointsAt base t' i' c → t = t' ∧ i = i')

/-- The table that entry `i` of table `t` points at, when it is a table
descriptor with no attribute of a table in use. -/
def Tables.pointsAt? (s : Tables r N) (base : UInt64) (t i : Nat) : Option Nat :=
  if isPlainTableDescriptor (s.entry t i) then s.child? base (s.entry t i) else none

/-- The tables that the entries of table `t` point at, in index order. -/
def Tables.childrenOf (s : Tables r N) (base : UInt64) (t : Nat) : List Nat :=
  (List.range ENTRIES).filterMap (s.pointsAt? base t)

/-- The level 2 tables, once for each root entry that points at one. -/
def Tables.level2Tables (s : Tables r N) (base : UInt64) : List Nat := s.childrenOf base 0

/-- The level 3 tables, once for each entry of a level 2 table that points
at one. -/
def Tables.level3Tables (s : Tables r N) (base : UInt64) : List Nat :=
  (s.level2Tables base).flatMap (s.childrenOf base)

/-- The check of `Tables.WellFormed`: the tables that the root and the level
2 tables point at are, once each, the tables from 1 below the record. -/
def Tables.checkWellFormed (s : Tables r N) (base : UInt64) (bits : UInt8) : Bool :=
  let entries := List.range ENTRIES
  poolOk N base bits && decide (1 ≤ s.used) && decide (s.used ≤ N) &&
  (List.range N).all (fun t => decide (t < s.used) || s.table t == Table.zero) &&
  entries.all (fun i => s.entry 0 i == 0 || (s.pointsAt? base 0 i).isSome) &&
  (s.level2Tables base).all (fun t => entries.all fun i =>
    let d := s.entry t i
    d == 0 || (s.pointsAt? base t i).isSome ||
      (isReadWriteBlock d && decide ((blockAddress d).toNat < 2 ^ bits.toNat))) &&
  (s.level3Tables base).all (fun t => entries.all fun i =>
    let d := s.entry t i
    d == 0 || ((Kind.ofPage d).isSome && decide ((outputAddress d).toNat < 2 ^ bits.toNat))) &&
  sortByKey id (s.level2Tables base ++ s.level3Tables base) == List.range' 1 (s.used - 1)

/-- The first address of a region: 0 for the lower region and `DIRECT_BASE`
for the upper. -/
def Region.first : Region → Nat
  | .lower => 0
  | .upper => DIRECT_BASE.toNat

/-- The leaves of the set at `base` that the walk reads, in index order, each
with the virtual address of its page or block, its form and its descriptor:
the block descriptors of `ReadWrite` of the level 2 tables and the page
descriptors of a kind of the level 3 tables, under root and level 2 entries
that point at tables in use. They are the leaves of $M$ (`Tables.M`), a block
once for its 512 pages. -/
def Tables.leaves (s : Tables r N) (base : UInt64) : List (Nat × Form × UInt64) :=
  (List.range ENTRIES).flatMap fun i =>
    let e1 := s.entry 0 i
    if !isValid e1 then [] else
    match s.child? base e1 with
    | none => []
    | some t2 => (List.range ENTRIES).flatMap fun j =>
      let e2 := s.entry t2 j
      let va := r.first + i * GIB_SIZE + j * BLOCK_SIZE
      if !isValid e2 then []
      else if typeBits e2 == BLOCK then (if isReadWriteBlock e2 then [(va, .block, e2)] else [])
      else match s.child? base e2 with
        | none => []
        | some t3 => (List.range ENTRIES).filterMap fun k =>
          let d := s.entry t3 k
          if typeBits d == TABLE_OR_PAGE && (Kind.ofPage d).isSome then
            some (va + k * PAGE_SIZE, .page, d)
          else none

/-! ## The page ownership table -/

/-- A managed page of the table: a page, a multiple of 4 KiB, that lies
wholly in a managed bank (line 62). -/
def Ownership.ManagedPage (t : Ownership E X) (q : Nat) : Prop :=
  q % PAGE_SIZE = 0 ∧ ∃ b ∈ t.banks, b.holdsPage q = true

/-- An extent lies in the bank that it names. -/
def Extent.InBank (e : Extent) (banks : List PhysRange) : Prop :=
  ∃ b, banks[e.bank]? = some b ∧ b.contains e.range = true

/-- **Structural invariant of a page ownership table.** The arena is not 0
(line 86); there is at least one bank, every bank starts and ends on a page
boundary, and the banks are in address order and do not overlap (lines 535
to 537); at most `E` extents, free and held together (lines 624 and 625),
each a range of whole pages in the bank that it names (lines 87 and 88),
in address order and disjoint (line 786); at most `X` exclusion records
(lines 630 to 634); and a counter that has given no generation 0, since it
starts at 1 (line 606). -/
def Ownership.WellFormed (t : Ownership E X) : Prop :=
  t.arena ≠ 0 ∧
  t.banks ≠ [] ∧ (∀ b ∈ t.banks, b.onPages = true) ∧
  t.banks.Pairwise (fun a b => a.endNat ≤ b.start.toNat) ∧
  t.extents.length ≤ E ∧
  (∀ e ∈ t.extents, e.range.onPages = true ∧ e.InBank t.banks) ∧
  t.extents.Pairwise (fun a b => a.range.endNat ≤ b.range.start.toNat) ∧
  t.exclusions.length ≤ X ∧
  t.counter ≠ .next 0

/-- The check of `Ownership.WellFormed`. -/
def Ownership.checkWellFormed (t : Ownership E X) : Bool :=
  t.arena != 0 && !t.banks.isEmpty && t.banks.all (·.onPages) &&
  Fdt.allPairs (fun a b => decide (a.endNat ≤ b.start.toNat)) t.banks &&
  decide (t.extents.length ≤ E) &&
  t.extents.all (fun e => e.range.onPages &&
    match t.banks[e.bank]? with
    | some b => b.contains e.range
    | none => false) &&
  Fdt.allPairs (fun a b => decide (a.range.endNat ≤ b.range.start.toNat)) t.extents &&
  decide (t.exclusions.length ≤ X) && t.counter != .next 0

/-- The owners that the table records for the page at `q`: the holding of
each extent that holds the page and, when exclusion records touch it, the
first of their owners in the order firmware, image, boot storage. -/
def Ownership.ownersOf (t : Ownership E X) (q : Nat) : List Owner :=
  (t.extents.filter (·.range.holdsPage q)).map (·.holding.owner) ++
    ((firstExcluder t.exclusions q).map Owner.excluded).toList

/-- **Functional invariant of a page ownership table: the uniqueness of page
ownership.** "Every managed page has exactly one owner" (line 520): the table
records exactly one owner for each managed page, the holding of one extent
or, for a page in no extent, that of the exclusion records that touch it, so
that the owner function $O$ (`Ownership.ownerOf`) gives it. -/
def Ownership.OneOwner (t : Ownership E X) : Prop :=
  ∀ q, t.ManagedPage q → (t.ownersOf q).length = 1

/-- The runs `[a, b)` of `runs` less the pages `[start, stop)` of each of
`cuts`. -/
def cutAll (cuts : List (Nat × Nat)) (runs : List (Nat × Nat)) : List (Nat × Nat) :=
  cuts.foldl (fun runs c => cutRuns c.1 c.2 runs) runs

/-- The check of `Ownership.OneOwner` on a well-formed table: no exclusion
record shares an address with an extent, and the extents with the pages
that the exclusion records touch cover every bank. -/
def Ownership.checkOneOwner (t : Ownership E X) : Bool :=
  t.extents.all (fun e => t.exclusions.all fun x => !x.range.overlaps e.range) &&
  t.banks.all fun b =>
    cutAll ((t.extents.map fun e => (e.range.start.toNat, e.range.endNat)) ++
      t.exclusions.filterMap (·.cut b)) [(b.start.toNat, b.endNat)] == []

/-- **Functional invariant of a page ownership table: the holders.** "The
pages of one holder generation form one range in one bank, the range of one
extent, and two holders never share a generation" (lines 521 and 522): the
pages whose owner is a holder of the generation of a held extent are exactly
the pages of that extent, a range of whole pages in one bank, so they are of
that one holder. A receipt, a reservation or a packet names such a range
(lines 338 to 340 and 597 to 605). -/
def Ownership.HolderRanges (t : Ownership E X) : Prop :=
  ∀ e ∈ t.extents, ∀ o n s, e.holding = .held o n s →
    ∀ q, q % PAGE_SIZE = 0 →
      ((∃ o' s', t.ownerOf q = some (.held o' n s')) ↔ e.range.holdsPage q = true)

/-- The generation of a holding, none for free pages. -/
def Holding.generation? : Holding → Option UInt64
  | .free => none
  | .held _ n _ => some n

/-- The check of `Ownership.HolderRanges` on a well-formed table that keeps
`Ownership.OneOwner`: no two held extents have one generation. -/
def Ownership.checkHolderRanges (t : Ownership E X) : Bool :=
  Fdt.allPairs (fun a b =>
    match a.holding.generation?, b.holding.generation? with
    | some n, some m => n != m
    | _, _ => true) t.extents

/-- **Functional invariant of a page ownership table: the generations.**
"The generation counter starts at 1, grows by one with each allocation and
reservation, and is never reused" (lines 606 to 608), and "the generation of
an allocation is the counter of the table" (line 794): every holder has a
generation from 1 that is below the counter, so that the counter gives a
generation that no holder has. -/
def Ownership.GenerationsBelowCounter (t : Ownership E X) : Prop :=
  ∀ q o n s, t.ownerOf q = some (.held o n s) →
    1 ≤ n.toNat ∧ ∀ g, t.counter = .next g → n.toNat < g.toNat

/-- The check of `Ownership.GenerationsBelowCounter` on a well-formed table. -/
def Ownership.checkGenerationsBelowCounter (t : Ownership E X) : Bool :=
  t.extents.all fun e =>
    match e.holding.generation? with
    | some n => decide (1 ≤ n.toNat) &&
      match t.counter with
      | .next g => decide (n.toNat < g.toNat)
      | .exhausted => true
    | none => true

/-- **Functional invariant of a page ownership table: the free runs.** "A
released or cancelled extent merges with the free extents next to it in the
same bank" (lines 605 and 606), and the table uses "one extent for each free
run" (lines 627 and 628): no free extent ends where a free extent of its bank
starts, so that, with `Ownership.OneOwner`, each free extent is a maximal
run of the free pages of its bank. -/
def Ownership.FreeExtentsMaximal (t : Ownership E X) : Prop :=
  ∀ a ∈ t.extents, ∀ b ∈ t.extents, a.holding = .free → b.holding = .free →
    a.bank = b.bank → a.range.endNat ≠ b.range.start.toNat

/-- The check of `Ownership.FreeExtentsMaximal`. -/
def Ownership.checkFreeExtentsMaximal (t : Ownership E X) : Bool :=
  t.extents.all fun a => t.extents.all fun b =>
    !(a.holding == .free && b.holding == .free && a.bank == b.bank &&
      a.range.endNat == b.range.start.toNat)

/-- Whether an owner is free or a holder. -/
def Owner.isFreeOrHeld : Owner → Bool
  | .free => true
  | .excluded _ => false
  | .held .. => true

/-- Whether the page at `q` is a page of a usable range of the boot memory
map `B`: a multiple of 4 KiB whose page lies wholly in one of
`MemoryPlan.availableRanges` (line 68). -/
def usablePage (B : Fdt.MemoryPlan) (q : Nat) : Bool :=
  q % PAGE_SIZE == 0 && B.availableRanges.any fun u => u.start.toNat ≤ q && q + PAGE_SIZE ≤ u.endNat

/-- **Functional invariant of the table of the kernel root.** "In the table
of the kernel root, which the boot wiring builds from the boot memory map,
the pages that are free or held are exactly the pages of its usable ranges,
so exactly the pages of the direct map" (lines 523 to 525): for the boot
memory map `B`, a page is free or held exactly when it is a page of a usable
range of `B`. -/
def Ownership.FreeOrHeldUsable (t : Ownership E X) (B : Fdt.MemoryPlan) : Prop :=
  ∀ q, q % PAGE_SIZE = 0 →
    ((∃ o, t.ownerOf q = some o ∧ o.isFreeOrHeld = true) ↔ usablePage B q = true)

/-- The pages of `[a, b)`, its start rounded up and its end rounded down to a
page, as an interval; none when no page lies wholly in it. -/
def pageInterval (a b : Nat) : List (Nat × Nat) :=
  if pageUp a < pageDown b then [(pageUp a, pageDown b)] else []

/-- The check of `Ownership.FreeOrHeldUsable` on a well-formed table that
keeps `Ownership.OneOwner`, whose free and held pages are those of its
extents: the extents cover the pages of every usable range, and the usable
ranges cover the pages of every extent. -/
def Ownership.checkFreeOrHeldUsable (t : Ownership E X) (B : Fdt.MemoryPlan) : Bool :=
  let extents := t.extents.map fun e => (e.range.start.toNat, e.range.endNat)
  let usable := B.availableRanges.flatMap fun u => pageInterval u.start.toNat u.endNat
  usable.all (fun u => cutAll extents [u] == []) && extents.all fun e => cutAll usable [e] == []

/-- The invariants of one page ownership table together: the hypothesis of
the preservation statements. -/
def Ownership.Invariant (t : Ownership E X) : Prop :=
  t.WellFormed ∧ t.OneOwner ∧ t.HolderRanges ∧ t.GenerationsBelowCounter ∧ t.FreeExtentsMaximal

/-- `c` is a choice that `choose` gives on the table: the requirement of
`assign`, "the choice $c$ of `choose` for owner identity $o$, taken under the
same token" (line 336). -/
def Ownership.Chose (t : Ownership E X) (c : Choice) : Prop :=
  ∃ owner pages alignment p, t.choose owner pages alignment p = .ok c

/-- The banks and the exclusions that the boot wiring gives `Ownership::new`
for the boot memory map `B`, by their ranges: the managed banks of `B` as
physical ranges, in their order, and one exclusion for each span of its boot
storage and each firmware reservation, in any order, each with an owner
(lines 71 to 75, 532 and 533). -/
def BootTableRanges (B : Fdt.MemoryPlan) (banks : List PhysRange) (exclusions : List Exclusion) :
    Prop :=
  banks.map (fun r => (r.start, r.len)) = B.managed.map (fun s => (s.start, s.size)) ∧
  (exclusions.map fun x => (x.range.start, x.range.len)).Perm
    (B.reservations.map fun s => (s.start, s.size))

/-! ## The shared state -/

/-- Where the kernel tables are and the physical width: the bases of the
pools of the lower kernel set and of the direct map's set, in the BSS of the
image, and `bits`, which the entries on them take as arguments. -/
structure Config where
  lowerBase : UInt64
  directBase : UInt64
  bits : UInt8
  deriving DecidableEq, Repr

/-- **Structural invariant of the shared state.** Both kernel sets are
well-formed in their pools, and the page ownership table, once built, is
well-formed: the fields of lines 803 to 806. -/
def Shared.WellFormed (s : Shared E X) (cfg : Config) : Prop :=
  s.lowerKernel.WellFormed cfg.lowerBase cfg.bits ∧
  s.directMap.WellFormed cfg.directBase cfg.bits ∧
  ∀ t, s.ownership = some t → t.WellFormed

/-- The check of `Shared.WellFormed`. -/
def Shared.checkWellFormed (s : Shared E X) (cfg : Config) : Bool :=
  s.lowerKernel.checkWellFormed cfg.lowerBase cfg.bits &&
  s.directMap.checkWellFormed cfg.directBase cfg.bits &&
  match s.ownership with
  | some t => t.checkWellFormed
  | none => true

/-- **Functional invariant of the shared state: the offset of the direct
map.** The direct map is "the mapping of `DIRECT_BASE | pa` to `pa`" (lines
54 and 55) as `ReadWrite` (lines 467 to 469), and it covers RAM below
$2^{39}$ (line 488): every page of the direct map's set maps
`DIRECT_BASE | pa` to a physical page `pa` below $2^{39}$ as `ReadWrite`. -/
def Shared.DirectMapOffset (s : Shared E X) (cfg : Config) : Prop :=
  ∀ v l, s.directMap.M cfg.directBase v l →
    v = DIRECT_BASE ||| l.pa ∧ l.pa.toNat < VA_LIMIT ∧ l.kind = .readWrite

/-- The check of `Shared.DirectMapOffset`, leaf by leaf: a block maps
`DIRECT_BASE | pa` to `pa` for its 512 pages when its first page does. -/
def Shared.checkDirectMapOffset (s : Shared E X) (cfg : Config) : Bool :=
  (s.directMap.leaves cfg.directBase).all fun (va, form, d) =>
    let pa := match form with
      | .block => (blockAddress d).toNat
      | .page => (outputAddress d).toNat
    decide (pa < VA_LIMIT) && va == DIRECT_BASE.toNat + pa &&
      (form == .block || Kind.ofPage d == some .readWrite)

end Krepi.Spec.PageTables

namespace Krepi.SpecProperties.PageTables

open Krepi.Spec.PageTables

/-! ## The checks

Each check agrees with its invariant: the structural checks and the check of
the free runs and of the offset of the direct map on every value, also one
that no entry builds; the other functional checks on every table that keeps
the invariants that they read. -/

/-- `Tables.checkWellFormed` decides `Tables.WellFormed`. -/
def CheckTablesWellFormed : Prop :=
  ∀ (r : Region) (N : Nat) (s : Tables r N) (base : UInt64) (bits : UInt8),
    s.checkWellFormed base bits = true ↔ s.WellFormed base bits

/-- `Ownership.checkWellFormed` decides `Ownership.WellFormed`. -/
def CheckOwnershipWellFormed : Prop :=
  ∀ (E X : Nat) (t : Ownership E X), t.checkWellFormed = true ↔ t.WellFormed

/-- `Shared.checkWellFormed` decides `Shared.WellFormed`. -/
def CheckSharedWellFormed : Prop :=
  ∀ (E X : Nat) (s : Shared E X) (cfg : Config), s.checkWellFormed cfg = true ↔ s.WellFormed cfg

/-- On a well-formed table, `Ownership.checkOneOwner` decides
`Ownership.OneOwner`. -/
def CheckOneOwner : Prop :=
  ∀ (E X : Nat) (t : Ownership E X), t.WellFormed → (t.checkOneOwner = true ↔ t.OneOwner)

/-- On a well-formed table with one owner for every managed page,
`Ownership.checkHolderRanges` decides `Ownership.HolderRanges`. -/
def CheckHolderRanges : Prop :=
  ∀ (E X : Nat) (t : Ownership E X), t.WellFormed → t.OneOwner →
    (t.checkHolderRanges = true ↔ t.HolderRanges)

/-- On a well-formed table, `Ownership.checkGenerationsBelowCounter` decides
`Ownership.GenerationsBelowCounter`. -/
def CheckGenerationsBelowCounter : Prop :=
  ∀ (E X : Nat) (t : Ownership E X), t.WellFormed →
    (t.checkGenerationsBelowCounter = true ↔ t.GenerationsBelowCounter)

/-- `Ownership.checkFreeExtentsMaximal` decides `Ownership.FreeExtentsMaximal`. -/
def CheckFreeExtentsMaximal : Prop :=
  ∀ (E X : Nat) (t : Ownership E X), t.checkFreeExtentsMaximal = true ↔ t.FreeExtentsMaximal

/-- On a well-formed table with one owner for every managed page,
`Ownership.checkFreeOrHeldUsable` decides `Ownership.FreeOrHeldUsable`. -/
def CheckFreeOrHeldUsable : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (B : Krepi.Spec.Fdt.MemoryPlan), t.WellFormed → t.OneOwner →
    (t.checkFreeOrHeldUsable B = true ↔ t.FreeOrHeldUsable B)

/-- `Shared.checkDirectMapOffset` decides `Shared.DirectMapOffset`. -/
def CheckDirectMapOffset : Prop :=
  ∀ (E X : Nat) (s : Shared E X) (cfg : Config),
    s.checkDirectMapOffset cfg = true ↔ s.DirectMapOffset cfg

/-! ## Establishment

The entries that build a value establish its invariants: `Tables::new` on
zero storage, and the kernel tables that `kernel_map` and `direct_map`
write into such sets at boot; the shared state of the boot; and
`Ownership::new`, with the free and held pages of the table of the kernel
root from the boot memory map. `reset` and `clone_kernel_from` establish
the invariant of their result from any record; their statements are in the
last group. -/

/-- `Tables::new` on storage that is zero in all its tables, in a pool that
the contract admits, gives a well-formed set: the root alone in use. -/
def NewWellFormed : Prop :=
  ∀ (r : Region) (N : Nat) (base : UInt64) (bits : UInt8), PoolOk N base bits →
    (Tables.new (Pool.zero N) : Tables r N).WellFormed base bits

/-- `kernel_map` on the lower set of `Tables::new` on zero storage gives a
well-formed set once its plan has run. -/
def BootKernelMapWellFormed : Prop :=
  ∀ (N : Nat) (layout : Layout) (base : UInt64) (bits : UInt8) (s : Tables .lower N) (plan : Plan),
    PoolOk N base bits →
    (Tables.new (Pool.zero N) : Tables .lower N).kernelMap layout base bits = .ok (s, plan) →
    (s.apply plan).WellFormed base bits

/-- `direct_map` on the upper set of `Tables::new` on zero storage gives a
well-formed set once its plan has run. -/
def BootDirectMapWellFormed : Prop :=
  ∀ (N : Nat) (memory : Krepi.Spec.Fdt.MemoryPlan) (base : UInt64) (bits : UInt8)
    (s : Tables .upper N) (plan : Plan), PoolOk N base bits →
    (Tables.new (Pool.zero N) : Tables .upper N).directMap memory base bits = .ok (s, plan) →
    (s.apply plan).WellFormed base bits

/-- The shared state of the boot, both kernel sets of `Tables::new` on zero
pools that the contract admits, is well-formed. -/
def BootWellFormed : Prop :=
  ∀ (E X : Nat) (cfg : Config), PoolOk KERNEL_TABLES cfg.lowerBase cfg.bits →
    PoolOk DIRECT_MAP_TABLES cfg.directBase cfg.bits →
    (Shared.boot BootCpu.boot (Pool.zero _) (Pool.zero _) : Shared E X).WellFormed cfg

/-- The shared state of the boot keeps the offset of the direct map: its
direct map's set maps nothing. -/
def BootDirectMapOffset : Prop :=
  ∀ (E X : Nat) (cfg : Config),
    (Shared.boot BootCpu.boot (Pool.zero _) (Pool.zero _) : Shared E X).DirectMapOffset cfg

/-- The table of `Ownership::new` is well-formed. -/
def NewOwnershipWellFormed : Prop :=
  ∀ (E X : Nat) (arena : UInt64) (banks : List PhysRange) (exclusions : List Exclusion)
    (t : Ownership E X), Ownership.new arena banks exclusions = .ok t → t.WellFormed

/-- The table of `Ownership::new` records one owner for every managed page. -/
def NewOneOwner : Prop :=
  ∀ (E X : Nat) (arena : UInt64) (banks : List PhysRange) (exclusions : List Exclusion)
    (t : Ownership E X), Ownership.new arena banks exclusions = .ok t → t.OneOwner

/-- The table of `Ownership::new` keeps the ranges of the holders: it has
none. -/
def NewHolderRanges : Prop :=
  ∀ (E X : Nat) (arena : UInt64) (banks : List PhysRange) (exclusions : List Exclusion)
    (t : Ownership E X), Ownership.new arena banks exclusions = .ok t → t.HolderRanges

/-- The table of `Ownership::new` keeps the generations below the counter:
it has no holder. -/
def NewGenerationsBelowCounter : Prop :=
  ∀ (E X : Nat) (arena : UInt64) (banks : List PhysRange) (exclusions : List Exclusion)
    (t : Ownership E X), Ownership.new arena banks exclusions = .ok t → t.GenerationsBelowCounter

/-- The table of `Ownership::new` has one free extent for each free run. -/
def NewFreeExtentsMaximal : Prop :=
  ∀ (E X : Nat) (arena : UInt64) (banks : List PhysRange) (exclusions : List Exclusion)
    (t : Ownership E X), Ownership.new arena banks exclusions = .ok t → t.FreeExtentsMaximal

/-- The table of the kernel root, which `Ownership::new` builds from the
managed banks and the exclusions of a well-formed boot memory map, has as
its free and held pages exactly the pages of the usable ranges of that map.
-/
def NewFreeOrHeldUsable : Prop :=
  ∀ (E X : Nat) (B : Krepi.Spec.Fdt.MemoryPlan) (arena : UInt64) (banks : List PhysRange)
    (exclusions : List Exclusion) (t : Ownership E X),
    B.WellFormed → BootTableRanges B banks exclusions →
    Ownership.new arena banks exclusions = .ok t → t.FreeOrHeldUsable B

/-! ## Preservation

Each write entry of the page ownership table that changes it, `assign`,
`reserve`, `publish`, `cancel` and `release`, preserves each functional
invariant of the table, on a table that keeps all of them. `assign` takes a
choice of `choose` on the same table, its requirement. The write entries of
a set have no functional invariant of one state to preserve: what a set
means is its abstract mapping, whose change by each entry is
`Krepi.SpecProperties.PageTables.AfterEveryWrite`. Of the transactions of the
shared state only `direct_map` writes the direct map's set. -/

/-- `assign` keeps one owner for every managed page. -/
def AssignOneOwner : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (c : Choice) (zeroed : Bool) (t' : Ownership E X)
    (a : Allocation), t.Invariant → t.Chose c → t.assign c zeroed = .ok (t', a) → t'.OneOwner

/-- `reserve` keeps one owner for every managed page. -/
def ReserveOneOwner : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner pages alignment : UInt64) (p : Placement)
    (t' : Ownership E X) (r : Reservation),
    t.Invariant → t.reserve owner pages alignment p = .ok (t', r) → t'.OneOwner

/-- `publish` keeps one owner for every managed page. -/
def PublishOneOwner : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner : UInt64) (x : Initialized) (t' : Ownership E X)
    (a : Allocation), t.Invariant → t.publish owner x = .ok (t', a) → t'.OneOwner

/-- `cancel` keeps one owner for every managed page. -/
def CancelOneOwner : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner : UInt64) (r : Reservation) (t' : Ownership E X),
    t.Invariant → t.cancel owner r = .ok t' → t'.OneOwner

/-- `release` keeps one owner for every managed page. -/
def ReleaseOneOwner : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner : UInt64) (x : Allocation) (t' : Ownership E X),
    t.Invariant → t.release owner x = .ok t' → t'.OneOwner

/-- `assign` keeps the ranges of the holders. -/
def AssignHolderRanges : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (c : Choice) (zeroed : Bool) (t' : Ownership E X)
    (a : Allocation), t.Invariant → t.Chose c → t.assign c zeroed = .ok (t', a) → t'.HolderRanges

/-- `reserve` keeps the ranges of the holders. -/
def ReserveHolderRanges : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner pages alignment : UInt64) (p : Placement)
    (t' : Ownership E X) (r : Reservation),
    t.Invariant → t.reserve owner pages alignment p = .ok (t', r) → t'.HolderRanges

/-- `publish` keeps the ranges of the holders. -/
def PublishHolderRanges : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner : UInt64) (x : Initialized) (t' : Ownership E X)
    (a : Allocation), t.Invariant → t.publish owner x = .ok (t', a) → t'.HolderRanges

/-- `cancel` keeps the ranges of the holders. -/
def CancelHolderRanges : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner : UInt64) (r : Reservation) (t' : Ownership E X),
    t.Invariant → t.cancel owner r = .ok t' → t'.HolderRanges

/-- `release` keeps the ranges of the holders. -/
def ReleaseHolderRanges : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner : UInt64) (x : Allocation) (t' : Ownership E X),
    t.Invariant → t.release owner x = .ok t' → t'.HolderRanges

/-- `assign` keeps the generations below the counter. -/
def AssignGenerationsBelowCounter : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (c : Choice) (zeroed : Bool) (t' : Ownership E X)
    (a : Allocation), t.Invariant → t.Chose c → t.assign c zeroed = .ok (t', a) →
    t'.GenerationsBelowCounter

/-- `reserve` keeps the generations below the counter. -/
def ReserveGenerationsBelowCounter : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner pages alignment : UInt64) (p : Placement)
    (t' : Ownership E X) (r : Reservation),
    t.Invariant → t.reserve owner pages alignment p = .ok (t', r) → t'.GenerationsBelowCounter

/-- `publish` keeps the generations below the counter. -/
def PublishGenerationsBelowCounter : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner : UInt64) (x : Initialized) (t' : Ownership E X)
    (a : Allocation), t.Invariant → t.publish owner x = .ok (t', a) → t'.GenerationsBelowCounter

/-- `cancel` keeps the generations below the counter. -/
def CancelGenerationsBelowCounter : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner : UInt64) (r : Reservation) (t' : Ownership E X),
    t.Invariant → t.cancel owner r = .ok t' → t'.GenerationsBelowCounter

/-- `release` keeps the generations below the counter. -/
def ReleaseGenerationsBelowCounter : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner : UInt64) (x : Allocation) (t' : Ownership E X),
    t.Invariant → t.release owner x = .ok t' → t'.GenerationsBelowCounter

/-- `assign` keeps one free extent for each free run. -/
def AssignFreeExtentsMaximal : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (c : Choice) (zeroed : Bool) (t' : Ownership E X)
    (a : Allocation), t.Invariant → t.Chose c → t.assign c zeroed = .ok (t', a) →
    t'.FreeExtentsMaximal

/-- `reserve` keeps one free extent for each free run. -/
def ReserveFreeExtentsMaximal : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner pages alignment : UInt64) (p : Placement)
    (t' : Ownership E X) (r : Reservation),
    t.Invariant → t.reserve owner pages alignment p = .ok (t', r) → t'.FreeExtentsMaximal

/-- `publish` keeps one free extent for each free run. -/
def PublishFreeExtentsMaximal : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner : UInt64) (x : Initialized) (t' : Ownership E X)
    (a : Allocation), t.Invariant → t.publish owner x = .ok (t', a) → t'.FreeExtentsMaximal

/-- `cancel` keeps one free extent for each free run. -/
def CancelFreeExtentsMaximal : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner : UInt64) (r : Reservation) (t' : Ownership E X),
    t.Invariant → t.cancel owner r = .ok t' → t'.FreeExtentsMaximal

/-- `release` keeps one free extent for each free run. -/
def ReleaseFreeExtentsMaximal : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner : UInt64) (x : Allocation) (t' : Ownership E X),
    t.Invariant → t.release owner x = .ok t' → t'.FreeExtentsMaximal

/-- `assign` keeps the free and held pages of the table of the kernel root.
-/
def AssignFreeOrHeldUsable : Prop :=
  ∀ (E X : Nat) (B : Krepi.Spec.Fdt.MemoryPlan) (t : Ownership E X) (c : Choice) (zeroed : Bool)
    (t' : Ownership E X) (a : Allocation), t.Invariant → t.FreeOrHeldUsable B → t.Chose c →
    t.assign c zeroed = .ok (t', a) → t'.FreeOrHeldUsable B

/-- `reserve` keeps the free and held pages of the table of the kernel root.
-/
def ReserveFreeOrHeldUsable : Prop :=
  ∀ (E X : Nat) (B : Krepi.Spec.Fdt.MemoryPlan) (t : Ownership E X) (owner pages alignment : UInt64)
    (p : Placement) (t' : Ownership E X) (r : Reservation),
    t.Invariant → t.FreeOrHeldUsable B → t.reserve owner pages alignment p = .ok (t', r) →
    t'.FreeOrHeldUsable B

/-- `publish` keeps the free and held pages of the table of the kernel root.
-/
def PublishFreeOrHeldUsable : Prop :=
  ∀ (E X : Nat) (B : Krepi.Spec.Fdt.MemoryPlan) (t : Ownership E X) (owner : UInt64) (x : Initialized)
    (t' : Ownership E X) (a : Allocation), t.Invariant → t.FreeOrHeldUsable B →
    t.publish owner x = .ok (t', a) → t'.FreeOrHeldUsable B

/-- `cancel` keeps the free and held pages of the table of the kernel root.
-/
def CancelFreeOrHeldUsable : Prop :=
  ∀ (E X : Nat) (B : Krepi.Spec.Fdt.MemoryPlan) (t : Ownership E X) (owner : UInt64) (r : Reservation)
    (t' : Ownership E X), t.Invariant → t.FreeOrHeldUsable B → t.cancel owner r = .ok t' →
    t'.FreeOrHeldUsable B

/-- `release` keeps the free and held pages of the table of the kernel root.
-/
def ReleaseFreeOrHeldUsable : Prop :=
  ∀ (E X : Nat) (B : Krepi.Spec.Fdt.MemoryPlan) (t : Ownership E X) (owner : UInt64) (x : Allocation)
    (t' : Ownership E X), t.Invariant → t.FreeOrHeldUsable B → t.release owner x = .ok t' →
    t'.FreeOrHeldUsable B

/-- `direct_map` by the boot CPU keeps the offset of the direct map. -/
def BuildDirectMapOffset : Prop :=
  ∀ (E X : Nat) (cfg : Config) (cpu : BootCpu) (s : Shared E X) (memory : Krepi.Spec.Fdt.MemoryPlan)
    (s' : Shared E X) (plan : Plan), s.WellFormed cfg → s.DirectMapOffset cfg →
    s.buildDirectMap cpu memory cfg.directBase cfg.bits = some (.ok (s', plan)) →
    s'.DirectMapOffset cfg

/-! ## Well-formedness

One lemma for each operation: on a well-formed value, the value that it
returns is well-formed. The operations are the write entries of a set, once
the plan has run; the write entries of the page ownership table; and the
transactions of the shared state. `reset` and `clone_kernel_from` need only
the zero storage of the tables not in use, so their lemmas are also the
establishment of the invariant of their result; `Tables::new` and
`Ownership::new` are in the group of establishment. `Reservation::initialized`
changes no table, and the read entries return values, so they have no lemma.
-/

/-- `reset` of a set whose tables not in use are zero, in a pool that the
contract admits, gives a well-formed set, from any record. -/
def ResetWellFormed : Prop :=
  ∀ (r : Region) (N : Nat) (s : Tables r N) (base : UInt64) (bits : UInt8),
    PoolOk N base bits → (∀ t, s.used ≤ t → t < N → s.table t = Table.zero) →
    (s.reset.1.apply s.reset.2).WellFormed base bits

/-- `clone_kernel_from` into a target whose tables not in use are zero gives
a well-formed target, from any source that it accepts. -/
def CloneKernelFromWellFormed : Prop :=
  ∀ (r : Region) (N : Nat) (target source : Tables r N) (sourceBase base : UInt64) (bits : UInt8)
    (s : Tables r N) (plan : Plan),
    (∀ t, target.used ≤ t → t < N → target.table t = Table.zero) →
    target.cloneKernelFrom source sourceBase base bits = .ok (s, plan) →
    (s.apply plan).WellFormed base bits

/-- `map_page` keeps a set well-formed. -/
def MapPageWellFormed : Prop :=
  ∀ (r : Region) (N : Nat) (s : Tables r N) (v p : UInt64) (k : Kind) (base : UInt64) (bits : UInt8)
    (s' : Tables r N) (plan : Plan), s.WellFormed base bits →
    s.mapPage v p k base bits = .ok (s', plan) → (s'.apply plan).WellFormed base bits

/-- `map_block` keeps a set well-formed. -/
def MapBlockWellFormed : Prop :=
  ∀ (r : Region) (N : Nat) (s : Tables r N) (v p base : UInt64) (bits : UInt8) (s' : Tables r N)
    (plan : Plan), s.WellFormed base bits →
    s.mapBlock v p base bits = .ok (s', plan) → (s'.apply plan).WellFormed base bits

/-- `unmap_page` keeps a set well-formed. -/
def UnmapPageWellFormed : Prop :=
  ∀ (r : Region) (N : Nat) (s : Tables r N) (v base : UInt64) (bits : UInt8) (plan : Plan)
    (p : UInt64), s.WellFormed base bits →
    s.unmapPage v base bits = .ok (plan, p) → (s.apply plan).WellFormed base bits

/-- `kernel_map` keeps a set well-formed. -/
def KernelMapWellFormed : Prop :=
  ∀ (N : Nat) (s : Tables .lower N) (layout : Layout) (base : UInt64) (bits : UInt8)
    (s' : Tables .lower N) (plan : Plan), s.WellFormed base bits →
    s.kernelMap layout base bits = .ok (s', plan) → (s'.apply plan).WellFormed base bits

/-- `direct_map` keeps a set well-formed. -/
def DirectMapWellFormed : Prop :=
  ∀ (N : Nat) (s : Tables .upper N) (memory : Krepi.Spec.Fdt.MemoryPlan) (base : UInt64)
    (bits : UInt8) (s' : Tables .upper N) (plan : Plan), s.WellFormed base bits →
    s.directMap memory base bits = .ok (s', plan) → (s'.apply plan).WellFormed base bits

/-- `assign` of a choice of `choose` keeps a table well-formed. -/
def AssignWellFormed : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (c : Choice) (zeroed : Bool) (t' : Ownership E X)
    (a : Allocation), t.WellFormed → t.Chose c → t.assign c zeroed = .ok (t', a) → t'.WellFormed

/-- `reserve` keeps a table well-formed. -/
def ReserveWellFormed : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner pages alignment : UInt64) (p : Placement)
    (t' : Ownership E X) (r : Reservation),
    t.WellFormed → t.reserve owner pages alignment p = .ok (t', r) → t'.WellFormed

/-- `publish` keeps a table well-formed. -/
def PublishWellFormed : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner : UInt64) (x : Initialized) (t' : Ownership E X)
    (a : Allocation), t.WellFormed → t.publish owner x = .ok (t', a) → t'.WellFormed

/-- `cancel` keeps a table well-formed. -/
def CancelWellFormed : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner : UInt64) (r : Reservation) (t' : Ownership E X),
    t.WellFormed → t.cancel owner r = .ok t' → t'.WellFormed

/-- `release` keeps a table well-formed. -/
def ReleaseWellFormed : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner : UInt64) (x : Allocation) (t' : Ownership E X),
    t.WellFormed → t.release owner x = .ok t' → t'.WellFormed

/-- `kernel_map` by the boot CPU keeps the shared state well-formed. -/
def BuildKernelMapWellFormed : Prop :=
  ∀ (E X : Nat) (cfg : Config) (cpu : BootCpu) (s : Shared E X) (layout : Layout)
    (s' : Shared E X) (plan : Plan), s.WellFormed cfg →
    s.buildKernelMap cpu layout cfg.lowerBase cfg.bits = some (.ok (s', plan)) → s'.WellFormed cfg

/-- `direct_map` by the boot CPU keeps the shared state well-formed. -/
def BuildDirectMapWellFormed : Prop :=
  ∀ (E X : Nat) (cfg : Config) (cpu : BootCpu) (s : Shared E X) (memory : Krepi.Spec.Fdt.MemoryPlan)
    (s' : Shared E X) (plan : Plan), s.WellFormed cfg →
    s.buildDirectMap cpu memory cfg.directBase cfg.bits = some (.ok (s', plan)) → s'.WellFormed cfg

/-- The end of the boot keeps the shared state well-formed. -/
def EnableWellFormed : Prop :=
  ∀ (E X : Nat) (cfg : Config) (cpu : BootCpu) (s s' : Shared E X), s.WellFormed cfg →
    s.enable cpu = some s' → s'.WellFormed cfg

/-- A fill of the lower kernel set under the token of the kernel tables
keeps the shared state well-formed. -/
def FillKernelWellFormed : Prop :=
  ∀ (E X : Nat) (cfg : Config) (tok : KernelTablesToken) (s : Shared E X) (v p : UInt64) (k : Kind)
    (s' : Shared E X) (plan : Plan), s.WellFormed cfg →
    s.fillKernel tok v p k cfg.lowerBase cfg.bits = some (.ok (s', plan)) → s'.WellFormed cfg

/-- `Ownership::new` under its token keeps the shared state well-formed. -/
def NewOwnershipSharedWellFormed : Prop :=
  ∀ (E X : Nat) (cfg : Config) (tok : OwnershipToken) (s : Shared E X) (arena : UInt64)
    (banks : List PhysRange) (exclusions : List Exclusion) (s' : Shared E X), s.WellFormed cfg →
    s.newOwnership tok arena banks exclusions = some (.ok s') → s'.WellFormed cfg

/-- A write entry of the page ownership table under its token keeps the
shared state well-formed when the entry keeps a table well-formed. -/
def WithOwnershipWellFormed : Prop :=
  ∀ (E X : Nat) (cfg : Config) (ε α : Type) (tok : OwnershipToken) (s : Shared E X)
    (entry : Ownership E X → Except ε (Ownership E X × α)) (s' : Shared E X) (a : α),
    (∀ t t' b, t.WellFormed → entry t = .ok (t', b) → t'.WellFormed) → s.WellFormed cfg →
    s.withOwnership tok entry = some (.ok (s', a)) → s'.WellFormed cfg

/-- An allocation of one step under the token of the page ownership table
keeps the shared state well-formed. -/
def AllocateWellFormed : Prop :=
  ∀ (E X : Nat) (cfg : Config) (tok : OwnershipToken) (s : Shared E X)
    (owner pages alignment : UInt64) (p : Placement) (zeroed : PhysRange → Bool) (s' : Shared E X)
    (a : Allocation), s.WellFormed cfg →
    s.allocate tok owner pages alignment p zeroed = some (.ok (s', a)) → s'.WellFormed cfg

end Krepi.SpecProperties.PageTables
