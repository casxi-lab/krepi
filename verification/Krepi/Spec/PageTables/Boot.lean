module

public import Krepi.Spec.PageTables.Map
public import Krepi.Spec.Fdt.Plan

/-!
# Page tables: the kernel mappings and the direct map

`page_tables::kernel_map` and `page_tables::direct_map` of the contract's
entry table, with the rules of `Kernel mappings`, `Kernel direct map`,
`Abstract mapping`, `Errors of table sets`, `Write plans and publication`,
`Table pool`, `Check and execute`, `Work bounds` and `Determinism`.

Both entries map many leaves with one plan. `kernel_map` maps the pages of a
layout that the board gives into the lower kernel set, each page at its
physical address with the kind of its range. `direct_map` maps every page of
every usable range of the boot memory map into the direct map's set, at
`DIRECT_BASE | pa`, as `ReadWrite`, with a 2 MiB block wherever the rule of
the direct map allows one. The boot memory map is the value `MemoryPlan` of
the fdt specification (`Krepi.Spec.Fdt.MemoryPlan`), whose usable ranges are
`MemoryPlan.availableRanges`; this module reads it and never changes it.

Each entry checks the whole map before it writes, in the order of
`Errors of table sets`: `base` and `bits`; then its ranges in address order,
each with the alignment of its ends, its width and the free slots of its
leaves, the leaves in address order; and last the tables that the whole plan
needs. The free slot of a leaf is read from the walk of the set, as for
`map_page` and `map_block`, and a leaf that an earlier range of the same map
covers, or for `kernel_map` a guard page, is not free. A failure returns the
error of the first broken rule and nothing else.

A success returns the set after the write phase, whose record holds the new
tables, and the plan. A new table is the one of the lowest free index, taken
in the order in which the walk of the leaves first needs it, so a level 2
table before the level 3 tables under it. The plan builds every new table
completely, a table under another new table first, before the one `Store`
that makes it reachable from a table that the set already holds, with a
`Fence` before that store, and ends with `Sync`. On one leaf it is the plan of
`map_page` or of `map_block` for that leaf.
-/

@[expose] public section

namespace Krepi.Spec.PageTables

/-! ## Leaves -/

/-- The bytes of a leaf of a form: 4 KiB for a page, 2 MiB for a block. -/
def Form.size : Form → Nat
  | .page => PAGE_SIZE
  | .block => BLOCK_SIZE

/-- One leaf that a mapping writes: its virtual address, its output address,
its descriptor and its form, a page at level 3 or a block at level 2. -/
structure MapLeaf where
  va : UInt64
  pa : UInt64
  desc : UInt64
  form : Form
  deriving DecidableEq, Repr

/-- The 1 GiB slot of a leaf, the number of its root entry's span. -/
def MapLeaf.gibSlot (l : MapLeaf) : Nat := l.va.toNat / GIB_SIZE

/-- The 2 MiB slot of a leaf, the number of its level 2 entry's span. -/
def MapLeaf.blockSlot (l : MapLeaf) : Nat := l.va.toNat / BLOCK_SIZE

/-- Whether a leaf shares an output address with the range from `start` up to
`stop`, compared at the exact ends. -/
def MapLeaf.meets (l : MapLeaf) (start stop : Nat) : Bool :=
  start < l.pa.toNat + l.form.size && l.pa.toNat < stop

/-! ## The free slot of a leaf -/

/-- Where the walk of the set before a mapping puts one of its leaves. -/
inductive Place where
  /-- The root entry of the leaf is invalid: the leaf needs a new level 2
  table, and a page a new level 3 table under it. -/
  | root
  /-- The level 2 entry of the leaf, in the level 2 table `t2` of the set, is
  invalid: a block takes the entry, and a page needs a new level 3 table
  there. -/
  | level2 (t2 : Nat)
  /-- The level 3 entry of the page, in the level 3 table `t3` of the set
  under `t2`, is invalid. -/
  | level3 (t2 t3 : Nat)
  deriving DecidableEq, Repr

/-- The walk of a leaf through the set at `base`, with the rules of
`map_page` and `map_block`: `TableBacking` for a valid root entry, or for a
page a valid level 2 entry other than a block, that does not point at a table
in use; `AlreadyMapped` for a block where the level 2 entry is valid, a block
or a level 3 table, and for a page where a block covers it or its level 3
entry is valid. Otherwise the place of the leaf. -/
def Tables.place (s : Tables r N) (base : UInt64) (l : MapLeaf) : Except TableError Place := do
  match ← s.walk2 base l.va with
  | none => pure .root
  | some (t2, e2) =>
    match l.form with
    | .block => if isValid e2 then throw .alreadyMapped else pure (.level2 t2)
    | .page =>
      if !isValid e2 then pure (.level2 t2)
      else if typeBits e2 == BLOCK then throw .alreadyMapped
      else
        let some t3 := s.child? base e2 | throw .tableBacking
        if isValid (s.entry t3 (index3 l.va)) then throw .alreadyMapped
        pure (.level3 t2 t3)

/-- The free-slot check of one leaf of a mapping, after the leaves before it:
the walk (`Tables.place`), then `AlreadyMapped` when `taken` says that the map
itself already covers the leaf. The leaf and its place are put before the
leaves `acc` that passed, the latest first. -/
def Tables.checkLeaf (s : Tables r N) (base : UInt64) (taken : MapLeaf → Bool)
    (acc : List (MapLeaf × Place)) (l : MapLeaf) :
    Except TableError (List (MapLeaf × Place)) := do
  let p ← s.place base l
  if taken l then throw .alreadyMapped
  pure ((l, p) :: acc)

/-! ## The new tables -/

/-- A leaf with its tables: the level 2 table and whether the plan builds it,
and for a page the level 3 table and whether the plan builds it; a block has
the level 3 table 0, which no step names. -/
structure Placed where
  leaf : MapLeaf
  t2 : Nat
  new2 : Bool
  t3 : Nat
  new3 : Bool
  deriving DecidableEq, Repr

/-- The tables of the leaves so far: the next free index, the 1 GiB slot and
the index of the last new level 2 table, the 2 MiB slot and the index of the
last new level 3 table, and the placed leaves, the latest first. -/
structure Alloc where
  next : Nat
  level2 : Option (Nat × Nat)
  level3 : Option (Nat × Nat)
  placed : List Placed
  deriving DecidableEq, Repr

/-- The tables of one more leaf. A leaf whose root entry is invalid takes the
new level 2 table of its 1 GiB slot, the one that an earlier leaf of the slot
took or else the next free index; then a page whose level 2 entry is invalid,
or under a new level 2 table, takes the new level 3 table of its 2 MiB slot
in the same way. The leaves come in address order, so the leaves of one slot
are consecutive and the last new table of a slot is its only one. -/
def Alloc.add (a : Alloc) (lp : MapLeaf × Place) : Alloc :=
  let (l, p) := lp
  let (t2, new2, a) : Nat × Bool × Alloc :=
    match p with
    | .root =>
      match a.level2 with
      | some (g, t) => if g == l.gibSlot then (t, true, a)
        else (a.next, true, { a with next := a.next + 1, level2 := some (l.gibSlot, a.next) })
      | none => (a.next, true, { a with next := a.next + 1, level2 := some (l.gibSlot, a.next) })
    | .level2 t2 => (t2, false, a)
    | .level3 t2 _ => (t2, false, a)
  let (t3, new3, a) : Nat × Bool × Alloc :=
    match l.form, p with
    | .block, _ => (0, false, a)
    | .page, .level3 _ t3 => (t3, false, a)
    | .page, _ =>
      match a.level3 with
      | some (b, t) => if b == l.blockSlot then (t, true, a)
        else (a.next, true, { a with next := a.next + 1, level3 := some (l.blockSlot, a.next) })
      | none => (a.next, true, { a with next := a.next + 1, level3 := some (l.blockSlot, a.next) })
  { a with placed := ⟨l, t2, new2, t3, new3⟩ :: a.placed }

/-- The tables of the leaves of a map, in address order, from the record
`used` of the set: the next free index after the new tables, and the placed
leaves in address order. -/
def assignTables (used : Nat) (leaves : List (MapLeaf × Place)) : Nat × List Placed :=
  let a := leaves.foldl Alloc.add ⟨used, none, none, []⟩
  (a.next, a.placed.reverse)

/-! ## The plan -/

/-- The runs of consecutive elements of a list that have one key, in order. -/
def runsBy (key : α → Nat) : List α → List (List α)
  | [] => []
  | x :: rest =>
    match runsBy key rest with
    | (y :: run) :: runs =>
      if key x == key y then (x :: y :: run) :: runs else [x] :: (y :: run) :: runs
    | runs => [x] :: runs

/-- The table descriptor of table `t` of the pool at `base`. -/
def tableAt (base : UInt64) (t : Nat) : UInt64 := tableDescriptor (tableAddress base t)

/-- The store of a leaf into its table: a page into entry `index3` of its
level 3 table, a block into entry `index2` of its level 2 table. -/
def Placed.store (p : Placed) : Step :=
  match p.leaf.form with
  | .page => .store p.t3 (index3 p.leaf.va) p.leaf.desc
  | .block => .store p.t2 (index2 p.leaf.va) p.leaf.desc

/-- The store into the level 2 table of the entry of one 2 MiB slot, whose
leaves are `run`: the block, or the table descriptor of the level 3 table of
the pages. -/
def level2Entry (base : UInt64) : List Placed → Plan
  | [] => []
  | p :: _ =>
    match p.leaf.form with
    | .block => [p.store]
    | .page => [.store p.t2 (index2 p.leaf.va) (tableAt base p.t3)]

/-- The steps of the leaves of one 2 MiB slot, `run`, under a level 2 table
that the set already holds: a block is one `Store`; pages in a level 3 table
of the set are a `Store` each; pages in a new level 3 table `t3` are
`Zero(t3)`, a `Store` of each page, `Fence` and the `Store` of the table
descriptor of `t3` into the level 2 table. -/
def heldLevel2Steps (base : UInt64) : List Placed → Plan
  | [] => []
  | run@(p :: _) =>
    match p.leaf.form with
    | .block => run.map Placed.store
    | .page =>
      if p.new3 then Step.zero p.t3 :: run.map Placed.store ++ Step.fence :: level2Entry base run
      else run.map Placed.store

/-- The steps of the leaves of one 1 GiB slot, `run`, in a new level 2 table
`t2`: first each new level 3 table under it, `Zero(t3)` and a `Store` of each
of its pages, in address order; then `Zero(t2)` and a `Store` of each of its
entries, the blocks and the table descriptors of the level 3 tables, in index
order; then `Fence` and the `Store` of the table descriptor of `t2` into the
root. -/
def newLevel2Steps (base : UInt64) : List Placed → Plan
  | [] => []
  | run@(p :: _) =>
    let slots := runsBy (·.leaf.blockSlot) run
    let children := slots.flatMap fun slot =>
      match slot with
      | q :: _ => if q.leaf.form == .page then Step.zero q.t3 :: slot.map Placed.store else []
      | [] => []
    children ++ Step.zero p.t2 :: slots.flatMap (level2Entry base) ++
      [Step.fence, Step.store 0 (index1 p.leaf.va) (tableAt base p.t2)]

/-- The plan of the placed leaves of a map, in address order: the steps of
each 1 GiB slot in address order (`newLevel2Steps` under a new level 2
table, and the steps of each 2 MiB slot, `heldLevel2Steps`, under one that the
set holds), then `Sync`. -/
def mapPlan (base : UInt64) (placed : List Placed) : Plan :=
  (runsBy (·.leaf.gibSlot) placed).flatMap (fun run =>
    match run with
    | p :: _ =>
      if p.new2 then newLevel2Steps base run
      else (runsBy (·.leaf.blockSlot) run).flatMap (heldLevel2Steps base)
    | [] => []) ++ [Step.sync]

/-- The write phase of a map whose leaves passed their checks, given in
address order: `OutOfTables` when the pool has fewer free tables than the new
tables that the whole plan needs; otherwise the set whose record holds them,
and the plan. -/
def Tables.mapLeaves (s : Tables r N) (base : UInt64) (leaves : List (MapLeaf × Place)) :
    Except TableError (Tables r N × Plan) := do
  let (next, placed) := assignTables s.used leaves
  if N - s.used < next - s.used then throw .outOfTables
  pure ({ s with used := next }, mapPlan base placed)

/-! ## The capacities of the kernel tables -/

/-- The tables of the pool of the direct map's set, 80, sized for 16 GiB of
RAM (`Table pool`). The entries are stated for every capacity `N`; the
kernel's direct map is a set of this capacity. -/
def DIRECT_MAP_TABLES : Nat := 80

/-- The tables of the pool of the lower kernel set, 32 (`Table pool`), which
the table pool of each address space shares, as the copy of the kernel tables
takes two sets of one capacity. -/
def KERNEL_TABLES : Nat := 32

/-! ## The kernel mappings -/

/-- The kinds that a layout names: `ReadExecute`, `ReadOnly`, `ReadWrite`
and `Device`. -/
def layoutKinds : List Kind := [.readExecute, .readOnly, .readWrite, .device]

/-- The most ranges of a layout, 16. -/
def MAX_LAYOUT_RANGES : Nat := 16

/-- A range of a layout: a physical range, mapped at its physical address,
with its kind, one of the kinds that a layout names. -/
structure LayoutRange where
  range : PhysRange
  kind : Kind
  named : layoutKinds.contains kind = true
  deriving DecidableEq

/-- The layout that the board gives `kernel_map`: at most 16 ranges, each with
a kernel kind, and the guard pages, each named by an address in it. The
contract gives no error for more ranges or another kind, so the type holds
these rules. -/
structure Layout where
  ranges : List LayoutRange
  guards : List UInt64
  bounded : ranges.length ≤ MAX_LAYOUT_RANGES
  deriving DecidableEq

/-- The `count` pages of a range of kind `k` from the address `pa`, each
mapped at its physical address. -/
def layoutPages (k : Kind) : (count pa : Nat) → List MapLeaf
  | 0, _ => []
  | count + 1, pa =>
    ⟨UInt64.ofNat pa, UInt64.ofNat pa, descriptor k (UInt64.ofNat pa), .page⟩ ::
      layoutPages k count (pa + PAGE_SIZE)

/-- Whether a guard address lies in the page of a leaf. -/
def MapLeaf.isGuard (guards : List UInt64) (l : MapLeaf) : Bool :=
  guards.any fun g => l.va.toNat ≤ g.toNat && g.toNat < l.va.toNat + PAGE_SIZE

/-- The checks of one range of a layout, after the ranges `earlier` before it
in address order and the leaves `acc` that passed: a start or an end off a
page boundary, `Alignment`; an end above $2^{39}$, outside the lower region,
or above $2^{\mathrm{bits}}$, `AddressWidth`; then each page in address order
(`Tables.checkLeaf`), not free when an earlier range or a guard page holds
it. -/
def Tables.checkLayoutRange (s : Tables .lower N) (base : UInt64) (bits : UInt8)
    (guards : List UInt64) (acc : List PhysRange × List (MapLeaf × Place)) (j : LayoutRange) :
    Except TableError (List PhysRange × List (MapLeaf × Place)) := do
  let (earlier, leaves) := acc
  let start := j.range.start.toNat
  let stop := j.range.endNat
  if start % PAGE_SIZE != 0 || stop % PAGE_SIZE != 0 then throw .alignment
  if VA_LIMIT < stop || 2 ^ bits.toNat < stop then throw .addressWidth
  let taken := fun (l : MapLeaf) =>
    earlier.any (fun e => l.meets e.start.toNat e.endNat) || l.isGuard guards
  let leaves ← (layoutPages j.kind (j.range.len.toNat / PAGE_SIZE) start).foldlM
    (s.checkLeaf base taken) leaves
  pure (earlier ++ [j.range], leaves)

/-- `page_tables::kernel_map(layout, base, bits)` on the lower kernel set: maps
every page of every range of the layout at its physical address with the
kind of its range, or the error of the first broken rule, checked in this
order:

1. `base` and `bits` (`checkPool`);
2. the ranges in address order, each (`Tables.checkLayoutRange`): its ends
   off a page boundary, `Alignment`; its end outside the lower region or above
   $2^{\mathrm{bits}}$, `AddressWidth`; then each of its pages in address
   order, the walk (`TableBacking` for a bad table descriptor, `AlreadyMapped`
   for a page or a block that covers it) and then `AlreadyMapped` for a page
   that an earlier range holds, so that two ranges share it, or that holds a
   guard address;
3. the tables that the whole plan needs, `OutOfTables` (`Tables.mapLeaves`).

The plan writes only the entries of the pages and of the new tables, and no
guard page: `mapPlan`. -/
def Tables.kernelMap (s : Tables .lower N) (layout : Layout) (base : UInt64) (bits : UInt8) :
    Except TableError (Tables .lower N × Plan) := do
  checkPool N base bits
  let (_, leaves) ← (sortByKey (·.range.start.toNat) layout.ranges).foldlM
    (s.checkLayoutRange base bits layout.guards) ([], [])
  s.mapLeaves base leaves.reverse

/-! ## The direct map -/

/-- The leaves of the direct map from the physical address `pa` up to `stop`,
with at most `fuel` more steps: at a multiple of 2 MiB with at least 2 MiB
left, the block of `ReadWrite`; elsewhere the page of `ReadWrite`; each at
`DIRECT_BASE | pa`. -/
def directLeaves (stop : Nat) : (fuel pa : Nat) → List MapLeaf
  | 0, _ => []
  | fuel + 1, pa =>
    if stop ≤ pa then []
    else
      let a := UInt64.ofNat pa
      if pa % BLOCK_SIZE == 0 && pa + BLOCK_SIZE ≤ stop then
        ⟨DIRECT_BASE ||| a, a, blockDescriptor a, .block⟩ ::
          directLeaves stop fuel (pa + BLOCK_SIZE)
      else
        ⟨DIRECT_BASE ||| a, a, descriptor .readWrite a, .page⟩ ::
          directLeaves stop fuel (pa + PAGE_SIZE)

/-- The steps of the walk of one usable range of `len` bytes, from the bounds
of `Work bounds`: at most one step for each 2 MiB block and, at each of the
two ends of the range, at most 511 pages. -/
def directFuel (len : Nat) : Nat := len / BLOCK_SIZE + 2 * (ENTRIES - 1)

/-- The checks of one usable range, after the ranges `earlier` before it in
address order and the leaves `acc` that passed: a start or an end off a page
boundary, `Alignment`; an end above $2^{39}$, so that the range has no direct
address, or above $2^{\mathrm{bits}}$, `AddressWidth`; then each leaf in
address order (`Tables.checkLeaf`), not free when an earlier range shares an
address with it. -/
def Tables.checkUsableRange (s : Tables .upper N) (base : UInt64) (bits : UInt8)
    (acc : List Fdt.Span × List (MapLeaf × Place)) (u : Fdt.Span) :
    Except TableError (List Fdt.Span × List (MapLeaf × Place)) := do
  let (earlier, leaves) := acc
  let start := u.start.toNat
  let stop := u.endNat
  if start % PAGE_SIZE != 0 || stop % PAGE_SIZE != 0 then throw .alignment
  if VA_LIMIT < stop || 2 ^ bits.toNat < stop then throw .addressWidth
  let taken := fun (l : MapLeaf) => earlier.any (fun e => l.meets e.start.toNat e.endNat)
  let leaves ← (directLeaves stop (directFuel (stop - start)) start).foldlM
    (s.checkLeaf base taken) leaves
  pure (earlier ++ [u], leaves)

/-- `page_tables::direct_map(memory, base, bits)` on the direct map's set: maps
every page of every usable range of the boot memory map `memory`
(`MemoryPlan.availableRanges`) at `DIRECT_BASE | pa` as `ReadWrite`, a block
at each multiple of 2 MiB with at least 2 MiB of its range left and a page
elsewhere, or the error of the first broken rule, checked in this order:

1. `base` and `bits` (`checkPool`);
2. the usable ranges in address order, each (`Tables.checkUsableRange`): its
   ends off a page boundary, `Alignment`; its end above $2^{39}$ or above
   $2^{\mathrm{bits}}$, `AddressWidth`; then each of its leaves in address
   order, the walk (`TableBacking` for a bad table descriptor, `AlreadyMapped`
   for a slot that is not free) and then `AlreadyMapped` for a leaf that an
   earlier range shares an address with;
3. the tables that the whole plan needs, `OutOfTables` (`Tables.mapLeaves`).

Nothing else is mapped: the usable ranges hold no page of a reservation, of a
hole between banks or outside the managed banks. -/
def Tables.directMap (s : Tables .upper N) (memory : Fdt.MemoryPlan) (base : UInt64)
    (bits : UInt8) :
    Except TableError (Tables .upper N × Plan) := do
  checkPool N base bits
  let (_, leaves) ← (sortByKey (·.start.toNat) memory.availableRanges).foldlM
    (s.checkUsableRange base bits) ([], [])
  s.mapLeaves base leaves.reverse

/-! ## The counts of a map -/

/-- Whether a step stores a block descriptor: bits 1 and 0 `0b01`. -/
def Step.storesBlock : Step → Bool
  | .store _ _ d => typeBits d == BLOCK
  | _ => false

/-- Whether a step stores the page descriptor of a kind: bits 1 and 0 `0b11`,
and the bits of a kind (`Kind.ofPage`). A table descriptor holds no
attribute, and every kind sets AF, so no table descriptor is one. -/
def Step.storesPage : Step → Bool
  | .store _ _ d => typeBits d == TABLE_OR_PAGE && (Kind.ofPage d).isSome
  | _ => false

/-- The counts of a map: the bytes, the blocks and the pages. -/
structure MapCounts where
  bytes : Nat
  blocks : Nat
  pages : Nat
  deriving DecidableEq, Repr

/-- The counts of the map that a plan writes: one block for each `Store` of a
block descriptor, one page for each `Store` of a page descriptor, and the
bytes of both, 2 MiB for a block and 4 KiB for a page. -/
def Plan.counts (plan : Plan) : MapCounts :=
  let blocks := plan.countP Step.storesBlock
  let pages := plan.countP Step.storesPage
  ⟨blocks * BLOCK_SIZE + pages * PAGE_SIZE, blocks, pages⟩

end Krepi.Spec.PageTables
