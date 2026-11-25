module

public import Krepi.SpecProperties.PageTables.Invariants

/-!
# Page tables: properties

The cross-cutting properties of the `page-tables` component, each a
proposition that a theorem below `Krepi.Proofs.PageTables` proves, drawn from
its requirements (`docs/domains/memory/page-tables/requirements.md`) and the
sentences of its contract that they restate:

1. `NoWritableExecutable`: no kind is writable and executable, and no frame
   is mapped writable and executable, counting the lower kernel set, the
   direct map's set and a copy of the lower kernel set together (PGT-R01,
   PGT-R05, PGT-R06).
2. `AfterEveryWrite`: each write entry of a set changes $M$, $G$ and $P$, and
   each write entry of the page ownership table changes $O$ and $g$, as its
   row of `After mapping` and `After ownership` states (PGT-R02 to PGT-R06,
   PGT-R08 to PGT-R10, PGT-R12).
3. `DirectMapUnchangedAfterBoot`: once the MMU is on, no transaction changes
   the direct map's set (PGT-R05).
4. `KernelTablesOnlyFilled`: a plan for one of the kernel tables writes only
   invalid entries and holds no `Invalidate`, and no transaction changes a
   valid entry of the kernel tables (PGT-R04, PGT-R07).
5. `PlansPublishInOrder`: every plan of a map zeroes a new table once and
   writes it completely, its entries in index order and each new table under
   it before its `Zero`, before the one store of its table descriptor that
   makes it reachable, with a `Fence` before that store, writes the valid
   entries of the root and of level 2 tables in the form that the walk reads,
   and ends with `Sync`; the plan of an unmap stores the invalid entry and
   then invalidates; the plan of a copy zeroes the target's tables in use,
   stores every valid entry of the source into the target's table of the same
   index in index order, and ends with `Sync` (PGT-R04, PGT-R07, PGT-R12).
6. `TablesInUseCounted`: the tables in use of a well-formed set are the root
   and one table for each element of $G$ and of $P$ (PGT-R03, PGT-R05,
   PGT-R11).
7. `PlacementFirstFit`: `choose` gives the lowest or the highest aligned range
   of the request in the window, in the first free extent in the order of
   its placement that holds one within the capacity (PGT-R09, PGT-R10).
8. `BootOwnersMatchDirectMap`: for every well-formed boot memory map, the
   table of the kernel root has one owner for every managed page, and its
   free pages are exactly the pages of the direct map (PGT-R08, PGT-R05).

Properties 1, 3 and 4 are stated over the transactions of
`Krepi.Spec.PageTables.Tokens`, as a list run from the shared state of the
boot (`runAll`). The definitions that the properties need on the values of
the specification extend its namespace. Lines are those of the contract,
`docs/domains/memory/page-tables/contract.md`.
-/

@[expose] public section

namespace Krepi.Spec.PageTables

/-! ## Transactions -/

/-- A transaction of the shared state, with its arguments: the boot CPU's
`kernel_map`, `direct_map` and turning the MMU on; a fill of the lower kernel
set under the token of the kernel tables; and the entries of the page
ownership table under its token, the allocation of one step with the outcome
of its zeroing among them. -/
inductive Txn where
  | kernelMap (layout : Layout)
  | directMap (memory : Fdt.MemoryPlan)
  | enable
  | fill (v p : UInt64) (k : Kind)
  | newOwnership (arena : UInt64) (banks : List PhysRange) (exclusions : List Exclusion)
  | allocate (owner pages alignment : UInt64) (placement : Placement) (zeroed : Bool)
  | reserve (owner pages alignment : UInt64) (placement : Placement)
  | publish (owner : UInt64) (packet : Initialized)
  | cancel (owner : UInt64) (reservation : Reservation)
  | release (owner : UInt64) (receipt : Allocation)

/-- One transaction on the shared state, by the executing CPU, which holds
each token with one CPU: the state after it, and the plan of a write of a
kernel set. A transaction that is not enabled, or whose entry fails, leaves
the state as it was. -/
def Txn.run (cfg : Config) : Txn → Shared E X → Shared E X × Option Plan
  | .kernelMap layout, s =>
    match s.buildKernelMap .boot layout cfg.lowerBase cfg.bits with
    | some (.ok (s', plan)) => (s', some plan)
    | _ => (s, none)
  | .directMap memory, s =>
    match s.buildDirectMap .boot memory cfg.directBase cfg.bits with
    | some (.ok (s', plan)) => (s', some plan)
    | _ => (s, none)
  | .enable, s => ((s.enable .boot).getD s, none)
  | .fill v p k, s =>
    match s.fillKernel .executing v p k cfg.lowerBase cfg.bits with
    | some (.ok (s', plan)) => (s', some plan)
    | _ => (s, none)
  | .newOwnership arena banks exclusions, s =>
    match s.newOwnership .executing arena banks exclusions with
    | some (.ok s') => (s', none)
    | _ => (s, none)
  | .allocate owner pages alignment p zeroed, s =>
    match s.allocate .executing owner pages alignment p (fun _ => zeroed) with
    | some (.ok (s', _)) => (s', none)
    | _ => (s, none)
  | .reserve owner pages alignment p, s =>
    match s.withOwnership .executing (·.reserve owner pages alignment p) with
    | some (.ok (s', _)) => (s', none)
    | _ => (s, none)
  | .publish owner x, s =>
    match s.withOwnership .executing (fun t => (t.publish owner x).mapError (·.1)) with
    | some (.ok (s', _)) => (s', none)
    | _ => (s, none)
  | .cancel owner r, s =>
    match s.withOwnership .executing (fun t => ((t.cancel owner r).mapError (·.1)).map (·, ())) with
    | some (.ok (s', _)) => (s', none)
    | _ => (s, none)
  | .release owner x, s =>
    match s.withOwnership .executing (fun t => (t.release owner x).map (·, ())) with
    | some (.ok (s', _)) => (s', none)
    | _ => (s, none)

/-- The transactions of a list, in order, each on the state that the ones
before it left. -/
def runAll (cfg : Config) (txns : List Txn) (s : Shared E X) : Shared E X :=
  txns.foldl (fun s txn => (txn.run cfg s).1) s

/-- The shared state of the boot: both kernel sets of `Tables::new` on zero
pools, no page ownership table and the MMU off. -/
def Shared.initial (E X : Nat) : Shared E X :=
  Shared.boot BootCpu.boot (Pool.zero _) (Pool.zero _)

/-- The layout of a transaction of `kernel_map`. -/
def Txn.layout? : Txn → Option Layout
  | .kernelMap layout => some layout
  | _ => none

/-- The boot memory map of a transaction of `direct_map`. -/
def Txn.memory? : Txn → Option Fdt.MemoryPlan
  | .directMap memory => some memory
  | _ => none

/-! ## Frames and kinds -/

/-- A table set at the base of its pool, one of the sets that W^X counts
together. -/
structure SetView where
  region : Region
  capacity : Nat
  set : Tables region capacity
  base : UInt64

/-- Whether one of the sets maps the frame at `q` with a kind of which `pred`
holds: a page of the abstract mapping of one of them whose physical page is
`q`. -/
def MapsFrame (views : List SetView) (pred : Kind → Bool) (q : Nat) : Prop :=
  ∃ w ∈ views, ∃ v l, w.set.M w.base v l ∧ l.pa.toNat = q ∧ pred l.kind = true

/-- No frame is mapped writable and executable, counting every alias in the
sets together. -/
def WxFree (views : List SetView) : Prop :=
  ∀ q, ¬ (MapsFrame views (·.attributes.writable) q ∧
    MapsFrame views (·.attributes.executable) q)

/-- Whether the page at `q` is a page of a `ReadExecute` range of a layout:
the text of the image. -/
def Layout.text (layout : Layout) (q : Nat) : Bool :=
  layout.ranges.any fun j =>
    j.kind == .readExecute && j.range.start.toNat ≤ q && q + PAGE_SIZE ≤ j.range.endNat

/-- The rules of the boot wiring and of the fills of the lower kernel set
that W^X rests on, for a list of transactions:

- `kernel_map` and `direct_map` run at most once each (line 112);
- the boot memory map is well-formed, and each `ReadExecute` range of the
  layout lies in a span of its boot storage: the contract names the span of
  the kernel image, and any span of boot storage suffices (lines 209 to 218
  and 525);
- a fill maps an executable kind only at a page of the text, and a page of
  the text only with `ReadExecute`: "the executable pages come only from the
  image and the boot bundle", and "the text has one kind in every set that
  maps it" (lines 219 to 230). -/
def WxPremises (txns : List Txn) : Prop :=
  (txns.filterMap Txn.layout?).length ≤ 1 ∧ (txns.filterMap Txn.memory?).length ≤ 1 ∧
  (∀ B ∈ txns.filterMap Txn.memory?, B.WellFormed) ∧
  (∀ layout ∈ txns.filterMap Txn.layout?, ∀ B ∈ txns.filterMap Txn.memory?,
    ∀ j ∈ layout.ranges, j.kind = .readExecute →
      ∃ b ∈ B.boot, b.start.toNat ≤ j.range.start.toNat ∧ j.range.endNat ≤ b.endNat) ∧
  ∀ v p k, Txn.fill v p k ∈ txns →
    (k.attributes.executable = true →
      ∃ layout ∈ txns.filterMap Txn.layout?, layout.text p.toNat) ∧
    ∀ layout ∈ txns.filterMap Txn.layout?, layout.text p.toNat = true → k = .readExecute

/-! ## Plans -/

/-- The table of the pool at `base` that a table descriptor `d` with no
attribute points at, by its address alone. The walk follows every valid root
entry, and every valid entry of a level 2 table other than a block, by its
address (`Tables.walk2`, `Tables.walk`); a well-formed set holds no other
form of these entries and `Plan.inOrder` admits none, so that from such a set
the tables that it reads as reached are those that the walk reaches. -/
def poolChild? (N : Nat) (base d : UInt64) : Option Nat :=
  let a := (outputAddress d).toNat
  if isPlainTableDescriptor d && base.toNat ≤ a && (a - base.toNat) / PAGE_SIZE < N then
    some ((a - base.toNat) / PAGE_SIZE)
  else none

/-- The tables that the entries of table `t` of a pool point at. -/
def Pool.children (p : Pool N) (base : UInt64) (t : Nat) : List Nat :=
  (List.range ENTRIES).filterMap fun i => poolChild? N base (p.get t i)

/-- The tables of a pool that a walk from the root reaches: the root, the
tables that its entries point at and the tables that theirs point at. A table
that a plan builds is reached once a table descriptor points at it. -/
def Pool.reached (p : Pool N) (base : UInt64) : List Nat :=
  let level2 := p.children base 0
  0 :: level2 ++ level2.flatMap (p.children base)

/-- Whether an entry `d` of the root, or with `level2` of a level 2 table, has
a form that the walk reads as the contract writes it: invalid; a block, in a
level 2 table; or a table descriptor with no attribute. The walk follows any
other valid entry of the root, and any other valid entry of a level 2 table,
by its address alone, as a table descriptor (`Tables.walk2`, `Tables.walk`). -/
def walkedAsWritten (level2 : Bool) (d : UInt64) : Bool :=
  !isValid d || (level2 && typeBits d == BLOCK) || isPlainTableDescriptor d

/-- Whether a step writes table `t`: a `Zero` or a `Store` of it. -/
def Step.writes (t : Nat) : Step → Bool
  | .zero u => u == t
  | .store u _ _ => u == t
  | _ => false

/-- The state of the check of the order of a plan: the pool so far, the
tables that the plan has zeroed, those written since the last `Fence`, the
tables whose table descriptor the plan has stored, which it has sealed,
whether a store has made an entry valid, and the steps so far, the latest
first. -/
structure PlanState (N : Nat) where
  pool : Pool N
  zeroed : List Nat
  dirty : List Nat
  sealed : List Nat
  valid : Bool
  steps : List Step

/-- Whether a plan, executed from the pool of a set at `base`, keeps the order
of `Write plans and publication` (lines 406 to 429):

- a reached table is never zeroed and takes only stores into invalid
  entries, and a table that the plan zeroed takes no step once it is
  reached;
- a table is zeroed at most once; a table that is not reached is zeroed
  before the plan stores into it, takes its stores in increasing order of
  their indices, and takes no step once the plan has stored its table
  descriptor, so that the plan writes it completely before that store;
- every table descriptor of a table of the pool that the plan stores points
  at a table that the plan has zeroed and whose table descriptor it has not
  stored before, so that a new table has one store of its table descriptor;
- a table descriptor stored into a table that is not reached points at a
  table that took no step after the `Zero` of the table that it is stored
  into, so that a new table under another new table is complete before the
  `Zero` of the other (lines 409 to 412 and 418 to 421);
- a store of a table descriptor into a reached table points at a table not
  yet reached, which with the tables under it the plan has zeroed and
  written before a `Fence` that comes before the store;
- every valid entry that the plan stores into the root, and every valid
  entry other than a block that it stores into a level 2 table, is a table
  descriptor with no attribute, the form that the walk follows
  (`walkedAsWritten`): an entry of a reached level 2 table when the plan
  stores it, and an entry of a new table when the plan stores its table
  descriptor into the root;
- no step is `Invalidate`, and a plan that makes an entry valid ends with
  `Sync`.

The rest of the rule of maps (lines 413 to 418), the leaves in address order
from one table to the next and in the tables that the set holds, and one 2
MiB slot after the other under a level 2 table that the set holds, is not
stated here: the specification test `PlansFollowContractOrder` shows it only
on sets that hold the root alone, within one 1 GiB slot. These orders leave
the same set, since every new table is complete and fenced before the one
store of its table descriptor and a leaf in a table that the set holds is
one store into an invalid entry, and the plans of `kernel_map` and
`direct_map` run with the MMU off, into sets that no `TTBR` holds (lines 452
to 454); the plans of the specification follow them by their definition,
which the refinement of the target relates to the plans of the
implementation. -/
def Plan.inOrder (base : UInt64) : Plan → PlanState N → Bool
  | [], st => !st.valid
  | [.sync], _ => true
  | step :: rest, st =>
    let reached := st.pool.reached base
    let next := { st with pool := step.exec st.pool, steps := step :: st.steps }
    match step with
    | .zero t =>
      !reached.contains t && !st.zeroed.contains t &&
        Plan.inOrder base rest { next with zeroed := t :: st.zeroed, dirty := t :: st.dirty }
    | .store t i d =>
      let child := poolChild? N base d
      let since := st.steps.takeWhile (· != .zero t)
      (t != 0 || walkedAsWritten false d) &&
      (!(st.pool.children base 0).contains t || walkedAsWritten true d) &&
      (match child with
        | some c => st.zeroed.contains c && !st.sealed.contains c &&
          (t != 0 || (List.range ENTRIES).all fun j => walkedAsWritten true (st.pool.get c j))
        | none => true) &&
      (if reached.contains t then
        !st.zeroed.contains t && !isValid (st.pool.get t i) &&
          match child with
          | some c => !reached.contains c &&
            (c :: st.pool.children base c).all fun u => st.zeroed.contains u && !st.dirty.contains u
          | none => true
      else
        st.zeroed.contains t && !st.sealed.contains t &&
          (since.all fun s => match s with
            | .store u j _ => u != t || j < i
            | _ => true) &&
          match child with
          | some c => since.all fun s => !s.writes c
          | none => true) &&
        Plan.inOrder base rest
          { next with dirty := if reached.contains t then st.dirty else t :: st.dirty,
                      sealed := match child with
                        | some c => c :: st.sealed
                        | none => st.sealed,
                      valid := st.valid || isValid d }
    | .fence => Plan.inOrder base rest { next with dirty := [] }
    | .sync => Plan.inOrder base rest next
    | .invalidate _ => false

/-- Whether a plan keeps the order of `Write plans and publication` from the
pool of a set at `base`. -/
def Plan.publishesInOrder (plan : Plan) (base : UInt64) (p : Pool N) : Bool :=
  plan.inOrder base ⟨p, [], [], [], false, []⟩

/-- Whether a plan, executed on the pool `p`, writes only entries that are
invalid when it writes them and holds no `Invalidate`: each `Store` writes
an invalid entry and each `Zero` a table whose entries are all invalid. -/
def Plan.fillsOnly : Plan → Pool N → Bool
  | [], _ => true
  | step :: rest, p =>
    (match step with
      | .store t i _ => !isValid (p.get t i)
      | .zero t => (List.range ENTRIES).all fun i => !isValid (p.get t i)
      | .invalidate _ => false
      | .fence => true
      | .sync => true) && Plan.fillsOnly rest (step.exec p)

/-- A plan of a transaction writes only invalid entries of the kernel set
that it writes: the lower kernel set for `kernel_map` and a fill, the direct
map's set for `direct_map`. -/
def Txn.FillsOnly (txn : Txn) (s : Shared E X) (plan : Plan) : Prop :=
  match txn with
  | .kernelMap _ => plan.fillsOnly s.lowerKernel.pool = true
  | .fill .. => plan.fillsOnly s.lowerKernel.pool = true
  | .directMap _ => plan.fillsOnly s.directMap.pool = true
  | _ => True

/-! ## The abstract mapping -/

/-- `v` is not in the domain of $M$ of the set at `base`. -/
def Tables.Unmapped (s : Tables r N) (base v : UInt64) : Prop := ∀ l, ¬ s.M base v l

/-- `v` is a page of the range of a layout: a multiple of 4 KiB whose page
lies wholly in the range. -/
def LayoutRange.HoldsPage (j : LayoutRange) (v : Nat) : Prop :=
  v % PAGE_SIZE = 0 ∧ j.range.start.toNat ≤ v ∧ v + PAGE_SIZE ≤ j.range.endNat

/-- $\ell(p)$ of the direct map: whether $\mathrm{blk}(p)$ and the 2 MiB after
it lie in one usable range of `B`, so that the page is mapped by a block. -/
def blockForm (B : Fdt.MemoryPlan) (p : Nat) : Bool :=
  B.availableRanges.any fun u =>
    u.start.toNat ≤ p / BLOCK_SIZE * BLOCK_SIZE &&
      p / BLOCK_SIZE * BLOCK_SIZE + BLOCK_SIZE ≤ u.endNat

/-- The 1 GiB slots of the region of a set whose root entry points at a table
in use, in index order: the elements of $G$. -/
def Tables.gSlots (s : Tables r N) (base : UInt64) : List UInt64 :=
  (List.range ENTRIES).filterMap fun i =>
    let g := UInt64.ofNat (r.first + i * GIB_SIZE)
    match s.walk2 base g with
    | .ok (some _) => some g
    | _ => none

/-- The 2 MiB slots of the region of a set whose level 2 entry points at a
table in use, in index order: the elements of $P$. -/
def Tables.pSlots (s : Tables r N) (base : UInt64) : List UInt64 :=
  (s.gSlots base).flatMap fun g => (List.range ENTRIES).filterMap fun j =>
    let b := g + UInt64.ofNat (j * BLOCK_SIZE)
    match s.walk base b with
    | .ok (.level3 ..) => some b
    | _ => none

/-! ## Placement -/

/-- The free extent `e` holds the range `r` for a request of `pages` pages at
the alignment of `alignment` pages: of the bytes of the request, at a
multiple of the alignment in bytes, inside the extent and inside the window
of the placement. -/
def Extent.Holds (e : Extent) (pages alignment : UInt64) (p : Placement) (r : PhysRange) : Prop :=
  e.holding = .free ∧ r.len.toNat = pages.toNat * PAGE_SIZE ∧
    r.start.toNat % (alignment.toNat * PAGE_SIZE) = 0 ∧ e.range.contains r = true ∧
    ∀ w, p.window = some w → w.contains r = true

/-- The range that the free extent `e` gives a request: one that it holds,
of the lowest start for a low placement and of the highest for a high one.
-/
def Extent.Gives (e : Extent) (pages alignment : UInt64) (p : Placement) (r : PhysRange) : Prop :=
  e.Holds pages alignment p r ∧ ∀ r', e.Holds pages alignment p r' →
    match p.direction with
    | .low => r.start.toNat ≤ r'.start.toNat
    | .high => r'.start.toNat ≤ r.start.toNat

/-- The extents in the order of the scan of a placement: from the lowest for
a low placement and from the highest for a high one. -/
def Ownership.scanOrder (t : Ownership E X) (p : Placement) : List Extent :=
  match p.direction with
  | .low => t.extents
  | .high => t.extents.reverse

end Krepi.Spec.PageTables

namespace Krepi.SpecProperties.PageTables

open Krepi.Spec.PageTables

/-! ## 1. W^X -/

/-- **No mapping is writable and executable** (PGT-R01, PGT-R05, PGT-R06).
"At no time is a frame mapped writable and executable, counting every alias
in every table set together" (lines 201 to 203):

- no kind is writable and executable (line 205);
- on every shared state that the transactions reach from the boot under the
  rules of the boot wiring and the fills (`WxPremises`, lines 209 to 230), no
  frame is mapped writable by the lower kernel set or the direct map's set
  and executable by one of them; and so for every copy of the lower kernel
  set that `clone_kernel_from` makes into a target whose tables not in use
  are zero, counted with them (lines 209 to 212).

The mappings of the address spaces of processes beyond the copy, and
`UserReadExecute` for the boot bundle, are those of the address-space
component.
Feature: `krepi.kernel.kernel-memory`. -/
def NoWritableExecutable : Prop :=
  (∀ k : Kind, ¬ (k.attributes.writable = true ∧ k.attributes.executable = true)) ∧
  ∀ (E X : Nat) (cfg : Config) (txns : List Txn), WxPremises txns →
    let s : Shared E X := runAll cfg txns (Shared.initial E X)
    let kernel : List SetView :=
      [⟨.lower, _, s.lowerKernel, cfg.lowerBase⟩, ⟨.upper, _, s.directMap, cfg.directBase⟩]
    WxFree kernel ∧
    ∀ (C : Tables .lower KERNEL_TABLES) (base : UInt64) (C' : Tables .lower KERNEL_TABLES)
      (plan : Plan), (∀ t, C.used ≤ t → t < KERNEL_TABLES → C.table t = Table.zero) →
      C.cloneKernelFrom s.lowerKernel cfg.lowerBase base cfg.bits = .ok (C', plan) →
      WxFree (⟨.lower, _, C'.apply plan, base⟩ :: kernel)

/-! ## 2. After every write

Each row of `After mapping` (lines 316 to 318 and 320 to 329) and of `After
ownership` (lines 333 to 336 and 338 to 345), stated for a success of its
entry on a valid state: the `Requires` column, which the checks of the entry
establish or which its caller vouches for, and the `After` column, between
the state before and the state once the plan has run. "A failed entry
returns an error, changes nothing and returns no plan" (lines 317 and 318,
334): a result of the specification is an `Except`, whose error carries no
state and no plan. -/

/-- `Tables::new`: on storage that is zero in all its $N$ tables,
$M = \emptyset$, $G = P = \emptyset$, so 1 table in use (line 322). -/
def AfterNew : Prop :=
  ∀ (r : Region) (N : Nat) (base : UInt64),
    let s : Tables r N := Tables.new (Pool.zero N)
    (∀ v l, ¬ s.M base v l) ∧ (∀ g, ¬ s.G base g) ∧ (∀ b, ¬ s.P base b) ∧
      s.usedTables = 1

/-- `reset`: $M' = \emptyset$, $G' = P' = \emptyset$ (line 323), and the root
alone in use with every entry 0 (PGT-R04), for a set of any record of
tables in use, also 0 (lines 745 and 746), whose tables not in use are zero
(line 679). -/
def AfterReset : Prop :=
  ∀ (r : Region) (N : Nat) (s : Tables r N) (base : UInt64),
    (∀ t, s.used ≤ t → t < N → s.table t = Table.zero) →
    let s' := s.reset.1.apply s.reset.2
    (∀ v l, ¬ s'.M base v l) ∧ (∀ g, ¬ s'.G base g) ∧ (∀ b, ¬ s'.P base b) ∧
      s'.usedTables = 1 ∧ ∀ i, s'.entry 0 i = 0

/-- `map_page(v, p, k)`: requires $v \notin \mathrm{dom}\,M$; then
$M' = M[v \mapsto (p, k, \mathrm{page})]$, $G' = G \cup \{\mathrm{gib}(v)\}$,
$P' = P \cup \{\mathrm{blk}(v)\}$ (line 324). -/
def AfterMapPage : Prop :=
  ∀ (r : Region) (N : Nat) (s : Tables r N) (v p : UInt64) (k : Kind) (base : UInt64) (bits : UInt8)
    (s₁ : Tables r N) (plan : Plan), s.WellFormed base bits →
    s.mapPage v p k base bits = .ok (s₁, plan) →
    let s' := s₁.apply plan
    s.Unmapped base v ∧
    (∀ v' l, s'.M base v' l ↔
      (v' = v ∧ l = ⟨p, k, .page⟩) ∨ (v' ≠ v ∧ s.M base v' l)) ∧
    (∀ g, s'.G base g ↔ s.G base g ∨ g = gib v) ∧
    (∀ b, s'.P base b ↔ s.P base b ∨ b = blk v)

/-- `map_block(v, p)`: requires $v = \mathrm{blk}(v)$, no page of
$[v, v + 2^{21})$ in $\mathrm{dom}\,M$ and $v \notin P$; then $M'$ adds
$v + i \mapsto (p + i, \mathrm{ReadWrite}, \mathrm{block})$ for
$i = 0, 4096, \ldots, 2^{21} - 4096$, $G' = G \cup \{\mathrm{gib}(v)\}$,
$P' = P$ (line 325). -/
def AfterMapBlock : Prop :=
  ∀ (r : Region) (N : Nat) (s : Tables r N) (v p base : UInt64) (bits : UInt8) (s₁ : Tables r N)
    (plan : Plan), s.WellFormed base bits → s.mapBlock v p base bits = .ok (s₁, plan) →
    let s' := s₁.apply plan
    v = blk v ∧ (∀ i, i < ENTRIES → s.Unmapped base (UInt64.ofNat (v.toNat + PAGE_SIZE * i))) ∧
    ¬ s.P base v ∧
    (∀ v' l, s'.M base v' l ↔ s.M base v' l ∨
      ∃ i, i < ENTRIES ∧ v'.toNat = v.toNat + PAGE_SIZE * i ∧
        l = ⟨UInt64.ofNat (p.toNat + PAGE_SIZE * i), .readWrite, .block⟩) ∧
    (∀ g, s'.G base g ↔ s.G base g ∨ g = gib v) ∧
    (∀ b, s'.P base b ↔ s.P base b)

/-- `unmap_page(v)`: requires $M(v) = (p, k, \mathrm{page})$; then
$M' = M \setminus \{v\}$, $G' = G$, $P' = P$, and the entry returns $p$
(line 326). -/
def AfterUnmapPage : Prop :=
  ∀ (r : Region) (N : Nat) (s : Tables r N) (v base : UInt64) (bits : UInt8) (plan : Plan)
    (p : UInt64), s.WellFormed base bits → s.unmapPage v base bits = .ok (plan, p) →
    let s' := s.apply plan
    (∃ k, s.M base v ⟨p, k, .page⟩) ∧
    (∀ v' l, s'.M base v' l ↔ v' ≠ v ∧ s.M base v' l) ∧
    (∀ g, s'.G base g ↔ s.G base g) ∧ (∀ b, s'.P base b ↔ s.P base b)

/-- `clone_kernel_from(S)`: requires every entry of $M_S$ a page of
`ReadExecute`, `ReadOnly`, `ReadWrite` or `Device` below
$2^{\mathrm{bits}}$; then $M' = M_S$, $G' = G_S$, $P' = P_S$, in the tables
of the indices that $S$ uses (line 327): "each table descriptor pointing at
the target's table of the same index" (lines 272 to 274), so the walk of
every address reaches in the copy the level 2 table, and the level 3 table,
of the index that it reaches in the source, and the copy has the record of
the source. The target is one whose tables not in use are zero (line 679),
as the plan of the copy takes it (lines 445 to 448); the source is an
argument, which the entry does not write. The entries are compared by the
tables that the walk reaches, not by their values, since an invalid entry
of the source is not copied, whatever its other bits. -/
def AfterCloneKernelFrom : Prop :=
  ∀ (r : Region) (N : Nat) (target source : Tables r N) (sourceBase base : UInt64) (bits : UInt8)
    (s₁ : Tables r N) (plan : Plan),
    (∀ t, target.used ≤ t → t < N → target.table t = Table.zero) →
    target.cloneKernelFrom source sourceBase base bits = .ok (s₁, plan) →
    let s' := s₁.apply plan
    (∀ v l, source.M sourceBase v l →
      l.form = .page ∧ copyKinds.contains l.kind = true ∧ l.pa.toNat < 2 ^ bits.toNat) ∧
    (∀ v l, s'.M base v l ↔ source.M sourceBase v l) ∧
    (∀ g, s'.G base g ↔ source.G sourceBase g) ∧
    (∀ b, s'.P base b ↔ source.P sourceBase b) ∧
    (∀ v t2, (∃ e, s'.walk2 base v = .ok (some (t2, e))) ↔
      ∃ e, source.walk2 sourceBase v = .ok (some (t2, e))) ∧
    (∀ v t2 t3, (∃ d, s'.walk base v = .ok (.level3 t2 t3 d)) ↔
      ∃ d, source.walk sourceBase v = .ok (.level3 t2 t3 d)) ∧
    s'.usedTables = source.usedTables

/-- `kernel_map(L)`: requires every page of every range of $L$ outside
$\mathrm{dom}\,M$, the ranges pairwise without a common page and without a
guard page of $L$; then $M'$ adds $v \mapsto (v, k_j, \mathrm{page})$ for
every page $v$ of range $j$ with kind $k_j$, $G'$ and $P'$ add the slots of
those pages, and the plan writes no entry of a guard page of $L$, so a guard
page outside $\mathrm{dom}\,M$ stays outside $\mathrm{dom}\,M'$ (line 328). -/
def AfterKernelMap : Prop :=
  ∀ (N : Nat) (s : Tables .lower N) (layout : Layout) (base : UInt64) (bits : UInt8)
    (s₁ : Tables .lower N) (plan : Plan), s.WellFormed base bits →
    s.kernelMap layout base bits = .ok (s₁, plan) →
    let s' := s₁.apply plan
    (∀ j ∈ layout.ranges, ∀ v, j.HoldsPage v → s.Unmapped base (UInt64.ofNat v)) ∧
    layout.ranges.Pairwise (fun j j' => ∀ v, ¬ (j.HoldsPage v ∧ j'.HoldsPage v)) ∧
    (∀ j ∈ layout.ranges, ∀ g ∈ layout.guards,
      ¬ (j.range.start.toNat ≤ g.toNat ∧ g.toNat < j.range.endNat)) ∧
    (∀ v l, s'.M base v l ↔ s.M base v l ∨
      ∃ j ∈ layout.ranges, j.HoldsPage v.toNat ∧ l = ⟨v, j.kind, .page⟩) ∧
    (∀ g, s'.G base g ↔ s.G base g ∨
      ∃ j ∈ layout.ranges, ∃ v, j.HoldsPage v.toNat ∧ g = gib v) ∧
    (∀ b, s'.P base b ↔ s.P base b ∨
      ∃ j ∈ layout.ranges, ∃ v, j.HoldsPage v.toNat ∧ b = blk v) ∧
    ∀ g ∈ layout.guards, s.Unmapped base (UInt64.ofNat (pageDown g.toNat)) →
      s'.Unmapped base (UInt64.ofNat (pageDown g.toNat))

/-- `direct_map(B)`: requires every page of every usable range of $B$ below
$2^{39}$, its address outside $\mathrm{dom}\,M$; then $M'$ adds
$\mathtt{DIRECT\_BASE} \mid p \mapsto (p, \mathrm{ReadWrite}, \ell(p))$ for
every page $p$ of a usable range, $\ell(p)$ a block when $\mathrm{blk}(p)$
and the 2 MiB after it lie in one usable range and a page otherwise; $G'$
adds the slots of those pages, and $P'$ those of the pages that are mapped
as pages (line 329). -/
def AfterDirectMap : Prop :=
  ∀ (N : Nat) (s : Tables .upper N) (B : Krepi.Spec.Fdt.MemoryPlan) (base : UInt64) (bits : UInt8)
    (s₁ : Tables .upper N) (plan : Plan), s.WellFormed base bits →
    s.directMap B base bits = .ok (s₁, plan) →
    let s' := s₁.apply plan
    (∀ p, usablePage B p = true →
      p < VA_LIMIT ∧ s.Unmapped base (DIRECT_BASE ||| UInt64.ofNat p)) ∧
    (∀ v l, s'.M base v l ↔ s.M base v l ∨
      ∃ p, usablePage B p = true ∧ v = DIRECT_BASE ||| UInt64.ofNat p ∧
        l = ⟨UInt64.ofNat p, .readWrite, if blockForm B p then .block else .page⟩) ∧
    (∀ g, s'.G base g ↔ s.G base g ∨
      ∃ p, usablePage B p = true ∧ g = gib (DIRECT_BASE ||| UInt64.ofNat p)) ∧
    (∀ b, s'.P base b ↔ s.P base b ∨
      ∃ p, usablePage B p = true ∧ blockForm B p = false ∧
        b = blk (DIRECT_BASE ||| UInt64.ofNat p))

/-- `Ownership::new(a, banks, X)`: requires the checks of the initialization,
the last of them the extents that the banks, split by the exclusions, need
against the capacity (lines 561 to 566); then $O(q)$ is the owner of the
exclusions of $X$ that touch $q$, by the order firmware, image, boot
storage, for every managed page $q$ that one touches, and free for every
other; $g = 1$ (line 340). -/
def AfterOwnershipNew : Prop :=
  ∀ (E X : Nat) (arena : UInt64) (banks : List PhysRange) (exclusions : List Exclusion)
    (t : Ownership E X), Ownership.new arena banks exclusions = .ok t →
    arena ≠ 0 ∧ banks ≠ [] ∧ (∀ b ∈ banks, b.onPages = true) ∧
    banks.Pairwise (fun a b => a.overlaps b = false) ∧ banks.length ≤ E ∧
    exclusions.length ≤ X ∧ t.extents.length ≤ E ∧
    (∀ q, q % PAGE_SIZE = 0 → (∃ b ∈ banks, b.holdsPage q = true) →
      t.ownerOf q = some ((firstExcluder exclusions q).elim .free .excluded)) ∧
    t.counter = .next 1

/-- `assign(c, zeroed)`: requires the choice $c$ of `choose` for owner
identity $o$ under the same token, $O(q) = $ free for every page $q$ of $c$,
all in one free extent; then $O' = O[q \mapsto \mathrm{held}(o, g,
\mathrm{published}) : q \in c]$, $g' = g + 1$, or exhausted after
$2^{64} - 1$, and the receipt; when the zeroing failed, `ZeroFailed`,
$O' = O$, $g' = g$ (line 341). -/
def AfterAssign : Prop :=
  (∀ (E X : Nat) (t : Ownership E X) (c : Choice) (zeroed : Bool) (t' : Ownership E X)
    (a : Allocation), t.Invariant → t.Chose c → t.assign c zeroed = .ok (t', a) →
    zeroed = true ∧ ∃ g, t.counter = .next g ∧
      (∀ q, q % PAGE_SIZE = 0 → c.range.holdsPage q = true → t.ownerOf q = some .free) ∧
      (∃ e ∈ t.extents, e.holding = .free ∧ e.range.contains c.range = true) ∧
      (∀ q, q % PAGE_SIZE = 0 →
        t'.ownerOf q = if c.range.holdsPage q then some (.held c.owner g .published)
          else t.ownerOf q) ∧
      t'.counter = Counter.after g ∧ a = ⟨t.arena, c.owner, g, c.range⟩) ∧
  ∀ (E X : Nat) (t : Ownership E X) (c : Choice), t.assign c false = .error .zeroFailed

/-- `reserve(o, m, a, w)`: requires the checks of `choose`; then
$O' = O[q \mapsto \mathrm{held}(o, g, \mathrm{reserved}) : q \in c]$ for the
range $c$ that `choose` would give, $g' = g + 1$ (line 342), and the
reservation, not attempted and with no failure. -/
def AfterReserve : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner pages alignment : UInt64) (p : Placement)
    (t' : Ownership E X) (r : Reservation), t.Invariant →
    t.reserve owner pages alignment p = .ok (t', r) →
    ∃ c g, t.choose owner pages alignment p = .ok c ∧ t.counter = .next g ∧
      (∀ q, q % PAGE_SIZE = 0 →
        t'.ownerOf q = if c.range.holdsPage q then some (.held owner g .reserved) else t.ownerOf q) ∧
      t'.counter = Counter.after g ∧ r = ⟨⟨t.arena, owner, g, c.range⟩, false, 0⟩

/-- `publish(o, x)`: requires $x$ from this arena and
$O(q) = \mathrm{held}(o, x.n, \mathrm{reserved})$ exactly for the pages $q$
of $x$; then $O' = O[q \mapsto \mathrm{held}(o, x.n, \mathrm{published}) :
q \in x]$, $g' = g$ (line 343), and the receipt. -/
def AfterPublish : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner : UInt64) (x : Initialized) (t' : Ownership E X)
    (a : Allocation), t.Invariant → t.publish owner x = .ok (t', a) →
    x.allocation.arena = t.arena ∧ x.allocation.owner = owner ∧
    (∀ q, q % PAGE_SIZE = 0 →
      (t.ownerOf q = some (.held owner x.allocation.generation .reserved) ↔
        x.allocation.range.holdsPage q = true)) ∧
    (∀ q, q % PAGE_SIZE = 0 →
      t'.ownerOf q = if x.allocation.range.holdsPage q then
        some (.held owner x.allocation.generation .published) else t.ownerOf q) ∧
    t'.counter = t.counter ∧ a = x.allocation

/-- `cancel(o, r)`: requires $r$ from this arena and
$O(q) = \mathrm{held}(o, r.n, \mathrm{reserved})$ exactly for the pages $q$
of $r$; when no zeroing of $r$ was attempted, $O' = O[q \mapsto \mathrm{free}
: q \in r]$, $g' = g$; after an attempted zeroing, `ZeroFailed`, $O' = O$,
$g' = g$, and $r$ is returned (line 344). -/
def AfterCancel : Prop :=
  (∀ (E X : Nat) (t : Ownership E X) (owner : UInt64) (r : Reservation) (t' : Ownership E X),
    t.Invariant → t.cancel owner r = .ok t' →
    r.attempted = false ∧ r.allocation.arena = t.arena ∧ r.allocation.owner = owner ∧
    (∀ q, q % PAGE_SIZE = 0 →
      (t.ownerOf q = some (.held owner r.allocation.generation .reserved) ↔
        r.allocation.range.holdsPage q = true)) ∧
    (∀ q, q % PAGE_SIZE = 0 →
      t'.ownerOf q = if r.allocation.range.holdsPage q then some .free else t.ownerOf q) ∧
    t'.counter = t.counter) ∧
  ∀ (E X : Nat) (t : Ownership E X) (owner : UInt64) (r : Reservation), r.attempted = true →
    t.cancel owner r = .error (.zeroFailed, r)

/-- `release(o, x)`: requires $x$ from this arena and
$O(q) = \mathrm{held}(o, x.n, \mathrm{published})$ exactly for the pages
$q$ of $x$; then $O' = O[q \mapsto \mathrm{free} : q \in x]$, $g' = g$
(line 345). -/
def AfterRelease : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner : UInt64) (x : Allocation) (t' : Ownership E X),
    t.Invariant → t.release owner x = .ok t' →
    x.arena = t.arena ∧ x.owner = owner ∧
    (∀ q, q % PAGE_SIZE = 0 → (t.ownerOf q = some (.held owner x.generation .published) ↔
      x.range.holdsPage q = true)) ∧
    (∀ q, q % PAGE_SIZE = 0 →
      t'.ownerOf q = if x.range.holdsPage q then some .free else t.ownerOf q) ∧
    t'.counter = t.counter

/-- **After every write the abstract mapping changes as the contract says**
(PGT-R02 to PGT-R06, PGT-R08 to PGT-R10, PGT-R12). "Each write entry of a set
changes $M$ as its row states once its write plan has been executed" (lines
316 and 317) and "each write entry of the page ownership table changes $O$
and $g$ as its row states" (lines 333 and 334), for the 14 write entries of
lines 347 to 350: the rows of `Tables::new`, `reset`, `map_page`,
`map_block`, `unmap_page`, `clone_kernel_from`, `kernel_map`, `direct_map`,
`Ownership::new`, `assign`, `reserve`, `publish`, `cancel` and `release`. The
fourth invariant of the page ownership table, that "the firmware, image and
boot storage pages never change owner" (line 541), is a statement of two
states that these rows give: each row changes $O$ only on pages that are
free or held.
Feature: `krepi.kernel.kernel-memory`. -/
def AfterEveryWrite : Prop :=
  AfterNew ∧ AfterReset ∧ AfterMapPage ∧ AfterMapBlock ∧ AfterUnmapPage ∧
  AfterCloneKernelFrom ∧ AfterKernelMap ∧ AfterDirectMap ∧ AfterOwnershipNew ∧ AfterAssign ∧
  AfterReserve ∧ AfterPublish ∧ AfterCancel ∧ AfterRelease

/-! ## 3. The direct map after boot -/

/-- **The direct map is unchanged after boot** (PGT-R05). "The boot wiring
writes the direct map once, before the MMU is on, and no entry changes it
afterwards" (lines 505 and 506), and its descriptors are "read-only after
boot" and "the field never changes after it" (line 826): from any shared
state with the MMU on, every list of transactions leaves the direct map's
set as it was, and the MMU on.
Feature: `krepi.kernel.kernel-memory`. -/
def DirectMapUnchangedAfterBoot : Prop :=
  ∀ (E X : Nat) (cfg : Config) (s : Shared E X) (txns : List Txn), s.mmuOn = true →
    (runAll cfg txns s).directMap = s.directMap ∧ (runAll cfg txns s).mmuOn = true

/-! ## 4. The kernel tables -/

/-- **The kernel tables are written only with empty entries** (PGT-R04,
PGT-R07). "A plan for one of the kernel tables writes only invalid entries
and holds no `Invalidate`; no entry of this page removes or changes a valid
entry of the kernel tables" (lines 426 to 429): on a well-formed shared
state, every transaction keeps every valid entry of both kernel sets, and
its plan for a kernel set writes only entries that are invalid when it
writes them and holds no `Invalidate`.
Feature: `krepi.kernel.kernel-memory`. -/
def KernelTablesOnlyFilled : Prop :=
  ∀ (E X : Nat) (cfg : Config) (s : Shared E X) (txn : Txn), s.WellFormed cfg →
    (∀ t i, isValid (s.lowerKernel.entry t i) = true →
      (txn.run cfg s).1.lowerKernel.entry t i = s.lowerKernel.entry t i) ∧
    (∀ t i, isValid (s.directMap.entry t i) = true →
      (txn.run cfg s).1.directMap.entry t i = s.directMap.entry t i) ∧
    ∀ plan, (txn.run cfg s).2 = some plan → txn.FillsOnly s plan

/-! ## 5. The order of the plans -/

/-- **The plans publish in order** (PGT-R07, PGT-R04, PGT-R12). On a
well-formed set:

- the plans of `map_page`, `map_block`, `kernel_map` and `direct_map` zero
  a new table once and write it completely before the one store of its table
  descriptor that makes it reachable, and nothing into it after that store,
  with a `Fence` before that store; they write the entries of a new table in
  index order, and a new table under another new table completely before the
  `Zero` of the other, as the example of new tables and the rule of maps
  order them; they write only invalid entries of the tables that a walk
  reaches, and each valid entry of the root and each valid entry of a level
  2 table other than a block as a table descriptor with no attribute, the
  form that the walk follows; and they end with `Sync` (lines 406 to 425 and
  452 to 454), as `Plan.inOrder` checks. The rest of the rule of maps (lines
  413 to 418), the leaves in address order from one table to the next and in
  the tables that the set holds, and one 2 MiB slot after the other under a
  level 2 table that the set holds, is not stated here: the specification
  test `PlansFollowContractOrder` shows it only on sets that hold the root
  alone, within one 1 GiB slot. These orders leave the same set, since every
  new table is complete and fenced before the one store of its table
  descriptor and a leaf in a table that the set holds is one store into an
  invalid entry, and the plans of `kernel_map` and `direct_map` run with the
  MMU off, into sets that no `TTBR` holds (lines 452 to 454); the plans of
  the specification follow them by their definition, which the refinement
  of the target relates to the plans of the implementation;
- the plan of `unmap_page` is `Store(t, i, 0)` of the leaf of $v$ and then
  `Invalidate(v)` (lines 430 to 432);
- the plan of `clone_kernel_from` is a `Zero` of every table in use of the
  target, in index order, then a `Store` of every valid entry of every table
  in use of the source into the target's table of the same index, in the
  order of the tables and of the entries of each, a leaf as it is and a
  table descriptor pointing at the target's table of the index that it
  points at in the source, and `Sync` last, with no `Fence` (lines 440 to
  451).
Feature: `krepi.kernel.kernel-memory`. -/
def PlansPublishInOrder : Prop :=
  (∀ (r : Region) (N : Nat) (s : Tables r N) (v p : UInt64) (k : Kind) (base : UInt64) (bits : UInt8)
    (s' : Tables r N) (plan : Plan), s.WellFormed base bits →
    s.mapPage v p k base bits = .ok (s', plan) → plan.publishesInOrder base s.pool = true) ∧
  (∀ (r : Region) (N : Nat) (s : Tables r N) (v p base : UInt64) (bits : UInt8) (s' : Tables r N)
    (plan : Plan), s.WellFormed base bits →
    s.mapBlock v p base bits = .ok (s', plan) → plan.publishesInOrder base s.pool = true) ∧
  (∀ (N : Nat) (s : Tables .lower N) (layout : Layout) (base : UInt64) (bits : UInt8)
    (s' : Tables .lower N) (plan : Plan), s.WellFormed base bits →
    s.kernelMap layout base bits = .ok (s', plan) → plan.publishesInOrder base s.pool = true) ∧
  (∀ (N : Nat) (s : Tables .upper N) (B : Krepi.Spec.Fdt.MemoryPlan) (base : UInt64) (bits : UInt8)
    (s' : Tables .upper N) (plan : Plan), s.WellFormed base bits →
    s.directMap B base bits = .ok (s', plan) → plan.publishesInOrder base s.pool = true) ∧
  (∀ (r : Region) (N : Nat) (s : Tables r N) (v base : UInt64) (bits : UInt8) (plan : Plan)
    (p : UInt64), s.WellFormed base bits → s.unmapPage v base bits = .ok (plan, p) →
    ∃ t2 t3 d, s.walk base v = .ok (.level3 t2 t3 d) ∧
      plan = [.store t3 (index3 v) INVALID, .invalidate v]) ∧
  ∀ (r : Region) (N : Nat) (target source : Tables r N) (sourceBase base : UInt64) (bits : UInt8)
    (s : Tables r N) (plan : Plan),
    target.cloneKernelFrom source sourceBase base bits = .ok (s, plan) →
    ∃ stores : List (Nat × Nat × UInt64),
      plan = (List.range (min target.used N)).map Step.zero ++
        stores.map (fun x => Step.store x.1 x.2.1 x.2.2) ++ [.sync] ∧
      stores.Pairwise (fun a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.1 < b.2.1)) ∧
      (∀ x ∈ stores, x.1 < source.used ∧ x.2.1 < ENTRIES ∧
        isValid (source.entry x.1 x.2.1) = true ∧
        if x.1 ∈ source.level3Tables sourceBase then x.2.2 = source.entry x.1 x.2.1
        else ∃ c, source.child? sourceBase (source.entry x.1 x.2.1) = some c ∧
          x.2.2 = tableDescriptor (tableAddress base c)) ∧
      ∀ t i, t < source.used → i < ENTRIES → isValid (source.entry t i) = true →
        ∃ d, (t, i, d) ∈ stores

/-! ## 6. The tables in use -/

/-- **The tables in use are counted by $G$ and $P$** (PGT-R03, PGT-R05,
PGT-R11). "The tables that it uses are the root and one table for each
element of $G$ and of $P$: $\mathrm{used} = 1 + |G| + |P|$" (lines 302 and
303), and "a mapping needs the root, one level 2 table for each 1 GiB slot
that it touches and one level 3 table for each 2 MiB slot that it maps in
part, with pages" (lines 687 to 689): on a well-formed set, the record of
the tables in use is 1 and the numbers of the elements of $G$ and of $P$,
listed once each by `Tables.gSlots` and `Tables.pSlots`.
Feature: `krepi.kernel.kernel-memory`. -/
def TablesInUseCounted : Prop :=
  ∀ (r : Region) (N : Nat) (s : Tables r N) (base : UInt64) (bits : UInt8), s.WellFormed base bits →
    s.usedTables = 1 + (s.gSlots base).length + (s.pSlots base).length ∧
    (s.gSlots base).Nodup ∧ (s.pSlots base).Nodup ∧
    (∀ g, s.G base g ↔ g ∈ s.gSlots base) ∧ (∀ b, s.P base b ↔ b ∈ s.pSlots base)

/-! ## 7. Placement -/

/-- **`choose` takes the first fit of its placement** (PGT-R09, PGT-R10).
"It scans the free extents in address order, from the lowest for a low
placement and from the highest for a high one. In an extent it takes the
part inside the window, and there the lowest aligned start, or, for a high
placement, the highest aligned start whose range ends inside that part. The
first extent that holds the range gives it, unless taking the range would
need more extents than the capacity has free; the scan then goes on" (lines
574 to 579), so that "a range never spans two banks" (line 580), and the
scan ends with "`MetadataExhausted` when an extent was passed over for
capacity and none held the range, and `OutOfMemory` otherwise" (lines 588
to 590). On a well-formed table, whose extents are in address order:

- a choice is of the owner identity of the request and is the range that an
  extent of the scan gives within the capacity, and every extent before it
  in the scan gives no range or one that needs more extents than the
  capacity has free;
- `OutOfMemory` means that no extent holds a range of the request;
- `MetadataExhausted` means that an extent gives a range and that every
  range that an extent gives needs more extents than the capacity has free.
Feature: `krepi.kernel.kernel-memory`.
-/
def PlacementFirstFit : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (owner pages alignment : UInt64) (p : Placement),
    t.WellFormed →
    (∀ c, t.choose owner pages alignment p = .ok c →
      c.owner = owner ∧
      ∃ i e, (t.scanOrder p)[i]? = some e ∧ e.Gives pages alignment p c.range ∧
        e.extra c.range ≤ E - t.extents.length ∧
        ∀ e' ∈ (t.scanOrder p).take i, ∀ r', e'.Gives pages alignment p r' →
          E - t.extents.length < e'.extra r') ∧
    (t.choose owner pages alignment p = .error .outOfMemory →
      ∀ e ∈ t.extents, ∀ r, ¬ e.Holds pages alignment p r) ∧
    (t.choose owner pages alignment p = .error .metadataExhausted →
      (∃ e ∈ t.extents, ∃ r, e.Gives pages alignment p r) ∧
      ∀ e ∈ t.extents, ∀ r, e.Gives pages alignment p r → E - t.extents.length < e.extra r)

/-! ## 8. The owners at boot -/

/-- **The table of the kernel root matches the direct map** (PGT-R08,
PGT-R05). The criterion of PGT-R08: "for the boot memory map of every board
shape, every managed page has exactly one owner, the free pages are exactly
the pages of the direct map"; and "the direct map maps only pages whose
owner is free or a holder" (lines 212 and 213). For every well-formed boot
memory map, the table that `Ownership::new` builds from its managed banks and
exclusions records one owner for every managed page, and once `direct_map`
of the same map has run on a set of `Tables::new` on zero storage, a page is
free exactly when the direct map maps it.
Feature: `krepi.kernel.kernel-memory`. -/
def BootOwnersMatchDirectMap : Prop :=
  ∀ (E X N : Nat) (B : Krepi.Spec.Fdt.MemoryPlan) (arena : UInt64) (banks : List PhysRange)
    (exclusions : List Exclusion) (t : Ownership E X) (base : UInt64) (bits : UInt8)
    (s : Tables .upper N) (plan : Plan),
    B.WellFormed → BootTableRanges B banks exclusions →
    Ownership.new arena banks exclusions = .ok t →
    (Tables.new (Pool.zero N) : Tables .upper N).directMap B base bits = .ok (s, plan) →
    t.OneOwner ∧
    ∀ q, q % PAGE_SIZE = 0 →
      (t.ownerOf q = some .free ↔ ∃ v l, (s.apply plan).M base v l ∧ l.pa.toNat = q)

end Krepi.SpecProperties.PageTables
