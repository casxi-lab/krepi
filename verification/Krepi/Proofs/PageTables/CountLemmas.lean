module

public import Krepi.Proofs.PageTables.MapCheckLemmas
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.EntryLemmas
import Krepi.Proofs.PageTables.LeavesLemmas
import Krepi.Proofs.PageTables.WalkLemmas

/-!
# Page tables: counting the tables, blocks and pages of a map

What a map gives the counts of its plan and the record of its set, so that a
large map is counted from closed forms of its leaves instead of being
evaluated leaf by leaf:

- `Except`: `ok_bind_eq` and `ok_map_eq`, the bind and the map of a success;
- the stores of a plan: `CountOk` (what a count of steps asks of the steps);
  privately, the steps of `mapPlan` that such a count counts are the stores
  of the placed leaves that it counts, so the blocks and the pages of the
  plan of a map are its block and page leaves;
- the new tables of leaves whose root entries are invalid: `tick` (the next
  free index and the slots of the last new tables after one more leaf);
  privately, the next free index of `assignTables` is that of the fold of
  `tick`;
- the leaves of the direct map in runs: `directPage`, `directBlock`,
  `pageRun`, `blockRun`, `pageRun_zero`, `blockRun_zero`,
  `directLeaves_pages` (a run of pages from a start where no block fits;
  privately, no leaf from the end of a range on), `usableLeaves_eq`
  (the leaves of a usable range are a run of pages, a run of blocks and a run
  of pages), the counts `pageRun_blocks`, `pageRun_pages`, `blockRun_blocks`,
  `blockRun_pages`, and the slots `dgib` and `dblk` with `tick_blockRun` and
  `tick_pageRun` (the fold of `tick` over a run of blocks, and over a run of
  pages in one 2 MiB slot; privately, `tick` of one block and of one page);
- `direct_map` into a set without valid root entries, where every leaf is
  placed at the root (private steps): **`directMap_counts`**: on a set whose
  pool is zero and whose record holds the root alone, the map succeeds with
  the tables of the fold of `tick` and the blocks and pages of the leaves
  when those tables fit.
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables
open Krepi.Proofs.Fdt (except_ok_bind)

theorem ok_bind_eq {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a : Except ε α).bind f = f a := rfl

theorem ok_map_eq {ε α β : Type} (a : α) (f : α → β) :
    (Except.ok a : Except ε α).map f = .ok (f a) := rfl

/-! ## The stores of a plan -/

private theorem countP_flatMap_eq {α β : Type} {p : β → Bool} {q : α → Bool}
    {F : List α → List β} : ∀ Rs : List (List α), (∀ R ∈ Rs, (F R).countP p = R.countP q) →
      (Rs.flatMap F).countP p = Rs.flatten.countP q
  | [], _ => rfl
  | R :: Rs, h => by
    rw [List.flatMap_cons, List.flatten_cons, List.countP_append, List.countP_append,
      h R List.mem_cons_self, countP_flatMap_eq Rs fun R' hR' => h R' (List.mem_cons_of_mem _ hR')]

private theorem countP_flatMap_two {α β : Type} {p : β → Bool} {q : α → Bool}
    {F G : List α → List β} : ∀ Rs : List (List α),
      (∀ R ∈ Rs, (F R).countP p + (G R).countP p = R.countP q) →
      (Rs.flatMap F).countP p + (Rs.flatMap G).countP p = Rs.flatten.countP q
  | [], _ => rfl
  | R :: Rs, h => by
    have ih := countP_flatMap_two Rs fun R' hR' => h R' (List.mem_cons_of_mem _ hR')
    have := h R List.mem_cons_self
    simp only [List.flatMap_cons, List.flatten_cons, List.countP_append]
    omega

/-- What a count `f` of the steps of the plan of placed leaves asks of the
steps: no `Zero`, `Fence`, `Sync` or store of a table descriptor counts, and
the store of a placed leaf counts as `g` counts the leaf. -/
structure CountOk (base : UInt64) (placed : List Placed) (f : Step → Bool) (g : Placed → Bool) :
    Prop where
  zero : ∀ t, f (.zero t) = false
  fence : f .fence = false
  sync : f .sync = false
  table : ∀ t i c, f (.store t i (tableAt base c)) = false
  leaf : ∀ q ∈ placed, f q.store = g q

section Count

variable {placed : List Placed} {base : UInt64} {f : Step → Bool} {g : Placed → Bool}

private theorem countP_map_store (hc : CountOk base placed f g) {S : List Placed}
    (hS : ∀ q ∈ S, q ∈ placed) : (S.map Placed.store).countP f = S.countP g := by
  rw [List.countP_map]
  exact List.countP_congr fun q hq => by simp [hc.leaf q (hS q hq)]

private theorem countP_runSteps (hp : PlacedOk placed) (hnd : placed.Nodup)
    (hc : CountOk base placed f g) {R : List Placed} (hR : R ∈ runsBy (·.leaf.gibSlot) placed) :
    (runSteps base R).countP f = R.countP g := by
  obtain ⟨p, rest, rfl, hq⟩ := gib_run hp hR
  have hmem : ∀ q ∈ p :: rest, q ∈ placed := fun q h => (hq q h).1
  have hsub : (p :: rest).Sublist placed := by
    have := List.sublist_flatten_of_mem hR; rwa [runsBy_flatten] at this
  -- a run of one 2 MiB slot whose first leaf is a block is that block alone
  have hslot : ∀ S ∈ runsBy (·.leaf.blockSlot) (p :: rest), ∃ q0 more, S = q0 :: more ∧
      (∀ q ∈ S, q ∈ placed) ∧ (q0.leaf.form = .block → more = []) := by
    intro S hS
    obtain ⟨q0, more, rfl, hS'⟩ := block_run hp hmem hS
    refine ⟨q0, more, rfl, fun q h => hmem q (hS' q h).1, fun hf => ?_⟩
    have hnd' : (q0 :: more).Nodup := by
      have h1 := List.sublist_flatten_of_mem hS
      rw [runsBy_flatten] at h1
      exact hnd.sublist (h1.trans hsub)
    cases more with
    | nil => rfl
    | cons q more =>
      have hq' := hS' q (List.mem_cons_of_mem _ List.mem_cons_self)
      have := hp.blockOne q0 (hmem q0 (hS' q0 List.mem_cons_self).1) q (hmem q hq'.1)
        hq'.2.1.symm hf
      exact absurd (this ▸ List.mem_cons_self) (List.nodup_cons.1 hnd').1
  have hfl := runsBy_flatten (·.leaf.blockSlot) (p :: rest)
  rw [show (p :: rest).countP g = (runsBy (·.leaf.blockSlot) (p :: rest)).flatten.countP g by
    rw [hfl]]
  simp only [runSteps]
  split
  · rw [newLevel2Steps_eq]
    simp only [List.countP_append, List.countP_cons, hc.zero, hc.fence, hc.table, List.countP_nil,
      Bool.false_eq_true, ite_false, Nat.add_zero]
    apply countP_flatMap_two
    intro S hS
    obtain ⟨q0, more, rfl, hall, hone⟩ := hslot S hS
    cases hf : q0.leaf.form
    · rw [← countP_map_store hc hall]
      simp only [childSteps, level2Entry, hf, beq_self_eq_true, ite_true, List.countP_cons,
        hc.zero, hc.table, List.countP_nil, Bool.false_eq_true, ite_false, Nat.add_zero]
    · rw [hone hf]
      simp only [childSteps, level2Entry, hf, List.countP_cons, List.countP_nil,
        hc.leaf q0 (hall q0 List.mem_cons_self), show (Form.block == Form.page) = false from rfl,
        Bool.false_eq_true, ite_false, Nat.zero_add]
  · apply countP_flatMap_eq
    intro S hS
    obtain ⟨q0, more, rfl, hall, -⟩ := hslot S hS
    rw [← countP_map_store hc hall]
    cases hf : q0.leaf.form
    · simp only [heldLevel2Steps, hf]
      split
      · simp only [List.countP_cons, List.countP_append, hc.zero, hc.fence, level2Entry, hf,
          hc.table, List.countP_nil, Bool.false_eq_true, ite_false, Nat.add_zero]
      · rfl
    · simp only [heldLevel2Steps, hf]

/-- The steps of the plan of placed leaves that a count `f` counts are the
placed leaves that `g` counts. -/
private theorem countP_mapPlan (hp : PlacedOk placed) (hnd : placed.Nodup) (hc : CountOk base placed f g) :
    (mapPlan base placed).countP f = placed.countP g := by
  rw [mapPlan_eq, List.countP_append, List.countP_cons, hc.sync, List.countP_nil]
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
  rw [countP_flatMap_eq _ fun R hR => countP_runSteps hp hnd hc hR, runsBy_flatten]

end Count

private theorem ofPage_table (a : UInt64) : Kind.ofPage (tableDescriptor a) = none := by
  cases h : Kind.ofPage (tableDescriptor a) with
  | none => rfl
  | some k =>
    obtain ⟨k', hk⟩ := (ofPage_isSome_iff _).1 (by rw [h]; rfl)
    have := congrArg isPlainTableDescriptor hk
    rw [isPlain_descriptor, isPlain_tableDescriptor] at this
    cases this

private theorem store_desc (q : Placed) : ∃ t i, q.store = .store t i q.leaf.desc := by
  unfold Placed.store; cases q.leaf.form <;> exact ⟨_, _, rfl⟩

private theorem storesBlock_leaf {bits : UInt8} {q : Placed} (h : LeafDesc bits q.leaf) :
    q.store.storesBlock = (q.leaf.form == .block) := by
  obtain ⟨t, i, hs⟩ := store_desc q
  rw [hs]
  cases hf : q.leaf.form
  · obtain ⟨k, hk⟩ := (h.1 hf).1
    simp only [Step.storesBlock]; rw [hk, typeBits_descriptor]; decide
  · simp only [Step.storesBlock, typeBits_of_isReadWriteBlock (h.2 hf).1]; decide

private theorem storesPage_leaf {bits : UInt8} {q : Placed} (h : LeafDesc bits q.leaf) :
    q.store.storesPage = (q.leaf.form == .page) := by
  obtain ⟨t, i, hs⟩ := store_desc q
  rw [hs]
  cases hf : q.leaf.form
  · obtain ⟨k, hk⟩ := (h.1 hf).1
    simp only [Step.storesPage]; rw [hk, typeBits_descriptor, ofPage_descriptor]; rfl
  · simp only [Step.storesPage, typeBits_of_isReadWriteBlock (h.2 hf).1,
      show (BLOCK == TABLE_OR_PAGE) = false by decide, Bool.false_and]
    rfl

/-- The blocks and the pages of the plan of a map whose leaves passed their
checks on a well-formed set are its block leaves and its page leaves. -/
private theorem counts_mapPlan {r : Region} {N : Nat} {s : Tables r N} {base : UInt64} {bits : UInt8}
    {leaves : List (MapLeaf × Place)} (hs : s.WellFormed base bits)
    (hl : LeafFacts s base bits leaves) :
    (mapPlan base (assignTables s.used leaves).2).counts.blocks =
        (leaves.map Prod.fst).countP (·.form == .block) ∧
      (mapPlan base (assignTables s.used leaves).2).counts.pages =
        (leaves.map Prod.fst).countP (·.form == .page) := by
  have hpo := placed_ok hs hl
  have hnd : (assignTables s.used leaves).2.Nodup := (placed_order hl).imp fun {a b} h e => by
    subst e; have := form_size_pos a.leaf.form; omega
  have hd : ∀ q ∈ (assignTables s.used leaves).2, LeafDesc bits q.leaf := fun q hq => by
    obtain ⟨p, hm, -⟩ := placed_leaf hl hq
    exact hl.desc _ hm
  have ht : ∀ t i c, Step.storesBlock (.store t i (tableAt base c)) = false ∧
      Step.storesPage (.store t i (tableAt base c)) = false := fun t i c => by
    simp only [Step.storesBlock, Step.storesPage, tableAt, typeBits_tableDescriptor, ofPage_table,
      Option.isSome_none, Bool.and_false, and_true]
    decide
  rw [← (assignTables_spec s.used leaves (leaves_mono hl)).1, List.countP_map, List.countP_map]
  exact ⟨countP_mapPlan hpo hnd ⟨fun _ => rfl, rfl, rfl, fun t i c => (ht t i c).1,
      fun q hq => storesBlock_leaf (hd q hq)⟩,
    countP_mapPlan hpo hnd ⟨fun _ => rfl, rfl, rfl, fun t i c => (ht t i c).2,
      fun q hq => storesPage_leaf (hd q hq)⟩⟩

/-! ## The new tables of leaves whose root entries are invalid -/

/-- One more leaf whose root entry is invalid, after leaves that took new
tables: from the next free index and the 1 GiB and 2 MiB slots of the last
new level 2 and level 3 tables, the same after the leaf. A leaf of another
1 GiB slot takes a new level 2 table, and a page of another 2 MiB slot a new
level 3 table. -/
def tick (k : Nat × Option Nat × Option Nat) (l : MapLeaf) : Nat × Option Nat × Option Nat :=
  let n := if k.2.1 = some l.gibSlot then k.1 else k.1 + 1
  match l.form with
  | .block => (n, some l.gibSlot, k.2.2)
  | .page => (if k.2.2 = some l.blockSlot then n else n + 1, some l.gibSlot, some l.blockSlot)

private def keysOf (a : Alloc) : Nat × Option Nat × Option Nat :=
  (a.next, a.level2.map Prod.fst, a.level3.map Prod.fst)

private theorem cacheStep_next (c : Option (Nat × Nat)) (slot next : Nat) :
    (cacheStep c slot next).2.2 = (if c.map Prod.fst = some slot then next else next + 1) ∧
      (cacheStep c slot next).2.1.map Prod.fst = some slot := by
  rcases c with _ | ⟨g, t⟩
  · simp [cacheStep]
  · by_cases h : g = slot
    · subst h; simp [cacheStep]
    · simp [cacheStep, h]

private theorem keysOf_add (a : Alloc) (l : MapLeaf) :
    keysOf (a.add (l, .root)) = tick (keysOf a) l := by
  rw [add_eq, stage2_root]
  obtain ⟨h1, h2⟩ := cacheStep_next a.level2 l.gibSlot a.next
  cases hf : l.form
  · rw [stage3_new _ _ _ hf (fun _ _ h => by cases h)]
    obtain ⟨h3, h4⟩ := cacheStep_next a.level3 l.blockSlot (cacheStep a.level2 l.gibSlot a.next).2.2
    simp only [keysOf, tick, hf]
    rw [h4, h3, h2, h1]
    rfl
  · simp only [stage3, hf, keysOf, tick, h1, h2]
    rfl

private theorem keysOf_foldl : ∀ (L : List MapLeaf) (a : Alloc),
    keysOf ((L.map (·, Place.root)).foldl Alloc.add a) = L.foldl tick (keysOf a)
  | [], _ => rfl
  | l :: L, a => by
    simp only [List.map_cons, List.foldl_cons]
    rw [keysOf_foldl L, keysOf_add]

/-- The next free index after the new tables of leaves whose root entries are
all invalid is that of the fold of `tick`. -/
private theorem assign_root_next (used : Nat) (L : List MapLeaf) :
    (assignTables used (L.map (·, Place.root))).1 = (L.foldl tick (used, none, none)).1 :=
  congrArg (·.1) (keysOf_foldl L ⟨used, none, none, []⟩)

/-! ## The leaves of the direct map in runs -/

/-- The page leaf of the direct map at the physical address `pa`. -/
def directPage (pa : Nat) : MapLeaf :=
  ⟨DIRECT_BASE ||| UInt64.ofNat pa, UInt64.ofNat pa, descriptor .readWrite (UInt64.ofNat pa), .page⟩

/-- The block leaf of the direct map at the physical address `pa`. -/
def directBlock (pa : Nat) : MapLeaf :=
  ⟨DIRECT_BASE ||| UInt64.ofNat pa, UInt64.ofNat pa, blockDescriptor (UInt64.ofNat pa), .block⟩

/-- The `k` page leaves of the direct map from `pa`. -/
def pageRun : Nat → Nat → List MapLeaf
  | _, 0 => []
  | pa, k + 1 => directPage pa :: pageRun (pa + PAGE_SIZE) k

/-- The `k` block leaves of the direct map from `pa`. -/
def blockRun : Nat → Nat → List MapLeaf
  | _, 0 => []
  | pa, k + 1 => directBlock pa :: blockRun (pa + BLOCK_SIZE) k

theorem pageRun_zero (pa : Nat) : pageRun pa 0 = [] := rfl

theorem blockRun_zero (pa : Nat) : blockRun pa 0 = [] := rfl

private theorem directLeaves_done {stop fuel pa : Nat} (h : stop ≤ pa) :
    directLeaves stop fuel pa = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp [directLeaves, h]

private theorem directLeaves_blocks {stop : Nat} : ∀ k fuel pa, pa % BLOCK_SIZE = 0 →
    pa + k * BLOCK_SIZE ≤ stop →
    directLeaves stop (fuel + k) pa = blockRun pa k ++ directLeaves stop fuel (pa + k * BLOCK_SIZE)
  | 0, _, _, _, _ => by simp [blockRun]
  | k + 1, fuel, pa, h1, h2 => by
    rw [show fuel + (k + 1) = (fuel + k) + 1 by omega]
    simp only [directLeaves]
    rw [ite_of_neg (by simp only [BLOCK_SIZE] at h2; omega),
      ite_of_pos (by
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
        simp only [BLOCK_SIZE] at h1 h2 ⊢; exact ⟨h1, by omega⟩),
      directLeaves_blocks k fuel (pa + BLOCK_SIZE) (by simp only [BLOCK_SIZE] at h1 ⊢; omega)
        (by simp only [BLOCK_SIZE] at h2 ⊢; omega),
      show pa + BLOCK_SIZE + k * BLOCK_SIZE = pa + (k + 1) * BLOCK_SIZE by
        simp only [BLOCK_SIZE]; omega]
    rfl

theorem directLeaves_pages {stop : Nat} : ∀ k fuel pa,
    (∀ j < k, ¬ ((pa + j * PAGE_SIZE) % BLOCK_SIZE = 0 ∧ pa + j * PAGE_SIZE + BLOCK_SIZE ≤ stop)) →
    pa + k * PAGE_SIZE ≤ stop →
    directLeaves stop (fuel + k) pa = pageRun pa k ++ directLeaves stop fuel (pa + k * PAGE_SIZE)
  | 0, _, _, _, _ => by simp [pageRun]
  | k + 1, fuel, pa, h1, h2 => by
    rw [show fuel + (k + 1) = (fuel + k) + 1 by omega]
    simp only [directLeaves]
    have h0 := h1 0 (by omega)
    simp only [Nat.zero_mul, Nat.add_zero] at h0
    rw [ite_of_neg (by simp only [PAGE_SIZE] at h2; omega),
      ite_of_neg (by simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]; exact h0),
      directLeaves_pages k fuel (pa + PAGE_SIZE) (fun j hj => by
          have := h1 (j + 1) (by omega)
          simp only [PAGE_SIZE] at this ⊢
          rw [show pa + 4096 + j * 4096 = pa + (j + 1) * 4096 by omega]; exact this)
        (by simp only [PAGE_SIZE] at h2 ⊢; omega),
      show pa + PAGE_SIZE + k * PAGE_SIZE = pa + (k + 1) * PAGE_SIZE by
        simp only [PAGE_SIZE]; omega]
    rfl

/-- The leaves of a usable range from `a` up to `e` as runs: `k1` pages, none
at a multiple of 2 MiB with 2 MiB left; then `k2` blocks from a multiple of
2 MiB; then `k3` pages up to `e`, none at a multiple of 2 MiB with 2 MiB left;
within the steps of `directFuel`. -/
theorem usableLeaves_eq {u : Krepi.Spec.Fdt.Span} (a e k1 k2 k3 : Nat) (hs : u.start.toNat = a)
    (he : u.endNat = e)
    (h1 : ∀ j < k1, ¬ ((a + j * PAGE_SIZE) % BLOCK_SIZE = 0 ∧ a + j * PAGE_SIZE + BLOCK_SIZE ≤ e))
    (h2 : (a + k1 * PAGE_SIZE) % BLOCK_SIZE = 0)
    (h3 : ∀ j < k3, ¬ ((a + k1 * PAGE_SIZE + k2 * BLOCK_SIZE + j * PAGE_SIZE) % BLOCK_SIZE = 0 ∧
      a + k1 * PAGE_SIZE + k2 * BLOCK_SIZE + j * PAGE_SIZE + BLOCK_SIZE ≤ e))
    (hk : a + k1 * PAGE_SIZE + k2 * BLOCK_SIZE + k3 * PAGE_SIZE = e)
    (hf : k1 + k2 + k3 ≤ directFuel (e - a)) :
    usableLeaves u = pageRun a k1 ++ blockRun (a + k1 * PAGE_SIZE) k2 ++
      pageRun (a + k1 * PAGE_SIZE + k2 * BLOCK_SIZE) k3 := by
  subst hs he
  unfold usableLeaves
  rw [show directFuel (u.endNat - u.start.toNat) =
    (directFuel (u.endNat - u.start.toNat) - (k1 + k2 + k3)) + k3 + k2 + k1 by omega,
    directLeaves_pages k1 _ _ h1 (by omega), directLeaves_blocks k2 _ _ h2 (by omega),
    directLeaves_pages k3 _ _ h3 (by omega), directLeaves_done (by omega)]
  simp

private theorem countP_pageRun : ∀ k pa, (pageRun pa k).countP (·.form == .block) = 0 ∧
    (pageRun pa k).countP (·.form == .page) = k
  | 0, _ => ⟨rfl, rfl⟩
  | k + 1, pa => by
    obtain ⟨h1, h2⟩ := countP_pageRun k (pa + PAGE_SIZE)
    simp only [pageRun, List.countP_cons, h1, h2, directPage]
    exact ⟨rfl, rfl⟩

private theorem countP_blockRun : ∀ k pa, (blockRun pa k).countP (·.form == .block) = k ∧
    (blockRun pa k).countP (·.form == .page) = 0
  | 0, _ => ⟨rfl, rfl⟩
  | k + 1, pa => by
    obtain ⟨h1, h2⟩ := countP_blockRun k (pa + BLOCK_SIZE)
    simp only [blockRun, List.countP_cons, h1, h2, directBlock]
    exact ⟨rfl, rfl⟩

theorem pageRun_blocks (k pa : Nat) : (pageRun pa k).countP (·.form == .block) = 0 :=
  (countP_pageRun k pa).1

theorem pageRun_pages (k pa : Nat) : (pageRun pa k).countP (·.form == .page) = k :=
  (countP_pageRun k pa).2

theorem blockRun_blocks (k pa : Nat) : (blockRun pa k).countP (·.form == .block) = k :=
  (countP_blockRun k pa).1

theorem blockRun_pages (k pa : Nat) : (blockRun pa k).countP (·.form == .page) = 0 :=
  (countP_blockRun k pa).2

/-- The 1 GiB slot of a leaf of the direct map at `pa`. -/
def dgib (pa : Nat) : Nat := DIRECT_BASE.toNat / GIB_SIZE + pa / GIB_SIZE

/-- The 2 MiB slot of a leaf of the direct map at `pa`. -/
def dblk (pa : Nat) : Nat := DIRECT_BASE.toNat / BLOCK_SIZE + pa / BLOCK_SIZE

private theorem slots_direct {pa : Nat} (h : pa < VA_LIMIT) {l : MapLeaf}
    (hl : l.va = DIRECT_BASE ||| UInt64.ofNat pa) : l.gibSlot = dgib pa ∧ l.blockSlot = dblk pa := by
  have hx : (UInt64.ofNat pa).toNat = pa := by
    rw [UInt64.toNat_ofNat']; apply Nat.mod_eq_of_lt; simp only [VA_LIMIT] at h; omega
  have hv := direct_or (a := UInt64.ofNat pa) (by rw [hx]; exact h)
  simp only [MapLeaf.gibSlot, MapLeaf.blockSlot, dgib, dblk, hl, hv, hx, direct_base_toNat,
    GIB_SIZE, BLOCK_SIZE]
  omega

private theorem tick_block {pa : Nat} (h : pa < VA_LIMIT) (n : Nat) (g b : Option Nat) :
    tick (n, g, b) (directBlock pa) =
      (n + (if g = some (dgib pa) then 0 else 1), some (dgib pa), b) := by
  have hs := (slots_direct (l := directBlock pa) h rfl).1
  simp only [tick, directBlock] at hs ⊢
  simp only [hs]
  split <;> rfl

private theorem tick_page {pa : Nat} (h : pa < VA_LIMIT) (n : Nat) (g b : Option Nat) :
    tick (n, g, b) (directPage pa) =
      (n + (if g = some (dgib pa) then 0 else 1) + (if b = some (dblk pa) then 0 else 1),
        some (dgib pa), some (dblk pa)) := by
  obtain ⟨hs1, hs2⟩ := slots_direct (l := directPage pa) h rfl
  simp only [tick, directPage] at hs1 hs2 ⊢
  simp only [hs1, hs2]
  split <;> split <;> rfl

/-- The fold of `tick` over `k + 1` blocks from `pa`: a new level 2 table for
the first block unless the last new one is of its slot, and one for each
further 1 GiB slot. -/
theorem tick_blockRun : ∀ k pa n g b, pa + (k + 1) * BLOCK_SIZE ≤ VA_LIMIT →
    (blockRun pa (k + 1)).foldl tick (n, g, b) =
      (n + (if g = some (dgib pa) then 0 else 1) + ((pa + k * BLOCK_SIZE) / GIB_SIZE - pa / GIB_SIZE),
        some (dgib (pa + k * BLOCK_SIZE)), b)
  | 0, pa, n, g, b, h => by
    rw [show blockRun pa (0 + 1) = [directBlock pa] from rfl, List.foldl_cons, List.foldl_nil,
      tick_block (by simp only [BLOCK_SIZE] at h; omega)]
    simp
  | k + 1, pa, n, g, b, h => by
    rw [show blockRun pa (k + 1 + 1) = directBlock pa :: blockRun (pa + BLOCK_SIZE) (k + 1) from rfl,
      List.foldl_cons, tick_block (by simp only [BLOCK_SIZE] at h; omega),
      tick_blockRun k (pa + BLOCK_SIZE) _ _ b (by simp only [BLOCK_SIZE] at h ⊢; omega),
      show pa + BLOCK_SIZE + k * BLOCK_SIZE = pa + (k + 1) * BLOCK_SIZE by
        simp only [BLOCK_SIZE]; omega]
    congr 1
    split <;> split <;>
      (rename_i h2; simp only [Option.some.injEq, dgib, Nat.add_left_cancel_iff] at h2;
       simp only [GIB_SIZE, BLOCK_SIZE] at h h2 ⊢; omega)

/-- The fold of `tick` over `k + 1` pages from `pa` in one 2 MiB slot: a new
level 2 table unless the last new one is of its 1 GiB slot, and a new level
3 table unless the last new one is of its 2 MiB slot. -/
theorem tick_pageRun : ∀ k pa n g b, pa + (k + 1) * PAGE_SIZE ≤ VA_LIMIT →
    pa / BLOCK_SIZE = (pa + k * PAGE_SIZE) / BLOCK_SIZE →
    (pageRun pa (k + 1)).foldl tick (n, g, b) =
      (n + (if g = some (dgib pa) then 0 else 1) + (if b = some (dblk pa) then 0 else 1),
        some (dgib pa), some (dblk pa))
  | 0, pa, n, g, b, h, _ => by
    rw [show pageRun pa (0 + 1) = [directPage pa] from rfl, List.foldl_cons, List.foldl_nil,
      tick_page (by simp only [PAGE_SIZE] at h; omega)]
  | k + 1, pa, n, g, b, h, hb => by
    rw [show pageRun pa (k + 1 + 1) = directPage pa :: pageRun (pa + PAGE_SIZE) (k + 1) from rfl,
      List.foldl_cons, tick_page (by simp only [PAGE_SIZE] at h; omega),
      tick_pageRun k (pa + PAGE_SIZE) _ _ _ (by simp only [PAGE_SIZE] at h ⊢; omega)
        (by simp only [PAGE_SIZE, BLOCK_SIZE] at hb ⊢; omega)]
    have e1 : dgib (pa + PAGE_SIZE) = dgib pa := by
      simp only [dgib, PAGE_SIZE, GIB_SIZE, BLOCK_SIZE] at hb ⊢; omega
    have e2 : dblk (pa + PAGE_SIZE) = dblk pa := by
      simp only [dblk, PAGE_SIZE, BLOCK_SIZE] at hb ⊢; omega
    simp only [e1, e2, ite_true, Nat.add_zero]

/-! ## The direct map on a set without valid root entries -/

section Fresh

variable {N : Nat} {s : Tables .upper N} {base : UInt64} {bits : UInt8}

private theorem place_fresh (h0 : ∀ i, s.entry 0 i = 0) (l : MapLeaf) :
    s.place base l = .ok .root := by
  unfold Tables.place
  rw [walk2_ok.2 (Or.inl ⟨by rw [h0]; rfl, rfl⟩)]
  rfl

private theorem fold_fresh (h0 : ∀ i, s.entry 0 i = 0) {taken : MapLeaf → Bool} :
    ∀ (ls : List MapLeaf) (acc : List (MapLeaf × Place)), (∀ l ∈ ls, taken l = false) →
      ls.foldlM (s.checkLeaf base taken) acc = .ok ((ls.map (·, Place.root)).reverse ++ acc)
  | [], acc, _ => rfl
  | l :: ls, acc, h => by
    have h1 : s.checkLeaf base taken acc l = .ok ((l, .root) :: acc) := by
      unfold Tables.checkLeaf
      rw [place_fresh h0, except_ok_bind, h l List.mem_cons_self]
      rfl
    rw [List.foldlM_cons, h1, except_ok_bind,
      fold_fresh h0 ls _ fun l' hl' => h l' (List.mem_cons_of_mem _ hl')]
    simp

private theorem checkUsableRange_fresh (h0 : ∀ i, s.entry 0 i = 0)
    {earlier : List Krepi.Spec.Fdt.Span} {acc : List (MapLeaf × Place)} {u : Krepi.Spec.Fdt.Span}
    (hu : UsableOk bits u) (he : ∀ e ∈ earlier, e.endNat ≤ u.start.toNat) :
    s.checkUsableRange base bits (earlier, acc) u =
      .ok (earlier ++ [u], ((usableLeaves u).map (·, Place.root)).reverse ++ acc) := by
  obtain ⟨h1, h2, h3, h4⟩ := hu
  have hf := fold_fresh (base := base) h0
    (taken := fun l => earlier.any fun e => l.meets e.start.toNat e.endNat) (usableLeaves u) acc
    (fun l hl => by
      have := ((usableLeaves_spec ⟨h1, h2, h3, h4⟩).1 l hl).1
      simp only [List.any_eq_false, MapLeaf.meets, Bool.and_eq_true, decide_eq_true_eq, not_and,
        Nat.not_lt]
      intro e hm _
      have := he e hm
      omega)
  unfold Tables.checkUsableRange
  simp only [show (u.start.toNat % PAGE_SIZE != 0 || u.endNat % PAGE_SIZE != 0) = false by
      simp [h1, h2],
    show (decide (VA_LIMIT < u.endNat) || decide (2 ^ bits.toNat < u.endNat)) = false by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt]; exact ⟨h3, h4⟩,
    Bool.false_eq_true, ite_false]
  unfold usableLeaves at hf
  rw [hf]
  rfl

private theorem usable_fold_fresh (h0 : ∀ i, s.entry 0 i = 0) :
    ∀ (us earlier : List Krepi.Spec.Fdt.Span) (acc : List (MapLeaf × Place)),
      (∀ u ∈ us, UsableOk bits u) → (∀ e ∈ earlier, ∀ u ∈ us, e.endNat ≤ u.start.toNat) →
      us.Pairwise (fun a b => a.endNat ≤ b.start.toNat) →
      us.foldlM (s.checkUsableRange base bits) (earlier, acc) =
        .ok (earlier ++ us, ((us.flatMap usableLeaves).map (·, Place.root)).reverse ++ acc)
  | [], earlier, acc, _, _, _ => by simp; rfl
  | u :: us, earlier, acc, hok, he, hpw => by
    rw [List.foldlM_cons, checkUsableRange_fresh h0 (hok u List.mem_cons_self)
      (fun e h => he e h u List.mem_cons_self), except_ok_bind,
      usable_fold_fresh h0 us _ _ (fun u' h => hok u' (List.mem_cons_of_mem _ h))
        (fun e h u' hu' => by
          rcases List.mem_append.1 h with h | h
          · exact he e h u' (List.mem_cons_of_mem _ hu')
          · rw [List.mem_singleton.1 h]; exact (List.pairwise_cons.1 hpw).1 u' hu')
        (List.pairwise_cons.1 hpw).2]
    simp

/-- `direct_map` into a set whose root entries are invalid, of usable ranges
that pass their checks and lie in ascending order apart: the write phase of
the leaves of the ranges, each placed at the root. -/
private theorem directMap_fresh (hp : PoolOk N base bits) (h0 : ∀ i, s.entry 0 i = 0)
    {M : Krepi.Spec.Fdt.MemoryPlan}
    (hok : ∀ u ∈ sortByKey (·.start.toNat) M.availableRanges, UsableOk bits u)
    (hpw : (sortByKey (·.start.toNat) M.availableRanges).Pairwise
      (fun a b => a.endNat ≤ b.start.toNat)) :
    s.directMap M base bits = s.mapLeaves base
      (((sortByKey (·.start.toNat) M.availableRanges).flatMap usableLeaves).map (·, Place.root)) := by
  unfold Tables.directMap
  rw [(checkPool_ok (u := ())).2 hp, except_ok_bind,
    usable_fold_fresh h0 _ [] [] hok (by simp) hpw, except_ok_bind]
  simp

end Fresh

private theorem mapLeaves_fits {r : Region} {N : Nat} {s : Tables r N} {base : UInt64}
    {L : List (MapLeaf × Place)} (h : (assignTables s.used L).1 ≤ N) :
    s.mapLeaves base L = .ok ({ s with used := (assignTables s.used L).1 },
      mapPlan base (assignTables s.used L).2) := by
  unfold Tables.mapLeaves
  generalize assignTables s.used L = res at h ⊢
  obtain ⟨next, placed⟩ := res
  simp only at h ⊢
  rw [ite_of_neg (by omega)]
  rfl

/-- `direct_map` into a set whose pool is zero and whose record holds the
root alone, of a boot memory map whose usable ranges `us` pass their checks
and lie in ascending order apart, when the tables of the fold of `tick` over
their leaves fit in the pool: it succeeds with those tables in use, and its
plan counts the block leaves and the page leaves. -/
theorem directMap_counts {N : Nat} {s : Tables .upper N} {base : UInt64} {bits : UInt8}
    {M : Krepi.Spec.Fdt.MemoryPlan} {us : List Krepi.Spec.Fdt.Span} (hp : PoolOk N base bits)
    (hz : ∀ t i, s.pool.get t i = 0) (hu : s.used = 1)
    (hus : sortByKey (·.start.toNat) M.availableRanges = us) (hok : ∀ u ∈ us, UsableOk bits u)
    (hpw : us.Pairwise (fun a b => a.endNat ≤ b.start.toNat))
    (hN : ((us.flatMap usableLeaves).foldl tick (1, none, none)).1 ≤ N) :
    ∃ s₁ plan, s.directMap M base bits = .ok (s₁, plan) ∧
      s₁.used = ((us.flatMap usableLeaves).foldl tick (1, none, none)).1 ∧
      plan.counts.blocks = (us.flatMap usableLeaves).countP (·.form == .block) ∧
      plan.counts.pages = (us.flatMap usableLeaves).countP (·.form == .page) := by
  have h0 : ∀ i, s.entry 0 i = 0 := fun i => by rw [entry_eq_get, hz]
  have hnext := assign_root_next s.used (us.flatMap usableLeaves)
  rw [hu] at hnext
  have hdm := directMap_fresh (M := M) hp h0 (hus ▸ hok) (hus ▸ hpw)
  rw [hus] at hdm
  have hok' := hdm.trans (mapLeaves_fits (s := s) (base := base)
    (L := (us.flatMap usableLeaves).map (·, Place.root)) (by rw [hu, hnext]; exact hN))
  obtain ⟨leaves, hl, -, -, -, hplan, -, hmap, -⟩ := directMap_facts (wf_zero hp hz hu) hok'
  rw [hus] at hmap
  obtain ⟨hb, hpg⟩ := counts_mapPlan (wf_zero hp hz hu) hl
  rw [hmap] at hb hpg
  refine ⟨_, _, hok', by show (assignTables s.used _).1 = _; rw [hu, hnext], ?_, ?_⟩
  · rw [hplan, hb]
  · rw [hplan, hpg]

end Krepi.Proofs.PageTables
