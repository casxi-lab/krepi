module

public import Krepi.Proofs.PageTables.Refinement.LayoutSpecLemmas
public import Krepi.Spec.PageTables.Witnesses.TableSets
public import Krepi.Proofs.Fdt.Plan
public import Krepi.Proofs.Fdt.PlanLemmas
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.BitLemmas

/-!
# Page tables: the checks and the leaf search of the direct map, on the specification side

Lemmas about `Tables.directMap` (`Tables.checkUsableRange`, the leaves
`directLeaves` of a usable range and the fold of `Tables.checkLeaf` over
them), in the forms that the triples of `boot::direct` need
(`Krepi.Proofs.PageTables.Refinement.DirectLemmas`), and the leaf search of
its plan on numbers. The module imports no generated definitions, so it is
built once and not again for every mutant of the code.

- The boot memory map: `builtPlan_wellFormed` (a map that the fdt entries
  build is well-formed), `usable_wf` (its usable ranges are nonempty, on
  pages and apart in address order) and `usable_sorted` (sorting them by
  their start leaves them as they are).
- The leaves of a usable range as the code walks them: `directLeaf` (the
  leaf at an address: a block at a multiple of 2 MiB with 2 MiB left, a page
  elsewhere), `directLeaf_form`, `directLeaf_of_block`, `directLeaf_of_page`,
  `directLeaf_size`, `directLeaf_pa`, `directLeaf_va`, `directLeaf_va_toNat`,
  `directLeaves_succ`,
  `directLeaves_stop`,
  and the fuel: `leafFuel` (an upper bound on the leaves left from an
  address), `leafFuel_step` and `leafFuel_leaf` (one leaf uses one),
  `leafFuel_start` (the fuel `directFuel` of the specification covers a
  range), `directFuel_le` (at most `2 ^ 19` leaves in a range below
  `2 ^ 39`) and `usable_room` (the room of the record of new tables before a
  range).
- The ranges before: `reachSpans`, `reachSpans_append`, and
  `any_meets_spans` (for ranges that start at or below a leaf, an earlier
  range shares an address with it exactly when the leaf starts below
  `reachSpans`).
- The fold of the checks of the leaves: `checkLeavesFrom`,
  `checkLeavesFrom_succ`, `checkLeavesFrom_stop`, `checkLeavesFrom_length`.
- The checks of one range as nested conditions: `checkUsableRange_eq`, and
  what a success adds: `checkUsableRange_passed`.
- `Tables.directMap` step by step: `directMap_pool_error`,
  `directMap_fold_error`, `directMap_fold_ok`.
- The leaf search of the plan on numbers: `leafAtFound`, `rangeFind`,
  `usableFind` (the first leaf at or above an address of the usable ranges,
  as `usable_leaf` finds it), `usableFind_cons_lt`, `usableFind_cons_ge`,
  `usableFind_nil`, `usableFind_skip` (ranges that end at or below the
  address do not change the search), `spanView`, `rangeFind_false`,
  `rangeFind_bounds` and `usableFind_bounds` (the leaf found lies at or above
  the address, below the limit and below the ends of the ranges).
- The cursor and the state of the search: `cur_take_gib` (a step whose
  search asks for pages keeps the 1 GiB slot), `cur_leaf_seek` and
  `cur_take_seek` (a step that asks for no step yet does so for the leaf
  found, from which the search of the children starts), `cur_search_frm`
  (every search starts at the address of the cursor).
- The start of the search and the ranges of a success:
  `usableFind_zero_cons` (the empty range at 0 of the start does not change
  the search), `fold_checkUsableRange_low` and `directMap_ok_low` (the usable
  ranges of a success of `Tables.directMap` end at or below `2 ^ 39`).
-/

@[expose] public section

open Krepi.Spec.PageTables

namespace Krepi.Proofs.PageTables.Refinement

variable {N : Nat}

/-! ## The boot memory map -/

/-- A boot memory map that an entry of the fdt specification builds is
well-formed. -/
theorem builtPlan_wellFormed {p : Krepi.Spec.Fdt.MemoryPlan}
    (hp : Witnesses.TableSets.BuiltPlan p) : p.WellFormed := by
  rcases hp with ⟨_, _, _, h⟩ | ⟨_, _, _, _, h⟩
  · exact Krepi.Proofs.Fdt.allRam_wellFormed h
  · exact Krepi.Proofs.Fdt.new_wellFormed h

/-- The usable ranges of a well-formed boot memory map: each nonempty and on
pages, each ending at or before the start of the next, and at most one for
each managed bank and each reservation. -/
theorem usable_wf {p : Krepi.Spec.Fdt.MemoryPlan} (hp : p.WellFormed) :
    (∀ u ∈ p.availableRanges, u.Nonempty ∧ u.OnPages) ∧
      p.availableRanges.Pairwise (fun a b => a.endNat ≤ b.start.toNat) ∧
      p.availableRanges.length ≤ p.managed.length + p.reservations.length :=
  Krepi.Proofs.Fdt.Plan.availableRangesWellFormed p hp

/-- The usable ranges of a well-formed boot memory map are in address order:
`Tables.directMap` sorts them into the same list. -/
theorem usable_sorted {p : Krepi.Spec.Fdt.MemoryPlan} (hp : p.WellFormed) :
    sortByKey (·.start.toNat) p.availableRanges = p.availableRanges := by
  obtain ⟨hne, hpw, -⟩ := usable_wf hp
  refine sortByKey_of_pairwise _ _ (List.Pairwise.imp_of_mem ?_ hpw)
  intro a b ha _ hab
  have := Krepi.Proofs.Fdt.nonempty_lt (hne a ha).1
  omega

/-! ## The leaves of a usable range -/

/-- The leaf of the direct map at the physical address `pa` of a usable range
that ends at `stop`, the head of `directLeaves stop (fuel + 1) pa`: the block
of `ReadWrite` at a multiple of 2 MiB with at least 2 MiB left, the page of
`ReadWrite` elsewhere, at `DIRECT_BASE | pa`. -/
def directLeaf (stop pa : Nat) : MapLeaf :=
  let a := UInt64.ofNat pa
  if pa % BLOCK_SIZE == 0 && pa + BLOCK_SIZE ≤ stop then
    ⟨DIRECT_BASE ||| a, a, blockDescriptor a, .block⟩
  else ⟨DIRECT_BASE ||| a, a, descriptor .readWrite a, .page⟩

/-- The form of `directLeaf` as a condition on numbers. -/
theorem directLeaf_form (stop pa : Nat) :
    (directLeaf stop pa).form =
      if pa % BLOCK_SIZE = 0 ∧ pa + BLOCK_SIZE ≤ stop then .block else .page := by
  unfold directLeaf
  by_cases h : pa % BLOCK_SIZE = 0 ∧ pa + BLOCK_SIZE ≤ stop
  · obtain ⟨h1, h2⟩ := h
    simp [h1, h2]
  · rw [not_and] at h
    by_cases h1 : pa % BLOCK_SIZE = 0
    · simp [h1, h h1]
    · simp [h1]

/-- `directLeaf` where a block goes. -/
theorem directLeaf_of_block {stop pa : Nat} (h : pa % BLOCK_SIZE = 0 ∧ pa + BLOCK_SIZE ≤ stop) :
    directLeaf stop pa = ⟨DIRECT_BASE ||| UInt64.ofNat pa, UInt64.ofNat pa,
      blockDescriptor (UInt64.ofNat pa), .block⟩ := by
  obtain ⟨h1, h2⟩ := h
  unfold directLeaf
  simp [h1, h2]

/-- `directLeaf` where a page goes. -/
theorem directLeaf_of_page {stop pa : Nat} (h : ¬ (pa % BLOCK_SIZE = 0 ∧ pa + BLOCK_SIZE ≤ stop)) :
    directLeaf stop pa = ⟨DIRECT_BASE ||| UInt64.ofNat pa, UInt64.ofNat pa,
      descriptor .readWrite (UInt64.ofNat pa), .page⟩ := by
  rw [not_and] at h
  unfold directLeaf
  by_cases h1 : pa % BLOCK_SIZE = 0
  · simp [h1, h h1]
  · simp [h1]

/-- The size of `directLeaf`, the step to the next leaf. -/
theorem directLeaf_size (stop pa : Nat) :
    (directLeaf stop pa).form.size =
      if pa % BLOCK_SIZE = 0 ∧ pa + BLOCK_SIZE ≤ stop then BLOCK_SIZE else PAGE_SIZE := by
  rw [directLeaf_form]; split <;> rfl

theorem directLeaf_pa (stop pa : Nat) : (directLeaf stop pa).pa = UInt64.ofNat pa := by
  unfold directLeaf; split <;> rfl

theorem directLeaf_va (stop pa : Nat) :
    (directLeaf stop pa).va = DIRECT_BASE ||| UInt64.ofNat pa := by
  unfold directLeaf; split <;> rfl

/-- The virtual address of `directLeaf` below `2 ^ 39` is `DIRECT_BASE` plus
its physical address. -/
theorem directLeaf_va_toNat {stop pa : Nat} (h : pa < 2 ^ 39) :
    (directLeaf stop pa).va.toNat = DIRECT_BASE.toNat + pa := by
  have ha : (UInt64.ofNat pa).toNat = pa :=
    UInt64.toNat_ofNat_of_lt' (Nat.lt_trans h (by decide))
  rw [directLeaf_va, direct_or (by rw [ha]; exact h), ha]

theorem directLeaves_succ (stop fuel : Nat) {pa : Nat} (h : pa < stop) :
    directLeaves stop (fuel + 1) pa =
      directLeaf stop pa :: directLeaves stop fuel (pa + (directLeaf stop pa).form.size) := by
  have hn : ¬ stop ≤ pa := Nat.not_le.2 h
  simp only [directLeaves, hn, ↓reduceIte, directLeaf]
  split <;> rfl

theorem directLeaves_stop {stop pa : Nat} (fuel : Nat) (h : stop ≤ pa) :
    directLeaves stop fuel pa = [] := by
  cases fuel with
  | zero => rfl
  | succ f => simp only [directLeaves, h, ↓reduceIte]

/-- An upper bound on the leaves of a usable range that ends at `stop` from
the page boundary `pa`: past the last multiple of 2 MiB at or below `stop`,
its pages; before it, its blocks and the pages before the next multiple of
2 MiB, and 511 more for the pages after the last block. -/
def leafFuel (stop pa : Nat) : Nat :=
  if stop / BLOCK_SIZE * BLOCK_SIZE ≤ pa then (stop - pa) / PAGE_SIZE
  else (stop - pa) / BLOCK_SIZE +
    (if pa % BLOCK_SIZE = 0 then 511 else (BLOCK_SIZE - pa % BLOCK_SIZE) / PAGE_SIZE + 511)

/-- One leaf of size `z` (a block where `directLeaf` puts one, a page
elsewhere) from a page boundary below the end, a page boundary, uses at
least one unit of `leafFuel`. -/
theorem leafFuel_step {stop pa z : Nat} (hpa : pa % PAGE_SIZE = 0) (hs : stop % PAGE_SIZE = 0)
    (h : pa < stop) (hz1 : pa % BLOCK_SIZE = 0 ∧ pa + BLOCK_SIZE ≤ stop → z = BLOCK_SIZE)
    (hz2 : ¬ (pa % BLOCK_SIZE = 0 ∧ pa + BLOCK_SIZE ≤ stop) → z = PAGE_SIZE) :
    leafFuel stop (pa + z) + 1 ≤ leafFuel stop pa := by
  unfold leafFuel
  simp only [BLOCK_SIZE, PAGE_SIZE] at hpa hs hz1 hz2 ⊢
  by_cases c1 : stop / 2097152 * 2097152 ≤ pa + z <;>
  by_cases c2 : (pa + z) % 2097152 = 0 <;>
  by_cases c3 : stop / 2097152 * 2097152 ≤ pa <;>
  by_cases c4 : pa % 2097152 = 0 <;>
  simp only [c1, c2, c3, c4, ↓reduceIte] <;> omega

/-- `leafFuel_step` for the leaf of `directLeaf`. -/
theorem leafFuel_leaf {stop pa : Nat} (hpa : pa % PAGE_SIZE = 0) (hs : stop % PAGE_SIZE = 0)
    (h : pa < stop) :
    leafFuel stop (pa + (directLeaf stop pa).form.size) + 1 ≤ leafFuel stop pa :=
  leafFuel_step hpa hs h (fun hb => by rw [directLeaf_size]; simp only [hb, and_self, ↓reduceIte])
    (fun hb => by rw [directLeaf_size]; simp only [hb, ↓reduceIte])

/-- The fuel `directFuel` of the specification covers the leaves of a range
whose ends are page boundaries. -/
theorem leafFuel_start {stop pa : Nat} (hpa : pa % PAGE_SIZE = 0) (hs : stop % PAGE_SIZE = 0) :
    leafFuel stop pa ≤ directFuel (stop - pa) := by
  simp only [leafFuel, directFuel, ENTRIES, BLOCK_SIZE, PAGE_SIZE] at hpa hs ⊢
  by_cases h1 : stop / 2097152 * 2097152 ≤ pa
  · simp only [h1, ↓reduceIte]; omega
  · by_cases h2 : pa % 2097152 = 0
    · simp only [h1, h2, ↓reduceIte]; omega
    · simp only [h1, h2, ↓reduceIte]; omega

/-- The fuel of a usable range below `2 ^ 39`: at most `2 ^ 19` leaves. -/
theorem directFuel_le {len : Nat} (h : len ≤ 2 ^ 39) : directFuel len ≤ 2 ^ 19 := by
  have h1 : len / 2097152 ≤ 262144 :=
    Nat.le_trans (Nat.div_le_div_right (c := 2097152) h) (by decide)
  simp only [directFuel, BLOCK_SIZE, ENTRIES]
  rw [show (2 : Nat) ^ 19 = 524288 from rfl]
  omega

/-- The bound on the record of new tables before a usable range of a boot
memory map of at most 164 usable ranges: at most `2 ^ 19` leaves a range and
two new tables a leaf. -/
theorem usable_room {u n m idx : Nat} (h1 : u + 2 ^ 28 ≤ m) (h2 : n ≤ idx * 2 ^ 19)
    (h3 : idx ≤ 163) : u + 2 * (n + 2 ^ 19) + 2 ≤ m := by
  have hn : n ≤ 163 * 2 ^ 19 := Nat.le_trans h2 (Nat.mul_le_mul_right _ h3)
  have hb : 2 * (n + 2 ^ 19) + 2 ≤ 2 ^ 28 :=
    Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hn _)) 2)
      (Nat.le_of_ble_eq_true rfl)
  rw [Nat.add_assoc]
  exact Nat.le_trans (Nat.add_le_add_left hb u) h1

/-! ## The ranges before -/

/-- The largest end of the usable ranges before, 0 for none: what the code
keeps as `reach`. -/
def reachSpans (earlier : List Krepi.Spec.Fdt.Span) : Nat :=
  earlier.foldl (fun m e => max m e.endNat) 0

private theorem foldl_max_spans (l : List Krepi.Spec.Fdt.Span) (a : Nat) :
    l.foldl (fun m e => max m e.endNat) a = max a (l.foldl (fun m e => max m e.endNat) 0) := by
  induction l generalizing a with
  | nil => simp
  | cons e l ih =>
    simp only [List.foldl_cons]
    rw [ih (max a e.endNat), ih (max 0 e.endNat)]
    omega

theorem reachSpans_append (earlier : List Krepi.Spec.Fdt.Span) (u : Krepi.Spec.Fdt.Span) :
    reachSpans (earlier ++ [u]) = max (reachSpans earlier) u.endNat := by
  simp only [reachSpans, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem lt_reachSpans_iff (pa : Nat) :
    ∀ earlier : List Krepi.Spec.Fdt.Span, pa < reachSpans earlier ↔ ∃ e ∈ earlier, pa < e.endNat := by
  intro earlier
  induction earlier using List.reverseRecOn with
  | nil => simp [reachSpans]
  | append_singleton l e ih =>
    rw [reachSpans_append]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · intro h
      rcases Nat.lt_or_ge pa (reachSpans l) with h1 | h1
      · obtain ⟨e', he', h'⟩ := ih.1 h1; exact ⟨e', Or.inl he', h'⟩
      · exact ⟨e, Or.inr rfl, by omega⟩
    · rintro ⟨e', he' | rfl, h'⟩
      · have := ih.2 ⟨e', he', h'⟩; omega
      · omega

/-- For a leaf at `pa` and usable ranges before that start at or below it,
a range before shares an address with the leaf exactly when the leaf starts
below the largest end of those ranges: the test of the code. -/
theorem any_meets_spans {l : MapLeaf} {pa : Nat} {earlier : List Krepi.Spec.Fdt.Span}
    (hpa : l.pa.toNat = pa) (hstart : ∀ e ∈ earlier, e.start.toNat ≤ pa) :
    earlier.any (fun e => l.meets e.start.toNat e.endNat) = decide (pa < reachSpans earlier) := by
  have hsz : 0 < l.form.size := by cases l.form <;> decide
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq, lt_reachSpans_iff]
  simp only [MapLeaf.meets, hpa, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨e, he, -, h⟩; exact ⟨e, he, h⟩
  · rintro ⟨e, he, h⟩; exact ⟨e, he, by have := hstart e he; omega, h⟩

/-! ## The checks of the leaves of a range -/

/-- The fold of the free-slot checks over the leaves of a usable range that
ends at `stop`, from `pa` with `fuel`, after the leaves `acc` that passed. -/
def checkLeavesFrom (s : Tables .upper N) (base : UInt64) (taken : MapLeaf → Bool)
    (stop fuel pa : Nat) (acc : List (MapLeaf × Place)) :
    Except TableError (List (MapLeaf × Place)) :=
  (directLeaves stop fuel pa).foldlM (s.checkLeaf base taken) acc

theorem checkLeavesFrom_stop (s : Tables .upper N) (base : UInt64) (taken : MapLeaf → Bool)
    {stop pa : Nat} (fuel : Nat) (acc : List (MapLeaf × Place)) (h : stop ≤ pa) :
    checkLeavesFrom s base taken stop fuel pa acc = .ok acc := by
  simp only [checkLeavesFrom, directLeaves_stop fuel h, List.foldlM_nil]; rfl

theorem checkLeavesFrom_succ (s : Tables .upper N) (base : UInt64) (taken : MapLeaf → Bool)
    (stop fuel : Nat) {pa : Nat} (acc : List (MapLeaf × Place)) (h : pa < stop) :
    checkLeavesFrom s base taken stop (fuel + 1) pa acc =
      (checkPlace s base (directLeaf stop pa) (taken (directLeaf stop pa))).bind
        (fun p => checkLeavesFrom s base taken stop fuel (pa + (directLeaf stop pa).form.size)
          ((directLeaf stop pa, p) :: acc)) := by
  simp only [checkLeavesFrom, directLeaves_succ stop fuel h, List.foldlM_cons, checkLeaf_eq]
  cases checkPlace s base (directLeaf stop pa) (taken (directLeaf stop pa)) <;> rfl

/-- The checks of the leaves that pass put at most `fuel` leaves before those
that passed. -/
theorem checkLeavesFrom_length (s : Tables .upper N) (base : UInt64) (taken : MapLeaf → Bool)
    (stop : Nat) : ∀ (fuel pa : Nat) (acc acc' : List (MapLeaf × Place)),
      checkLeavesFrom s base taken stop fuel pa acc = .ok acc' → acc'.length ≤ acc.length + fuel
  | 0, pa, acc, acc', h => by
    simp only [checkLeavesFrom, directLeaves, List.foldlM_nil] at h; cases h; omega
  | fuel + 1, pa, acc, acc', h => by
    by_cases hp : pa < stop
    · rw [checkLeavesFrom_succ s base taken stop fuel acc hp] at h
      cases hc : checkPlace s base (directLeaf stop pa) (taken (directLeaf stop pa)) with
      | error x => rw [hc] at h; cases h
      | ok p =>
        rw [hc] at h
        have := checkLeavesFrom_length s base taken stop fuel _ _ acc' h
        rw [List.length_cons] at this; omega
    · rw [checkLeavesFrom_stop s base taken _ acc (Nat.le_of_not_lt hp)] at h
      cases h; omega

/-! ## The checks of one usable range -/

/-- Whether a leaf of a usable range is not free for `direct_map`: an
earlier range shares an address with it. -/
def usableTaken (earlier : List Krepi.Spec.Fdt.Span) (l : MapLeaf) : Bool :=
  earlier.any (fun e => l.meets e.start.toNat e.endNat)

/-- `Tables.checkUsableRange` as nested conditions. -/
theorem checkUsableRange_eq (s : Tables .upper N) (base : UInt64) (bits : UInt8)
    (earlier : List Krepi.Spec.Fdt.Span) (leaves : List (MapLeaf × Place))
    (u : Krepi.Spec.Fdt.Span) :
    s.checkUsableRange base bits (earlier, leaves) u =
      if u.start.toNat % PAGE_SIZE ≠ 0 ∨ u.endNat % PAGE_SIZE ≠ 0 then .error .alignment
      else if VA_LIMIT < u.endNat ∨ 2 ^ bits.toNat < u.endNat then .error .addressWidth
      else
        (checkLeavesFrom s base (usableTaken earlier) u.endNat
          (directFuel (u.endNat - u.start.toNat)) u.start.toNat leaves).map
          (fun ls => (earlier ++ [u], ls)) := by
  simp only [Tables.checkUsableRange, checkLeavesFrom]
  by_cases h1 : u.start.toNat % PAGE_SIZE ≠ 0 ∨ u.endNat % PAGE_SIZE ≠ 0
  · have h1' : (u.start.toNat % PAGE_SIZE != 0 || u.endNat % PAGE_SIZE != 0) = true := by
      simpa [bne_iff_ne] using h1
    simp only [h1', h1, ↓reduceIte]; rfl
  · have h1' : (u.start.toNat % PAGE_SIZE != 0 || u.endNat % PAGE_SIZE != 0) = false := by
      simpa [bne_iff_ne] using h1
    simp only [h1', h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : VA_LIMIT < u.endNat ∨ 2 ^ bits.toNat < u.endNat
    · have h2' : (decide (VA_LIMIT < u.endNat) || decide (2 ^ bits.toNat < u.endNat)) = true := by
        simpa using h2
      simp only [h2', h2, ↓reduceIte]; rfl
    · have h2' : (decide (VA_LIMIT < u.endNat) || decide (2 ^ bits.toNat < u.endNat)) = false := by
        simpa using h2
      simp only [h2', h2, Bool.false_eq_true, ↓reduceIte]
      rw [show ∀ x : Except TableError (List (MapLeaf × Place)),
          Except.map (fun ls => (earlier ++ [u], ls)) x =
            (do let y ← x; pure (earlier ++ [u], y)) from fun x => by cases x <;> rfl]
      rfl

private theorem room_of_fuel {a b len : Nat} (hl : b ≤ a + (len / 2097152 + 2 * (512 - 1)))
    (he : len ≤ 549755813888) : b ≤ a + 524288 := by
  have h1 : len / 2097152 ≤ 262144 := Nat.le_trans (Nat.div_le_div_right (c := 2097152) he) (by decide)
  have h2 : len / 2097152 + 2 * (512 - 1) ≤ 524288 := by omega
  exact Nat.le_trans hl (Nat.add_le_add_left h2 a)

/-- The checks of one usable range that pass: the range is put after the
ranges before, and at most `2 ^ 19` leaves, the leaves of a range below
`2 ^ 39`, before the leaves that passed. -/
theorem checkUsableRange_passed {s : Tables .upper N} {base : UInt64} {bits : UInt8}
    {earlier earlier' : List Krepi.Spec.Fdt.Span} {leaves leaves' : List (MapLeaf × Place)}
    {u : Krepi.Spec.Fdt.Span}
    (h : s.checkUsableRange base bits (earlier, leaves) u = .ok (earlier', leaves')) :
    earlier' = earlier ++ [u] ∧ leaves'.length ≤ leaves.length + 2 ^ 19 := by
  rw [checkUsableRange_eq] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i h2
      cases hc : checkLeavesFrom s base (usableTaken earlier) u.endNat
          (directFuel (u.endNat - u.start.toNat)) u.start.toNat leaves with
      | error x => rw [hc] at h; cases h
      | ok ls =>
        rw [hc] at h
        simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, ?_⟩
        have hl := checkLeavesFrom_length s base _ _ _ _ leaves ls hc
        have he : u.endNat ≤ 549755813888 := by
          simp only [not_or, Nat.not_lt, VA_LIMIT, Nat.reducePow] at h2; exact h2.1
        simp only [directFuel, BLOCK_SIZE, ENTRIES] at hl
        rw [show (2 : Nat) ^ 19 = 524288 from rfl]
        exact room_of_fuel hl (Nat.le_trans (Nat.sub_le _ _) he)

/-! ## `Tables.directMap` step by step -/

theorem directMap_pool_error {s : Tables .upper N} {P : Krepi.Spec.Fdt.MemoryPlan} {base : UInt64}
    {bits : UInt8} {x : TableError} (h : checkPool N base bits = .error x) :
    s.directMap P base bits = .error x := by
  simp only [Tables.directMap, h, bind, Except.bind]

theorem directMap_fold_error {s : Tables .upper N} {P : Krepi.Spec.Fdt.MemoryPlan} {base : UInt64}
    {bits : UInt8} {x : TableError} (hp : checkPool N base bits = .ok ())
    (h : (sortByKey (·.start.toNat) P.availableRanges).foldlM
      (s.checkUsableRange base bits) ([], []) = .error x) :
    s.directMap P base bits = .error x := by
  simp only [Tables.directMap, hp, h, bind, Except.bind]

/-- `Tables.directMap` after its checks pass: the write phase of the leaves
that passed, with the next free index of `allocOf`. -/
theorem directMap_fold_ok {s : Tables .upper N} {P : Krepi.Spec.Fdt.MemoryPlan} {base : UInt64}
    {bits : UInt8} {earlier : List Krepi.Spec.Fdt.Span} {leaves : List (MapLeaf × Place)}
    (hp : checkPool N base bits = .ok ())
    (h : (sortByKey (·.start.toNat) P.availableRanges).foldlM
      (s.checkUsableRange base bits) ([], []) = .ok (earlier, leaves)) :
    s.directMap P base bits =
      if N - s.used < (allocOf s.used leaves).next - s.used then .error .outOfTables
      else .ok ({ s with used := (allocOf s.used leaves).next },
        mapPlan base (allocOf s.used leaves).placed.reverse) := by
  simp only [Tables.directMap, hp, h, bind, Except.bind, Tables.mapLeaves, assignTables, allocOf]
  by_cases hc : N - s.used <
      (List.foldl Alloc.add ⟨s.used, none, none, []⟩ leaves.reverse).next - s.used
  · simp only [hc, ↓reduceIte]; rfl
  · simp only [hc, ↓reduceIte]; rfl

/-! ## The leaf search of the direct map -/

/-- The leaf of the code at `pa` of a usable range that ends at `stop`, on
numbers (`leaf_at`): the leaf of `directLeaf`, with its physical address,
its descriptor and its form. -/
def leafAtFound (stop pa : Nat) : Found :=
  ⟨pa, (directLeaf stop pa).desc, decide (pa % BLOCK_SIZE = 0 ∧ pa + BLOCK_SIZE ≤ stop)⟩

/-- The first leaf at or above `pa` of a usable range that ends at `stop`, a
page when `pages` (`range_leaf`): the leaf at `pa`, or for a block when
pages are asked, the page at the last multiple of 2 MiB at or below `stop`,
none when that is `stop`. -/
def rangeFind (stop pa : Nat) (pages : Bool) : Option Found :=
  if (leafAtFound stop pa).block && pages then
    if stop / BLOCK_SIZE * BLOCK_SIZE < stop then
      some (leafAtFound stop (stop / BLOCK_SIZE * BLOCK_SIZE))
    else none
  else some (leafAtFound stop pa)

/-- The leaf search of the plan of `direct_map` over the usable ranges in
address order, each by its start and end, as `usable_leaf` finds it: in the
first range that ends above `frm`, the leaf of `rangeFind` at the larger of
`frm` and its start, when it lies below `limit`; a range where `rangeFind`
finds none moves `frm` to its end. -/
def usableFind : List (Nat × Nat) → Nat → Nat → Bool → Option Found
  | [], _, _, _ => none
  | (start, stop) :: rest, frm, limit, pages =>
    if frm < stop then
      match rangeFind stop (max start frm) pages with
      | some l => if l.pa < limit then some l else none
      | none => usableFind rest stop limit pages
    else usableFind rest frm limit pages

theorem usableFind_nil (frm limit : Nat) (pages : Bool) : usableFind [] frm limit pages = none :=
  rfl

theorem usableFind_cons_ge {start stop frm limit : Nat} {pages : Bool} {rest : List (Nat × Nat)}
    (h : ¬ frm < stop) :
    usableFind ((start, stop) :: rest) frm limit pages = usableFind rest frm limit pages := by
  simp only [usableFind, h, ↓reduceIte]

theorem usableFind_cons_lt {start stop frm limit : Nat} {pages : Bool} {rest : List (Nat × Nat)}
    (h : frm < stop) :
    usableFind ((start, stop) :: rest) frm limit pages =
      match rangeFind stop (max start frm) pages with
      | some l => if l.pa < limit then some l else none
      | none => usableFind rest stop limit pages := by
  simp only [usableFind, h, ↓reduceIte]

/-- Ranges that end at or below `frm` do not change the search from `frm`. -/
theorem usableFind_skip {frm limit : Nat} {pages : Bool} :
    ∀ (skipped rest : List (Nat × Nat)), (∀ r ∈ skipped, r.2 ≤ frm) →
      usableFind (skipped ++ rest) frm limit pages = usableFind rest frm limit pages
  | [], rest, _ => rfl
  | (a, b) :: skipped, rest, h => by
    rw [List.cons_append, usableFind_cons_ge (Nat.not_lt.2 (h (a, b) List.mem_cons_self))]
    exact usableFind_skip skipped rest (fun r hr => h r (List.mem_cons_of_mem _ hr))

/-- A span of the specification as the start and the end of `usableFind`. -/
def spanView (u : Krepi.Spec.Fdt.Span) : Nat × Nat := (u.start.toNat, u.endNat)

/-- `rangeFind` without the page filter finds the leaf at the address. -/
theorem rangeFind_false (stop pa : Nat) : rangeFind stop pa false = some (leafAtFound stop pa) := by
  simp only [rangeFind, Bool.and_false, Bool.false_eq_true, ↓reduceIte]

/-- The leaf that `rangeFind` finds lies at or above the address, below the
end, for an address below the end. -/
theorem rangeFind_bounds {stop pa : Nat} {pages : Bool} {f : Found} (h : pa < stop)
    (hf : rangeFind stop pa pages = some f) : pa ≤ f.pa ∧ f.pa < stop := by
  unfold rangeFind at hf
  split at hf
  · rename_i hb
    split at hf
    · rename_i hlt
      simp only [Option.some.injEq] at hf
      subst hf
      simp only [leafAtFound, Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
      obtain ⟨⟨h1, h2⟩, -⟩ := hb
      simp only [BLOCK_SIZE] at h1 h2 hlt ⊢
      omega
    · cases hf
  · simp only [Option.some.injEq] at hf
    subst hf
    exact ⟨Nat.le_refl _, h⟩

/-- The leaf that `usableFind` finds lies at or above the address, below the
limit, and below every bound of the ends of ranges that are nonempty or end
at 0. -/
theorem usableFind_bounds {limit B : Nat} {pages : Bool} :
    ∀ (L : List (Nat × Nat)) (frm : Nat) (f : Found), usableFind L frm limit pages = some f →
      (∀ r ∈ L, (r.1 < r.2 ∨ r.2 = 0) ∧ r.2 ≤ B) → frm ≤ f.pa ∧ f.pa < limit ∧ f.pa < B
  | [], _, _, h, _ => by cases h
  | (a, b) :: rest, frm, f, h, hB => by
    by_cases hlt : frm < b
    · rw [usableFind_cons_lt hlt] at h
      cases hr : rangeFind b (max a frm) pages with
      | none =>
        rw [hr] at h
        have := usableFind_bounds rest b f h (fun r hr => hB r (List.mem_cons_of_mem _ hr))
        exact ⟨by omega, this.2⟩
      | some l =>
        rw [hr] at h
        simp only at h
        split at h
        · rename_i hl
          simp only [Option.some.injEq] at h
          subst h
          have hb := hB (a, b) List.mem_cons_self
          simp only at hb
          have hm1 := Nat.le_max_right a frm
          have hm2 : max a frm < b := by
            rcases Nat.lt_or_ge a frm with h1 | h1
            · rw [Nat.max_eq_right (Nat.le_of_lt h1)]; exact hlt
            · rw [Nat.max_eq_left h1]; omega
          have := rangeFind_bounds hm2 hr
          exact ⟨by omega, hl, by omega⟩
        · cases h
    · rw [usableFind_cons_ge hlt] at h
      exact usableFind_bounds rest frm f h (fun r hr => hB r (List.mem_cons_of_mem _ hr))

/-! ## The cursor and the state of the search -/

/-- A step of the cursor whose search asks for pages, under a new level 2
table, keeps its 1 GiB slot. -/
theorem cur_take_gib (place : Found → Place) (base : UInt64) (c : Cur) (f : Option Found)
    (h : c.search.2.2 = true) : (c.take place base f).2.gib = c.gib := by
  unfold Cur.search at h
  unfold Cur.take
  cases hp : c.phase <;> simp only [hp, Bool.false_eq_true] at h ⊢
  cases f with
  | none => rfl
  | some p =>
    simp only [Cur.children]
    split <;> rfl

/-- `Cur.leaf` asks for no step yet only for a leaf found, from which the
search of the children starts. -/
theorem cur_leaf_seek (place : Found → Place) (c : Cur) (f : Option Found)
    (h : (c.leaf place f).1 = .seek) :
    ∃ l, f = some l ∧ (c.leaf place f).2.frm = l.pa ∧ (c.leaf place f).2.phase = .children := by
  cases f with
  | none => simp [Cur.leaf] at h
  | some l =>
    refine ⟨l, rfl, ?_⟩
    simp only [Cur.leaf] at h ⊢
    cases hp : place l with
    | root =>
      simp only [hp] at h ⊢
      cases hb : l.block
      · simp [hb] at h
      · simp only [↓reduceIte, and_self]
    | level2 t2 =>
      simp only [hp] at h
      cases hb : l.block <;> simp [hb] at h
    | level3 t2 t3 => simp [hp] at h

/-- `Cur.take` asks for no step yet only for a leaf found, from which the
search of the children starts. -/
theorem cur_take_seek (place : Found → Place) (base : UInt64) (c : Cur) (f : Option Found)
    (h : (c.take place base f).1 = .seek) :
    ∃ l, f = some l ∧ (c.take place base f).2.frm = l.pa ∧
      (c.take place base f).2.phase = .children := by
  unfold Cur.take at h ⊢
  cases hp : c.phase <;> simp only [hp] at h ⊢
  · exact cur_leaf_seek place c f h
  · cases f with
    | none => exact cur_leaf_seek place _ none h
    | some p =>
      simp only [Cur.heldPage] at h ⊢
      split at h
      · cases h
      · rename_i hs
        simp only [hs, ↓reduceIte]
        exact cur_leaf_seek place _ (some p) h
  all_goals simp at h

/-- Every search of the cursor starts at its address `frm`. -/
theorem cur_search_frm (c : Cur) : c.search.1 = c.frm := by
  unfold Cur.search; cases c.phase <;> rfl

/-! ## The start of the search and the ranges of a success -/

/-- The empty range at 0 does not change the search. -/
theorem usableFind_zero_cons (Us : List (Nat × Nat)) (frm limit : Nat) (pages : Bool) :
    usableFind ((0, 0) :: Us) frm limit pages = usableFind Us frm limit pages :=
  usableFind_cons_ge (Nat.not_lt_zero _)

/-- The checks of the usable ranges that pass pass each range at its end at
or below `2 ^ 39`. -/
theorem fold_checkUsableRange_low {s : Tables .upper N} {base : UInt64} {bits : UInt8} :
    ∀ (us : List Krepi.Spec.Fdt.Span) (acc acc' : List Krepi.Spec.Fdt.Span × List (MapLeaf × Place)),
      us.foldlM (s.checkUsableRange base bits) acc = .ok acc' → ∀ u ∈ us, u.endNat ≤ 2 ^ 39
  | [], _, _, _, u, hu => absurd hu List.not_mem_nil
  | v :: us, acc, acc', h, u, hu => by
    rw [List.foldlM_cons] at h
    obtain ⟨earlier, leaves⟩ := acc
    cases hv : s.checkUsableRange base bits (earlier, leaves) v with
    | error x => rw [hv] at h; cases h
    | ok y =>
      rw [hv] at h
      rcases List.mem_cons.1 hu with rfl | hu
      · rw [checkUsableRange_eq] at hv
        split at hv
        · cases hv
        · split at hv
          · cases hv
          · rename_i h2
            simp only [not_or, Nat.not_lt, VA_LIMIT] at h2
            exact h2.1
      · exact fold_checkUsableRange_low us y acc' h u hu

/-- A success of `Tables.directMap` on a well-formed boot memory map passed
every usable range, each ending at or below `2 ^ 39`. -/
theorem directMap_ok_low {s : Tables .upper N} {P : Krepi.Spec.Fdt.MemoryPlan} {base : UInt64}
    {bits : UInt8} {x : Tables .upper N × Plan} (hw : P.WellFormed)
    (h : s.directMap P base bits = .ok x) : ∀ u ∈ P.availableRanges, u.endNat ≤ 2 ^ 39 := by
  unfold Tables.directMap at h
  cases hp : checkPool N base bits with
  | error e => rw [hp] at h; cases h
  | ok u =>
    rw [hp] at h
    simp only [bind, Except.bind] at h
    rw [usable_sorted hw] at h
    cases hf : P.availableRanges.foldlM (s.checkUsableRange base bits) ([], []) with
    | error e => rw [hf] at h; cases h
    | ok y => exact fold_checkUsableRange_low _ _ _ hf

end Krepi.Proofs.PageTables.Refinement
