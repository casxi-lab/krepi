module

public import Krepi.Proofs.PageTables.Refinement.LayoutSpecLemmas
public import Krepi.Spec.PageTables.Witnesses.TableSets
public import Krepi.Proofs.Fdt.Plan
public import Krepi.Proofs.Fdt.PlanLemmas
public import Krepi.Proofs.PageTables.MapCheckLemmas
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
- The leaf search as the first leaf at or above an address: `foundOfLeaf`,
  `firstFound`, `LeafStart`, `foundOfLeaf_directLeaf`, `leafFuel_pos`,
  `find_blocks`, `find_directLeaves`, `directLeaves_bounds`, `find?_congr`
  and `usableFind_eq_firstFound` (`usableFind` of the usable ranges is the
  first leaf at or above the address of `usableLeaves` of the ranges, from an
  address where a leaf starts), and `usable_ranges_ok` (the usable ranges of
  a well-formed map are as it takes them).
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

/-! ## The leaf search as the first leaf at or above an address -/

/-- A leaf of a map as the leaf that a search of the code finds: its
physical address, its descriptor and whether it is a block. -/
def foundOfLeaf (x : MapLeaf) : Found := ⟨x.pa.toNat, x.desc, decide (x.form = .block)⟩

/-- The first of leaves in address order at or above `frm`, a page when
`pages`, when it lies below `limit`: what the leaf search of a map plan gives
for the leaves of the map. -/
def firstFound (ls : List Found) (frm limit : Nat) (pages : Bool) : Option Found :=
  match ls.find? (fun l => decide (frm ≤ l.pa) && (!pages || !l.block)) with
  | some l => if l.pa < limit then some l else none
  | none => none

/-- `x` is where a leaf of the walk of a usable range from `pa` to `e` can
start: a page boundary that no block of the walk holds strictly inside. -/
def LeafStart (pa e x : Nat) : Prop :=
  x % PAGE_SIZE = 0 ∧
    (x % BLOCK_SIZE = 0 ∨ x / BLOCK_SIZE * BLOCK_SIZE < pa ∨ e < x / BLOCK_SIZE * BLOCK_SIZE + BLOCK_SIZE)

/-- The leaf of `directLeaf` as found is `leafAtFound`. -/
theorem foundOfLeaf_directLeaf {e pa : Nat} (h : pa < 2 ^ 64) :
    foundOfLeaf (directLeaf e pa) = leafAtFound e pa := by
  simp only [foundOfLeaf, leafAtFound, directLeaf_pa, UInt64.toNat_ofNat_of_lt' h, directLeaf_form]
  split <;> simp_all

/-- An address below the end has fuel left. -/
theorem leafFuel_pos {e pa : Nat} (hpa : pa % PAGE_SIZE = 0) (hs : e % PAGE_SIZE = 0) (h : pa < e) :
    1 ≤ leafFuel e pa := by
  have := leafFuel_leaf hpa hs h; omega

/-- The walk of a usable range from a multiple of 2 MiB: its first page at
or above an address at or below the start is at the last multiple of 2 MiB
at or below the end, none when that is the end. -/
theorem find_blocks {e frm : Nat} (hs : e % PAGE_SIZE = 0) (he : e < 2 ^ 64) :
    ∀ (fuel y : Nat), y % BLOCK_SIZE = 0 → y ≤ e → leafFuel e y ≤ fuel → frm ≤ y →
      ((directLeaves e fuel y).map foundOfLeaf).find?
          (fun l => decide (frm ≤ l.pa) && !l.block) =
        if e / BLOCK_SIZE * BLOCK_SIZE < e then some (leafAtFound e (e / BLOCK_SIZE * BLOCK_SIZE))
        else none
  | 0, y, hy, hye, hf, hfy => by
    by_cases hlt : y < e
    · have := leafFuel_pos (by simp only [PAGE_SIZE, BLOCK_SIZE] at hy ⊢; omega) hs hlt; omega
    · have hyl : y = e := by omega
      subst hyl
      have : ¬ y / BLOCK_SIZE * BLOCK_SIZE < y := by simp only [BLOCK_SIZE] at hy ⊢; omega
      simp only [directLeaves, List.map_nil, List.find?_nil, this, ↓reduceIte]
  | fuel + 1, y, hy, hye, hf, hfy => by
    by_cases hlt : y < e
    · rw [directLeaves_succ e fuel hlt, List.map_cons, List.find?_cons]
      have hyP : y % PAGE_SIZE = 0 := by simp only [PAGE_SIZE, BLOCK_SIZE] at hy ⊢; omega
      by_cases hb : y + BLOCK_SIZE ≤ e
      · have hc : y % BLOCK_SIZE = 0 ∧ y + BLOCK_SIZE ≤ e := ⟨hy, hb⟩
        have hblk : (foundOfLeaf (directLeaf e y)).block = true := by
          rw [foundOfLeaf_directLeaf (by omega)]; simp only [leafAtFound, decide_eq_true_eq]; exact hc
        simp only [hblk, Bool.not_true, Bool.and_false]
        have hstep := leafFuel_leaf hyP hs hlt
        rw [directLeaf_size] at hstep ⊢
        simp only [hc, and_self, ↓reduceIte] at hstep ⊢
        exact find_blocks hs he fuel (y + BLOCK_SIZE) (by simp only [BLOCK_SIZE] at hy ⊢; omega)
          hb (by omega) (by omega)
      · have hL : e / BLOCK_SIZE * BLOCK_SIZE = y := by simp only [BLOCK_SIZE] at hy hb ⊢; omega
        have hc : ¬ (y % BLOCK_SIZE = 0 ∧ y + BLOCK_SIZE ≤ e) := fun h => hb h.2
        have hpg : (foundOfLeaf (directLeaf e y)).block = false := by
          rw [foundOfLeaf_directLeaf (by omega)]; simp only [leafAtFound, decide_eq_false_iff_not]
          exact hc
        have hpa : (foundOfLeaf (directLeaf e y)).pa = y := by
          rw [foundOfLeaf_directLeaf (by omega)]; rfl
        simp only [hpg, hpa, Bool.not_false, Bool.and_true, decide_eq_true hfy, hL, hlt, ↓reduceIte]
        rw [foundOfLeaf_directLeaf (by omega)]
    · have hyl : y = e := by omega
      subst hyl
      have : ¬ y / BLOCK_SIZE * BLOCK_SIZE < y := by simp only [BLOCK_SIZE] at hy ⊢; omega
      simp only [directLeaves_stop _ (Nat.le_refl y), List.map_nil, List.find?_nil, this, ↓reduceIte]

/-- The first leaf at or above `frm`, a page when `pages`, of the walk of a
usable range from `pa` with enough fuel is the leaf of `rangeFind` at `x`,
for `x` where a leaf of the walk starts, which is `frm` or, when `frm` lies
at or below `pa`, `pa` itself. -/
theorem find_directLeaves {e frm : Nat} {pages : Bool} (hs : e % PAGE_SIZE = 0) (he : e < 2 ^ 64) :
    ∀ (fuel pa x : Nat), pa % PAGE_SIZE = 0 → leafFuel e pa ≤ fuel → pa ≤ x → x < e →
      LeafStart pa e x → (x = frm ∨ (x = pa ∧ frm ≤ pa)) →
      ((directLeaves e fuel pa).map foundOfLeaf).find?
          (fun l => decide (frm ≤ l.pa) && (!pages || !l.block)) = rangeFind e x pages
  | 0, pa, x, hpa, hf, hpx, hxe, hls, hfx => by
    have := leafFuel_pos hpa hs (show pa < e by omega); omega
  | fuel + 1, pa, x, hpa, hf, hpx, hxe, hls, hfx => by
    have hlt : pa < e := by omega
    rw [directLeaves_succ e fuel hlt, List.map_cons, List.find?_cons]
    have hstep := leafFuel_leaf hpa hs hlt
    rw [foundOfLeaf_directLeaf (by omega)]
    by_cases hxp : x = pa
    · subst hxp
      have hfrm : frm ≤ x := by rcases hfx with h | h <;> omega
      have hpx' : (leafAtFound e x).pa = x := rfl
      by_cases hc : x % BLOCK_SIZE = 0 ∧ x + BLOCK_SIZE ≤ e
      · have hblk : (leafAtFound e x).block = true := by
          simp only [leafAtFound, decide_eq_true_eq]; exact hc
        cases pages
        · simp only [hpx', hfrm, decide_true, Bool.not_false, Bool.true_or, Bool.and_self,
            rangeFind_false]
        · simp only [hpx', hblk, Bool.not_true, Bool.false_or, Bool.and_false, rangeFind,
            Bool.and_self, ↓reduceIte]
          rw [directLeaf_size] at hstep ⊢
          simp only [hc, and_self, ↓reduceIte] at hstep ⊢
          exact find_blocks hs he fuel (x + BLOCK_SIZE) (by simp only [BLOCK_SIZE] at hc ⊢; omega)
            hc.2 (by omega) (by simp only [BLOCK_SIZE]; omega)
      · have hpg : (leafAtFound e x).block = false := by
          simp only [leafAtFound, decide_eq_false_iff_not]; exact hc
        simp only [hpx', hpg, hfrm, decide_true, Bool.not_false, Bool.or_true, Bool.and_self,
          rangeFind, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    · have hxf : x = frm := by rcases hfx with h | h; exact h; exact absurd h.1 hxp
      have hpa' : (leafAtFound e pa).pa = pa := rfl
      have hnf : ¬ frm ≤ pa := by omega
      simp only [hpa', hnf, decide_false, Bool.false_and]
      have hsz := directLeaf_size e pa
      simp only [LeafStart, PAGE_SIZE, BLOCK_SIZE] at hls hpa hs
      by_cases hc : pa % BLOCK_SIZE = 0 ∧ pa + BLOCK_SIZE ≤ e
      · simp only [hc, and_self, ↓reduceIte] at hsz
        rw [hsz] at hstep ⊢
        simp only [BLOCK_SIZE] at hc hsz hstep ⊢
        exact find_directLeaves hs he fuel (pa + 2097152) x (by simp only [PAGE_SIZE]; omega)
          (by omega) (by omega) hxe (by simp only [LeafStart, PAGE_SIZE, BLOCK_SIZE]; omega)
          (Or.inl hxf)
      · simp only [hc, ↓reduceIte] at hsz
        rw [hsz] at hstep ⊢
        simp only [BLOCK_SIZE, PAGE_SIZE] at hc hsz hstep ⊢
        exact find_directLeaves hs he fuel (pa + 4096) x (by simp only [PAGE_SIZE]; omega)
          (by omega) (by omega) hxe (by simp only [LeafStart, PAGE_SIZE, BLOCK_SIZE]; omega)
          (Or.inl hxf)

/-- The leaves of the walk from `pa` to `e` lie at or above `pa`, below `e`. -/
theorem directLeaves_bounds {e : Nat} (he : e < 2 ^ 64) :
    ∀ (fuel pa : Nat), ∀ y ∈ directLeaves e fuel pa,
      pa ≤ (foundOfLeaf y).pa ∧ (foundOfLeaf y).pa < e
  | 0, _, y, hy => by simp [directLeaves] at hy
  | fuel + 1, pa, y, hy => by
    by_cases hlt : pa < e
    · rw [directLeaves_succ e fuel hlt] at hy
      rcases List.mem_cons.1 hy with rfl | hy
      · rw [foundOfLeaf_directLeaf (by omega)]; exact ⟨Nat.le_refl _, hlt⟩
      · have := directLeaves_bounds he fuel _ y hy
        exact ⟨by omega, this.2⟩
    · rw [directLeaves_stop _ (by omega)] at hy; exact absurd hy List.not_mem_nil

/-- `List.find?` reads its predicate on the elements of the list alone. -/
theorem find?_congr {α : Type} {p q : α → Bool} : ∀ (l : List α), (∀ x ∈ l, p x = q x) →
    l.find? p = l.find? q
  | [], _ => rfl
  | a :: l, h => by
    rw [List.find?_cons, List.find?_cons, h a List.mem_cons_self,
      find?_congr l (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- **The leaf search of the direct map is the first leaf at or above the
address.** For usable ranges nonempty, on pages, within 64 bits and apart in
address order, and an address where a leaf starts in the range that holds
it, `usableFind` of the ranges is `firstFound` of the leaves of the direct
map of the ranges in order, `usableLeaves`. -/
theorem usableFind_eq_firstFound {limit : Nat} {pages : Bool} :
    ∀ (Us : List Krepi.Spec.Fdt.Span) (frm : Nat),
      (∀ u ∈ Us, u.start.toNat < u.endNat ∧ u.start.toNat % PAGE_SIZE = 0 ∧
        u.endNat % PAGE_SIZE = 0 ∧ u.endNat < 2 ^ 64) →
      Us.Pairwise (fun a b => a.endNat ≤ b.start.toNat) →
      (∀ u ∈ Us, u.start.toNat < frm → frm < u.endNat → LeafStart u.start.toNat u.endNat frm) →
      usableFind (Us.map spanView) frm limit pages =
        firstFound ((Us.flatMap usableLeaves).map foundOfLeaf) frm limit pages
  | [], frm, _, _, _ => by simp [usableFind, firstFound]
  | u :: rest, frm, hok, hpw, hls => by
    obtain ⟨hse, hs4, he4, he64⟩ := hok u List.mem_cons_self
    rw [List.pairwise_cons] at hpw
    have hokr : ∀ v ∈ rest, v.start.toNat < v.endNat ∧ v.start.toNat % PAGE_SIZE = 0 ∧
        v.endNat % PAGE_SIZE = 0 ∧ v.endNat < 2 ^ 64 := fun v hv => hok v (List.mem_cons_of_mem _ hv)
    have hB : ∀ l ∈ (rest.flatMap usableLeaves).map foundOfLeaf, u.endNat ≤ l.pa := by
      intro l hl
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
      obtain ⟨v, hv, hyv⟩ := List.mem_flatMap.1 hy
      have := (directLeaves_bounds (hokr v hv).2.2.2 _ _ y hyv).1
      exact Nat.le_trans (hpw.1 v hv) this
    simp only [List.map_cons, List.flatMap_cons, List.map_append, firstFound, List.find?_append]
    have hview : spanView u = (u.start.toNat, u.endNat) := rfl
    rw [hview]
    by_cases hlt : frm < u.endNat
    · rw [usableFind_cons_lt hlt]
      have hA := find_directLeaves (frm := frm) (pages := pages) he4 he64
        (directFuel (u.endNat - u.start.toNat)) u.start.toNat (max u.start.toNat frm) hs4
        (leafFuel_start hs4 he4) (Nat.le_max_left _ _) (by omega)
        (by
          rcases Nat.lt_or_ge u.start.toNat frm with h | h
          · rw [Nat.max_eq_right (Nat.le_of_lt h)]; exact hls u List.mem_cons_self h hlt
          · rw [Nat.max_eq_left h]
            simp only [LeafStart, PAGE_SIZE, BLOCK_SIZE] at hs4 ⊢; omega)
        (by
          rcases Nat.lt_or_ge u.start.toNat frm with h | h
          · left; omega
          · right; omega)
      have hU : usableLeaves u = directLeaves u.endNat (directFuel (u.endNat - u.start.toNat))
          u.start.toNat := rfl
      rw [hU, hA]
      cases hr : rangeFind u.endNat (max u.start.toNat frm) pages with
      | some l => simp only [Option.some_or]
      | none =>
        simp only [Option.none_or]
        rw [usableFind_eq_firstFound rest u.endNat hokr hpw.2
          (fun v hv h1 _ => absurd h1 (Nat.not_lt.2 (hpw.1 v hv)))]
        simp only [firstFound]
        rw [find?_congr (p := fun (l : Found) => decide (frm ≤ l.pa) && (!pages || !l.block))
          (q := fun (l : Found) => decide (u.endNat ≤ l.pa) && (!pages || !l.block)) _
          (fun l hl => by
            have := hB l hl
            simp only [decide_eq_true (Nat.le_trans (Nat.le_of_lt hlt) this),
              decide_eq_true this])]
    · rw [usableFind_cons_ge hlt]
      have hnone : ((directLeaves u.endNat (directFuel (u.endNat - u.start.toNat))
          u.start.toNat).map foundOfLeaf).find?
            (fun l => decide (frm ≤ l.pa) && (!pages || !l.block)) = none := by
        rw [List.find?_eq_none]
        intro l hl
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
        have := (directLeaves_bounds he64 _ _ y hy).2
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
        intro h; omega
      have hU : usableLeaves u = directLeaves u.endNat (directFuel (u.endNat - u.start.toNat))
          u.start.toNat := rfl
      rw [hU, hnone, Option.none_or]
      rw [usableFind_eq_firstFound rest frm hokr hpw.2
        (fun v hv => hls v (List.mem_cons_of_mem _ hv))]
      simp only [firstFound]

/-- The usable ranges of a well-formed boot memory map are nonempty, on
pages and within 64 bits, as `usableFind_eq_firstFound` takes them. -/
theorem usable_ranges_ok {p : Krepi.Spec.Fdt.MemoryPlan} (hp : p.WellFormed) :
    ∀ u ∈ p.availableRanges, u.start.toNat < u.endNat ∧ u.start.toNat % PAGE_SIZE = 0 ∧
      u.endNat % PAGE_SIZE = 0 ∧ u.endNat < 2 ^ 64 := by
  obtain ⟨hne, -, -⟩ := usable_wf hp
  intro u hu
  obtain ⟨⟨-, hv⟩, h1, h2⟩ := hne u hu
  exact ⟨Krepi.Proofs.Fdt.nonempty_lt ⟨(hne u hu).1.1, hv⟩, h1, h2, hv⟩

end Krepi.Proofs.PageTables.Refinement
