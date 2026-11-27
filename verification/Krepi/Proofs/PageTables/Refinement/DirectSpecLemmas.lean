module

public import Krepi.Proofs.PageTables.Refinement.LayoutSpecLemmas
public import Krepi.Spec.PageTables.Witnesses.TableSets
public import Krepi.Proofs.Fdt.Plan
public import Krepi.Proofs.Fdt.PlanLemmas
import Mathlib.Util.CountHeartbeats

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
  elsewhere), `directLeaf_size`, `directLeaves_succ`, `directLeaves_stop`,
  and the fuel: `leafFuel` (an upper bound on the leaves left from an
  address), `leafFuel_step` (one leaf uses one), `leafFuel_start` (the fuel
  `directFuel` of the specification covers a range).
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
  address do not change the search).
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

end Krepi.Proofs.PageTables.Refinement
