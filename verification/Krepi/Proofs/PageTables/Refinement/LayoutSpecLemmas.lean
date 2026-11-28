module

public import Krepi.Proofs.PageTables.Refinement.CursorSpecLemmas
public import Krepi.Proofs.PageTables.ListLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: the checks of a layout, on the specification side

Lemmas about the checks of `Tables.kernelMap` (`Tables.checkLayoutRange`
and the fold of `Tables.checkLeaf` over the pages of a range), in the forms
that the triples of `boot::layout` need
(`Krepi.Proofs.PageTables.Refinement.LayoutLemmas`). The module imports no
generated definitions, so it is built once and not again for every mutant of
the code.

- The fold of `Alloc.add` over the leaves that passed, latest first:
  `allocOf`, `allocOf_nil`, `allocOf_cons`.
- The leaves of a layout: `pageLeaf` (the page of a kind at an address,
  mapped at it), `layoutPages_succ`, `layoutPages_length`, `sub_page_div`,
  `layout_room` (the bound on the count of new tables before a range).
- The ranges before: `reachOf` (the largest end of the ranges before, 0 for
  none), `reachOf_append`, and `any_meets_eq` (for ranges that start at or
  below a page, an earlier range shares an address with the page exactly
  when the page lies below `reachOf`).
- The guard pages: `isGuard_pageLeaf`.
- The fold of the checks of the pages: `layoutTaken` (the leaves that are
  not free), `checkPlace_congr`, `checkPages` (the fold that
  `checkLayoutRange` makes), `checkPages_zero`, `checkPages_succ`.
- The checks of one range as nested conditions: `checkLayoutRange_eq`;
  `checkPages_length` and `checkLayoutRange_ok` (what a success adds).
- The leaf search of the plan: `RangeView`, `layoutFind`,
  `layoutFind_cons_lt`, `layoutFind_cons_ge`, `layoutFind_nil`, `layoutFind_low`.
- `Tables.kernelMap` step by step: `checkPool_ok_facts`,
  `kernelMap_pool_error`, `kernelMap_fold_error`, `kernelMap_fold_ok`.
- Lists: `layout_listRel_getElem`.
- The insertion sort of the code: `insertAfter`, `insert_insertAfter`,
  `sortByKey_concat` (`sortByKey` of a list with one more element at its end
  is `insertAfter` of it), `insertAfter_append`, `insertAfter_of_le`,
  `set_swap`, `listRel_insert`, `listRel_sortByKey`.
-/

@[expose] public section

open Krepi.Spec.PageTables

namespace Krepi.Proofs.PageTables.Refinement

variable {r : Region} {N : Nat}

/-! ## The new tables of the leaves that passed -/

/-- The fold of `Alloc.add` over the leaves that passed, given latest first,
from the record `used`: what `assignTables` folds over them in address
order. -/
def allocOf (used : Nat) (acc : List (MapLeaf × Place)) : Alloc :=
  acc.reverse.foldl Alloc.add ⟨used, none, none, []⟩

theorem allocOf_nil (used : Nat) : allocOf used [] = ⟨used, none, none, []⟩ := rfl

theorem allocOf_cons (used : Nat) (x : MapLeaf × Place) (acc : List (MapLeaf × Place)) :
    allocOf used (x :: acc) = (allocOf used acc).add x := by
  simp only [allocOf, List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-! ## The leaves of a layout -/

/-- The page of kind `k` at the address `pa`, mapped at `pa`: a leaf of
`layoutPages`. -/
def pageLeaf (k : Kind) (pa : Nat) : MapLeaf :=
  ⟨UInt64.ofNat pa, UInt64.ofNat pa, descriptor k (UInt64.ofNat pa), .page⟩

theorem layoutPages_succ (k : Kind) (n pa : Nat) :
    layoutPages k (n + 1) pa = pageLeaf k pa :: layoutPages k n (pa + PAGE_SIZE) := rfl

/-- The bound on the count of new tables before a range of a layout of at
most 16 ranges, `n` leaves before it: at most `2 ^ 27` pages a range and two
new tables a page, below `2 ^ 33` with the pages of the range. -/
theorem layout_room {n m idx : Nat} (h1 : 2 ^ 33 ≤ m) (h2 : n ≤ idx * 2 ^ 27)
    (h3 : idx ≤ 15) : 2 * (n + 2 ^ 27) + 2 ≤ m := by
  have hn : n ≤ 15 * 2 ^ 27 := Nat.le_trans h2 (Nat.mul_le_mul_right _ h3)
  have hb : 2 * (n + 2 ^ 27) + 2 ≤ 2 ^ 33 :=
    Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hn _)) 2)
      (Nat.le_of_ble_eq_true rfl)
  exact Nat.le_trans hb h1

/-- One page fewer from one page further. -/
theorem sub_page_div {a b m : Nat} (h : (a - b) / 4096 = m + 1) : (a - (b + 4096)) / 4096 = m := by
  omega

theorem layoutPages_length (k : Kind) : ∀ n pa, (layoutPages k n pa).length = n
  | 0, _ => rfl
  | n + 1, pa => by rw [layoutPages_succ, List.length_cons, layoutPages_length k n]

/-! ## The ranges before -/

/-- The largest end of the ranges before, 0 for none: what the code keeps as
`reach`. -/
def reachOf (earlier : List PhysRange) : Nat :=
  earlier.foldl (fun m e => max m e.endNat) 0

private theorem foldl_max_init (l : List PhysRange) (a : Nat) :
    l.foldl (fun m e => max m e.endNat) a = max a (l.foldl (fun m e => max m e.endNat) 0) := by
  induction l generalizing a with
  | nil => simp
  | cons e l ih =>
    simp only [List.foldl_cons]
    rw [ih (max a e.endNat), ih (max 0 e.endNat)]
    omega

theorem reachOf_append (earlier : List PhysRange) (j : PhysRange) :
    reachOf (earlier ++ [j]) = max (reachOf earlier) j.endNat := by
  simp only [reachOf, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem lt_reachOf_iff (pa : Nat) :
    ∀ earlier : List PhysRange, pa < reachOf earlier ↔ ∃ e ∈ earlier, pa < e.endNat := by
  intro earlier
  induction earlier using List.reverseRecOn with
  | nil => simp [reachOf]
  | append_singleton l e ih =>
    rw [reachOf_append]
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · intro h
      rcases Nat.lt_or_ge pa (reachOf l) with h1 | h1
      · obtain ⟨e', he', h'⟩ := ih.1 h1; exact ⟨e', Or.inl he', h'⟩
      · exact ⟨e, Or.inr rfl, by omega⟩
    · rintro ⟨e', he' | rfl, h'⟩
      · have := ih.2 ⟨e', he', h'⟩; omega
      · omega

/-- For a page at `pa` and ranges that start at or below it, a range before
shares an address with the page exactly when the page lies below the largest
end of those ranges: the test of the code. -/
theorem any_meets_eq {l : MapLeaf} {pa : Nat} {earlier : List PhysRange}
    (hpa : l.pa.toNat = pa) (hf : l.form = .page)
    (hstart : ∀ e ∈ earlier, e.start.toNat ≤ pa) :
    earlier.any (fun e => l.meets e.start.toNat e.endNat) = decide (pa < reachOf earlier) := by
  rw [Bool.eq_iff_iff, List.any_eq_true, decide_eq_true_eq, lt_reachOf_iff]
  simp only [MapLeaf.meets, hpa, hf, Form.size, PAGE_SIZE, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨e, he, -, h⟩; exact ⟨e, he, h⟩
  · rintro ⟨e, he, h⟩; exact ⟨e, he, by have := hstart e he; omega, h⟩

/-! ## The guard pages -/

theorem isGuard_pageLeaf (guards : List UInt64) (k : Kind) (pa : Nat) (hpa : pa < 2 ^ 64) :
    (pageLeaf k pa).isGuard guards =
      guards.any (fun g => decide (pa ≤ g.toNat) && decide (g.toNat < pa + PAGE_SIZE)) := by
  simp only [MapLeaf.isGuard, pageLeaf, UInt64.toNat_ofNat_of_lt' hpa]

/-! ## The checks of the pages of a range -/

/-- Whether a leaf of a range is not free for `kernel_map`: an earlier range
shares an address with it, or it holds a guard address. -/
def layoutTaken (earlier : List PhysRange) (guards : List UInt64) (l : MapLeaf) : Bool :=
  earlier.any (fun e => l.meets e.start.toNat e.endNat) || l.isGuard guards

/-- `checkPlace` reads the place of a leaf alone. -/
theorem checkPlace_congr {s : Tables r N} {base : UInt64} {l l' : MapLeaf} (taken : Bool)
    (h : s.place base l = s.place base l') : checkPlace s base l taken = checkPlace s base l' taken := by
  simp only [checkPlace, h]


/-- The fold of the free-slot checks over the `n` pages of kind `k` from
`pa`, after the leaves `acc` that passed. -/
def checkPages (s : Tables r N) (base : UInt64) (taken : MapLeaf → Bool) (k : Kind) (n pa : Nat)
    (acc : List (MapLeaf × Place)) : Except TableError (List (MapLeaf × Place)) :=
  (layoutPages k n pa).foldlM (s.checkLeaf base taken) acc

theorem checkPages_zero (s : Tables r N) (base : UInt64) (taken : MapLeaf → Bool) (k : Kind)
    (pa : Nat) (acc : List (MapLeaf × Place)) : checkPages s base taken k 0 pa acc = .ok acc := rfl

theorem checkPages_succ (s : Tables r N) (base : UInt64) (taken : MapLeaf → Bool) (k : Kind)
    (n pa : Nat) (acc : List (MapLeaf × Place)) :
    checkPages s base taken k (n + 1) pa acc =
      (checkPlace s base (pageLeaf k pa) (taken (pageLeaf k pa))).bind
        (fun p => checkPages s base taken k n (pa + PAGE_SIZE) ((pageLeaf k pa, p) :: acc)) := by
  simp only [checkPages, layoutPages_succ, List.foldlM_cons, checkLeaf_eq]
  cases checkPlace s base (pageLeaf k pa) (taken (pageLeaf k pa)) <;> rfl

/-! ## The checks of one range -/

/-- `Tables.checkLayoutRange` as nested conditions. -/
theorem checkLayoutRange_eq (s : Tables .lower N) (base : UInt64) (bits : UInt8)
    (guards : List UInt64) (earlier : List PhysRange) (leaves : List (MapLeaf × Place))
    (j : LayoutRange) :
    s.checkLayoutRange base bits guards (earlier, leaves) j =
      if j.range.start.toNat % PAGE_SIZE ≠ 0 ∨ j.range.endNat % PAGE_SIZE ≠ 0 then
        .error .alignment
      else if VA_LIMIT < j.range.endNat ∨ 2 ^ bits.toNat < j.range.endNat then .error .addressWidth
      else
        (checkPages s base (layoutTaken earlier guards) j.kind (j.range.len.toNat / PAGE_SIZE) j.range.start.toNat leaves).map
          (fun ls => (earlier ++ [j.range], ls)) := by
  simp only [Tables.checkLayoutRange, checkPages]
  by_cases h1 : j.range.start.toNat % PAGE_SIZE ≠ 0 ∨ j.range.endNat % PAGE_SIZE ≠ 0
  · have h1' : (j.range.start.toNat % PAGE_SIZE != 0 || j.range.endNat % PAGE_SIZE != 0) = true := by
      simpa [bne_iff_ne] using h1
    simp only [h1', h1, ↓reduceIte]; rfl
  · have h1' : (j.range.start.toNat % PAGE_SIZE != 0 || j.range.endNat % PAGE_SIZE != 0) = false := by
      simpa [bne_iff_ne] using h1
    simp only [h1', h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h2 : VA_LIMIT < j.range.endNat ∨ 2 ^ bits.toNat < j.range.endNat
    · have h2' : (decide (VA_LIMIT < j.range.endNat) || decide (2 ^ bits.toNat < j.range.endNat)) =
          true := by simpa using h2
      simp only [h2', h2, ↓reduceIte]; rfl
    · have h2' : (decide (VA_LIMIT < j.range.endNat) || decide (2 ^ bits.toNat < j.range.endNat)) =
          false := by simpa using h2
      simp only [h2', h2, Bool.false_eq_true, ↓reduceIte]
      rw [show ∀ x : Except TableError (List (MapLeaf × Place)),
          Except.map (fun ls => (earlier ++ [j.range], ls)) x =
            (do let y ← x; pure (earlier ++ [j.range], y)) from fun x => by cases x <;> rfl]
      rfl

/-- The checks of `n` pages that pass put `n` leaves before those that
passed. -/
theorem checkPages_length (s : Tables r N) (base : UInt64) (taken : MapLeaf → Bool) (k : Kind) :
    ∀ (n pa : Nat) (acc acc' : List (MapLeaf × Place)),
      checkPages s base taken k n pa acc = .ok acc' → acc'.length = acc.length + n
  | 0, pa, acc, acc', h => by
    rw [checkPages_zero] at h; cases h; rfl
  | n + 1, pa, acc, acc', h => by
    rw [checkPages_succ] at h
    cases hp : checkPlace s base (pageLeaf k pa) (taken (pageLeaf k pa)) with
    | error x => rw [hp] at h; cases h
    | ok p =>
      rw [hp] at h
      have := checkPages_length s base taken k n (pa + PAGE_SIZE) _ acc' h
      rw [this, List.length_cons]; omega

/-- The checks of one range that pass: the range is put after the ranges
before, and at most `2 ^ 27` leaves, the pages of a range below `2 ^ 39`,
before the leaves that passed. -/
theorem checkLayoutRange_ok {s : Tables .lower N} {base : UInt64} {bits : UInt8}
    {guards : List UInt64} {earlier earlier' : List PhysRange}
    {leaves leaves' : List (MapLeaf × Place)} {j : LayoutRange}
    (h : s.checkLayoutRange base bits guards (earlier, leaves) j = .ok (earlier', leaves')) :
    earlier' = earlier ++ [j.range] ∧ leaves'.length ≤ leaves.length + 2 ^ 27 := by
  rw [checkLayoutRange_eq] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i h2
      cases hc : checkPages s base (layoutTaken earlier guards) j.kind
          (j.range.len.toNat / PAGE_SIZE) j.range.start.toNat leaves with
      | error x => rw [hc] at h; cases h
      | ok ls =>
        rw [hc] at h
        simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, ?_⟩
        rw [checkPages_length s base _ j.kind _ _ leaves ls hc]
        have : j.range.endNat ≤ 2 ^ 39 := by
          simp only [not_or, Nat.not_lt, VA_LIMIT] at h2; exact h2.1
        have hl : j.range.len.toNat ≤ j.range.endNat := by simp only [PhysRange.endNat]; omega
        simp only [PAGE_SIZE]; omega

/-! ## `Tables.kernelMap` step by step -/

theorem checkPool_ok_facts {base : UInt64} {bits : UInt8} (h : checkPool N base bits = .ok ()) :
    widthOk bits = true ∧ poolFits N base bits = true := by
  rw [checkPool_eq] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i h2 h3
        exact ⟨by simpa using h2, by simpa using h3⟩

theorem kernelMap_pool_error {s : Tables .lower N} {L : Layout} {base : UInt64} {bits : UInt8}
    {x : TableError} (h : checkPool N base bits = .error x) :
    s.kernelMap L base bits = .error x := by
  simp only [Tables.kernelMap, h, bind, Except.bind]

theorem kernelMap_fold_error {s : Tables .lower N} {L : Layout} {base : UInt64} {bits : UInt8}
    {x : TableError} (hp : checkPool N base bits = .ok ())
    (h : (sortByKey (·.range.start.toNat) L.ranges).foldlM
      (s.checkLayoutRange base bits L.guards) ([], []) = .error x) :
    s.kernelMap L base bits = .error x := by
  simp only [Tables.kernelMap, hp, h, bind, Except.bind]

/-- `Tables.kernelMap` after its checks pass: the write phase of the leaves
that passed, with the next free index of `allocOf`. -/
theorem kernelMap_fold_ok {s : Tables .lower N} {L : Layout} {base : UInt64} {bits : UInt8}
    {earlier : List PhysRange} {leaves : List (MapLeaf × Place)}
    (hp : checkPool N base bits = .ok ())
    (h : (sortByKey (·.range.start.toNat) L.ranges).foldlM
      (s.checkLayoutRange base bits L.guards) ([], []) = .ok (earlier, leaves)) :
    s.kernelMap L base bits =
      if N - s.used < (allocOf s.used leaves).next - s.used then .error .outOfTables
      else .ok ({ s with used := (allocOf s.used leaves).next },
        mapPlan base (allocOf s.used leaves).placed.reverse) := by
  simp only [Tables.kernelMap, hp, h, bind, Except.bind, Tables.mapLeaves, assignTables, allocOf]
  by_cases hc : N - s.used <
      (List.foldl Alloc.add ⟨s.used, none, none, []⟩ leaves.reverse).next - s.used
  · simp only [hc, ↓reduceIte]; rfl
  · simp only [hc, ↓reduceIte]; rfl

/-! ## The leaf search of the kernel map -/

/-- A range of a layout on numbers: its start, its end and its kind. -/
structure RangeView where
  start : Nat
  stop : Nat
  kind : Kind

/-- The leaf search of the plan of `kernel_map` over sorted ranges that
passed their checks: the first page at or above `frm` of the first range that
ends above `frm`, when it lies below `limit`. -/
def layoutFind (rs : List RangeView) (frm limit : Nat) : Option Found :=
  match rs.find? (fun r => decide (frm < r.stop)) with
  | none => none
  | some r =>
    if max r.start frm < limit then
      some ⟨max r.start frm, descriptor r.kind (UInt64.ofNat (max r.start frm)), false⟩
    else none

theorem layoutFind_cons_lt {r : RangeView} {rs : List RangeView} {frm limit : Nat}
    (h : frm < r.stop) :
    layoutFind (r :: rs) frm limit =
      if max r.start frm < limit then
        some ⟨max r.start frm, descriptor r.kind (UInt64.ofNat (max r.start frm)), false⟩
      else none := by
  simp only [layoutFind, List.find?_cons, h, decide_true]

theorem layoutFind_cons_ge {r : RangeView} {rs : List RangeView} {frm limit : Nat}
    (h : ¬ frm < r.stop) : layoutFind (r :: rs) frm limit = layoutFind rs frm limit := by
  simp only [layoutFind, List.find?_cons, h, decide_false]

theorem layoutFind_nil (frm limit : Nat) : layoutFind [] frm limit = none := rfl

/-- A leaf found among nonempty ranges that end at or below `2 ^ 39` lies
below `2 ^ 39`. -/
theorem layoutFind_low {rs : List RangeView} {frm limit : Nat} {f : Found}
    (hlow : ∀ r ∈ rs, r.start < r.stop ∧ r.stop ≤ 2 ^ 39) (h : layoutFind rs frm limit = some f) :
    f.pa < 2 ^ 39 := by
  unfold layoutFind at h
  split at h
  · cases h
  · rename_i r hr
    have hm := List.mem_of_find?_eq_some hr
    have hp := List.find?_some hr
    simp only [decide_eq_true_eq] at hp
    split at h
    · cases h
      have := hlow r hm
      simp only
      omega
    · cases h

/-! ## Lists of ranges -/

/-- Two lists that agree item by item agree at each index. -/
theorem layout_listRel_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, Krepi.Statements.ListRel R l m →
      ∀ (i : Nat) (h1 : i < l.length) (h2 : i < m.length), R l[i] m[i]
  | [], [], _, i, h1, _ => absurd h1 (by simp)
  | a :: l, b :: m, h, i, h1, h2 => by
    obtain ⟨hab, hlm⟩ := h
    cases i with
    | zero => exact hab
    | succ i =>
      exact layout_listRel_getElem hlm i (by simpa using h1) (by simpa using h2)
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim

/-! ## The insertion sort of the code -/

section InsertionSort

variable {α : Type}

/-- The insertion of `x` after the elements of a list from its front whose
key is at most that of `x`: where `insert_range` moves the range at its
index among the sorted ranges before it. -/
def insertAfter (key : α → Nat) (x : α) : List α → List α
  | [] => [x]
  | z :: s => if key z ≤ key x then z :: insertAfter key x s else x :: z :: s

/-- The insertion of `sortByKey` and `insertAfter` commute. -/
theorem insert_insertAfter (key : α → Nat) (x y : α) :
    ∀ s, sortByKey.insert key y (insertAfter key x s) =
      insertAfter key x (sortByKey.insert key y s)
  | [] => by
    by_cases h : key y ≤ key x
    · simp only [insertAfter, sortByKey.insert, h, ↓reduceIte]
    · simp only [insertAfter, sortByKey.insert, h, ↓reduceIte]
  | z :: s => by
    by_cases hzx : key z ≤ key x <;> by_cases hyz : key y ≤ key z
    · have hyx : key y ≤ key x := Nat.le_trans hyz hzx
      simp only [insertAfter, sortByKey.insert, hzx, hyz, hyx, ↓reduceIte]
    · simp only [insertAfter, sortByKey.insert, hzx, hyz, ↓reduceIte,
        insert_insertAfter key x y s]
    · by_cases hyx : key y ≤ key x
      · simp only [insertAfter, sortByKey.insert, hzx, hyz, hyx, ↓reduceIte]
      · simp only [insertAfter, sortByKey.insert, hzx, hyz, hyx, ↓reduceIte]
    · have hyx : ¬ key y ≤ key x := by omega
      simp only [insertAfter, sortByKey.insert, hzx, hyz, hyx, ↓reduceIte]

/-- `sortByKey` of a list with one more element at its end inserts it after
the elements of key at most its own. -/
theorem sortByKey_concat (key : α → Nat) (x : α) :
    ∀ l, sortByKey key (l ++ [x]) = insertAfter key x (sortByKey key l)
  | [] => rfl
  | y :: l => by
    simp only [List.cons_append, sortByKey, sortByKey_concat key x l, insert_insertAfter]

/-- Inserting before elements of larger key. -/
theorem insertAfter_append (key : α → Nat) (x : α) (B : List α) (hB : ∀ b ∈ B, key x < key b) :
    ∀ A, insertAfter key x (A ++ B) = insertAfter key x A ++ B
  | [] => by
    cases B with
    | nil => rfl
    | cons b B =>
      have : ¬ key b ≤ key x := Nat.not_le.2 (hB b List.mem_cons_self)
      simp only [List.nil_append, insertAfter, this, ↓reduceIte, List.singleton_append]
  | a :: A => by
    by_cases h : key a ≤ key x
    · simp only [List.cons_append, insertAfter, h, ↓reduceIte, insertAfter_append key x B hB A]
    · simp only [List.cons_append, insertAfter, h, ↓reduceIte]

/-- Inserting after elements of key at most its own. -/
theorem insertAfter_of_le (key : α → Nat) (x : α) :
    ∀ A, (∀ a ∈ A, key a ≤ key x) → insertAfter key x A = A ++ [x]
  | [], _ => rfl
  | a :: A, h => by
    simp only [insertAfter, h a List.mem_cons_self, ↓reduceIte, List.cons_append,
      insertAfter_of_le key x A (fun b hb => h b (List.mem_cons_of_mem a hb))]

/-- The swap of two neighbours at the end of a prefix. -/
theorem set_swap (A : List α) (a x : α) (T : List α) :
    ((A ++ a :: x :: T).set (A.length + 1) a).set A.length x = A ++ x :: a :: T := by
  induction A with
  | nil => rfl
  | cons b A ih => simp only [List.cons_append, List.length_cons, List.set_cons_succ, ih]

/-- The insertion of `sortByKey` of two lists that agree item by item, with
keys that agree on related items. -/
theorem listRel_insert {β : Type} {R : α → β → Prop} {k1 : α → Nat} {k2 : β → Nat}
    (hk : ∀ a b, R a b → k1 a = k2 b) {x : α} {X : β} (hx : R x X) :
    ∀ (l : List α) (L : List β), Krepi.Statements.ListRel R l L →
      Krepi.Statements.ListRel R (sortByKey.insert k1 x l) (sortByKey.insert k2 X L)
  | [], [], _ => ⟨hx, trivial⟩
  | a :: l, b :: L, h => by
    obtain ⟨hab, hlL⟩ := h
    simp only [sortByKey.insert, hk x X hx, hk a b hab]
    split
    · exact ⟨hx, hab, hlL⟩
    · exact ⟨hab, listRel_insert hk hx l L hlL⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- `sortByKey` of two lists that agree item by item, with keys that agree on
related items. -/
theorem listRel_sortByKey {β : Type} {R : α → β → Prop} {k1 : α → Nat} {k2 : β → Nat}
    (hk : ∀ a b, R a b → k1 a = k2 b) :
    ∀ (l : List α) (L : List β), Krepi.Statements.ListRel R l L →
      Krepi.Statements.ListRel R (sortByKey k1 l) (sortByKey k2 L)
  | [], [], _ => trivial
  | a :: l, b :: L, h => by
    obtain ⟨hab, hlL⟩ := h
    simp only [sortByKey]
    exact listRel_insert hk hab _ _ (listRel_sortByKey hk l L hlL)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

end InsertionSort

end Krepi.Proofs.PageTables.Refinement
