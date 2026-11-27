module

public import Krepi.Proofs.PageTables.Refinement.CursorSpecLemmas
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
  `layout_room`.
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
- Lists: `listRel_getElem`.
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

/-- The bound on the record of new tables before a range of a layout of at
most 16 ranges: at most `2 ^ 27` pages a range and two new tables a page. -/
theorem layout_room {u n m idx : Nat} (h1 : u + 2 ^ 33 ≤ m) (h2 : n ≤ idx * 2 ^ 27)
    (h3 : idx ≤ 15) : u + 2 * (n + 2 ^ 27) + 2 ≤ m := by
  have hn : n ≤ 15 * 2 ^ 27 := Nat.le_trans h2 (Nat.mul_le_mul_right _ h3)
  have hb : 2 * (n + 2 ^ 27) + 2 ≤ 2 ^ 33 :=
    Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.add_le_add_right hn _)) 2)
      (Nat.le_of_ble_eq_true rfl)
  rw [Nat.add_assoc]
  exact Nat.le_trans (Nat.add_le_add_left hb u) h1

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

/-! ## Lists of ranges -/

/-- Two lists that agree item by item agree at each index. -/
theorem listRel_getElem {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, Krepi.Statements.ListRel R l m →
      ∀ (i : Nat) (h1 : i < l.length) (h2 : i < m.length), R l[i] m[i]
  | [], [], _, i, h1, _ => absurd h1 (by simp)
  | a :: l, b :: m, h, i, h1, h2 => by
    obtain ⟨hab, hlm⟩ := h
    cases i with
    | zero => exact hab
    | succ i =>
      exact listRel_getElem hlm i (by simpa using h1) (by simpa using h2)
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim

end Krepi.Proofs.PageTables.Refinement
