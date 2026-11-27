module

public import Krepi.Proofs.PageTables.Refinement.BasicLemmas
public import Krepi.Proofs.PageTables.WriteLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: lemmas of the specification for the receipts of the page ownership table

Lemmas that need no generated definition, for the refinement of the entries
on receipts of the page ownership table (`Ownership::validate`, `publish`,
`cancel`, `release`). The module imports no generated definitions, so it is
built once and not again for every mutant of the code.

- Lists that `ListRel` relates: `receipt_listRel_append`,
  `receipt_listRel_take`, `receipt_listRel_drop`, `receipt_listRel_set`,
  `receipt_listRel_getElem?` and `receipt_listRel_at` (items of one index),
  `receipt_findIdx_eq` (searches with tests that agree on related items find
  one index) and `receipt_listRel_replace` (a block of the list replaced by
  one item and the items after it moved down).
- The search of the code, an index from the start: `receipt_findIdx_drop`
  (one step of the search from an index) and `receipt_findIdx_drop_end`.
- Closing a gap in an array, one copy at a time: `receipt_gap_step` (the
  items after one copy) and `receipt_gap_done` (the list after the last).
- Values: `receipt_range_beq` (ranges by their starts and lengths),
  `receipt_not_bne_iff`, `receipt_word64_beq`.
- The search of the specification: `receipt_splitFirst_none` and
  `receipt_splitFirst_some` (`splitFirst` from `List.findIdx?`), and the
  outcomes of `Ownership.findHeld`: `receipt_findHeld_arena`,
  `receipt_findHeld_owner`, `receipt_findHeld_none`, `receipt_findHeld_some`.
- The extents around the extent that `findHeld` finds:
  `receipt_getElem?_found`, `receipt_getElem?_freed`,
  `receipt_getElem?_before`, `receipt_getElem?_after`, and
  `receipt_set_found` (another extent written in its place).
- `mergeFreed` as a block replaced by one free extent: `ExtentsJoin` (the test
  of `Extent.join`), `receipt_mergeFreed_shape` (the block `[first, last]`
  from the joins with the extents next to the freed one), and the cases of
  those joins: `receipt_left_join`, `receipt_left_apart`, `receipt_left_nil`,
  `receipt_right_join`, `receipt_right_apart`, `receipt_right_nil`.
-/

@[expose] public section

open Krepi.Statements Krepi.Spec.PageTables Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

section Lists

variable {α β : Type} {R : α → β → Prop}

/-- Lists related item by item, appended. -/
theorem receipt_listRel_append : ∀ {a : List α} {A : List β} {b : List α} {B : List β},
    ListRel R a A → ListRel R b B → ListRel R (a ++ b) (A ++ B)
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, h, hb => ⟨h.1, receipt_listRel_append h.2 hb⟩
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim

/-- The first `n` items of lists related item by item. -/
theorem receipt_listRel_take : ∀ (n : Nat) {l : List α} {L : List β},
    ListRel R l L → ListRel R (l.take n) (L.take n)
  | 0, _, _, _ => by simp
  | _ + 1, [], [], _ => by simp
  | n + 1, _ :: _, _ :: _, h => ⟨h.1, receipt_listRel_take n h.2⟩
  | _ + 1, [], _ :: _, h => h.elim
  | _ + 1, _ :: _, [], h => h.elim

/-- The items from index `n` of lists related item by item. -/
theorem receipt_listRel_drop : ∀ (n : Nat) {l : List α} {L : List β},
    ListRel R l L → ListRel R (l.drop n) (L.drop n)
  | 0, _, _, h => h
  | _ + 1, [], [], _ => by simp
  | n + 1, _ :: _, _ :: _, h => receipt_listRel_drop n h.2
  | _ + 1, [], _ :: _, h => h.elim
  | _ + 1, _ :: _, [], h => h.elim

/-- The items of one index of lists related item by item, as options. -/
theorem receipt_listRel_getElem? : ∀ {l : List α} {L : List β}, ListRel R l L →
    ∀ (j : Nat), OptionRel R l[j]? L[j]?
  | [], [], _, _ => by simp
  | _ :: _, _ :: _, h, 0 => by simpa using h.1
  | _ :: _, _ :: _, h, j + 1 => by simpa using receipt_listRel_getElem? h.2 j
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

/-- Lists related item by item with related items written at one index. -/
theorem receipt_listRel_set : ∀ {l : List α} {L : List β}, ListRel R l L →
    ∀ (j : Nat) {a : α} {A : β}, R a A → ListRel R (l.set j a) (L.set j A)
  | [], [], _, _, _, _, _ => by simp
  | _ :: _, _ :: _, h, 0, _, _, hr => ⟨hr, h.2⟩
  | _ :: _, _ :: _, h, j + 1, _, _, hr => ⟨h.1, receipt_listRel_set h.2 j hr⟩
  | [], _ :: _, h, _, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _, _ => h.elim

/-- Searches with tests that agree on related items find the same index in
lists related item by item. -/
theorem receipt_findIdx_eq {p : α → Bool} {q : β → Bool} (hpq : ∀ a b, R a b → p a = q b) :
    ∀ {l : List α} {L : List β}, ListRel R l L → l.findIdx? p = L.findIdx? q
  | [], [], _ => rfl
  | a :: _, b :: _, h => by
    rw [List.findIdx?_cons, List.findIdx?_cons, hpq a b h.1, receipt_findIdx_eq hpq h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- One step of a search from the index `i` of the list, below its length:
the item at `i`, or the search from `i + 1`. Indices count from the start. -/
theorem receipt_findIdx_drop {p : α → Bool} {l : List α} {i : Nat} (h : i < l.length) :
    ((l.drop i).findIdx? p).map (· + i) =
      if p l[i] then some i else ((l.drop (i + 1)).findIdx? p).map (· + (i + 1)) := by
  rw [List.drop_eq_getElem_cons h, List.findIdx?_cons]
  split
  · simp
  · rw [Option.map_map]
    congr 1
    funext k
    simp only [Function.comp_apply]
    omega

/-- A search from an index at or after the end finds nothing. -/
theorem receipt_findIdx_drop_end {p : α → Bool} {l : List α} {i : Nat} (h : l.length ≤ i) :
    (l.drop i).findIdx? p = none := by
  rw [List.drop_eq_nil_of_le h]; rfl

/-- One copy of the loop that closes a gap of `gap` items at `at₀`: with the
items below `at₀` and from `at'` those of `l`, and those of `[at₀, at')` the
items `gap` later, a copy of the item at `at' + gap` to `at'`, with
`at' + gap` within the list, keeps that form one item further. -/
theorem receipt_gap_step {l a : List α} {at₀ at' gap : Nat} (hlen : a.length = l.length)
    (hle : at₀ ≤ at') (hlt : at' + gap < l.length)
    (hinv : ∀ j, a[j]? = if j < at₀ ∨ at' ≤ j then l[j]? else l[j + gap]?) (x : α)
    (hx : a[at' + gap]? = some x) :
    ∀ j, (a.set at' x)[j]? = if j < at₀ ∨ at' + 1 ≤ j then l[j]? else l[j + gap]? := by
  intro j
  rw [List.getElem?_set]
  by_cases hj : at' = j
  · subst hj
    have h1 : a[at' + gap]? = l[at' + gap]? := by
      rw [hinv]; simp only [show at' ≤ at' + gap by omega, or_true, ↓reduceIte]
    rw [h1] at hx
    simp only [show at' < a.length by omega, ↓reduceIte, ← hx]
    split <;> first | rfl | omega
  · simp only [hj, ↓reduceIte, hinv]
    by_cases h2 : j < at₀ <;> by_cases h3 : at' ≤ j <;> by_cases h4 : at' + 1 ≤ j <;>
      simp only [h2, h3, h4, or_true, or_false, ↓reduceIte] <;> omega

/-- The loop that closes a gap, once `at' + gap` reaches `count`, within the
list: the first `count - gap` items are the items of `l` below `at₀` and
those of `[at₀ + gap, count)`. -/
theorem receipt_gap_done {l a : List α} {at₀ at' gap count : Nat}
    (hle : at₀ ≤ at') (hend : at' + gap = count) (hc : count ≤ l.length)
    (hinv : ∀ j, a[j]? = if j < at₀ ∨ at' ≤ j then l[j]? else l[j + gap]?) :
    a.take (count - gap) = l.take at₀ ++ (l.take count).drop (at₀ + gap) := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_take, List.getElem?_append, List.getElem?_take, List.length_take,
    List.getElem?_drop, List.getElem?_take]
  by_cases h1 : j < count - gap
  · simp only [h1, ↓reduceIte]
    rw [hinv]
    by_cases h2 : j < at₀
    · simp [h2, show j < l.length by omega]
    · simp only [h2, show ¬ at' ≤ j by omega, or_self, ↓reduceIte,
        show ¬ j < min at₀ l.length by omega,
        show at₀ + gap + (j - min at₀ l.length) < count by omega]
      congr 1; omega
  · simp only [h1, ↓reduceIte]
    by_cases h2 : j < at₀
    · omega
    · simp only [show ¬ j < min at₀ l.length by omega, ↓reduceIte,
        show ¬ at₀ + gap + (j - min at₀ l.length) < count by omega]

/-- The item of index `j` of a list related item by item to the first `c`
items of `l`, for `j` below `c` and the length of `l`. -/
theorem receipt_listRel_at {l : List α} {L : List β} {c j : Nat} (h : ListRel R (l.take c) L)
    (hj : j < c) (hl : j < l.length) : ∃ X, L[j]? = some X ∧ R l[j] X := by
  have := receipt_listRel_getElem? h j
  rw [List.getElem?_take_of_lt hj, List.getElem?_eq_getElem hl] at this
  cases hX : L[j]? with
  | none => rw [hX] at this; exact this.elim
  | some X => rw [hX] at this; exact ⟨X, rfl, this⟩

/-- A block `[first, last]` of the first `count` items of a list, with
`first ≤ last < count` and `count` within the list, replaced by one item,
written at `first`, and the items after the block moved down to it: the
lists related item by item stay related, the block of the other list replaced
by an item related to the new one. -/
theorem receipt_listRel_replace {l : List α} {L : List β} {y : α} {Y : β}
    {count first last : Nat} (h : ListRel R (l.take count) L) (hfl : first ≤ last)
    (hlc : last < count) (hc : count ≤ l.length) (hY : R y Y) :
    ListRel R ((l.set first y).take (first + 1) ++ ((l.set first y).take count).drop (last + 1))
      (L.take first ++ Y :: L.drop (last + 1)) := by
  have hA : (l.set first y).take (first + 1) = l.take first ++ [y] := by
    rw [List.take_add_one, List.take_set_of_le (le_refl _), List.getElem?_set_self (by omega)]
    rfl
  have hB : ((l.set first y).take count).drop (last + 1) = (l.take count).drop (last + 1) := by
    rw [List.take_set, List.drop_set_of_lt (by omega : first < last + 1)]
  rw [hA, hB, List.append_assoc]
  refine receipt_listRel_append ?_ ⟨hY, receipt_listRel_drop (last + 1) h⟩
  have := receipt_listRel_take first h
  rwa [List.take_take, Nat.min_eq_left (by omega)] at this

end Lists

section Values

/-- Two ranges are equal exactly when their starts and lengths are. -/
theorem receipt_range_beq (R R' : PhysRange) :
    (R == R') = (R.start == R'.start && R.len == R'.len) := by
  obtain ⟨s, l, _, _⟩ := R
  obtain ⟨s', l', _, _⟩ := R'
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, Bool.and_eq_true, PhysRange.mk.injEq]

/-- A `!=` that does not hold, as an equality. -/
theorem receipt_not_bne_iff {α : Type} [BEq α] [LawfulBEq α] {a b : α} :
    ¬ (a != b) = true ↔ a = b := by
  rw [bne_iff_ne, ne_eq, not_not]

/-- Words of the specification are equal exactly when the words of the code
are. -/
theorem receipt_word64_beq (x y : Aeneas.Std.U64) : (word64 x == word64 y) = (x == y) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, word64_inj]

end Values

section Search

/-- No extent passes the test: `splitFirst` finds none. -/
theorem receipt_splitFirst_none {p : Extent → Bool} : ∀ {l acc : List Extent},
    l.findIdx? p = none → splitFirst p l acc = none
  | [], _, _ => rfl
  | x :: xs, acc, h => by
    rw [List.findIdx?_cons] at h
    unfold splitFirst
    by_cases hx : p x = true
    · simp only [hx, ↓reduceIte] at h
      exact absurd h (by simp)
    · simp only [hx, Bool.false_eq_true, ↓reduceIte, Option.map_eq_none_iff] at h ⊢
      exact receipt_splitFirst_none h

/-- The first extent that passes the test is at index `i`: `splitFirst`
finds it with the `i` extents before it. -/
theorem receipt_splitFirst_some {p : Extent → Bool} : ∀ {l acc : List Extent} {i : Nat},
    l.findIdx? p = some i →
      ∃ b e a, splitFirst p l acc = some (b, e, a) ∧ b.length = i + acc.length
  | [], _, _, h => absurd h (by simp)
  | x :: xs, acc, i, h => by
    rw [List.findIdx?_cons] at h
    unfold splitFirst
    by_cases hx : p x = true
    · simp only [hx, ↓reduceIte, Option.some.injEq] at h ⊢
      exact ⟨acc, x, xs, rfl, by omega⟩
    · simp only [hx, Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨b, e, a, h1, h2⟩ := receipt_splitFirst_some (acc := x :: acc) hk
      exact ⟨b, e, a, h1, by simp only [List.length_cons] at h2; omega⟩

variable {E X : Nat}

/-- `findHeld` of a value of another arena. -/
theorem receipt_findHeld_arena {t : Ownership E X} {o : UInt64} {a : Allocation} {s : HoldState}
    (h : a.arena ≠ t.arena) : t.findHeld o a s = .error .wrongArena := by
  simp [Ownership.findHeld, h, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- `findHeld` of a value of the arena of another owner identity. -/
theorem receipt_findHeld_owner {t : Ownership E X} {o : UInt64} {a : Allocation} {s : HoldState}
    (h1 : a.arena = t.arena) (h2 : a.owner ≠ o) : t.findHeld o a s = .error .wrongOwner := by
  simp [Ownership.findHeld, h1, h2, throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- `findHeld` of a value whose range no extent holds as it names it. -/
theorem receipt_findHeld_none {t : Ownership E X} {o : UInt64} {a : Allocation} {s : HoldState}
    (h1 : a.arena = t.arena) (h2 : a.owner = o)
    (h : t.extents.findIdx? (fun e => e.range == a.range && e.holding == .held o a.generation s) =
      none) :
    t.findHeld o a s = .error .invalidAllocation := by
  simp only [Ownership.findHeld, h1, h2, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
    receipt_splitFirst_none h]
  rfl

/-- `findHeld` of a value that the extent of index `i` holds as it names it:
the extents before it, `i` of them, the extent and the extents after it. -/
theorem receipt_findHeld_some {t : Ownership E X} {o : UInt64} {a : Allocation} {s : HoldState}
    {i : Nat} (h1 : a.arena = t.arena) (h2 : a.owner = o)
    (h : t.extents.findIdx? (fun e => e.range == a.range && e.holding == .held o a.generation s) =
      some i) :
    ∃ b e a', t.findHeld o a s = .ok (b, e, a') ∧ b.length = i := by
  obtain ⟨b, e, a', hs, hl⟩ := receipt_splitFirst_some (acc := []) h
  refine ⟨b, e, a', ?_, by simpa using hl⟩
  simp only [Ownership.findHeld, h1, h2, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hs]
  rfl

/-- The extent that `findHeld` finds is at the index of the number of
extents before it. -/
theorem receipt_getElem?_found (before after : List Extent) (e : Extent) :
    (before.reverse ++ e :: after)[before.length]? = some e := by
  rw [List.getElem?_append_right (by simp)]; simp

/-- The extent before it, when there is one, is the first of the extents
before it, in reverse order. -/
theorem receipt_getElem?_before {before : List Extent} (after : List Extent) (e : Extent)
    (h : 0 < before.length) :
    (before.reverse ++ e :: after)[before.length - 1]? = before.head? := by
  cases before with
  | nil => simp at h
  | cons x xs =>
    rw [List.getElem?_append_left (by simp)]
    simp

/-- The extent after it is the first of the extents after it. -/
theorem receipt_getElem?_after (before after : List Extent) (e : Extent) :
    (before.reverse ++ e :: after)[before.length + 1]? = after.head? := by
  rw [List.getElem?_append_right (by simp)]
  cases after <;> simp

/-- The extent freed by `mergeFreed`, read at its index. -/
theorem receipt_getElem?_freed (before after : List Extent) (e : Extent) (j : Nat)
    (hj : j = before.length) :
    (before.reverse ++ e :: after)[j]? = some e := by
  rw [hj]; exact receipt_getElem?_found before after e

/-- Two extents in address order that `Extent.join` joins: both free, of one
bank, the first ending where the second starts. -/
def ExtentsJoin (a b : Extent) : Prop :=
  a.holding = .free ∧ b.holding = .free ∧ a.bank = b.bank ∧ a.range.endNat = b.range.start.toNat

/-- `mergeFreed` as the block `[first, last]` of the extents, with the
extent freed at its index, replaced by one free extent: `first` is the index
of the extent before it when the two join and its own index otherwise, and
`last` that of the extent after it when the two join and its own index
otherwise. The free extent starts where the extent at `first` starts, in its
bank, and ends where the extent at `last` ends. -/
theorem receipt_mergeFreed_shape {before after : List Extent} {e : Extent} {first last : Nat}
    (hL1 : ∀ x, before.head? = some x → ExtentsJoin x { e with holding := .free } →
      first + 1 = before.length)
    (hL2 : (∀ x, before.head? = some x → ¬ ExtentsJoin x { e with holding := .free }) →
      first = before.length)
    (hR1 : ∀ y, after.head? = some y → ExtentsJoin { e with holding := .free } y →
      last = before.length + 1)
    (hR2 : (∀ y, after.head? = some y → ¬ ExtentsJoin { e with holding := .free } y) →
      last = before.length) :
    ∃ m : Extent, mergeFreed before e after =
        (before.reverse ++ { e with holding := .free } :: after).take first ++
          m :: (before.reverse ++ { e with holding := .free } :: after).drop (last + 1) ∧
      m.holding = .free ∧
      (∀ X, (before.reverse ++ { e with holding := .free } :: after)[first]? = some X →
        X.holding = .free ∧ X.bank = m.bank ∧ X.range.start.toNat = m.range.start.toNat) ∧
      (∀ Y, (before.reverse ++ { e with holding := .free } :: after)[last]? = some Y →
        Y.range.endNat = m.range.endNat) := by
  obtain ⟨l₁, lo, hi, l₂, m, -, h2, hm1, hm2, hlo, hhi⟩ := mergeFreed_spec before e after
  refine ⟨m, ?_, hm1, ?_, ?_⟩
  · rw [h2]
    congr 1
    · rcases hlo with ⟨-, rfl, -, hneg⟩ | ⟨x, -, hx, rfl, hx1, hx2, hx3, -⟩
      · have hf : first = before.length :=
          hL2 (fun x hx hj => hneg x (by simp [hx]) ⟨hj.1, hj.2.2.1, hj.2.2.2⟩)
        rw [hf, List.take_left' (by simp)]
      · have hf : first + 1 = before.length := hL1 x hx ⟨hx1, rfl, hx2, hx3⟩
        cases before with
        | nil => simp at hx
        | cons z zs =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hf
          rw [hf, List.reverse_cons, List.append_assoc, List.take_left' (by simp)]
          rfl
    · congr 1
      rcases hhi with ⟨-, rfl, -, hneg⟩ | ⟨y, -, hy, rfl, hy1, hy2, hy3, -⟩
      · have hl : last = before.length :=
          hR2 (fun y hy hj => hneg y (by simp [hy]) ⟨hj.2.1, hj.2.2.1.symm, hj.2.2.2⟩)
        rw [hl, show before.reverse ++ { e with holding := .free } :: l₂ =
          (before.reverse ++ [{ e with holding := .free }]) ++ l₂ by simp,
          List.drop_left' (by simp)]
      · have hl : last = before.length + 1 := hR1 y hy ⟨rfl, hy1, hy2.symm, hy3⟩
        cases after with
        | nil => simp at hy
        | cons z zs =>
          rw [hl, show before.length + 1 + 1 =
            (before.reverse ++ [{ e with holding := .free }, z]).length by simp,
            show before.reverse ++ { e with holding := .free } :: z :: zs =
              (before.reverse ++ [{ e with holding := .free }, z]) ++ zs by simp,
            List.drop_left' rfl]
          rfl
  · intro X hX
    rcases hlo with ⟨-, -, hms, hneg⟩ | ⟨x, -, hx, -, hx1, hx2, hx3, hms⟩
    · have hf : first = before.length :=
        hL2 (fun x hx hj => hneg x (by simp [hx]) ⟨hj.1, hj.2.2.1, hj.2.2.2⟩)
      rw [receipt_getElem?_freed before after _ first hf, Option.some.injEq] at hX
      subst hX
      exact ⟨rfl, hm2.symm, hms.symm⟩
    · have hf : first + 1 = before.length := hL1 x hx ⟨hx1, rfl, hx2, hx3⟩
      rw [show first = before.length - 1 by omega,
        receipt_getElem?_before after _ (by omega), hx, Option.some.injEq] at hX
      subst hX
      exact ⟨hx1, by rw [hm2, hx2], hms.symm⟩
  · intro Y hY
    rcases hhi with ⟨-, -, hme, hneg⟩ | ⟨y, -, hy, -, hy1, hy2, hy3, hme⟩
    · have hl : last = before.length :=
        hR2 (fun y hy hj => hneg y (by simp [hy]) ⟨hj.2.1, hj.2.2.1.symm, hj.2.2.2⟩)
      rw [receipt_getElem?_freed before after _ last hl, Option.some.injEq] at hY
      subst hY
      exact hme.symm
    · have hl : last = before.length + 1 := hR1 y hy ⟨rfl, hy1, hy2.symm, hy3⟩
      rw [hl, receipt_getElem?_after, hy, Option.some.injEq] at hY
      subst hY
      exact hme.symm

/-- The extents around the extent found, with another extent written in its
place. -/
theorem receipt_set_found (before after : List Extent) (e x : Extent) :
    (before.reverse ++ e :: after).set before.length x = before.reverse ++ x :: after := by
  rw [List.set_append_right _ _ (by simp)]; simp

/-- The extent before the freed one joins it, and `first` is its index, one
below the number of extents before the freed one. -/
theorem receipt_left_join {before : List Extent} {F x : Extent} {first : Nat}
    (hx : before.head? = some x) (hj : ExtentsJoin x F) (hf : first + 1 = before.length) :
    (∀ x', before.head? = some x' → ExtentsJoin x' F → first + 1 = before.length) ∧
    ((∀ x', before.head? = some x' → ¬ ExtentsJoin x' F) → first = before.length) :=
  ⟨fun _ _ _ => hf, fun h => absurd hj (h x hx)⟩

/-- The extent before the freed one does not join it, and `first` is the
index of the freed one. -/
theorem receipt_left_apart {before : List Extent} {F x : Extent} {first : Nat}
    (hx : before.head? = some x) (hj : ¬ ExtentsJoin x F) (hf : first = before.length) :
    (∀ x', before.head? = some x' → ExtentsJoin x' F → first + 1 = before.length) ∧
    ((∀ x', before.head? = some x' → ¬ ExtentsJoin x' F) → first = before.length) :=
  ⟨fun x' hx' hj' => by rw [hx, Option.some.injEq] at hx'; subst hx'; exact absurd hj' hj,
    fun _ => hf⟩

/-- No extent before the freed one, and `first` is its index. -/
theorem receipt_left_nil {before : List Extent} {F : Extent} {first : Nat} (hb : before = [])
    (hf : first = before.length) :
    (∀ x', before.head? = some x' → ExtentsJoin x' F → first + 1 = before.length) ∧
    ((∀ x', before.head? = some x' → ¬ ExtentsJoin x' F) → first = before.length) :=
  ⟨fun _ hx' _ => by simp [hb] at hx', fun _ => hf⟩

/-- The extent after the freed one joins it, and `last` is its index. -/
theorem receipt_right_join {after : List Extent} {F y : Extent} {k last : Nat}
    (hy : after.head? = some y) (hj : ExtentsJoin F y) (hl : last = k + 1) :
    (∀ y', after.head? = some y' → ExtentsJoin F y' → last = k + 1) ∧
    ((∀ y', after.head? = some y' → ¬ ExtentsJoin F y') → last = k) :=
  ⟨fun _ _ _ => hl, fun h => absurd hj (h y hy)⟩

/-- The extent after the freed one does not join it, and `last` is the index
of the freed one. -/
theorem receipt_right_apart {after : List Extent} {F y : Extent} {k last : Nat}
    (hy : after.head? = some y) (hj : ¬ ExtentsJoin F y) (hl : last = k) :
    (∀ y', after.head? = some y' → ExtentsJoin F y' → last = k + 1) ∧
    ((∀ y', after.head? = some y' → ¬ ExtentsJoin F y') → last = k) :=
  ⟨fun y' hy' hj' => by rw [hy, Option.some.injEq] at hy'; subst hy'; exact absurd hj' hj,
    fun _ => hl⟩

/-- No extent after the freed one, and `last` is its index. -/
theorem receipt_right_nil {after : List Extent} {F : Extent} {k last : Nat} (ha : after = [])
    (hl : last = k) :
    (∀ y', after.head? = some y' → ExtentsJoin F y' → last = k + 1) ∧
    ((∀ y', after.head? = some y' → ¬ ExtentsJoin F y') → last = k) :=
  ⟨fun _ hy' _ => by simp [ha] at hy', fun _ => hl⟩


end Search

end Krepi.Proofs.PageTables.Refinement
