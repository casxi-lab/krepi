module

public import Krepi.Proofs.PageTables.Refinement.BasicLemmas
public import Krepi.Spec.PageTables.Ownership
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: lemmas about the arrays of the page ownership table

The page ownership table of the code keeps its extents, banks and exclusion
records in arrays, of which the first `count` entries are in use; a write
shifts the entries after a position and overwrites a few at it. These lemmas
read such arrays as lists, element by element, against the lists of the
specification that `ListRel` relates to the first `count` entries, and
locate the extent that `splitFirst` finds by its index, as the loops of the
code search for it. The module imports no generated definitions, so it is
built once and not again for every mutant of the code.

- Related lists: `listRel_append`, `listRel_take`, `listRel_drop`,
  `listRel_getElem` (the elements at one index are related) and
  `listRel_replace` (an array whose entries before a position are kept,
  whose entries at it are new and related to a list, and whose entries
  after it are those of the array shifted, stands for the list with the
  block of the specification replaced; the shape of the writes of `take`,
  `release` and `cancel`).
- Lists element by element: `getElem?_take_eq_of` (two lists that agree
  below a bound have one prefix) and `getElem?_shift` (a list whose
  entries from a position are those of another list shifted).
- The search of an extent: `splitFirst_of_index` (the first index whose
  extent passes the test gives the extents around it) and
  `splitFirst_of_none` (no extent passes it).
-/

@[expose] public section

open Krepi.Statements Krepi.Spec.PageTables Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

/-! ## Related lists -/

section ListRel

variable {α β : Type} {R : α → β → Prop}

theorem listRel_append : ∀ {a : List α} {c : List β} {b : List α} {d : List β},
    ListRel R a c → ListRel R b d → ListRel R (a ++ b) (c ++ d)
  | [], [], _, _, _, h => h
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim
  | _ :: _, _ :: _, _, _, h, hb => ⟨h.1, listRel_append h.2 hb⟩

theorem listRel_take (n : Nat) : ∀ {l : List α} {m : List β},
    ListRel R l m → ListRel R (l.take n) (m.take n) := by
  induction n with
  | zero => intro l m _; simp
  | succ n ih =>
    intro l m h
    match l, m, h with
    | [], [], _ => simp
    | a :: l, b :: m, h => exact ⟨h.1, ih h.2⟩

theorem listRel_drop (n : Nat) : ∀ {l : List α} {m : List β},
    ListRel R l m → ListRel R (l.drop n) (m.drop n) := by
  induction n with
  | zero => intro l m h; simpa using h
  | succ n ih =>
    intro l m h
    match l, m, h with
    | [], [], _ => simp
    | a :: l, b :: m, h => exact ih h.2

/-- The elements at one index of related lists are related. -/
theorem listRel_getElem : ∀ {l : List α} {m : List β} (h : ListRel R l m) {i : Nat}
    (hi : i < l.length), R l[i] (m[i]'(listRel_length h ▸ hi))
  | [], [], _, _, hi => absurd hi (by simp)
  | a :: l, b :: m, h, 0, _ => h.1
  | a :: l, b :: m, h, i + 1, hi => listRel_getElem h.2 (by simpa using hi)

end ListRel

/-! ## Lists element by element -/

/-- Two lists that agree below a bound have one prefix up to it. -/
theorem getElem?_take_eq_of {α : Type} {l l' : List α} {n : Nat}
    (h : ∀ j < n, l[j]? = l'[j]?) : l.take n = l'.take n := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_take, List.getElem?_take]
  split
  · exact h j ‹_›
  · rfl

/-- The entries of `l` from `a` up to `b` (excluded) are those of `l'` from
`c`: the two blocks are one list. -/
theorem getElem?_shift {α : Type} {l l' : List α} {a b c : Nat}
    (h : ∀ j, a ≤ j → j < b → l[j]? = l'[j - a + c]?) :
    (l.drop a).take (b - a) = (l'.drop c).take (b - a) := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_take, List.getElem?_take]
  split
  · rw [List.getElem?_drop, List.getElem?_drop, h (a + j) (by omega) (by omega)]
    congr 1
    omega
  · rfl

section ListRel

variable {α β : Type} {R : α → β → Prop}

/-- An array of `count` entries in use, stood for by `Ts`, in which `d`
entries from `index` are replaced by `p` entries: the entries before
`index` are kept, the `p` entries from `index` stand for `Ps`, and the
entries after them are those that followed the replaced ones, shifted. The
first `count + p - d` entries of the new array stand for `Ts` with its block
replaced by `Ps`. -/
theorem listRel_replace {L F : List α} {Ts Ps : List β} {count index d p : Nat}
    (hL : ListRel R (L.take count) Ts) (hc : index + d ≤ count)
    (hP : ListRel R ((F.drop index).take p) Ps)
    (hb : ∀ j < index, F[j]? = L[j]?)
    (ha : ∀ j, index + p ≤ j → j < count + p - d → F[j]? = L[j + d - p]?) :
    ListRel R (F.take (count + p - d)) (Ts.take index ++ Ps ++ Ts.drop (index + d)) := by
  have e1 : count + p - d = index + (p + (count - (index + d))) := by omega
  rw [e1, List.take_add, List.take_add, List.drop_drop, List.append_assoc]
  refine listRel_append ?_ (listRel_append hP ?_)
  · rw [getElem?_take_eq_of hb]
    have := listRel_take index hL
    rwa [List.take_take, Nat.min_eq_left (by omega)] at this
  · have e2 : (F.drop (index + p)).take (count - (index + d)) =
        (L.drop (index + d)).take (count - (index + d)) := by
      have := getElem?_shift (l := F) (l' := L) (a := index + p) (b := count + p - d)
        (c := index + d) (fun j h1 h2 => by
          rw [ha j h1 h2]; congr 1; omega)
      rwa [show count + p - d - (index + p) = count - (index + d) by omega] at this
    rw [e2]
    have := listRel_drop (index + d) hL
    rwa [List.drop_take] at this

end ListRel

/-! ## The search of an extent -/

/-- The first extent at an index that passes the test: `splitFirst` gives
the extents before it, in reverse order after `acc`, the extent and the
extents after it. -/
theorem splitFirst_of_index {p : Extent → Bool} : ∀ {l acc : List Extent} {i : Nat}
    (hi : i < l.length), (∀ j (hj : j < i), p (l[j]'(by omega)) = false) → p l[i] = true →
    splitFirst p l acc = some ((l.take i).reverse ++ acc, l[i], l.drop (i + 1))
  | [], _, _, hi, _, _ => absurd hi (by simp)
  | e :: rest, acc, 0, _, _, h => by
    simp only [List.getElem_cons_zero] at h
    simp [splitFirst, h]
  | e :: rest, acc, i + 1, hi, hj, h => by
    have he : p e = false := hj 0 (by omega)
    simp only [splitFirst, he, Bool.false_eq_true, ↓reduceIte]
    rw [splitFirst_of_index (acc := e :: acc) (i := i) (by simpa using hi)
      (fun j hj' => hj (j + 1) (by omega)) h]
    simp

/-- No extent passes the test: `splitFirst` gives none. -/
theorem splitFirst_of_none {p : Extent → Bool} : ∀ {l acc : List Extent},
    (∀ j (hj : j < l.length), p l[j] = false) → splitFirst p l acc = none
  | [], _, _ => rfl
  | e :: rest, acc, h => by
    have he : p e = false := h 0 (by simp)
    simp only [splitFirst, he, Bool.false_eq_true, ↓reduceIte]
    exact splitFirst_of_none (fun j hj => h (j + 1) (by simpa using hj))

end Krepi.Proofs.PageTables.Refinement
