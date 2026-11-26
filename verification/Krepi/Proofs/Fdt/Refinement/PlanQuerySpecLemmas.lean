module

public import Krepi.Proofs.Fdt.PlanLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Device tree: lemmas about the queries of the boot memory map

Lemmas about the specification of the queries of the boot memory map, for
the refinement proofs of `Krepi.Proofs.Fdt.Refinement.PlanQueryLemmas`. The
module imports no generated definitions, so it is built once and not again
for every mutant of the code.

- Sums of sizes: `foldl_size_ge` (a sum is at least its start),
  `foldl_size_le_of_pairwise` and `spansBytes_lt_of_pairwise` (the sizes of
  spans in address order within 64 bits sum below `2 ^ 64`).
- The fuel of `usableFrom`: `usableNeed`, the steps that it takes from a
  cursor, at most `2 * R + 2` for `R` reservations (`usableNeed_le`), fewer
  after each step (`usableNeed_free`, `usableNeed_held`), so that any fuel of
  at least that many steps gives the same ranges (`usableFrom_fuel`).
- The usable ranges from a cursor in a managed bank, the state of the
  iterator of the code: `availableFrom`, with `availableRanges_eq` (the
  usable ranges are those from the first bank), `availableFrom_zero`,
  `availableFrom_end`, `availableFrom_cons`, and one lemma for each move of
  the cursor of the code: to the next bank (`availableFrom_skip`), past the
  reservations that hold it (`availableFrom_held`), and past a usable range
  (`availableFrom_free`); and `availableMeasure`, which each move that gives
  no range decreases (`availableMeasure_skip`, `availableMeasure_held`).
- The reservations that hold a cursor, as the loop of the code finds them:
  `holdStep`, one reservation, and `foldl_holdStep`, none when no
  reservation holds the cursor and otherwise their furthest end `maxEndOf`.
-/

@[expose] public section

open Krepi.Spec.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## Sums of sizes -/

/-- A sum of sizes is at least the value that it starts from. -/
theorem foldl_size_ge : ∀ (l : List Span) (acc : Nat),
    acc ≤ l.foldl (fun sum s => sum + s.size.toNat) acc
  | [], _ => Nat.le_refl _
  | a :: l, acc => Nat.le_trans (Nat.le_add_right _ _) (foldl_size_ge l (acc + a.size.toNat))

/-- Spans in address order that start at `S` or above and end below `2 ^ 64`
add at most `2 ^ 64 - 1 - S` to a sum. -/
theorem foldl_size_le_of_pairwise : ∀ (l : List Span) (acc S : Nat),
    (∀ s ∈ l, S ≤ s.start.toNat ∧ s.endNat < 2 ^ 64) →
    l.Pairwise (fun a b => a.endNat ≤ b.start.toNat) →
    l.foldl (fun sum s => sum + s.size.toNat) acc ≤ acc + (2 ^ 64 - 1 - S)
  | [], _, _, _, _ => Nat.le_add_right _ _
  | a :: l, acc, S, hb, hp => by
    rw [List.pairwise_cons] at hp
    have ha := hb a List.mem_cons_self
    have ih := foldl_size_le_of_pairwise l (acc + a.size.toNat) a.endNat
      (fun s hs => ⟨hp.1 s hs, (hb s (List.mem_cons_of_mem _ hs)).2⟩) hp.2
    rw [List.foldl_cons]
    unfold Span.endNat at ha ih
    omega

/-- The sizes of spans in address order, each within 64 bits, sum below
`2 ^ 64`. -/
theorem spansBytes_lt_of_pairwise {l : List Span} (hv : ∀ s ∈ l, s.Valid)
    (hp : l.Pairwise (fun a b => a.endNat ≤ b.start.toNat)) : spansBytes l < 2 ^ 64 := by
  have := foldl_size_le_of_pairwise l 0 0 (fun s hs => ⟨Nat.zero_le _, hv s hs⟩) hp
  unfold spansBytes
  omega

/-! ## The fuel of `usableFrom` -/

/-- The steps that `usableFrom` takes from the cursor `c` before it stops:
none at or past the end of the bank; otherwise one, two for each reservation
that ends after the cursor, and one more when no reservation holds it. -/
def usableNeed (excl : List Span) (stop c : Nat) : Nat :=
  if stop ≤ c then 0
  else 2 * excl.countP (fun x => decide (c < x.endNat)) +
    (if (holdingOf excl c).isEmpty then 1 else 0) + 1

/-- The fuel of `MemoryPlan.availableRanges`, `2 * R + 2`, covers the steps
from any cursor. -/
theorem usableNeed_le (excl : List Span) (stop c : Nat) :
    usableNeed excl stop c ≤ 2 * excl.length + 2 := by
  have := List.countP_le_length (p := fun x : Span => decide (c < x.endNat)) (l := excl)
  unfold usableNeed
  split
  · omega
  · split <;> omega

/-- A cursor before the end of the bank takes a step. -/
theorem usableNeed_pos {excl : List Span} {stop c : Nat} (h : c < stop) :
    0 < usableNeed excl stop c := by
  unfold usableNeed
  rw [ite_eq_right (by omega : ¬ stop ≤ c)]
  omega

theorem ite_isEmpty_le (b : Bool) : (if b = true then 1 else 0) ≤ 1 := by
  cases b <;> simp

/-- The step that gives a usable range leaves fewer steps: the cursor moves
to the end of the range, the end of the bank or the start of a reservation,
which then holds it. -/
theorem usableNeed_free {excl : List Span} {stop c : Nat}
    (hne : ∀ x ∈ excl, x.start.toNat < x.endNat) (hc : c < stop)
    (hh : (holdingOf excl c).isEmpty = true) :
    usableNeed excl stop (nextOf excl stop c) < usableNeed excl stop c := by
  obtain ⟨hn1, -, hn3⟩ := nextOf_spec excl stop c
  by_cases hs : stop ≤ nextOf excl stop c
  · have := usableNeed_pos (excl := excl) hc
    unfold usableNeed
    rw [ite_eq_left hs]
    exact this
  · rcases hn3 with hn3 | ⟨x, hx, hcx, hn3⟩
    · omega
    · have hheld : ¬ (holdingOf excl (nextOf excl stop c)).isEmpty = true := by
        intro h0
        exact holdingOf_empty h0 x hx ⟨by omega, by have := hne x hx; omega⟩
      have hmono : excl.countP (fun x => decide (nextOf excl stop c < x.endNat)) ≤
          excl.countP (fun x => decide (c < x.endNat)) :=
        List.countP_mono_left (fun y _ hy => by
          simp only [decide_eq_true_eq] at hy ⊢
          omega)
      unfold usableNeed
      rw [ite_eq_right hs, ite_eq_right (by omega : ¬ stop ≤ c), ite_eq_right hheld, ite_eq_left hh]
      omega

/-- The step past the reservations that hold the cursor leaves fewer steps:
one of them no longer ends after the cursor. -/
theorem usableNeed_held {excl : List Span} {stop c : Nat} (hc : c < stop)
    (hh : ¬ (holdingOf excl c).isEmpty = true) :
    usableNeed excl stop (min stop (maxEndOf excl c)) < usableNeed excl stop c := by
  obtain ⟨hm1, hm2, -⟩ := maxEndOf_spec excl c
  obtain ⟨y, hy, hy1, hy2⟩ := holdingOf_nonempty hh
  have hyM := hm2 y hy hy1 hy2
  by_cases hs : stop ≤ min stop (maxEndOf excl c)
  · have := usableNeed_pos (excl := excl) hc
    unfold usableNeed
    rw [ite_eq_left hs]
    exact this
  · have hlt : excl.countP (fun x => decide (min stop (maxEndOf excl c) < x.endNat)) <
        excl.countP (fun x => decide (c < x.endNat)) :=
      countP_lt (fun z _ hz => by
        simp only [decide_eq_true_eq] at hz ⊢
        omega) ⟨y, hy, by simp only [decide_eq_true_eq]; omega,
          by simp only [decide_eq_false_iff_not]; omega⟩
    have := ite_isEmpty_le (holdingOf excl (min stop (maxEndOf excl c))).isEmpty
    unfold usableNeed
    rw [ite_eq_right hs, ite_eq_right (by omega : ¬ stop ≤ c), ite_eq_right hh]
    omega

/-- Two fuels that both cover the steps from a cursor give the same usable
ranges. -/
theorem usableFrom_fuel {excl : List Span} {stop : Nat}
    (hne : ∀ x ∈ excl, x.start.toNat < x.endNat) :
    ∀ fuel fuel' c, usableNeed excl stop c ≤ fuel → usableNeed excl stop c ≤ fuel' →
      usableFrom excl stop fuel c = usableFrom excl stop fuel' c
  | 0, fuel', c, h, _ => by
    have hs : stop ≤ c := by
      rcases Nat.lt_or_ge c stop with hs | hs
      · have := usableNeed_pos (excl := excl) hs
        omega
      · exact hs
    cases fuel' with
    | zero => rfl
    | succ f' => rw [usableFrom_succ, ite_eq_left hs]; rfl
  | fuel + 1, 0, c, _, h => by
    have hs : stop ≤ c := by
      rcases Nat.lt_or_ge c stop with hs | hs
      · have := usableNeed_pos (excl := excl) hs
        omega
      · exact hs
    rw [usableFrom_succ, ite_eq_left hs]; rfl
  | fuel + 1, fuel' + 1, c, h, h' => by
    rw [usableFrom_succ, usableFrom_succ]
    by_cases hs : stop ≤ c
    · rw [ite_eq_left hs, ite_eq_left hs]
    · rw [ite_eq_right hs, ite_eq_right hs]
      have hc : c < stop := Nat.lt_of_not_le hs
      by_cases hh : (holdingOf excl c).isEmpty = true
      · rw [ite_eq_left hh, ite_eq_left hh]
        have := usableNeed_free hne hc hh
        rw [usableFrom_fuel hne fuel fuel' _ (by omega) (by omega)]
      · rw [ite_eq_right hh, ite_eq_right hh]
        have := usableNeed_held (excl := excl) hc hh
        exact usableFrom_fuel hne fuel fuel' _ (by omega) (by omega)

/-! ## The usable ranges from a cursor -/

/-- The usable ranges from the cursor `a` in the managed bank of index `k`
on, with the reservations `Rs`: those of bank `k` from the cursor, or from
its start if the cursor lies below it, then those of the banks after it. -/
def availableFrom (M Rs : List Span) (k a : Nat) : List Span :=
  match M.drop k with
  | [] => []
  | b :: bs => usableFrom Rs b.endNat (2 * Rs.length + 2) (max a b.start.toNat) ++
      bs.flatMap fun b => usableFrom Rs b.endNat (2 * Rs.length + 2) b.start.toNat

/-- A measure of the work left from the cursor `a` in the bank of index `k`:
the banks left, each worth more than the steps of one bank, and the steps
left in bank `k`. -/
def availableMeasure (M Rs : List Span) (k a : Nat) : Nat :=
  (M.length - k) * (2 * Rs.length + 3) +
    match M[k]? with
    | none => 0
    | some b => usableNeed Rs b.endNat (max a b.start.toNat)

/-- From the cursor 0, the usable ranges of the banks from `k` on. -/
theorem availableFrom_zero (M Rs : List Span) (k : Nat) :
    availableFrom M Rs k 0 =
      (M.drop k).flatMap fun b => usableFrom Rs b.endNat (2 * Rs.length + 2) b.start.toNat := by
  unfold availableFrom
  split
  · rename_i h; rw [h]; rfl
  · rename_i b bs h; rw [h, List.flatMap_cons, Nat.zero_max]

/-- The usable ranges of a boot memory map are those from the cursor 0 in the
first managed bank. -/
theorem availableRanges_eq (p : MemoryPlan) :
    p.availableRanges = availableFrom p.managed p.reservations 0 0 := by
  rw [availableFrom_zero, List.drop_zero]; rfl

/-- Past the last bank, no usable range. -/
theorem availableFrom_end {M Rs : List Span} {k : Nat} (h : M.length ≤ k) (a : Nat) :
    availableFrom M Rs k a = [] := by
  unfold availableFrom
  rw [List.drop_eq_nil_of_le h]

/-- In bank `b` of index `k`, the usable ranges of `b` from the cursor, then
those of the next banks. -/
theorem availableFrom_cons {M Rs : List Span} {k : Nat} {b : Span} (h : M[k]? = some b)
    (a : Nat) :
    availableFrom M Rs k a =
      usableFrom Rs b.endNat (2 * Rs.length + 2) (max a b.start.toNat) ++
        availableFrom M Rs (k + 1) 0 := by
  obtain ⟨hk, hb⟩ := List.getElem?_eq_some_iff.1 h
  rw [availableFrom_zero]
  unfold availableFrom
  rw [List.drop_eq_getElem_cons hk, hb]

/-- A cursor at or past the end of its bank moves to the start of the next
bank. -/
theorem availableFrom_skip {M Rs : List Span} {k : Nat} {b : Span} (h : M[k]? = some b)
    {a : Nat} (hs : b.endNat ≤ max a b.start.toNat) :
    availableFrom M Rs k a = availableFrom M Rs (k + 1) 0 := by
  rw [availableFrom_cons h, usableFrom_succ, ite_eq_left hs, List.nil_append]

/-- A cursor that reservations hold moves to their furthest end, or to the
end of the bank. -/
theorem availableFrom_held {M Rs : List Span} {k : Nat} {b : Span} (h : M[k]? = some b)
    {a : Nat} (hne : ∀ x ∈ Rs, x.start.toNat < x.endNat) (hc : max a b.start.toNat < b.endNat)
    (hh : ¬ (holdingOf Rs (max a b.start.toNat)).isEmpty = true) :
    availableFrom M Rs k a =
      availableFrom M Rs k (min b.endNat (maxEndOf Rs (max a b.start.toNat))) := by
  have hd := usableNeed_held (excl := Rs) hc hh
  have hle := usableNeed_le Rs b.endNat (max a b.start.toNat)
  have hle' := usableNeed_le Rs b.endNat (min b.endNat (maxEndOf Rs (max a b.start.toNat)))
  have hm := (maxEndOf_spec Rs (max a b.start.toNat)).1
  have hmax : max (min b.endNat (maxEndOf Rs (max a b.start.toNat))) b.start.toNat =
      min b.endNat (maxEndOf Rs (max a b.start.toNat)) := by omega
  rw [availableFrom_cons h, availableFrom_cons h, usableFrom_succ,
    ite_eq_right (Nat.not_le_of_lt hc), ite_eq_right hh, hmax,
    usableFrom_fuel hne (2 * Rs.length + 1) (2 * Rs.length + 2) _ (by omega) (by omega)]

/-- A cursor that no reservation holds gives the usable range up to the
nearest start of a reservation above it, or the end of the bank, and moves to
its end. -/
theorem availableFrom_free {M Rs : List Span} {k : Nat} {b : Span} (h : M[k]? = some b)
    {a : Nat} (hne : ∀ x ∈ Rs, x.start.toNat < x.endNat) (hc : max a b.start.toNat < b.endNat)
    (hh : (holdingOf Rs (max a b.start.toNat)).isEmpty = true) :
    availableFrom M Rs k a =
      spanBetween (max a b.start.toNat) (nextOf Rs b.endNat (max a b.start.toNat)) ::
        availableFrom M Rs k (nextOf Rs b.endNat (max a b.start.toNat)) := by
  have hd := usableNeed_free hne hc hh
  have hle := usableNeed_le Rs b.endNat (max a b.start.toNat)
  have hle' := usableNeed_le Rs b.endNat (nextOf Rs b.endNat (max a b.start.toNat))
  have hn : max a b.start.toNat < nextOf Rs b.endNat (max a b.start.toNat) := by
    obtain ⟨-, -, h3⟩ := nextOf_spec Rs b.endNat (max a b.start.toNat)
    rcases h3 with h3 | ⟨x, -, hx, h3⟩ <;> omega
  have hmax : max (nextOf Rs b.endNat (max a b.start.toNat)) b.start.toNat =
      nextOf Rs b.endNat (max a b.start.toNat) := by omega
  rw [availableFrom_cons h, availableFrom_cons h, usableFrom_succ,
    ite_eq_right (Nat.not_le_of_lt hc), ite_eq_left hh, hmax,
    usableFrom_fuel hne (2 * Rs.length + 1) (2 * Rs.length + 2) _ (by omega) (by omega),
    List.cons_append]

/-- The move to the next bank decreases the measure. -/
theorem availableMeasure_skip {M Rs : List Span} {k : Nat} {b : Span} (h : M[k]? = some b)
    (a : Nat) : availableMeasure M Rs (k + 1) 0 < availableMeasure M Rs k a := by
  have hk := (List.getElem?_eq_some_iff.1 h).1
  have e : M.length - k = (M.length - (k + 1)) + 1 := by omega
  unfold availableMeasure
  rw [e, Nat.add_mul, Nat.one_mul]
  split
  · omega
  · rename_i b' _
    have := usableNeed_le Rs b'.endNat (max 0 b'.start.toNat)
    omega

/-- The move past the reservations that hold the cursor decreases the
measure. -/
theorem availableMeasure_held {M Rs : List Span} {k : Nat} {b : Span} (h : M[k]? = some b)
    {a : Nat} (hc : max a b.start.toNat < b.endNat)
    (hh : ¬ (holdingOf Rs (max a b.start.toNat)).isEmpty = true) :
    availableMeasure M Rs k (min b.endNat (maxEndOf Rs (max a b.start.toNat))) <
      availableMeasure M Rs k a := by
  have hd := usableNeed_held (excl := Rs) hc hh
  have hm := (maxEndOf_spec Rs (max a b.start.toNat)).1
  have hmax : max (min b.endNat (maxEndOf Rs (max a b.start.toNat))) b.start.toNat =
      min b.endNat (maxEndOf Rs (max a b.start.toNat)) := by omega
  unfold availableMeasure
  rw [h]
  simp only
  rw [hmax]
  omega

/-! ## The reservations that hold a cursor -/

/-- One reservation `r` in the search for those that hold the cursor `c`:
none so far, or the furthest end so far. -/
def holdStep (c : Nat) (acc : Option Nat) (r : Span) : Option Nat :=
  if r.start.toNat ≤ c then
    if c < r.endNat then
      match acc with
      | some e => if e < r.endNat then some r.endNat else some e
      | none => some r.endNat
    else acc
  else acc

/-- The furthest end so far, with the end of one more reservation that holds
the cursor. -/
def maxStep (acc : Option Nat) (r : Span) : Option Nat :=
  some (match acc with
    | none => r.endNat
    | some e => max e r.endNat)

/-- The search runs over the reservations that hold the cursor. -/
theorem foldl_holdStep_filter (c : Nat) : ∀ (l : List Span) (acc : Option Nat),
    l.foldl (holdStep c) acc = (holdingOf l c).foldl maxStep acc
  | [], _ => rfl
  | r :: l, acc => by
    have ih := foldl_holdStep_filter c l
    unfold holdingOf at ih ⊢
    rw [List.filter_cons, List.foldl_cons]
    by_cases hr : r.start.toNat ≤ c ∧ c < r.endNat
    · have hb : (decide (r.start.toNat ≤ c) && decide (c < r.endNat)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hr
      rw [ite_eq_left hb, List.foldl_cons, ← ih]
      congr 1
      simp only [holdStep, hr.1, hr.2, ↓reduceIte, maxStep]
      cases acc with
      | none => rfl
      | some e =>
        simp only
        by_cases he : e < r.endNat
        · rw [ite_eq_left he, Nat.max_eq_right (Nat.le_of_lt he)]
        · rw [ite_eq_right he, Nat.max_eq_left (Nat.le_of_not_lt he)]
    · have hb : ¬ (decide (r.start.toNat ≤ c) && decide (c < r.endNat)) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hr
      rw [ite_eq_right hb, ← ih]
      congr 1
      unfold holdStep
      by_cases h1 : r.start.toNat ≤ c
      · rw [ite_eq_left h1, ite_eq_right (fun h2 => hr ⟨h1, h2⟩)]
      · rw [ite_eq_right h1]

theorem foldl_maxStep_some : ∀ (l : List Span) (e : Nat),
    l.foldl maxStep (some e) = some (l.foldl (fun e r => max e r.endNat) e)
  | [], _ => rfl
  | r :: l, e => by
    rw [List.foldl_cons, List.foldl_cons, ← foldl_maxStep_some l]
    rfl

/-- The search gives none when no reservation holds the cursor, and
otherwise their furthest end. -/
theorem foldl_holdStep (c : Nat) (l : List Span) :
    l.foldl (holdStep c) none =
      if (holdingOf l c).isEmpty then none else some (maxEndOf l c) := by
  rw [foldl_holdStep_filter]
  unfold maxEndOf
  cases hh : holdingOf l c with
  | nil => rfl
  | cons r t =>
    have hr : r ∈ holdingOf l c := by rw [hh]; exact List.mem_cons_self
    have hc := (mem_holdingOf.1 hr).2.2
    rw [List.foldl_cons, List.foldl_cons]
    simp only [maxStep, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
    rw [foldl_maxStep_some, Nat.max_eq_right (Nat.le_of_lt hc)]

end Krepi.Proofs.Fdt.Refinement
