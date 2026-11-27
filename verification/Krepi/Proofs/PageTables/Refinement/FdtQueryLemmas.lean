module

public import Krepi.Statements.PageTables.Representation
public import Krepi.Proofs.PageTables.Refinement.BasicLemmas
public import Krepi.Proofs.Fdt.Refinement.PlanQuerySpecLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: refinement of the queries of the boot memory map

The page-tables translation holds its own copy of the eight functions of the
`fdt` component that `direct_map` reaches: `fdt::span::prefix`,
`MemoryPlan::managed_banks`, `MemoryPlan::reservations`,
`MemoryPlan::available_ranges`, and the iterator of the usable ranges,
`AvailableRanges::next` with `available_step`, `nearest_start` and
`furthest_holding` and their loops. Their code is that of the `fdt`
extraction, so their triples here are those of
`Krepi.Proofs.Fdt.Refinement.PlanQueryLemmas` (with what they need of
`SpanLemmas` and `AccessorLemmas`) over this translation and the
representation `spanOf`, `MemoryPlanRepr` of
`Krepi.Statements.PageTables.Representation`, for every input under the
premises of the `fdt` triples:

- the spans of the specification of the code's spans: `spansOf`, `SpanRepr`,
  `spanOf_start`, `spanOf_size`, `spanOf_endNat`, `spanOf_valid_iff`;
- the lists of the boot memory map: `prefix_spec`,
  `memory_plan_managed_banks_spec` and `memory_plan_reservations_spec`;
- the iterator: the loops `furthest_holding_spec` and `nearest_start_spec`,
  the loop of one step `available_step_loop_spec` and
  `available_step_spec`, `available_ranges_next_spec` (one call of
  `AvailableRanges::next`), `available_ranges_next_end` (its fixed point
  past the last bank), `available_ranges_stands` (an iterator stands for the
  usable ranges from its cursor, `availableFrom`) and
  `available_ranges_spec` (`MemoryPlan::available_ranges` stands for the
  usable ranges of a well-formed map).

The module imports the generated definitions of the page-tables target
alone; the spec-side lemmas come from
`Krepi.Proofs.Fdt.Refinement.PlanQuerySpecLemmas`, which imports none.
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.PageTables Krepi.Spec.Fdt Krepi.Statements Krepi.Statements.PageTables
open Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

/-! ## Spans -/

/-- The spans of the specification of a slice of spans of the code. -/
def spansOf (s : Slice fdt.Span) : List Span := s.val.map spanOf

/-- A span of the code stands for its span of the specification. -/
def SpanRepr (s : fdt.Span) (t : Span) : Prop := spanOf s = t

@[simp] theorem spanOf_start (s : fdt.Span) : (spanOf s).start = word64 s.start := rfl

@[simp] theorem spanOf_size (s : fdt.Span) : (spanOf s).size = word64 s.size := rfl

theorem spanOf_endNat (s : fdt.Span) : (spanOf s).endNat = s.start.val + s.size.val := by
  simp only [Span.endNat, spanOf_start, spanOf_size, word64_toNat]

theorem spanOf_valid_iff (s : fdt.Span) :
    (spanOf s).Valid ↔ s.start.val + s.size.val < 2 ^ 64 := by
  simp only [Span.Valid, Span.endNat, spanOf, word64_toNat]

/-! ## The lists of the boot memory map -/

/-- `prefix(items, count)`: the first `count` items. -/
@[step] theorem prefix_spec {T : Type} (items : Slice T) (count : Usize)
    (h : count.val ≤ items.length) :
    fdt.span.prefix items count ⦃ s => s.val = items.val.take count.val ⦄ := by
  unfold fdt.span.prefix
  step*
  simp [s_post, List.slice]

/-- `MemoryPlan::managed_banks()`: the managed banks. -/
@[step] theorem memory_plan_managed_banks_spec {p : fdt.MemoryPlan} {P : MemoryPlan}
    (h : MemoryPlanRepr p P) :
    fdt.plan.MemoryPlan.managed_banks p ⦃ s => spansOf s = P.managedBanks ⦄ := by
  obtain ⟨-, h2, -, -, rfl⟩ := h
  unfold fdt.plan.MemoryPlan.managed_banks
  step*
  · simp only [s_post, Array.length_to_slice]; exact h2
  · subst_vars; simp only [spansOf, s_post, Array.val_to_slice, MemoryPlan.managedBanks]

/-- `MemoryPlan::reservations()`: the boot storage and then the firmware
reservations, the first `reserved_count` entries of the array. -/
@[step] theorem memory_plan_reservations_spec {p : fdt.MemoryPlan} {P : MemoryPlan}
    (h : MemoryPlanRepr p P) :
    fdt.plan.MemoryPlan.reservations p ⦃ s => spansOf s = P.reservations ⦄ := by
  obtain ⟨-, -, h3, h4, rfl⟩ := h
  unfold fdt.plan.MemoryPlan.reservations
  step*
  · simp only [s_post, Array.length_to_slice, MemoryPlan.MAX_BOOT_SPANS,
      MemoryPlan.MAX_FIRMWARE] at h4 ⊢
    scalar_tac
  · subst_vars
    have e : List.take p.boot_count.val p.reserved.val =
        List.take p.boot_count.val (List.take p.reserved_count.val p.reserved.val) := by
      rw [List.take_take, Nat.min_eq_left h3]
    simp only [spansOf, s_post, Array.val_to_slice, MemoryPlan.reservations, ← List.map_append, e,
      List.take_append_drop]

/-! ## The iterator of the usable ranges -/

/-- `furthest_holding(reservations, at)`: the furthest end of the reservations
that hold `at`, none when none does (`foldl_holdStep`), for reservations
within 64 bits. -/
@[step] theorem furthest_holding_spec (reservations : Slice fdt.Span) (pos : U64)
    (hv : ∀ r ∈ spansOf reservations, r.Valid) :
    fdt.plan.available.furthest_holding reservations pos ⦃ o =>
      o.map (·.val) = (spansOf reservations).foldl (holdStep pos.val) none ⦄ := by
  unfold fdt.plan.available.furthest_holding fdt.plan.available.furthest_holding_loop
  step with loop.spec_decr_nat
    (measure := fun (x : Bool × U64 × Usize) => reservations.length - x.2.2.val)
    (inv := fun (x : Bool × U64 × Usize) =>
      ((spansOf reservations).drop x.2.2.val).foldl (holdStep pos.val)
          (if x.1 then some x.2.1.val else none) =
        (spansOf reservations).foldl (holdStep pos.val) none)
    (post := fun (y : Bool × U64) =>
      (if y.1 then some y.2.val else none) = (spansOf reservations).foldl (holdStep pos.val) none)
  · rintro ⟨held, e, i⟩ hinv
    simp only at hinv
    unfold fdt.plan.available.furthest_holding_loop.body
    have hl : (spansOf reservations).length = reservations.length := List.length_map _
    step*
    · have hi : i.val < (spansOf reservations).length := by rw [hl]; scalar_tac
      have hm : spanOf reservation ∈ spansOf reservations := by
        rw [reservation_post]; exact List.mem_map_of_mem (List.getElem_mem _)
      have := (spanOf_valid_iff reservation).1 (hv _ hm)
      rw [u64_max_eq]
      omega
    · have hi : i.val < (spansOf reservations).length := by rw [hl]; scalar_tac
      have e1 : (spansOf reservations)[i.val] = spanOf reservation := by
        simp only [spansOf, List.getElem_map, reservation_post]
      rw [List.drop_eq_getElem_cons hi, e1, List.foldl_cons] at hinv
      have hs : (spanOf reservation).start.toNat = reservation.start.val := by simp
      have he : (spanOf reservation).endNat = reservation_end.val := by
        rw [spanOf_endNat, reservation_end_post]
      simp only [holdStep, hs, he] at hinv
      simp only [UScalar.le_equiv, UScalar.lt_equiv, gt_iff_lt]
      by_cases h1 : reservation.start.val ≤ pos.val
      · by_cases h2 : pos.val < reservation_end.val
        · cases held
          · simp only [h1, h2, ↓reduceIte, Bool.false_eq_true] at hinv ⊢
            step*
          · by_cases h3 : e.val < reservation_end.val
            · simp only [h1, h2, h3, ↓reduceIte] at hinv ⊢
              step*
            · simp only [h1, h2, h3, ↓reduceIte] at hinv ⊢
              step*
        · simp only [h1, h2, ↓reduceIte] at hinv ⊢
          step*
      · simp only [h1, ↓reduceIte] at hinv ⊢
        step*
    · rw [List.drop_eq_nil_of_le (by rw [hl]; scalar_tac), List.foldl_nil] at hinv
      exact hinv
  · rfl
  · rw [← held_post]
    cases held <;> simp only [Bool.false_eq_true, ↓reduceIte, spec_ok, Option.map_none,
      Option.map_some]

/-- `nearest_start(reservations, at, stop)`: `nextOf`, the nearest start of a
reservation above `at`, or `stop`. -/
@[step] theorem nearest_start_spec (reservations : Slice fdt.Span) (pos stop : U64) :
    fdt.plan.available.nearest_start reservations pos stop ⦃ n =>
      n.val = Krepi.Proofs.Fdt.nextOf (spansOf reservations) stop.val pos.val ⦄ := by
  unfold fdt.plan.available.nearest_start fdt.plan.available.nearest_start_loop
  apply loop.spec_decr_nat
    (measure := fun (x : U64 × Usize) => reservations.length - x.2.val)
    (inv := fun (x : U64 × Usize) =>
      ((spansOf reservations).drop x.2.val).foldl
          (fun e r => if pos.val < r.start.toNat then min e r.start.toNat else e) x.1.val =
        Krepi.Proofs.Fdt.nextOf (spansOf reservations) stop.val pos.val)
  · rintro ⟨nearest, i⟩ hinv
    simp only at hinv
    unfold fdt.plan.available.nearest_start_loop.body
    have hl : (spansOf reservations).length = reservations.length := List.length_map _
    step*
    · have hi : i.val < (spansOf reservations).length := by rw [hl]; scalar_tac
      have e1 : (spansOf reservations)[i.val] = spanOf s := by
        simp only [spansOf, List.getElem_map, s_post]
      have hs : (spanOf s).start.toNat = s.start.val := by simp
      rw [List.drop_eq_getElem_cons hi, e1, List.foldl_cons, hs] at hinv
      simp only [UScalar.lt_equiv]
      by_cases h1 : pos.val < s.start.val
      · by_cases h2 : s.start.val < nearest.val
        · simp only [h1, h2, ↓reduceIte, Nat.min_eq_right (Nat.le_of_lt h2)] at hinv ⊢
          step*
        · simp only [h1, h2, ↓reduceIte, Nat.min_eq_left (Nat.le_of_not_lt h2)] at hinv ⊢
          step*
      · simp only [h1, ↓reduceIte] at hinv ⊢
        step*
    · rw [List.drop_eq_nil_of_le (by rw [hl]; scalar_tac), List.foldl_nil] at hinv
      exact hinv
  · rfl

/-- The loop of `available_step(managed, reservations, cursor)`, for managed
banks within 64 bits and nonempty reservations: none when the usable ranges
from the cursor are none, with the cursor past the last bank; otherwise the
first of them, and a cursor from which the others follow. -/
@[step] theorem available_step_loop_spec (managed reservations : Slice fdt.Span)
    (hm : ∀ b ∈ spansOf managed, b.Valid) (hr : ∀ r ∈ spansOf reservations, r.Nonempty)
    (cursor : fdt.Cursor) :
    fdt.plan.available.available_step_loop managed reservations cursor ⦃ y =>
      match y.2.2 with
      | none =>
        availableFrom (spansOf managed) (spansOf reservations) cursor.bank.val cursor.at.val = [] ∧
          managed.length ≤ y.1.val
      | some r =>
        availableFrom (spansOf managed) (spansOf reservations) cursor.bank.val cursor.at.val =
          spanOf r ::
            availableFrom (spansOf managed) (spansOf reservations) y.1.val y.2.1.val ⦄ := by
  unfold fdt.plan.available.available_step_loop
  apply loop.spec_decr_nat
    (measure := fun (x : fdt.Cursor) =>
      availableMeasure (spansOf managed) (spansOf reservations) x.bank.val x.at.val)
    (inv := fun (x : fdt.Cursor) =>
      availableFrom (spansOf managed) (spansOf reservations) x.bank.val x.at.val =
        availableFrom (spansOf managed) (spansOf reservations) cursor.bank.val cursor.at.val)
  · intro x hinv
    unfold fdt.plan.available.available_step_loop.body
    have hl : (spansOf managed).length = managed.length := List.length_map _
    have hne : ∀ r ∈ spansOf reservations, r.start.toNat < r.endNat :=
      fun r h => Krepi.Proofs.Fdt.nonempty_lt (hr r h)
    step*
    · have hk : spanOf bank ∈ spansOf managed := by
        rw [bank_post]; exact List.mem_map_of_mem (List.getElem_mem _)
      have := (spanOf_valid_iff bank).1 (hm _ hk)
      rw [u64_max_eq]
      omega
    · have hk : (spansOf managed)[x.bank.val]? = some (spanOf bank) := by
        rw [List.getElem?_eq_some_iff]
        exact ⟨by rw [hl]; scalar_tac, by simp only [spansOf, List.getElem_map, bank_post]⟩
      have hb0 : (spanOf bank).start.toNat = bank.start.val := by simp
      have hstop : (spanOf bank).endNat = stop.val := by rw [spanOf_endNat, stop_post]
      have hat : (if x.at > bank.start then ok x.at else ok bank.start : Result U64) =
          ok (if x.at > bank.start then x.at else bank.start) := by split <;> rfl
      rw [hat]
      generalize hA : (if x.at > bank.start then x.at else bank.start) = a
      have hc0 : max x.at.val (spanOf bank).start.toNat = a.val := by
        rw [hb0, ← hA]
        split
        · rename_i h; rw [gt_iff_lt, UScalar.lt_equiv] at h; omega
        · rename_i h; rw [gt_iff_lt, UScalar.lt_equiv] at h; omega
      step*
      · have hs : (spanOf bank).endNat ≤ max x.at.val (spanOf bank).start.toNat := by
          have := ‹a ≥ stop›
          rw [ge_iff_le, UScalar.le_equiv] at this
          rw [hc0, hstop]; exact this
        have h0 : (0#u64).val = 0 := rfl
        rw [h0, i1_post]
        exact ⟨by rw [← hinv, availableFrom_skip hk hs], availableMeasure_skip hk _⟩
      · exact fun r h => (hr r h).2
      · have := ‹¬a ≥ stop›
        rw [ge_iff_le, UScalar.le_equiv] at this
        obtain ⟨-, -, h3⟩ := Krepi.Proofs.Fdt.nextOf_spec (spansOf reservations) stop.val a.val
        rw [end_post]
        rcases h3 with h3 | ⟨y, -, hy, h3⟩ <;> omega
      · have hc : max x.at.val (spanOf bank).start.toNat < (spanOf bank).endNat := by
          have := ‹¬a ≥ stop›
          rw [ge_iff_le, UScalar.le_equiv] at this
          rw [hc0, hstop]; omega
        have hh : (Krepi.Proofs.Fdt.holdingOf (spansOf reservations) a.val).isEmpty = true := by
          rw [‹o = none›, Option.map_none, foldl_holdStep] at o_post
          cases hE : (Krepi.Proofs.Fdt.holdingOf (spansOf reservations) a.val).isEmpty
          · simp only [hE, Bool.false_eq_true, ↓reduceIte] at o_post
            cases o_post
          · rfl
        have hF := availableFrom_free hk hne hc (by rw [hc0]; exact hh)
        rw [hc0, hstop] at hF
        rw [← hinv, hF, ← end_post]
        simp only [spanOf, spanBetween, word64, i1_post]
      · have hc : max x.at.val (spanOf bank).start.toNat < (spanOf bank).endNat := by
          have := ‹¬a ≥ stop›
          rw [ge_iff_le, UScalar.le_equiv] at this
          rw [hc0, hstop]; omega
        obtain ⟨hh, he⟩ :
            ¬ (Krepi.Proofs.Fdt.holdingOf (spansOf reservations) a.val).isEmpty = true ∧
              «end».val = Krepi.Proofs.Fdt.maxEndOf (spansOf reservations) a.val := by
          rw [‹o = some «end»›, Option.map_some, foldl_holdStep] at o_post
          cases hE : (Krepi.Proofs.Fdt.holdingOf (spansOf reservations) a.val).isEmpty
          · simp only [hE, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at o_post
            exact ⟨Bool.false_ne_true, o_post⟩
          · simp only [hE, ↓reduceIte] at o_post
            cases o_post
        have hmin : min (spanOf bank).endNat
            (Krepi.Proofs.Fdt.maxEndOf (spansOf reservations)
              (max x.at.val (spanOf bank).start.toNat)) =
            «end».val := by
          have := ‹«end» < stop›
          rw [UScalar.lt_equiv] at this
          rw [hc0, hstop, ← he]; omega
        have hH := availableFrom_held hk hne hc (by rw [hc0]; exact hh)
        have hM := availableMeasure_held hk hc (by rw [hc0]; exact hh)
        rw [hmin] at hH hM
        exact ⟨by rw [← hinv, hH], hM⟩
      · have hc : max x.at.val (spanOf bank).start.toNat < (spanOf bank).endNat := by
          have := ‹¬a ≥ stop›
          rw [ge_iff_le, UScalar.le_equiv] at this
          rw [hc0, hstop]; omega
        obtain ⟨hh, he⟩ :
            ¬ (Krepi.Proofs.Fdt.holdingOf (spansOf reservations) a.val).isEmpty = true ∧
              «end».val = Krepi.Proofs.Fdt.maxEndOf (spansOf reservations) a.val := by
          rw [‹o = some «end»›, Option.map_some, foldl_holdStep] at o_post
          cases hE : (Krepi.Proofs.Fdt.holdingOf (spansOf reservations) a.val).isEmpty
          · simp only [hE, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at o_post
            exact ⟨Bool.false_ne_true, o_post⟩
          · simp only [hE, ↓reduceIte] at o_post
            cases o_post
        have hmin : min (spanOf bank).endNat
            (Krepi.Proofs.Fdt.maxEndOf (spansOf reservations)
              (max x.at.val (spanOf bank).start.toNat)) =
            stop.val := by
          have := ‹¬«end» < stop›
          rw [UScalar.lt_equiv] at this
          rw [hc0, hstop, ← he]; omega
        have hH := availableFrom_held hk hne hc (by rw [hc0]; exact hh)
        have hM := availableMeasure_held hk hc (by rw [hc0]; exact hh)
        rw [hmin] at hH hM
        exact ⟨by rw [← hinv, hH], hM⟩
    · exact ⟨by rw [← hinv, availableFrom_end (by rw [hl]; scalar_tac)], by scalar_tac⟩
  · rfl

/-- `available_step(managed, reservations, cursor)`: the loop, with its
cursor. -/
@[step] theorem available_step_spec (managed reservations : Slice fdt.Span)
    (hm : ∀ b ∈ spansOf managed, b.Valid) (hr : ∀ r ∈ spansOf reservations, r.Nonempty)
    (cursor : fdt.Cursor) :
    fdt.plan.available.available_step managed reservations cursor ⦃ c o =>
      match o with
      | none =>
        availableFrom (spansOf managed) (spansOf reservations) cursor.bank.val cursor.at.val = [] ∧
          managed.length ≤ c.bank.val
      | some r =>
        availableFrom (spansOf managed) (spansOf reservations) cursor.bank.val cursor.at.val =
          spanOf r ::
            availableFrom (spansOf managed) (spansOf reservations) c.bank.val c.at.val ⦄ := by
  unfold fdt.plan.available.available_step
  step*

/-- One turn of the loop of `available_step` past the last bank gives none and
the same cursor. -/
theorem available_step_loop_body_end (managed reservations : Slice fdt.Span) (cursor : fdt.Cursor)
    (h : managed.length ≤ cursor.bank.val) :
    fdt.plan.available.available_step_loop.body managed reservations cursor =
      .ok (.done (cursor.bank, cursor.at, none)) := by
  unfold fdt.plan.available.available_step_loop.body
  have hc : ¬ cursor.bank < managed.len := by scalar_tac
  simp only [hc, ↓reduceIte]

/-- `AvailableRanges::next()` past the last bank gives none and the same
iterator: the fixed point at the end of the list. -/
theorem available_ranges_next_end (it : fdt.AvailableRanges)
    (h : it.managed.length ≤ it.cursor.bank.val) :
    fdt.plan.available.AvailableRanges.next it = .ok (none, it) := by
  unfold fdt.plan.available.AvailableRanges.next fdt.plan.available.available_step
    fdt.plan.available.available_step_loop
  rw [loop, available_step_loop_body_end _ _ _ h]
  simp only [bind_ok, uncurry_apply_pair]

/-- `AvailableRanges::next()`, for managed banks within 64 bits and nonempty
reservations: the slices stay; none when the usable ranges from the cursor
are none, with the cursor past the last bank; otherwise the first of them,
and a cursor from which the others follow. -/
@[step] theorem available_ranges_next_spec (it : fdt.AvailableRanges)
    (hm : ∀ b ∈ spansOf it.managed, b.Valid) (hr : ∀ r ∈ spansOf it.reservations, r.Nonempty) :
    fdt.plan.available.AvailableRanges.next it ⦃ o it' =>
      it'.managed = it.managed ∧ it'.reservations = it.reservations ∧
      match o with
      | none =>
        availableFrom (spansOf it.managed) (spansOf it.reservations) it.cursor.bank.val
            it.cursor.at.val = [] ∧
          it.managed.length ≤ it'.cursor.bank.val
      | some r =>
        availableFrom (spansOf it.managed) (spansOf it.reservations) it.cursor.bank.val
            it.cursor.at.val =
          spanOf r :: availableFrom (spansOf it.managed) (spansOf it.reservations)
            it'.cursor.bank.val it'.cursor.at.val ⦄ := by
  unfold fdt.plan.available.AvailableRanges.next
  step*

/-- An iterator over managed banks within 64 bits and nonempty reservations
stands for the usable ranges from its cursor: `stands_of_sim` with the
relation that `available_ranges_next_spec` keeps. -/
theorem available_ranges_stands (managed reservations : Slice fdt.Span)
    (hm : ∀ b ∈ spansOf managed, b.Valid) (hr : ∀ r ∈ spansOf reservations, r.Nonempty) :
    ∀ (l : List Span) (it : fdt.AvailableRanges), it.managed = managed →
      it.reservations = reservations →
      l = availableFrom (spansOf managed) (spansOf reservations) it.cursor.bank.val
        it.cursor.at.val →
      Stands fdt.plan.available.AvailableRanges.next SpanRepr it l := by
  intro l it h1 h2 h3
  refine stands_of_sim (fun s l => s.managed = managed ∧ s.reservations = reservations ∧
      l = availableFrom (spansOf managed) (spansOf reservations) s.cursor.bank.val s.cursor.at.val)
    ?_ ?_ l it ⟨h1, h2, h3⟩
  · rintro s ⟨e1, e2, e3⟩
    subst e1 e2
    refine spec_mono (available_ranges_next_spec s hm hr) ?_
    rintro ⟨o, s'⟩ ⟨f1, f2, ho⟩
    cases o with
    | none => exact ⟨rfl, available_ranges_next_end s' (by rw [f1]; exact ho.2)⟩
    | some r => rw [← e3] at ho; cases ho
  · rintro s b l ⟨e1, e2, e3⟩
    subst e1 e2
    refine spec_mono (available_ranges_next_spec s hm hr) ?_
    rintro ⟨o, s'⟩ ⟨f1, f2, ho⟩
    cases o with
    | none => rw [← e3] at ho; cases ho.1
    | some r =>
      simp only [← e3, List.cons.injEq] at ho
      exact ⟨r, rfl, ho.1.symm, f1, f2, ho.2⟩

/-- `MemoryPlan::available_ranges()`, for a map that stands for a
well-formed boot memory map: the slices of its managed banks and of its
reservations, the cursor at the start, and an iterator that stands for the
usable ranges. -/
@[step] theorem available_ranges_spec {p : fdt.MemoryPlan} {P : MemoryPlan}
    (h : MemoryPlanRepr p P) (hw : P.WellFormed) :
    fdt.plan.MemoryPlan.available_ranges p ⦃ it =>
      spansOf it.managed = P.managed ∧ spansOf it.reservations = P.reservations ∧
        it.cursor.bank.val = 0 ∧ it.cursor.at.val = 0 ∧
        Stands fdt.plan.available.AvailableRanges.next SpanRepr it P.availableRanges ⦄ := by
  unfold fdt.plan.MemoryPlan.available_ranges
  step*
  have hman := hw.2.2.2.2.2.2.1
  refine ⟨s_post, s1_post, rfl, rfl, available_ranges_stands s s1 ?_ ?_ _ _ rfl rfl ?_⟩
  · rw [s_post, MemoryPlan.managedBanks]
    exact fun b hb => (hman b hb).1.2
  · rw [s1_post]
    exact fun r hr => (Krepi.Proofs.Fdt.reservations_wf hw r hr).1
  · rw [availableRanges_eq, s_post, s1_post, MemoryPlan.managedBanks]
    rfl

end Krepi.Proofs.PageTables.Refinement
