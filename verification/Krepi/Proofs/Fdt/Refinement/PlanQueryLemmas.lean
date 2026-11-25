module

public import Krepi.Proofs.Fdt.Refinement.AccessorLemmas
public import Krepi.Proofs.Fdt.Refinement.PlanQuerySpecLemmas

/-!
# Device tree: refinement of the queries of the boot memory map

The triples of the generated queries of a boot memory map and of the
iterator of its usable ranges, each a `@[step]` lemma under the
representation of the map, so that the proof of a caller steps over the call
with the triple of the callee:

- the sums: `sum_sizes_spec`, `described_bytes_spec` and
  `managed_bytes_spec`, the last two the statements `MemoryPlanDescribedBytes`
  and `MemoryPlanManagedBytes` without their premise `Usize64`;
- the tests of a range: `contains_ram_spec`, `is_available_spec` and
  `permits_backing_spec`, the statements `MemoryPlanContainsRam`,
  `MemoryPlanIsAvailable` and `MemoryPlanPermitsBacking` without `Usize64`
  and the well-formedness of the map, which they do not need;
- the iterator: the loops `furthest_holding_spec` and `nearest_start_spec`,
  the loop of one step `available_step_loop_spec` and `available_step_spec`,
  `available_ranges_next_spec` (one call of `AvailableRanges::next`),
  `available_ranges_next_end` (its fixed point past the last bank),
  `available_ranges_stands` (an iterator stands for the usable ranges from
  its cursor, `availableFrom`), and `available_ranges_spec`, the statement
  `MemoryPlanAvailableRanges` without its premise `Usize64`.

The cursor of the iterator walks the managed banks with no fuel, where the
specification gives each bank `2 * R + 2` steps for `R` reservations;
`usableFrom_fuel` of `Krepi.Proofs.Fdt.Refinement.PlanQuerySpecLemmas` shows
that this fuel covers every cursor, so the two agree.
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.Fdt Krepi.Spec.Fdt Krepi.Statements Krepi.Statements.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## The sums and the tests of a range -/

/-- `sum_sizes(spans)`: the exact sum of the sizes, for spans whose sum does not
leave 64 bits. -/
@[step] theorem sum_sizes_spec (spans : Slice fdt.Span) (h : spansBytes (spansOf spans) < 2 ^ 64) :
    fdt.plan.sum_sizes spans ⦃ n => n.val = spansBytes (spansOf spans) ⦄ := by
  unfold fdt.plan.sum_sizes fdt.plan.sum_sizes_loop
  apply loop.spec_decr_nat
    (measure := fun (x : U64 × Usize) => spans.length - x.2.val)
    (inv := fun (x : U64 × Usize) =>
      ((spansOf spans).drop x.2.val).foldl (fun sum s => sum + s.size.toNat) x.1.val =
        spansBytes (spansOf spans))
  · rintro ⟨sum, i⟩ hinv
    simp only at hinv
    unfold fdt.plan.sum_sizes_loop.body
    have hl : (spansOf spans).length = spans.length := List.length_map _
    step*
    · have hi : i.val < (spansOf spans).length := by rw [hl]; scalar_tac
      have e : (spansOf spans)[i.val] = spanOf s := by simp only [spansOf, List.getElem_map, s_post]
      rw [List.drop_eq_getElem_cons hi, e, List.foldl_cons, spanOf_size, word64_toNat] at hinv
      have := foldl_size_ge ((spansOf spans).drop (i.val + 1)) (sum.val + s.size.val)
      rw [u64_max_eq]
      omega
    · have hi : i.val < (spansOf spans).length := by rw [hl]; scalar_tac
      have e : (spansOf spans)[i.val] = spanOf s := by simp only [spansOf, List.getElem_map, s_post]
      rw [List.drop_eq_getElem_cons hi, e, List.foldl_cons, spanOf_size, word64_toNat] at hinv
      rw [sum1_post, index1_post]
      exact ⟨hinv, by scalar_tac⟩
    · rw [List.drop_eq_nil_of_le (by rw [hl]; scalar_tac), List.foldl_nil] at hinv
      exact hinv
  · rfl

/-- `MemoryPlan::contains_ram(range)`: `MemoryPlan.containsRam`. -/
@[step] theorem contains_ram_spec {p : fdt.MemoryPlan} {P : MemoryPlan} (h : MemoryPlanRepr p P)
    (range : fdt.Span) :
    fdt.plan.MemoryPlan.contains_ram p range ⦃ b => b = P.containsRam (spanOf range) ⦄ := by
  unfold fdt.plan.MemoryPlan.contains_ram
  step*
  · subst_vars
    simp only [MemoryPlan.containsRam, s_post, spanOf_size, word64_bne_zero,
      ‹(range.size != 0#u64) = true›, ‹decide (spanOf range).Valid = true›, Bool.true_and]
  · subst_vars
    simp only [MemoryPlan.containsRam,
      (Bool.not_eq_true _).mp ‹¬decide (spanOf range).Valid = true›, Bool.and_false, Bool.false_and]
  · simp only [MemoryPlan.containsRam, spanOf_size, word64_bne_zero,
      (Bool.not_eq_true _).mp ‹¬(range.size != 0#u64) = true›, Bool.false_and]

/-- `MemoryPlan::is_available(range)`: `MemoryPlan.isAvailable`. -/
@[step] theorem is_available_spec {p : fdt.MemoryPlan} {P : MemoryPlan} (h : MemoryPlanRepr p P)
    (range : fdt.Span) :
    fdt.plan.MemoryPlan.is_available p range ⦃ b => b = P.isAvailable (spanOf range) ⦄ := by
  unfold fdt.plan.MemoryPlan.is_available
  step*
  · subst_vars
    simp only [MemoryPlan.isAvailable, ← s_post, ‹P.containsRam (spanOf range) = true›, decide_not,
      Bool.decide_eq_true, Bool.true_and]
  · subst_vars
    simp only [MemoryPlan.isAvailable,
      (Bool.not_eq_true _).mp ‹¬P.containsRam (spanOf range) = true›, Bool.false_and]

/-- `MemoryPlan::permits_backing(range)`: `MemoryPlan.permitsBacking`. -/
@[step] theorem permits_backing_spec {p : fdt.MemoryPlan} {P : MemoryPlan}
    (h : MemoryPlanRepr p P) (range : fdt.Span) :
    fdt.plan.MemoryPlan.permits_backing p range ⦃ b => b = P.permitsBacking (spanOf range) ⦄ := by
  unfold fdt.plan.MemoryPlan.permits_backing
  step*
  · subst_vars
    have hb := ‹inOneRange (spansOf s) (spanOf range) = true›
    rw [s_post, MemoryPlan.managedBanks] at hb
    simp only [MemoryPlan.permitsBacking, hb, Bool.true_and]
  · subst_vars
    have hb := (Bool.not_eq_true _).mp ‹¬inOneRange (spansOf s) (spanOf range) = true›
    rw [s_post, MemoryPlan.managedBanks] at hb
    simp only [MemoryPlan.permitsBacking, hb, Bool.false_and]

/-- `MemoryPlan::described_bytes()`: the sum of the banks, which a well-formed
map keeps within 16 GiB. -/
@[step] theorem described_bytes_spec {p : fdt.MemoryPlan} {P : MemoryPlan}
    (h : MemoryPlanRepr p P) (hw : P.WellFormed) :
    fdt.plan.MemoryPlan.described_bytes p ⦃ n => word64 n = P.describedBytes ⦄ := by
  unfold fdt.plan.MemoryPlan.described_bytes
  step*
  · obtain ⟨-, -, -, -, hb, -⟩ := hw
    rw [s_post]
    unfold MemoryPlan.MAX_RAM_BYTES at hb
    omega
  · rw [MemoryPlan.describedBytes, sumSizes, word64, n_post, s_post]
    rfl

/-- `MemoryPlan::managed_bytes()`: the sum of the managed banks, which lie in
address order within 64 bits in a well-formed map. -/
@[step] theorem managed_bytes_spec {p : fdt.MemoryPlan} {P : MemoryPlan}
    (h : MemoryPlanRepr p P) (hw : P.WellFormed) :
    fdt.plan.MemoryPlan.managed_bytes p ⦃ n => word64 n = P.managedBytes ⦄ := by
  unfold fdt.plan.MemoryPlan.managed_bytes
  step*
  · obtain ⟨-, -, -, -, -, -, hm, hp, -⟩ := hw
    rw [s_post, MemoryPlan.managedBanks]
    exact spansBytes_lt_of_pairwise (fun s hs => (hm s hs).1.2) hp
  · rw [MemoryPlan.managedBytes, sumSizes, word64, n_post, s_post, MemoryPlan.managedBanks]
    rfl

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
      n.val = nextOf (spansOf reservations) stop.val pos.val ⦄ := by
  unfold fdt.plan.available.nearest_start fdt.plan.available.nearest_start_loop
  apply loop.spec_decr_nat
    (measure := fun (x : U64 × Usize) => reservations.length - x.2.val)
    (inv := fun (x : U64 × Usize) =>
      ((spansOf reservations).drop x.2.val).foldl
          (fun e r => if pos.val < r.start.toNat then min e r.start.toNat else e) x.1.val =
        nextOf (spansOf reservations) stop.val pos.val)
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

/-- The loop of `available_step(managed, reservations, cursor)`: none when the
usable ranges from the cursor are none, with the cursor past the last bank;
otherwise the first of them, and a cursor from which the others follow. -/
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
      fun r h => nonempty_lt (hr r h)
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
        obtain ⟨-, -, h3⟩ := nextOf_spec (spansOf reservations) stop.val a.val
        rw [end_post]
        rcases h3 with h3 | ⟨y, -, hy, h3⟩ <;> omega
      · have hc : max x.at.val (spanOf bank).start.toNat < (spanOf bank).endNat := by
          have := ‹¬a ≥ stop›
          rw [ge_iff_le, UScalar.le_equiv] at this
          rw [hc0, hstop]; omega
        have hh : (holdingOf (spansOf reservations) a.val).isEmpty = true := by
          rw [‹o = none›, Option.map_none, foldl_holdStep] at o_post
          cases hE : (holdingOf (spansOf reservations) a.val).isEmpty
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
        obtain ⟨hh, he⟩ : ¬ (holdingOf (spansOf reservations) a.val).isEmpty = true ∧
            «end».val = maxEndOf (spansOf reservations) a.val := by
          rw [‹o = some «end»›, Option.map_some, foldl_holdStep] at o_post
          cases hE : (holdingOf (spansOf reservations) a.val).isEmpty
          · simp only [hE, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at o_post
            exact ⟨Bool.false_ne_true, o_post⟩
          · simp only [hE, ↓reduceIte] at o_post
            cases o_post
        have hmin : min (spanOf bank).endNat
            (maxEndOf (spansOf reservations) (max x.at.val (spanOf bank).start.toNat)) =
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
        obtain ⟨hh, he⟩ : ¬ (holdingOf (spansOf reservations) a.val).isEmpty = true ∧
            «end».val = maxEndOf (spansOf reservations) a.val := by
          rw [‹o = some «end»›, Option.map_some, foldl_holdStep] at o_post
          cases hE : (holdingOf (spansOf reservations) a.val).isEmpty
          · simp only [hE, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at o_post
            exact ⟨Bool.false_ne_true, o_post⟩
          · simp only [hE, ↓reduceIte] at o_post
            cases o_post
        have hmin : min (spanOf bank).endNat
            (maxEndOf (spansOf reservations) (max x.at.val (spanOf bank).start.toNat)) =
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

/-- `available_step(managed, reservations, cursor)`: the loop, with its cursor.
-/
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

/-- `AvailableRanges::next()`: the slices stay; none when the usable ranges
from the cursor are none, with the cursor past the last bank; otherwise the
first of them, and a cursor from which the others follow. -/
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

/-- `MemoryPlan::available_ranges()`: an iterator that stands for the usable
ranges, for a well-formed map. -/
@[step] theorem available_ranges_spec {p : fdt.MemoryPlan} {P : MemoryPlan}
    (h : MemoryPlanRepr p P) (hw : P.WellFormed) :
    fdt.plan.MemoryPlan.available_ranges p ⦃ it =>
      Stands fdt.plan.available.AvailableRanges.next SpanRepr it P.availableRanges ⦄ := by
  unfold fdt.plan.MemoryPlan.available_ranges
  step*
  have hman := hw.2.2.2.2.2.2.1
  refine available_ranges_stands s s1 ?_ ?_ _ _ rfl rfl ?_
  · rw [s_post, MemoryPlan.managedBanks]
    exact fun b hb => (hman b hb).1.2
  · rw [s1_post]
    exact fun r hr => (reservations_wf hw r hr).1
  · rw [availableRanges_eq, s_post, s1_post, MemoryPlan.managedBanks]
    rfl

end Krepi.Proofs.Fdt.Refinement
