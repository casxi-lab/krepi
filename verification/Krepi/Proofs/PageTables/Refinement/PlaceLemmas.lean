module

public import Krepi.Statements.PageTables.Ownership
public import Krepi.Proofs.PageTables.Refinement.WalkLemmas
public import Krepi.Proofs.PageTables.Refinement.PlaceSpecLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: refinement of the placement of the page ownership table

The triples of the generated functions of `ownership::placement` and of
`Reservation::initialized`, so that the proof of a caller steps over the
call with the triple of the callee and a mutant of a callee fails the proof
of the callee alone. None needs the premise `Usize64`, nor the invariant of
the table or the premise that a choice comes from `choose`: the code checks
everything that the specification checks, in the same order.

- `page_limit_eq` (the constant of the code), `reservation_initialized_spec`
  (`Reservation::initialized`, the statement `ReservationInitialized`
  without its premise).
- The fit of a request: `FitRel` (the outcome of the code against `Fit`),
  `fitRel_none`, `fitRel_some`, `fitRel_err`, and the triples
  `extra_extents_spec` (`Extent.extra` on numbers), `low_fit_spec`,
  `high_fit_spec` and `placement_fit_spec` (`fit` of the part of a free
  extent inside the window), each for a request that is not empty and a
  power of two as the alignment.
- The scan: `placement_scan_loop_spec` (the loop, with the invariant that
  the scan from the current step and flag is the scan from the start) and
  `placement_scan_spec`; `ownership_choose_spec` (the statement
  `OwnershipChoose` without its premises).
- The write of `take`: `free_containing_loop_spec` and
  `free_containing_spec` (the extent that `splitFirst` finds, by its
  index), `open_gap_loop_spec` and `open_gap_spec` (the extents after a
  position moved on), `physRangeRepr_of`, `extentRepr_with` and
  `placement_split_spec` (the pieces of `Extent.take` written in place);
  `ownership_take_spec`, `ownership_assign_spec` and
  `ownership_reserve_spec` (the statements `OwnershipAssign` and
  `OwnershipReserve` without their premises).
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.PageTables Krepi.Spec.PageTables Krepi.Statements Krepi.Statements.PageTables
open Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

/-! ## Constants and words -/

theorem page_limit_eq : page_tables.ownership.placement.PAGE_LIMIT = ok 4503599627370496#u64 := by
  unfold page_tables.ownership.placement.PAGE_LIMIT; rfl

/-! ## A reservation -/

/-- `Reservation::initialized(zeroed)`: the packet of
`Reservation.initialized`, or the reservation that it retains. -/
@[step] theorem reservation_initialized_spec (r : page_tables.Reservation) (R : Reservation)
    (zeroed : Bool) (h : ReservationRepr r R) :
    page_tables.ownership.receipts.Reservation.initialized r zeroed ⦃ x =>
      match x, R.initialized zeroed with
      | .Ok packet, .packet X => InitializedRepr packet X
      | .Err kept, .retained K => ReservationRepr kept K
      | _, _ => False ⦄ := by
  obtain ⟨ha, hat, hf⟩ := h
  unfold page_tables.ownership.receipts.Reservation.initialized
  cases zeroed
  · simp only [lift, bind_ok]
    apply spec_of_eq rfl
    simp only [Reservation.initialized, Bool.false_eq_true, ↓reduceIte]
    refine ⟨ha, rfl, ?_⟩
    have h1 : (1#u64 : U64).val = 1 := rfl
    have := u64_lt r.failures
    dsimp only
    rw [hf, eq_comm, word64_eq_iff, u64_saturating_add_val, h1]
    split
    · rename_i hlt
      rw [word64_toNat] at hlt
      rw [UInt64.toNat_add, word64_toNat, UInt64.toNat_one, Nat.mod_eq_of_lt hlt]
      omega
    · rename_i hlt
      rw [word64_toNat] at hlt ⊢
      omega
  · exact spec_of_eq rfl ⟨ha, hf⟩

/-! ## Ranges of a request -/

/-- The outcome of the fit of the code, `Ok(None)`, `Ok(Some(range))` or the
error, against the `Fit` of the specification. -/
def FitRel : core.result.Result (Option page_tables.PhysRange) page_tables.OwnershipError →
    Fit → Prop
  | .Ok none, .none => True
  | .Ok (some r), .range R => PhysRangeRepr r R
  | .Err e, .overflow => e = .AddressOverflow
  | _, _ => False

/-- `extra_extents(extent, range)`: the extents that taking `range` from
`extent` adds, one before it and one after it, for ranges whose ends fit in
64 bits. -/
@[step] theorem extra_extents_spec (a b : page_tables.PhysRange)
    (ha : a.start.val + a.len.val < 2 ^ 64) (hb : b.start.val + b.len.val < 2 ^ 64) :
    page_tables.ownership.placement.extra_extents a b ⦃ n =>
      n.val = (if a.start.val < b.start.val then 1 else 0) +
        (if b.start.val + b.len.val < a.start.val + a.len.val then 1 else 0) ⦄ := by
  unfold page_tables.ownership.placement.extra_extents
  by_cases h : a.start < b.start
  · simp only [h, ↓reduceIte]
    step*
  · simp only [h, ↓reduceIte, bind_ok]
    step*

/-- `low_fit(low, high, bytes, align)`: the lowest range of the request in
`[low, high)`, for a part that is not empty, a request that is not empty and
a power of two as the alignment. -/
@[step] theorem low_fit_spec (low high bytes align : U64) (hlh : low.val < high.val)
    (hb : 0 < bytes.val) {k : Nat} (ha : align.val = 2 ^ k) :
    page_tables.ownership.placement.low_fit low high bytes align ⦃ x =>
      FitRel x (fit .low low.val high.val bytes.val align.val) ⦄ := by
  have hk : k < 64 := by
    have := u64_lt align
    by_contra hc
    have : 2 ^ 64 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hd : align.val ∣ 2 ^ 64 := by rw [ha]; exact Nat.pow_dvd_pow 2 (by omega)
  have h1 : 1 ≤ align.val := by rw [ha]; exact Nat.one_le_two_pow
  have hm := u64_max_eq
  unfold page_tables.ownership.placement.low_fit
  step*
  · simp only [‹o = none›] at o_post
    have ho : 2 ^ 64 ≤ alignUp low.val align.val + bytes.val := by
      have := alignUp_overflow (lo := low.val) hd (by omega)
      omega
    rw [fit_low_overflow hlh ho]; rfl
  all_goals
    simp only [‹o = some up›] at o_post
    have hup : up.val = low.val + align.val - 1 := by omega
    have hs : start.val = alignUp low.val align.val := by
      rw [start_post, UScalar.val_and, i1_post, u64_complement_val, i_post, hup,
        alignDown_and (by omega) ha hk.le, alignUp_eq_alignDown]
  · simp only [‹o1 = none›] at o1_post
    rw [fit_low_overflow hlh (by omega)]; rfl
  · simp only [‹o1 = some «end»›] at o1_post
    have hh : «end».val ≤ high.val := by scalar_tac
    obtain ⟨r, hr, hrs, hrl⟩ := fit_low_range (align := align.val) hlh hb (by omega) (by omega)
    rw [hr]
    exact ⟨(word64_eq_iff.2 (by rw [hrs, hs])).symm, (word64_eq_iff.2 hrl.symm).symm⟩
  · simp only [‹o1 = some «end»›] at o1_post
    have hh : high.val < «end».val := by scalar_tac
    rw [fit_low_none (align := align.val) hlh (by omega) (by omega)]; trivial

/-- `high_fit(low, high, bytes, align)`: the highest range of the request in
`[low, high)`, for a part that is not empty, a request that is not empty and
a power of two as the alignment. -/
@[step] theorem high_fit_spec (low high bytes align : U64) (hlh : low.val < high.val)
    (hb : 0 < bytes.val) {k : Nat} (ha : align.val = 2 ^ k) :
    page_tables.ownership.placement.high_fit low high bytes align ⦃ o =>
      FitRel (.Ok o) (fit .high low.val high.val bytes.val align.val) ⦄ := by
  have hk : k < 64 := by
    have := u64_lt align
    by_contra hc
    have : 2 ^ 64 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have h1 : 1 ≤ align.val := by rw [ha]; exact Nat.one_le_two_pow
  unfold page_tables.ownership.placement.high_fit
  step*
  · rw [fit_high_small hlh (by scalar_tac)]; trivial
  all_goals
    have hs : start.val = alignDown (high.val - bytes.val) align.val := by
      rw [start_post, UScalar.val_and, i2_post, u64_complement_val, i1_post, i_post,
        alignDown_and (by have := u64_lt high; omega) ha hk.le]
  · have hl : low.val ≤ start.val := by scalar_tac
    obtain ⟨r, hr, hrs, hrl⟩ := fit_high_range (align := align.val) hlh i_post1 hb (u64_lt high)
      (by omega)
    rw [hr]
    exact ⟨(word64_eq_iff.2 (by rw [hrs, hs])).symm, (word64_eq_iff.2 hrl.symm).symm⟩
  · have hl : start.val < low.val := by scalar_tac
    rw [fit_high_below hlh i_post1 (by omega)]; trivial

/-- `fit(placement, extent, bytes, align)`: the range that the part of a free
extent inside the window of the placement gives, `fit` of the
specification, for a request that is not empty and a power of two as the
alignment. -/
@[step] theorem placement_fit_spec (placement : page_tables.Placement) (extent : page_tables.PhysRange)
    (bytes align : U64) (P : Placement) (R : PhysRange) (hP : PlacementRepr placement P)
    (hR : PhysRangeRepr extent R) (hb : 0 < bytes.val) {k : Nat} (ha : align.val = 2 ^ k) :
    page_tables.ownership.placement.fit placement extent bytes align ⦃ x =>
      FitRel x (fit P.direction (P.part R).1 (P.part R).2 bytes.val align.val) ⦄ := by
  obtain ⟨hd, hw⟩ := hP
  have hf := physRange_fits hR
  unfold page_tables.ownership.placement.fit
  step
  cases hwin : placement.window with
  | none =>
    rw [hwin] at hw
    cases hPw : P.window with
    | some W => rw [hPw] at hw; exact hw.elim
    | none =>
      have hpart : P.part R = (extent.start.val, high.val) := by
        simp only [Placement.part, hPw, physRange_start hR, physRange_endNat hR, high_post]
      rw [hpart, hd]
      simp only [bind_ok]
      cases hdir : placement.direction <;> simp only [directionOf] <;> step* <;>
        (rw [fit_empty _ (by scalar_tac)]; trivial)
  | some w =>
    rw [hwin] at hw
    cases hPw : P.window with
    | none => rw [hPw] at hw; exact hw.elim
    | some W =>
      rw [hPw] at hw
      have hwf := physRange_fits hw
      simp only [ite_ok_eq, bind_ok]
      step as ⟨wend, wend_post⟩
      have hpart : P.part R = ((if w.start > extent.start then w.start else extent.start).val,
          (if wend < high then wend else high).val) := by
        simp only [Placement.part, hPw, u64_max_val, u64_min_val, physRange_start hR,
          physRange_start hw, physRange_endNat hR, physRange_endNat hw, high_post, wend_post]
      rw [hpart, hd]
      cases hdir : placement.direction <;> simp only [directionOf] <;> step* <;>
        (rename_i hle; rw [fit_empty _ ((UScalar.le_equiv _ _).1 hle)]; trivial)

/-! ## The scan -/

theorem fitRel_none {F : Fit} (h : FitRel (.Ok none) F) : F = .none := by
  cases F <;> first | rfl | exact h.elim

theorem fitRel_some {r : page_tables.PhysRange} {F : Fit} (h : FitRel (.Ok (some r)) F) :
    ∃ R, F = .range R ∧ PhysRangeRepr r R := by
  cases F with
  | range R => exact ⟨R, rfl, h⟩
  | _ => exact h.elim

theorem fitRel_err {e : page_tables.OwnershipError} {F : Fit} (h : FitRel (.Err e) F) :
    F = .overflow ∧ e = .AddressOverflow := by
  cases F with
  | overflow => exact ⟨rfl, h⟩
  | _ => exact h.elim

/-- The loop of `scan(extents, count, room, bytes, align, placement)` from the
step `step`: the scan of the specification of the extents in the order of
the placement from that step, for the first `count` extents of the array
standing for `Ts`, a request that is not empty and a power of two as the
alignment. -/
theorem placement_scan_loop_spec {E : Usize} (extents : Aeneas.Std.Array page_tables.Extent E)
    (count room : Usize) (bytes align : U64) (placement : page_tables.Placement)
    (limited : Bool) (step : Usize) (Ts : List Extent) (P : Placement)
    (hT : ListRel ExtentRepr (extents.val.take count.val) Ts) (hc : count.val ≤ E.val)
    (hP : PlacementRepr placement P) (hb : 0 < bytes.val) {k : Nat} (ha : align.val = 2 ^ k)
    (hs : step.val ≤ count.val) :
    page_tables.ownership.placement.scan_loop extents count room bytes align placement limited
      step ⦃ r =>
      Agrees PhysRangeRepr ownershipErrorOf r
        (scan room.val bytes.val align.val P ((placeOrder P.direction Ts).drop step.val)
          limited) ⦄ := by
  have hlen : Ts.length = count.val := by
    rw [← listRel_length hT, List.length_take, extents.property]; omega
  unfold page_tables.ownership.placement.scan_loop
  apply loop.spec_decr_nat
    (measure := fun (x : page_tables.Placement × Bool × Usize) => count.val - x.2.2.val)
    (inv := fun (x : page_tables.Placement × Bool × Usize) =>
      PlacementRepr x.1 P ∧ x.2.2.val ≤ count.val ∧
      scan room.val bytes.val align.val P ((placeOrder P.direction Ts).drop x.2.2.val) x.2.1 =
        scan room.val bytes.val align.val P ((placeOrder P.direction Ts).drop step.val) limited)
  · rintro ⟨pl, lim, st⟩ ⟨hP', hst, hinv⟩
    simp only at hP' hst hinv
    unfold page_tables.ownership.placement.scan_loop.body
    by_cases h1 : st < count
    · have h1' : st.val < count.val := by scalar_tac
      have h2 : st < E := by scalar_tac
      simp only [h1, h2, ↓reduceIte]
      apply spec_bind (Pₘ := fun (x : page_tables.Direction × page_tables.Extent) =>
        x.1 = pl.direction ∧ ∃ X, (placeOrder P.direction Ts)[st.val]? = some X ∧
          ExtentRepr x.2 X)
      · rw [hP'.1]
        cases hdir : pl.direction
        · simp only [directionOf]
          step*
          have hi1 : st.val < extents.val.length := by rw [extents.property]; omega
          obtain ⟨X, hX, hXr⟩ := listRel_take_getElem? hT h1' (List.getElem?_eq_getElem hi1)
          exact ⟨X, by rw [getElem?_placeOrder_low]; exact hX, by rw [extent1_post]; exact hXr⟩
        · simp only [directionOf]
          step*
          have hi : i1.val = count.val - 1 - st.val := by scalar_tac
          have hi1 : i1.val < extents.val.length := by rw [extents.property]; omega
          obtain ⟨X, hX, hXr⟩ := listRel_take_getElem? hT (i := i1.val) (by omega)
            (List.getElem?_eq_getElem hi1)
          refine ⟨X, ?_, by rw [extent1_post]; exact hXr⟩
          rw [getElem?_placeOrder_high _ (by omega), hlen, ← hi]; exact hX
      · rintro ⟨d, extent⟩ ⟨hd, X, hX, hXr⟩
        simp only at hd hXr
        have hP'' : PlacementRepr { pl with direction := d } P := ⟨by rw [hd]; exact hP'.1, hP'.2⟩
        have hdrop := drop_of_getElem? hX
        have hxf := physRange_fits hXr.1
        rw [hdrop] at hinv
        step as ⟨b, b_post⟩
        by_cases hfree : b = true
        · simp only [hfree, ↓reduceIte]
          have hfree' : (X.holding == .free) = true := by rw [hXr.2.2, ← b_post, hfree]
          step with placement_fit_spec { pl with direction := d } extent.range bytes align P X.range hP''
            hXr.1 hb ha
          step*
          · have hrv : r = .Ok none := by rw [branch_ok cf_post (by assumption), ‹val = none›]
            rw [hrv] at r_post
            refine ⟨hP'', by scalar_tac, ?_, by scalar_tac⟩
            rw [step1_post, ← hinv, scan_free_none hfree' (fitRel_none r_post)]
          · have hrv : r = .Ok (some range) := by
              rw [branch_ok cf_post (by assumption), ‹val = some range›]
            rw [hrv] at r_post
            obtain ⟨R', -, hR'⟩ := fitRel_some r_post
            exact physRange_fits hR'
          · have hrv : r = .Ok (some range) := by
              rw [branch_ok cf_post (by assumption), ‹val = some range›]
            rw [hrv] at r_post
            obtain ⟨R', hF, hR'⟩ := fitRel_some r_post
            have hextra : i.val = X.extra R' := by
              rw [i_post, extra_eq, physRange_start hXr.1, physRange_start hR',
                physRange_endNat hXr.1, physRange_endNat hR']
            refine ⟨hP'', by scalar_tac, ?_, by scalar_tac⟩
            rw [step1_post, ← hinv, scan_free_more hfree' hF (by scalar_tac)]
          · have hrv : r = .Ok (some range) := by
              rw [branch_ok cf_post (by assumption), ‹val = some range›]
            rw [hrv] at r_post
            obtain ⟨R', hF, hR'⟩ := fitRel_some r_post
            have hextra : i.val = X.extra R' := by
              rw [i_post, extra_eq, physRange_start hXr.1, physRange_start hR',
                physRange_endNat hXr.1, physRange_endNat hR']
            rw [← hinv, scan_free_ok hfree' hF (by scalar_tac)]
            exact hR'
          · have hre : r = .Err e := branch_err cf_post (by assumption) residual_post
            rw [hre] at r_post
            obtain ⟨hF, he⟩ := fitRel_err r_post
            rw [← hinv, scan_free_overflow hfree' hF, r1_post, ← e_post, he]; rfl
        · simp only [hfree, Bool.false_eq_true, ↓reduceIte]
          have hheld : (X.holding == .free) = false := by
            rw [hXr.2.2, ← b_post]; simpa using hfree
          step*
          and_intros
          all_goals first
            | exact hP''.1
            | exact hP''.2
            | scalar_tac
            | rw [step1_post, ← hinv, scan_held hheld]
    · have h1' : count.val ≤ st.val := by scalar_tac
      simp only [h1, ↓reduceIte]
      have hnil : (placeOrder P.direction Ts).drop st.val = [] :=
        List.drop_eq_nil_of_le (by rw [placeOrder_length]; omega)
      rw [hnil, scan_nil_eq] at hinv
      cases lim
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact spec_of_eq rfl (by rw [← hinv]; rfl)
      · simp only [↓reduceIte]
        exact spec_of_eq rfl (by rw [← hinv]; rfl)
  · exact ⟨hP, hs, rfl⟩

/-- `scan(extents, count, room, bytes, align, placement)`: `scan` of the
specification over the first `count` extents of the array, standing for
`Ts`, in the order of the placement, for a request that is not empty and a
power of two as the alignment. -/
@[step] theorem placement_scan_spec {E : Usize} (extents : Aeneas.Std.Array page_tables.Extent E)
    (count room : Usize) (bytes align : U64) (placement : page_tables.Placement)
    (Ts : List Extent) (P : Placement)
    (hT : ListRel ExtentRepr (extents.val.take count.val) Ts) (hc : count.val ≤ E.val)
    (hP : PlacementRepr placement P) (hb : 0 < bytes.val) (ha : ∃ k, align.val = 2 ^ k) :
    page_tables.ownership.placement.scan extents count room bytes align placement ⦃ r =>
      Agrees PhysRangeRepr ownershipErrorOf r
        (scan room.val bytes.val align.val P (placeOrder P.direction Ts) false) ⦄ := by
  obtain ⟨k, ha⟩ := ha
  unfold page_tables.ownership.placement.scan
  exact spec_mono (placement_scan_loop_spec extents count room bytes align placement false 0#usize
    Ts P hT hc hP hb ha (by simp)) fun r h => by
      rwa [show (0#usize : Usize).val = 0 from rfl, List.drop_zero] at h

/-! ## `choose` -/

/-- `Ownership::choose(owner, pages, alignment, placement)`: the choice of
`Ownership.choose`, or its error. -/
@[step] theorem ownership_choose_spec {E X : Usize} (t : page_tables.Ownership E X)
    (T : Ownership E.val X.val) (owner pages alignment : U64) (placement : page_tables.Placement)
    (P : Placement) (ht : OwnershipRepr t T) (hP : PlacementRepr placement P) :
    page_tables.ownership.placement.Ownership.choose t owner pages alignment placement ⦃ r =>
      Agrees ChoiceRepr ownershipErrorOf r
        (T.choose (word64 owner) (word64 pages) (word64 alignment) P) ⦄ := by
  have hlen := ownershipRepr_extents_length ht
  obtain ⟨-, hc, -, -, -, hT, -, hcnt⟩ := ht
  unfold page_tables.ownership.placement.Ownership.choose
  simp only [page_limit_eq, page_size_eq, bind_ok]
  rw [choose_eq, word64_toNat, word64_toNat]
  have h0 : (0#u64 : U64).val = 0 := rfl
  step*
  · simp only [show 2 ^ 52 ≤ pages.val by scalar_tac, ↓reduceIte, agrees_err_error,
      ownershipErrorOf]
  · simp only [show ¬ 2 ^ 52 ≤ pages.val by scalar_tac, show 2 ^ 52 ≤ alignment.val by scalar_tac,
      ↓reduceIte, agrees_err_error, ownershipErrorOf]
  · simp only [h0, show ¬ 2 ^ 52 ≤ alignment.val by scalar_tac, Nat.not_le.mpr (Nat.two_pow_pos 52),
      ↓reduceIte, agrees_err_error, ownershipErrorOf]
  · simp only [h0, show ¬ 2 ^ 52 ≤ pages.val by scalar_tac, show ¬ pages.val = 0 by scalar_tac,
      Nat.not_le.mpr (Nat.two_pow_pos 52), ↓reduceIte, agrees_err_error, ownershipErrorOf]
  · have h6 : alignment.val &&& (alignment.val - 1) ≠ 0 := by
      rw [← i1_post, ← UScalar.val_and, ← i2_post]; exact bne_zero_iff.1 ‹_›
    simp only [show ¬ 2 ^ 52 ≤ pages.val by scalar_tac, show ¬ 2 ^ 52 ≤ alignment.val by scalar_tac,
      show ¬ pages.val = 0 by scalar_tac, show ¬ alignment.val = 0 by scalar_tac, h6, ne_eq,
      not_false_eq_true, ↓reduceIte, agrees_err_error, ownershipErrorOf]
  · have h6 : alignment.val &&& (alignment.val - 1) = 0 := by
      rw [← i1_post, ← UScalar.val_and, ← i2_post]; exact not_bne_zero_iff.1 ‹_›
    obtain ⟨k, hk⟩ := pow_two_of_and_pred (show alignment.val ≠ 0 by scalar_tac) h6
    exact ⟨k + 12, by rw [i5_post, hk, Nat.pow_add]⟩
  · have h6 : alignment.val &&& (alignment.val - 1) = 0 := by
      rw [← i1_post, ← UScalar.val_and, ← i2_post]; exact not_bne_zero_iff.1 ‹_›
    have hcn : T.counter ≠ .exhausted := by rw [hcnt, ‹t.counter = _›]; simp [counterOf]
    have hr := branch_ok cf_post ‹_›
    rw [hr] at r_post
    obtain ⟨R, hR, hRr⟩ := agrees_ok_iff.1 r_post
    have e3 : E.val - T.extents.length = i3.val := by rw [i3_post, hlen]
    have e4 : pages.val * PAGE_SIZE = i4.val := by rw [i4_post]; rfl
    have e5 : alignment.val * PAGE_SIZE = i5.val := by rw [i5_post]; rfl
    simp only [show ¬ 2 ^ 52 ≤ pages.val by scalar_tac, show ¬ 2 ^ 52 ≤ alignment.val by scalar_tac,
      show ¬ pages.val = 0 by scalar_tac, show ¬ alignment.val = 0 by scalar_tac, h6, ne_eq,
      not_true_eq_false, hcn, ↓reduceIte, e3, e4, e5, hR]
    exact ⟨rfl, hRr⟩
  · have h6 : alignment.val &&& (alignment.val - 1) = 0 := by
      rw [← i1_post, ← UScalar.val_and, ← i2_post]; exact not_bne_zero_iff.1 ‹_›
    have hcn : T.counter ≠ .exhausted := by rw [hcnt, ‹t.counter = _›]; simp [counterOf]
    have hs := agrees_err_of_branch cf_post ‹_› residual_post ‹_›
    have e3 : E.val - T.extents.length = i3.val := by rw [i3_post, hlen]
    have e4 : pages.val * PAGE_SIZE = i4.val := by rw [i4_post]; rfl
    have e5 : alignment.val * PAGE_SIZE = i5.val := by rw [i5_post]; rfl
    simp only [show ¬ 2 ^ 52 ≤ pages.val by scalar_tac, show ¬ 2 ^ 52 ≤ alignment.val by scalar_tac,
      show ¬ pages.val = 0 by scalar_tac, show ¬ alignment.val = 0 by scalar_tac, h6, ne_eq,
      not_true_eq_false, hcn, ↓reduceIte, e3, e4, e5, hs, r_post, ← e_post]
    rfl
  · have h6 : alignment.val &&& (alignment.val - 1) = 0 := by
      rw [← i1_post, ← UScalar.val_and, ← i2_post]; exact not_bne_zero_iff.1 ‹_›
    have hce : T.counter = .exhausted := by rw [hcnt, ‹t.counter = _›]; rfl
    simp only [show ¬ 2 ^ 52 ≤ pages.val by scalar_tac, show ¬ 2 ^ 52 ≤ alignment.val by scalar_tac,
      show ¬ pages.val = 0 by scalar_tac, show ¬ alignment.val = 0 by scalar_tac, h6, ne_eq,
      not_true_eq_false, hce, ↓reduceIte, agrees_err_error, ownershipErrorOf]

/-! ## The search of a free extent -/

/-- The loop of `free_containing(extents, count, range)` from `index`: the
first extent from there, of the first `count` extents of the array standing
for `Ts`, that is free and contains the range, as `splitFirst` of `take`
finds it, when no extent before `index` passes the test. -/
theorem free_containing_loop_spec {E : Usize} (extents : Aeneas.Std.Array page_tables.Extent E)
    (count : Usize) (range : page_tables.PhysRange) (index : Usize) (Ts : List Extent)
    (R : PhysRange) (hT : ListRel ExtentRepr (extents.val.take count.val) Ts)
    (hc : count.val ≤ E.val) (hR : PhysRangeRepr range R) (hi : index.val ≤ count.val)
    (hb : ∀ j < index.val, ∀ Y, Ts[j]? = some Y →
      (Y.holding == .free && Y.range.contains R) = false) :
    page_tables.ownership.placement.free_containing_loop extents count range index ⦃ o =>
      match o with
      | none => splitFirst (fun e => e.holding == .free && e.range.contains R) Ts [] = none
      | some i => ∃ Y, Ts[i.val]? = some Y ∧ (Y.holding == .free && Y.range.contains R) = true ∧
          splitFirst (fun e => e.holding == .free && e.range.contains R) Ts [] =
            some ((Ts.take i.val).reverse ++ [], Y, Ts.drop (i.val + 1)) ⦄ := by
  have hlen : Ts.length = count.val := by
    rw [← listRel_length hT, List.length_take, extents.property]; omega
  have hrf := physRange_fits hR
  unfold page_tables.ownership.placement.free_containing_loop
  apply loop.spec_decr_nat (measure := fun (i : Usize) => count.val - i.val)
    (inv := fun (i : Usize) => i.val ≤ count.val ∧ ∀ j < i.val, ∀ Y, Ts[j]? = some Y →
      (Y.holding == .free && Y.range.contains R) = false)
  · rintro idx ⟨hidx, hinv⟩
    unfold page_tables.ownership.placement.free_containing_loop.body
    by_cases h1 : idx < count
    · have h1' : idx.val < count.val := by scalar_tac
      have h2 : idx < E := by scalar_tac
      simp only [h1, h2, ↓reduceIte]
      have hi1 : idx.val < extents.val.length := by rw [extents.property]; omega
      obtain ⟨X, hX, hXr⟩ := listRel_take_getElem? hT h1' (List.getElem?_eq_getElem hi1)
      have hxf := physRange_fits hXr.1
      step as ⟨e, e_post⟩
      subst e_post
      step*
      · have hcont : X.range.contains R = true := by
          rwa [PhysRange.contains, physRange_start hXr.1, physRange_start hR,
            physRange_endNat hXr.1, physRange_endNat hR, ← Bool.decide_and, ← b1_post]
        have hfree : (X.holding == .free) = true := by rwa [hXr.2.2, ← b_post]
        refine ⟨X, hX, by rw [hfree, hcont]; rfl, ?_⟩
        obtain ⟨hlt, hXe⟩ := List.getElem?_eq_some_iff.1 hX
        rw [splitFirst_of_index (acc := []) hlt (fun j hj => hinv j hj _
          (List.getElem?_eq_getElem _)) (by rw [hXe, hfree, hcont]; rfl), hXe]
      · have hcont : X.range.contains R = false := by
          rw [PhysRange.contains, physRange_start hXr.1, physRange_start hR,
            physRange_endNat hXr.1, physRange_endNat hR, ← Bool.decide_and, ← b1_post]
          simpa using ‹¬b1 = true›
        refine ⟨by scalar_tac, fun j hj Y hY => ?_, by scalar_tac⟩
        rcases Nat.lt_or_ge j idx.val with hj' | hj'
        · exact hinv j hj' Y hY
        · have : j = idx.val := by scalar_tac
          subst this
          rw [hX] at hY; cases hY
          rw [hcont, Bool.and_false]
      · have hfree : (X.holding == .free) = false := by
          rw [hXr.2.2, ← b_post]; simpa using ‹¬b = true›
        refine ⟨by scalar_tac, fun j hj Y hY => ?_, by scalar_tac⟩
        rcases Nat.lt_or_ge j idx.val with hj' | hj'
        · exact hinv j hj' Y hY
        · have : j = idx.val := by scalar_tac
          subst this
          rw [hX] at hY; cases hY
          rw [hfree, Bool.false_and]
    · have h1' : count.val ≤ idx.val := by scalar_tac
      simp only [h1, ↓reduceIte]
      apply spec_of_eq rfl
      exact splitFirst_of_none fun j hj => hinv j (by omega) _ (List.getElem?_eq_getElem hj)
  · exact ⟨hi, hb⟩

/-- `free_containing(extents, count, range)`: the first of the first
`count` extents of the array, standing for `Ts`, that is free and contains
the range, as `splitFirst` of `take` finds it. -/
@[step] theorem free_containing_spec {E : Usize} (extents : Aeneas.Std.Array page_tables.Extent E)
    (count : Usize) (range : page_tables.PhysRange) (Ts : List Extent) (R : PhysRange)
    (hT : ListRel ExtentRepr (extents.val.take count.val) Ts) (hc : count.val ≤ E.val)
    (hR : PhysRangeRepr range R) :
    page_tables.ownership.placement.free_containing extents count range ⦃ o =>
      match o with
      | none => splitFirst (fun e => e.holding == .free && e.range.contains R) Ts [] = none
      | some i => ∃ Y, Ts[i.val]? = some Y ∧ (Y.holding == .free && Y.range.contains R) = true ∧
          splitFirst (fun e => e.holding == .free && e.range.contains R) Ts [] =
            some ((Ts.take i.val).reverse ++ [], Y, Ts.drop (i.val + 1)) ⦄ := by
  unfold page_tables.ownership.placement.free_containing
  exact free_containing_loop_spec extents count range 0#usize Ts R hT hc hR (by simp)
    (fun j hj => absurd hj (by simp))

/-! ## Opening a gap -/

/-- The loop of `open_gap(extents, count, index, by)` from the position
`pos`: the extents from `pos` up to `count` (excluded) are moved `by`
places on, for `index < pos ≤ count` and `count + by` within the array, the
extents of `L` from `pos` on having been moved already. -/
theorem open_gap_loop_spec {E : Usize} (extents : Aeneas.Std.Array page_tables.Extent E)
    (index gap pos : Usize) (count : Nat) (L : List page_tables.Extent)
    (h1 : index.val + 1 ≤ pos.val) (h2 : pos.val ≤ count) (h3 : count + gap.val ≤ E.val)
    (hA : ∀ j, extents.val[j]? =
      if pos.val + gap.val ≤ j ∧ j < count + gap.val then L[j - gap.val]? else L[j]?) :
    page_tables.ownership.placement.open_gap_loop extents index gap pos ⦃ A =>
      ∀ j, A.val[j]? =
        if index.val + 1 + gap.val ≤ j ∧ j < count + gap.val then L[j - gap.val]? else L[j]? ⦄ := by
  unfold page_tables.ownership.placement.open_gap_loop
  apply loop.spec_decr_nat
    (measure := fun (x : Aeneas.Std.Array page_tables.Extent E × Usize) => x.2.val)
    (inv := fun (x : Aeneas.Std.Array page_tables.Extent E × Usize) =>
      index.val + 1 ≤ x.2.val ∧ x.2.val ≤ count ∧ ∀ j, x.1.val[j]? =
        if x.2.val + gap.val ≤ j ∧ j < count + gap.val then L[j - gap.val]? else L[j]?)
  · rintro ⟨A, p⟩ ⟨ha1, ha2, hinv⟩
    simp only at ha1 ha2 hinv
    unfold page_tables.ownership.placement.open_gap_loop.body
    step*
    · refine ⟨by scalar_tac, by scalar_tac, fun j => ?_, by scalar_tac⟩
      have hl : A.val.length = E.val := A.property
      have he : A.val[at1.val]? = some e := by
        rw [e_post]; exact List.getElem?_eq_getElem _
      rw [hinv at1.val] at he
      simp only [show ¬ (p.val + gap.val ≤ at1.val ∧ at1.val < count + gap.val) by scalar_tac,
        ↓reduceIte] at he
      rw [a_post, Array.set_val_eq, List.getElem?_set]
      by_cases hj : i1.val = j
      · subst hj
        simp only [↓reduceIte, show i1.val < A.val.length by scalar_tac]
        split_ifs with hc
        · rw [show i1.val - gap.val = at1.val by scalar_tac, he]
        · exfalso; scalar_tac
      · simp only [hj, ↓reduceIte, hinv j]
        split_ifs <;> first | rfl | (exfalso; omega)
    · have : p.val = index.val + 1 := by scalar_tac
      rw [this] at hinv
      exact hinv
  · exact ⟨h1, h2, hA⟩

/-- `open_gap(extents, count, index, by)`: the extents after `index` up to
`count` (excluded) moved `by` places on, the others kept, for
`index < count` and `count + by` within the array. -/
@[step] theorem open_gap_spec {E : Usize} (extents : Aeneas.Std.Array page_tables.Extent E)
    (count index gap : Usize) (h1 : index.val < count.val) (h3 : count.val + gap.val ≤ E.val) :
    page_tables.ownership.placement.open_gap extents count index gap ⦃ A =>
      ∀ j, A.val[j]? = if index.val + 1 + gap.val ≤ j ∧ j < count.val + gap.val then
        extents.val[j - gap.val]? else extents.val[j]? ⦄ := by
  unfold page_tables.ownership.placement.open_gap
  exact open_gap_loop_spec extents index gap count count.val extents.val (by omega) le_rfl h3
    (fun j => by split_ifs <;> first | rfl | (exfalso; omega))

/-! ## Splitting an extent -/

/-- A range of the code stands for a range with the same numbers. -/
theorem physRangeRepr_of {r : page_tables.PhysRange} {R : PhysRange}
    (h1 : R.start.toNat = r.start.val) (h2 : R.len.toNat = r.len.val) : PhysRangeRepr r R :=
  ⟨(word64_eq_iff.2 h1.symm).symm, (word64_eq_iff.2 h2.symm).symm⟩

/-- An extent of the code with a new range and holding stands for the extent
of the same bank with the range and holding they stand for. -/
theorem extentRepr_with {e : page_tables.Extent} {X : Extent} (hX : ExtentRepr e X)
    {r : page_tables.PhysRange} {R : PhysRange} (hr : PhysRangeRepr r R) (h : page_tables.Holding) :
    ExtentRepr { e with range := r, holding := h } ⟨R, X.bank, holdingOf h⟩ :=
  ⟨hr, hX.2.1, rfl⟩

/-- `split(extents, index, extent, range, holding)`: the entries from
`index` hold the pieces of `Extent.take` of the extent that the code's
extent stands for, for a range inside it; the entries before `index` and
after the pieces are kept. -/
theorem placement_split_spec {E : Usize} (A : Aeneas.Std.Array page_tables.Extent E) (index : Usize)
    (extent : page_tables.Extent) (range : page_tables.PhysRange) (holding : page_tables.Holding)
    (X : Extent) (R : PhysRange) (hX : ExtentRepr extent X) (hR : PhysRangeRepr range R)
    (hc : X.range.contains R = true) (hE : index.val + X.extra R < E.val) :
    page_tables.ownership.placement.split A index extent range holding ⦃ F =>
      (∀ j, (j < index.val ∨ index.val + 1 + X.extra R ≤ j) → F.val[j]? = A.val[j]?) ∧
      ListRel ExtentRepr ((F.val.drop index.val).take (1 + X.extra R))
        (X.take R (holdingOf holding)) ⦄ := by
  have hxf := physRange_fits hX.1
  have hrf := physRange_fits hR
  have hs := physRange_start hX.1
  have hrs := physRange_start hR
  have hen := physRange_endNat hX.1
  have hren := physRange_endNat hR
  have hcont : X.range.start.toNat ≤ R.start.toNat ∧ R.endNat ≤ X.range.endNat := by
    simpa [PhysRange.contains] using hc
  have hl : A.val.length = E.val := A.property
  unfold page_tables.ownership.placement.split
  by_cases hb : extent.range.start < range.start
  · have hlt : X.range.start.toNat < R.start.toNat := by have := hb; scalar_tac
    simp only [hb, ↓reduceIte]
    obtain ⟨B1, hB1, hB1s, hB1l⟩ := before_some hlt
    by_cases ha : range.start.val + range.len.val < extent.range.start.val + extent.range.len.val
    · have hgt : R.endNat < X.range.endNat := by omega
      have hx : X.extra R = 2 := by rw [extra_eq]; simp only [hlt, hgt, ↓reduceIte]
      obtain ⟨B2, hB2, hB2s, hB2l⟩ := after_some hgt
      step*
      subst_vars
      refine ⟨fun j hj => ?_, ?_⟩
      · simp only [Array.set_val_eq, List.getElem?_set]
        split_ifs <;> first | rfl | (exfalso; omega)
      · simp only [Array.set_val_eq]
        rw [hx, i3_post, x_post, show index.val + 1 + 1 = index.val + 2 by omega,
          show 1 + 2 = 3 from rfl, drop_take_set_three (by omega)]
        simp only [Extent.take, hB1, hB2, Option.map_some, Option.toList_some, List.cons_append,
          List.nil_append, listRel_cons_cons, listRel_nil_nil, and_true]
        exact ⟨⟨physRangeRepr_of (by dsimp only; omega) (by dsimp only; omega), hX.2.1, rfl⟩,
          ⟨hR, hX.2.1, rfl⟩,
          ⟨physRangeRepr_of (by dsimp only; omega) (by dsimp only; omega), hX.2.1, rfl⟩⟩
    · have hgt : X.range.endNat ≤ R.endNat := by omega
      have hx : X.extra R = 1 := by
        rw [extra_eq]; simp only [hlt, Nat.not_lt.mpr hgt, ↓reduceIte]
      step*
      subst_vars
      refine ⟨fun j hj => ?_, ?_⟩
      · simp only [Array.set_val_eq, List.getElem?_set]
        split_ifs <;> first | rfl | (exfalso; omega)
      · simp only [Array.set_val_eq]
        rw [hx, x_post, show 1 + 1 = 2 from rfl, drop_take_set_two (by omega)]
        simp only [Extent.take, hB1, after_none hgt, Option.map_some, Option.map_none,
          Option.toList_some, Option.toList_none, List.cons_append, List.nil_append,
          listRel_cons_cons, listRel_nil_nil, and_true]
        exact ⟨⟨physRangeRepr_of (by dsimp only; omega) (by dsimp only; omega), hX.2.1, rfl⟩,
          ⟨hR, hX.2.1, rfl⟩⟩
  · have hlt : R.start.toNat ≤ X.range.start.toNat := by have := hb; scalar_tac
    simp only [hb, ↓reduceIte, bind_ok]
    by_cases ha : range.start.val + range.len.val < extent.range.start.val + extent.range.len.val
    · have hgt : R.endNat < X.range.endNat := by omega
      have hx : X.extra R = 1 := by
        rw [extra_eq]; simp only [Nat.not_lt.mpr hlt, hgt, ↓reduceIte]
      obtain ⟨B2, hB2, hB2s, hB2l⟩ := after_some hgt
      step*
      subst_vars
      refine ⟨fun j hj => ?_, ?_⟩
      · simp only [Array.set_val_eq, List.getElem?_set]
        split_ifs <;> first | rfl | (exfalso; omega)
      · simp only [Array.set_val_eq]
        rw [hx, i3_post, show 1 + 1 = 2 from rfl, drop_take_set_two (by omega)]
        simp only [Extent.take, before_none hlt, hB2, Option.map_some, Option.map_none,
          Option.toList_some, Option.toList_none, List.nil_append,
          listRel_cons_cons, listRel_nil_nil, and_true]
        exact ⟨⟨hR, hX.2.1, rfl⟩,
          ⟨physRangeRepr_of (by dsimp only; omega) (by dsimp only; omega), hX.2.1, rfl⟩⟩
    · have hgt : X.range.endNat ≤ R.endNat := by omega
      have hx : X.extra R = 0 := by
        rw [extra_eq]; simp only [Nat.not_lt.mpr hlt, Nat.not_lt.mpr hgt, ↓reduceIte]
      step*
      subst_vars
      refine ⟨fun j hj => ?_, ?_⟩
      · simp only [Array.set_val_eq, List.getElem?_set]
        split_ifs <;> first | rfl | (exfalso; omega)
      · simp only [Array.set_val_eq]
        rw [hx, drop_take_set_one (by omega)]
        simp only [Extent.take, before_none hlt, after_none hgt, Option.map_none,
          Option.toList_none, List.nil_append, listRel_cons_cons,
          listRel_nil_nil, and_true]
        exact ⟨hR, hX.2.1, rfl⟩

/-! ## `take`, `assign` and `reserve` -/

/-- `Ownership::take(choice, state)`: the table and the receipt of
`Ownership.take`, or its error with the table unchanged. -/
@[step] theorem ownership_take_spec {E X : Usize} (t : page_tables.Ownership E X)
    (T : Ownership E.val X.val) (choice : page_tables.Choice) (C : Choice)
    (state : page_tables.HoldState) (ht : OwnershipRepr t T) (hc : ChoiceRepr choice C) :
    page_tables.ownership.placement.Ownership.take t choice state ⦃ r t' =>
      Writes OwnershipRepr AllocationRepr (ownershipErrorOf · = ·) t r t'
        (T.take C (holdStateOf state)) ⦄ := by
  have hlen := ownershipRepr_extents_length ht
  obtain ⟨hbc, hec, hxc, har, hbanks, hT, hexcl, hcnt⟩ := ht
  obtain ⟨hco, hcr⟩ := hc
  have hrf := physRange_fits hcr
  have hl : t.extents.val.length = E.val := t.extents.property
  unfold page_tables.ownership.placement.Ownership.take
  cases hg : t.counter with
  | Exhausted =>
    have hT' : T.counter = .exhausted := by rw [hcnt, hg]; rfl
    rw [take_exhausted hT']
    exact spec_of_eq rfl ⟨rfl, rfl⟩
  | Next g =>
    have hT' : T.counter = .next (word64 g) := by rw [hcnt, hg]; rfl
    step as ⟨o, o_post⟩
    cases o with
    | none =>
      rw [take_none hT' o_post]
      exact spec_of_eq rfl ⟨rfl, rfl⟩
    | some idx =>
      obtain ⟨Y, hY, hp, hsplit⟩ := o_post
      have hidx : idx.val < t.extent_count.val := by
        have := (List.getElem?_eq_some_iff.1 hY).1; omega
      have hi1 : idx.val < t.extents.val.length := by omega
      obtain ⟨Y', hY', hYr⟩ := listRel_take_getElem? hT hidx (List.getElem?_eq_getElem hi1)
      rw [hY] at hY'; cases hY'
      have hcont : Y.range.contains C.range = true := by
        simp only [Bool.and_eq_true] at hp; exact hp.2
      step as ⟨extent, extent_post⟩
      have hYe : ExtentRepr extent Y := by rw [extent_post]; exact hYr
      have hxf := physRange_fits hYe.1
      step as ⟨extra, extra_post⟩
      step as ⟨room, room_post⟩
      have hextra : extra.val = Y.extra C.range := by
        rw [extra_post, extra_eq, physRange_start hYe.1, physRange_start hcr,
          physRange_endNat hYe.1, physRange_endNat hcr]
      by_cases hm : extra > room
      · simp only [hm, ↓reduceIte]
        rw [take_more hT' hsplit (by scalar_tac)]
        exact spec_of_eq rfl ⟨rfl, rfl⟩
      · simp only [hm, ↓reduceIte]
        step as ⟨a, a_post⟩
        have hH : holdingOf (.Held choice.owner g state) =
            .held C.owner (word64 g) (holdStateOf state) := by rw [hco]; rfl
        have hE : idx.val + Y.extra C.range < E.val := by scalar_tac
        have hsp := placement_split_spec a idx extent choice.range (.Held choice.owner g state) Y
          C.range hYe hcr hcont hE
        step with hsp as ⟨F, hFo, hFp⟩
        rw [hH] at hFp
        rw [take_some hT' hsplit (by scalar_tac)]
        have hrel : ListRel ExtentRepr (F.val.take (t.extent_count.val + extra.val))
            (((T.extents.take idx.val).reverse ++ []).reverseAux
              (Y.take C.range (.held C.owner (word64 g) (holdStateOf state)) ++
                T.extents.drop (idx.val + 1))) := by
          rw [List.append_nil, List.reverseAux_eq, List.reverse_reverse, ← List.append_assoc]
          have := listRel_replace (L := t.extents.val) (F := F.val) (Ts := T.extents)
            (count := t.extent_count.val) (index := idx.val) (d := 1) (p := 1 + extra.val) hT
            (by omega) (by rw [hextra]; exact hFp)
            (fun j hj => by
              rw [hFo j (Or.inl hj), a_post j]
              split_ifs <;> first | rfl | (exfalso; omega))
            (fun j h1 h2 => by
              rw [hFo j (Or.inr (by omega)), a_post j]
              split_ifs <;> (congr 1; omega))
          rwa [show t.extent_count.val + (1 + extra.val) - 1 = t.extent_count.val + extra.val by
            omega] at this
        have hm1 := u64_max_eq
        step*
        · simp only [‹o1 = none›] at o1_post
          simp only [Writes]
          refine ⟨⟨har, hco, rfl, hcr⟩, hbc, by scalar_tac, hxc, har, hbanks,
            by rw [i1_post]; exact hrel, hexcl, ?_⟩
          rw [Counter.after, word64_toNat]
          simp only [show ¬ g.val + 1 < 2 ^ 64 by omega, ↓reduceIte]
          rfl
        · simp only [‹o1 = some next›] at o1_post
          simp only [Writes]
          refine ⟨⟨har, hco, rfl, hcr⟩, hbc, by scalar_tac, hxc, har, hbanks,
            by rw [i1_post]; exact hrel, hexcl, ?_⟩
          rw [Counter.after, word64_toNat]
          simp only [show g.val + 1 < 2 ^ 64 by omega, ↓reduceIte, counterOf]
          congr 1
          rw [eq_comm, word64_eq_iff, UInt64.toNat_add, word64_toNat, UInt64.toNat_one,
            Nat.mod_eq_of_lt (by omega)]
          omega

/-- `Ownership::assign(choice, zeroed)`: the table and the receipt of
`Ownership.assign`, or its error with the table unchanged. -/
@[step] theorem ownership_assign_spec {E X : Usize} (t : page_tables.Ownership E X)
    (T : Ownership E.val X.val) (choice : page_tables.Choice) (C : Choice) (zeroed : Bool)
    (ht : OwnershipRepr t T) (hc : ChoiceRepr choice C) :
    page_tables.ownership.placement.Ownership.assign t choice zeroed ⦃ r t' =>
      Writes OwnershipRepr AllocationRepr (ownershipErrorOf · = ·) t r t' (T.assign C zeroed) ⦄ := by
  unfold page_tables.ownership.placement.Ownership.assign
  cases zeroed
  · simp only [Ownership.assign, Bool.false_eq_true, ↓reduceIte]
    exact spec_of_eq rfl ⟨rfl, rfl⟩
  · simp only [Ownership.assign, ↓reduceIte]
    exact ownership_take_spec t T choice C .Published ht hc

/-- `Ownership::reserve(owner, pages, alignment, placement)`: the table and
the reservation of `Ownership.reserve`, or its error with the table
unchanged. -/
@[step] theorem ownership_reserve_spec {E X : Usize} (t : page_tables.Ownership E X)
    (T : Ownership E.val X.val) (owner pages alignment : U64) (placement : page_tables.Placement)
    (P : Placement) (ht : OwnershipRepr t T) (hP : PlacementRepr placement P) :
    page_tables.ownership.placement.Ownership.reserve t owner pages alignment placement ⦃ r t' =>
      Writes OwnershipRepr ReservationRepr (ownershipErrorOf · = ·) t r t'
        (T.reserve (word64 owner) (word64 pages) (word64 alignment) P) ⦄ := by
  unfold page_tables.ownership.placement.Ownership.reserve
  step as ⟨r, r_post⟩
  step as ⟨cf, cf_post⟩
  cases r with
  | Ok c =>
    obtain ⟨C, hC, hCr⟩ := agrees_ok_iff.1 r_post
    simp only at cf_post
    subst cf_post
    rw [reserve_ok_eq hC]
    step with ownership_take_spec t T c C .Reserved ht hCr as ⟨r1, t1, h1⟩
    simp only [holdStateOf] at h1
    cases hTt : T.take C .reserved with
    | error y =>
      rw [hTt] at h1
      cases r1 with
      | Ok a => simp [Writes] at h1
      | Err x =>
        obtain ⟨hx, rfl⟩ := h1
        step*
        have h' := ‹cf1 = core.ops.control_flow.ControlFlow.Break residual›
        rw [cf1_post] at h'
        cases h'
        cases residual_post
        subst_vars
        exact ⟨rfl, rfl⟩
    | ok v =>
      obtain ⟨T', A⟩ := v
      rw [hTt] at h1
      cases r1 with
      | Err x => simp [Writes] at h1
      | Ok a =>
        obtain ⟨ha, ht1⟩ := h1
        step*
        have h' := ‹cf1 = core.ops.control_flow.ControlFlow.Continue val1›
        rw [cf1_post] at h'
        cases h'
        exact ⟨⟨ha, rfl, rfl⟩, ht1⟩
  | Err e =>
    have hC := agrees_err_iff.1 r_post
    simp only at cf_post
    subst cf_post
    rw [reserve_error_eq hC]
    step*
    case hfrom => rfl
    rw [r1_post]
    exact ⟨rfl, rfl⟩
