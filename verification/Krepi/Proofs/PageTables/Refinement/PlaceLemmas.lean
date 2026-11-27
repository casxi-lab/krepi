module

public import Krepi.Statements.PageTables.Ownership
public import Krepi.Proofs.PageTables.Refinement.WalkLemmas
public import Krepi.Proofs.PageTables.Refinement.PlaceSpecLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: refinement of the placement of the page ownership table

The triples of the generated functions of `ownership::placement` and of
`Reservation::initialized`, each a `@[step]` lemma, so that the proof of a
caller steps over the call with the triple of the callee and a mutant of a
callee fails the proof of the callee alone.
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
@[step] theorem fit_spec (placement : page_tables.Placement) (extent : page_tables.PhysRange)
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
theorem scan_loop_spec {E : Usize} (extents : Aeneas.Std.Array page_tables.Extent E)
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
          step with fit_spec { pl with direction := d } extent.range bytes align P X.range hP''
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
@[step] theorem scan_spec {E : Usize} (extents : Aeneas.Std.Array page_tables.Extent E)
    (count room : Usize) (bytes align : U64) (placement : page_tables.Placement)
    (Ts : List Extent) (P : Placement)
    (hT : ListRel ExtentRepr (extents.val.take count.val) Ts) (hc : count.val ≤ E.val)
    (hP : PlacementRepr placement P) (hb : 0 < bytes.val) (ha : ∃ k, align.val = 2 ^ k) :
    page_tables.ownership.placement.scan extents count room bytes align placement ⦃ r =>
      Agrees PhysRangeRepr ownershipErrorOf r
        (scan room.val bytes.val align.val P (placeOrder P.direction Ts) false) ⦄ := by
  obtain ⟨k, ha⟩ := ha
  unfold page_tables.ownership.placement.scan
  exact spec_mono (scan_loop_spec extents count room bytes align placement false 0#usize Ts P hT hc
    hP hb ha (by simp)) fun r h => by
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
