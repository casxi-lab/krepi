module

public import Krepi.Proofs.PageTables.Refinement.LayoutLemmas
public import Krepi.Proofs.PageTables.Refinement.KernelPlanSpecLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: the plan iterator of `kernel_map` stands for its plan

The plan iterator that `kernel_map` returns, `KernelMapPlan`, stands for the
plan `mapPlan` of `Tables.kernelMap`. `kernel_map_plan_next_spec`
(`Krepi.Proofs.PageTables.Refinement.LayoutLemmas`) makes each call of
`KernelMapPlan::next` one call of the cursor on numbers, `Cur.step`, with
the leaf search `layoutFind` of the sorted ranges; the leaves of the layout
that passed its checks satisfy `SimOk` with that search
(`Krepi.Proofs.PageTables.Refinement.KernelPlanSpecLemmas`); and the
simulation `stands_mapPlan`
(`Krepi.Proofs.PageTables.Refinement.PlanSimSpecLemmas`) turns the two into
`Stands`.

- `curOf_inj`, `optionRel_stepRepr` and `views_eq` (the ranges of the code
  on numbers are those of the sorted ranges of the layout).
- `kernel_map_plan_stands`: from the success of `Tables.kernelMap` and an
  iterator at its start (`KernelMapStart`) on a set whose record of tables
  in use is at or above that of the set before the write phase,
  `Stands KernelMapPlan.next StepRepr` of the plan, for a record of the set
  before the write phase at least 2 below the largest `usize`. It reads no
  bound of the count of the checks of the code.
- `kernel_map_start_spec`: `kernel_map_set_spec` with the set of the
  iterator: the set that `kernel_map` returns.
- `kernel_map_of_room`: the conclusion of the statement `KernelMap` for a
  record of the set at least `2 ^ 33` below the largest `usize` (the premise
  of the checks of the code, `kernel_map_set_spec`).
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.PageTables Krepi.Spec.PageTables Krepi.Statements Krepi.Statements.PageTables
open Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

/-- The cursor of the code is its cursor on numbers. -/
theorem curOf_inj {c c' : page_tables.boot.MapCursor} (h : curOf c = curOf c') : c = c' := by
  obtain ⟨ph, frm, nx, g, sl, t2, t3⟩ := c
  obtain ⟨ph', frm', nx', g', sl', t2', t3'⟩ := c'
  simp only [curOf, Cur.mk.injEq] at h
  obtain ⟨hp, h1, h2, h3, h4, h5, h6⟩ := h
  have hph : ph = ph' := by
    cases ph <;> cases ph' <;> first | rfl | (simp only [phaseOf, reduceCtorEq] at hp)
  subst hph
  rw [UScalar.eq_of_val_eq h1, UScalar.eq_of_val_eq h2, UScalar.eq_of_val_eq h3,
    UScalar.eq_of_val_eq h4, UScalar.eq_of_val_eq h5, UScalar.eq_of_val_eq h6]

theorem optionRel_stepRepr {o : Option page_tables.Step} {x : Option Step} (h : o.map stepOf = x) :
    OptionRel StepRepr o x := by
  subst h; cases o <;> simp [StepRepr]

/-- The ranges of the code on numbers are those of the ranges of the
specification that they stand for. -/
theorem views_eq : ∀ {l : List page_tables.LayoutRange} {m : List LayoutRange},
    ListRel LayoutRangeRepr l m → l.map viewOf = m.map viewOfL
  | [], [], _ => rfl
  | a :: l, b :: m, h => by
    obtain ⟨⟨⟨hs, hl⟩, hk⟩, h'⟩ := h
    rw [List.map_cons, List.map_cons, views_eq h']
    congr 1
    simp only [viewOf, viewOfL, PhysRange.endNat, hs, hl, hk, word64_toNat]

/-- **The plan iterator of `kernel_map` stands for its plan.** For a layout
that stands for a layout, a success of `Tables.kernelMap` with the plan
`plan`, and an iterator at its start (`KernelMapStart`) whose set has a record
of tables in use at or above that of the set before the write phase (the set
that `kernel_map` returns has the record after it), `KernelMapPlan::next`
stands for `plan`, for a record of the set before the write phase at least 2
below the largest `usize` (the cursor lemmas of the code ask for room for two
more tables at each call, even where a call takes none). -/
theorem kernel_map_plan_stands (hU : Usize64) {N : Usize} (s : page_tables.Tables N false)
    (layout : page_tables.Layout) (L : Layout) (base : U64) (bits : U8) (hL : LayoutRepr layout L)
    {S : Tables .lower N.val} {plan : Plan}
    (hk : (tablesOf s).kernelMap L (word64 base) (byte bits) = .ok (S, plan))
    (it : page_tables.KernelMapPlan N) (hstart : KernelMapStart s layout L base it)
    (hused : s.used.val ≤ it.set.used.val) (hroom : s.used.val + 2 ≤ Usize.max) :
    Stands page_tables.boot.layout.KernelMapPlan.next StepRepr it plan := by
  obtain ⟨hpool, hbase, hcur, hcount, hR⟩ := hstart
  have hmax := usize_max hU
  -- the specification: the checks pass, and the plan is `mapPlan` of the placed leaves
  cases hp : checkPool N.val (word64 base) (byte bits) with
  | error x => rw [kernelMap_pool_error (s := tablesOf s) hp] at hk; cases hk
  | ok u =>
  cases u
  cases hfo : (sortByKey (·.range.start.toNat) L.ranges).foldlM
      ((tablesOf s).checkLayoutRange (word64 base) (byte bits) L.guards) ([], []) with
  | error x => rw [kernelMap_fold_error (s := tablesOf s) hp hfo] at hk; cases hk
  | ok res =>
  obtain ⟨earlier, leaves⟩ := res
  rw [kernelMap_fold_ok (s := tablesOf s) hp hfo, tablesOf_used] at hk
  have hassign1 : (assignTables s.used.val leaves.reverse).1 = (allocOf s.used.val leaves).next := rfl
  have hassign2 : (assignTables s.used.val leaves.reverse).2 =
      (allocOf s.used.val leaves).placed.reverse := rfl
  split at hk
  · cases hk
  · rename_i hfit
    simp only [Except.ok.injEq, Prod.mk.injEq] at hk
    obtain ⟨-, hplan⟩ := hk
    rw [← hassign1] at hfit
    rw [← hassign2] at hplan
    subst hplan
    -- the pool
    obtain ⟨hw, hpf⟩ := checkPool_ok_facts hp
    obtain ⟨hN0, hfits⟩ := (poolFits_iff _ _ _).1 hpf
    have hb := (widthOk_byte_iff bits).1 hw
    rw [word64_toNat, byte_toNat] at hfits
    have h48 : 2 ^ bits.val ≤ 2 ^ 48 := Nat.pow_le_pow_right (by decide) hb.2
    have hN : 0 < N.val := Nat.pos_of_ne_zero hN0
    simp only [PAGE_SIZE] at hfits
    -- the leaves
    set rs := sortByKey (fun j : LayoutRange => j.range.start.toNat) L.ranges with hrs
    obtain ⟨new, hnew, hLL, -⟩ := layout_fold (tablesOf s) (word64 base) (byte bits) L.guards rs [] []
      (earlier, leaves) (sortByKey_pairwise _ _) (by simp) hfo
    simp only [List.append_nil] at hnew
    subst hnew
    have hviews : (it.ranges.val.take it.count.val).map viewOf = rs.map viewOfL := views_eq hR
    have hset : tablesOf it.set = (⟨(tablesOf s).pool, it.set.used.val⟩ : Tables .lower N.val) := by
      show (⟨poolOf it.set.pool, it.set.used.val⟩ : Tables .lower N.val) = ⟨poolOf s.pool, it.set.used.val⟩
      rw [hpool]
    have hSim := kernel_simOk hLL (u' := it.set.used.val) (by rw [tablesOf_used]; exact hused)
    rw [← hset, ← hviews, ← hbase] at hSim
    set NX := (assignTables s.used.val leaves.reverse).1 with hNX
    have hused_le : s.used.val ≤ NX := by
      rw [hNX, assignTables_eq]; exact next_le_stOf leaves.reverse ⟨s.used.val, none, none, []⟩
    have hnewTT : s.used.val < NX → NX ≤ N.val := fun h => by omega
    have hNXroom : NX + 2 ≤ Usize.max := by
      by_cases h : s.used.val < NX
      · have := hnewTT h; rw [hmax]; omega
      · omega
    have hc : it.count.val ≤ 16 := by rw [hcount]; exact hL.1
    have hlowL : ∀ r ∈ (it.ranges.val.take it.count.val).map viewOf,
        r.start < r.stop ∧ r.stop ≤ 2 ^ 39 := by
      rw [hviews]
      intro r hr
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hr
      obtain ⟨-, -, hw'⟩ := hLL.ranges j hj
      have hl := j.range.nonempty
      have hl' : j.range.len.toNat ≠ 0 := fun h0 => hl (UInt64.toNat_inj.1 (by rw [h0]; rfl))
      simp only [viewOfL, PhysRange.endNat] at hw' ⊢
      omega
    have hfitR : ∀ r ∈ it.ranges.val.take it.count.val,
        r.range.start.val + r.range.len.val < 2 ^ 64 := by
      intro r hr
      have := hlowL (viewOf r) (List.mem_map_of_mem hr)
      simp only [viewOf] at this
      omega
    rw [← hbase]
    refine stands_mapPlan (abs := fun it' => curOf it'.cursor)
      (Inv := fun it' => it'.set = it.set ∧ it'.base = it.base ∧ it'.ranges = it.ranges ∧
        it'.count = it.count) hSim s.used.val N.val
      (fun x hx => placeLe_of_place (hLL.place x hx)) hnewTT ?_ it ⟨rfl, rfl, rfl, rfl⟩ ?_
    · rintro it' ⟨h1, h2, h3, h4⟩ hbd
      obtain ⟨hbn, hbt2, hbt3, hbslot, hbgib⟩ := hbd
      have hcur' : CurFits it'.cursor it'.base := by
        refine ⟨by simp only [curOf] at hbn; omega, by simp only [curOf] at hbt2; rw [hmax]; omega,
          by simp only [curOf] at hbt3; rw [hmax]; omega, ?_, ?_, ?_, ?_⟩
        · rw [h2, hbase]; simp only [curOf] at hbt2
          have := Nat.mul_le_mul_left 4096 hbt2; omega
        · rw [h2, hbase]; simp only [curOf] at hbt3
          have := Nat.mul_le_mul_left 4096 hbt3; omega
        · intro hph
          have := hbslot (Or.inr (by simp only [curOf, phaseOf, hph]))
          simp only [curOf] at this; omega
        · intro hph
          have := hbgib (Or.inr (Or.inr (by simp only [curOf, phaseOf, hph])))
          simp only [curOf] at this; omega
      have hs' : it'.cursor.phase = .NewPages → it'.cursor.slot.val + 2 ^ 21 < 2 ^ 64 := by
        intro hph
        have := hbslot (Or.inl (by simp only [curOf, phaseOf, hph]))
        simp only [curOf] at this; omega
      have hg' : it'.cursor.phase = .Children ∨ it'.cursor.phase = .Entries →
          it'.cursor.gib.val + 2 ^ 30 < 2 ^ 64 := by
        intro hph
        have := hbgib (by rcases hph with hph | hph <;> simp only [curOf, phaseOf, hph] <;> simp)
        simp only [curOf] at this; omega
      have hspec := kernel_map_plan_next_spec it' hN (by rw [h4]; exact hc)
        (by rw [h3, h4]; exact hfitR) (by rw [h3, h4]; exact hlowL) hcur' hs' hg'
        (fun hseek => by
          obtain ⟨f, hf, hc'⟩ := take_seek _ _ hseek
          have hfl : f.pa < 2 ^ 39 := layoutFind_low (by rw [h3, h4]; exact hlowL) hf
          dsimp only
          rw [hc']
          refine ⟨?_, ?_, ?_, rfl⟩
          · show it'.cursor.next.val + 1 + 1 ≤ Usize.max
            simp only [curOf] at hbn; omega
          · show it'.cursor.next.val + 1 ≤ Usize.max
            simp only [curOf] at hbn; omega
          · show gibOf f.pa + 2 ^ 30 < 2 ^ 64
            simp only [gibOf, GIB_SIZE]; omega)
      rw [h1, h2, h3, h4] at hspec
      refine spec_mono hspec ?_
      rintro ⟨o, it''⟩ ⟨ho, hcur'', e1, e2, e3, e4⟩
      refine ⟨optionRel_stepRepr ho, hcur'', ⟨e1, e2, e3, e4⟩, fun hcc => ?_⟩
      have hcc' := curOf_inj hcc
      obtain ⟨a1, a2, a3, a4, a5⟩ := it''
      obtain ⟨b1, b2, b3, b4, b5⟩ := it'
      simp only at e1 e2 e3 e4 hcc' h1 h2 h3 h4
      simp only [page_tables.KernelMapPlan.mk.injEq]
      exact ⟨e1.trans h1.symm, e2.trans h2.symm, hcc', e3.trans h3.symm, e4.trans h4.symm⟩
    · rw [hcur]
      simp only [curOf, startCursor, phaseOf, no_slot_val]
      rfl

/-- `kernel_map(set, layout, base, bits)` for a layout that stands for a
layout and a record of the set at least `2 ^ 33` below the largest `usize`:
`kernel_map_set_spec`, and on success the set of the iterator is the set that
`kernel_map` returns. -/
theorem kernel_map_start_spec {N : Usize} (s : page_tables.Tables N false)
    (layout : page_tables.Layout) (L : Layout) (base : U64) (bits : U8)
    (hL : LayoutRepr layout L) (hov : s.used.val + 2 ^ 33 ≤ Usize.max) :
    page_tables.kernel_map s layout base bits ⦃ r s' =>
      Writes (fun s' S => tablesOf s' = S) (fun it _ => KernelMapStart s layout L base it)
        (tableErrorOf · = ·) s r s' ((tablesOf s).kernelMap L (word64 base) (byte bits)) ∧
        ∀ it, r = .Ok it → it.set = s' ⦄ := by
  obtain ⟨hc16, hR, hg⟩ := hL
  have hc : layout.count.val ≤ 16 := hc16
  unfold page_tables.kernel_map
  simp only [max_layout_ranges_eq]
  step*
  · have hp : checkPool N.val (word64 base) (byte bits) = .ok () := by
      obtain ⟨u, hu, -⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf_post ‹_› r_post); rw [hu]
    obtain ⟨hw, hpf⟩ := checkPool_ok_facts hp
    have hN : 0 < N.val := Nat.pos_of_ne_zero ((poolFits_iff _ _ _).1 hpf).1
    have hb : bits.val < 64 := lt_64_of_widthOk hw
    have hcnt : (if layout.count < 16#usize then ok layout.count else ok 16#usize :
        Result Usize) = ok layout.count := by
      split
      · rfl
      · rename_i h
        have h16 : layout.count.val = 16 := by have := h; scalar_tac
        rw [show (16#usize : Usize) = layout.count from UScalar.eq_of_val_eq (by rw [h16]; rfl)]
    rw [hcnt, bind_ok]
    step*
    have hR' : ListRel LayoutRangeRepr (ranges.val.take layout.count.val)
        (sortByKey (·.range.start.toNat) L.ranges) := by
      rw [ranges_post]
      exact listRel_sortByKey (fun a b hab => (physRange_start hab.1).symm) _ _ hR
    have hcl := check_layout_spec s ranges layout.count layout.guards base bits _ hN hb hc hR'
      (sortByKey_pairwise _ _) hov
    rw [← hg] at hcl
    refine WP.spec_bind hcl ?_
    intro r1 hr1
    step*
    · obtain ⟨⟨earlier, leaves⟩, -, hrel⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf1_post ‹_› hr1)
      exact hrel.2.2.2
    · obtain ⟨⟨earlier, leaves⟩, hy, hrel⟩ :=
        agrees_ok_iff.1 (agrees_of_branch_ok cf1_post ‹_› hr1)
      have hnext : (allocOf s.used.val leaves).next = val.next.val := hrel.2.1.1
      rw [kernelMap_fold_ok (s := tablesOf s) hp hy, tablesOf_used, hnext]
      have hr2 := branch_ok cf2_post ‹_›
      by_cases hcond : N.val - s.used.val < val.next.val - s.used.val
      · simp only [hcond, ↓reduceIte] at r2_post
        rw [hr2] at r2_post
        cases r2_post.1
      · simp only [hcond, ↓reduceIte] at r2_post ⊢
        rw [hr2] at r2_post
        obtain ⟨hv1, hs1⟩ := r2_post
        cases hv1
        refine ⟨⟨⟨by rw [hs1], rfl, rfl, rfl, hR'⟩, ?_⟩, fun it h => by cases h; rfl⟩
        rw [hs1]
        rfl
    · obtain ⟨⟨earlier, leaves⟩, hy, hrel⟩ :=
        agrees_ok_iff.1 (agrees_of_branch_ok cf1_post ‹_› hr1)
      have hnext : (allocOf s.used.val leaves).next = val.next.val := hrel.2.1.1
      rw [kernelMap_fold_ok (s := tablesOf s) hp hy, tablesOf_used, hnext]
      have hr2 := branch_err cf2_post ‹_› residual_post
      by_cases hcond : N.val - s.used.val < val.next.val - s.used.val
      · simp only [hcond, ↓reduceIte] at r2_post ⊢
        rw [hr2] at r2_post
        obtain ⟨he, hs1⟩ := r2_post
        cases he
        refine ⟨?_, fun it h => by rw [r3_post] at h; cases h⟩
        rw [r3_post, ← e_post, hs1]
        exact ⟨rfl, rfl⟩
      · simp only [hcond, ↓reduceIte] at r2_post
        rw [hr2] at r2_post
        cases r2_post.1
    · refine ⟨?_, fun it h => by rw [r2_post] at h; cases h⟩
      rw [kernelMap_fold_error (s := tablesOf s) hp
        (agrees_err_of_branch cf1_post ‹_› residual_post hr1), r2_post, e_post]
      exact ⟨rfl, rfl⟩
  · refine ⟨?_, fun it h => by rw [r2_post] at h; cases h⟩
    rw [kernelMap_pool_error (s := tablesOf s) (agrees_err_of_branch cf_post ‹_› residual_post r_post),
      r2_post, e_post]
    exact ⟨rfl, rfl⟩

/-- **`KernelMap` for a record with room.** The conclusion of the statement
`KernelMap` for a layout that stands for a layout and a set whose record of
tables in use is at least `2 ^ 33` below the largest `usize`: the premise of
the checks of the code (`kernel_map_set_spec`), which is all that this
theorem adds to the statement. -/
theorem kernel_map_of_room (hU : Usize64) {N : Usize} (s : page_tables.Tables N false)
    (layout : page_tables.Layout) (L : Layout) (base : U64) (bits : U8)
    (hL : LayoutRepr layout L) (hov : s.used.val + 2 ^ 33 ≤ Usize.max) :
    page_tables.kernel_map s layout base bits ⦃ r s' =>
      Writes (fun s' S => tablesOf s' = S) (Stands page_tables.boot.layout.KernelMapPlan.next StepRepr)
        (tableErrorOf · = ·) s r s' ((tablesOf s).kernelMap L (word64 base) (byte bits)) ⦄ := by
  refine spec_mono (kernel_map_start_spec s layout L base bits hL hov) ?_
  rintro ⟨r, s'⟩ ⟨hw, hset⟩
  cases hk : (tablesOf s).kernelMap L (word64 base) (byte bits) with
  | error e =>
    rw [hk] at hw
    cases r with
    | Ok it => exact hw.elim
    | Err x => exact hw
  | ok tp =>
    obtain ⟨S, plan⟩ := tp
    rw [hk] at hw
    cases r with
    | Err x => exact hw.elim
    | Ok it =>
      obtain ⟨hstart, hrepr⟩ := hw
      have hs' := hset it rfl
      have hle := kernelMap_used_le hk
      refine ⟨kernel_map_plan_stands hU s layout L base bits hL hk it hstart ?_ (by omega), hrepr⟩
      rw [hs']
      show (tablesOf s).used ≤ (tablesOf s').used
      rw [hrepr]
      exact hle

end Krepi.Proofs.PageTables.Refinement
