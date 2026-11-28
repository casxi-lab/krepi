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
  `Stands KernelMapPlan.next StepRepr` of the plan. The cursor takes a new
  table only when the plan has one, and then its next free table stays at or
  below the record after the write phase, which is at most `N`; so no call
  overflows, whatever the record of the set.
- `kernel_map_spec`: the conclusion of the statement `KernelMap`, from
  `kernel_map_set_spec` and `kernel_map_plan_stands`.
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
stands for `plan`. -/
theorem kernel_map_plan_stands (hU : Usize64) {N : Usize} (s : page_tables.Tables N false)
    (layout : page_tables.Layout) (L : Layout) (base : U64) (bits : U8) (hL : LayoutRepr layout L)
    {S : Tables .lower N.val} {plan : Plan}
    (hk : (tablesOf s).kernelMap L (word64 base) (byte bits) = .ok (S, plan))
    (it : page_tables.KernelMapPlan N) (hstart : KernelMapStart s layout L base it)
    (hused : s.used.val ≤ it.set.used.val) :
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
    -- the next free table of the cursor stays at or below `NX`, a `usize`
    have hNXmax : NX ≤ Usize.max := by
      by_cases h : s.used.val < NX
      · have := hnewTT h; scalar_tac
      · have : NX ≤ s.used.val := by omega
        scalar_tac
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
    · rintro it' ⟨h1, h2, h3, h4⟩ hbd hbd'
      obtain ⟨⟨-, hbt2, hbt3, hbslot, hbgib⟩, -⟩ := hbd
      have hcur' : CurFits it'.cursor it'.base := by
        refine ⟨by simp only [curOf] at hbt2; rw [hmax]; omega,
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
      have hn' : ((curOf it'.cursor).step
          (fun f l _ => layoutFind ((it'.ranges.val.take it'.count.val).map viewOf) f l)
          (placeOr (tablesOf it'.set) (word64 it'.base)) (word64 it'.base)).2.next ≤ Usize.max := by
        rw [h1, h2, h3, h4]
        exact Nat.le_trans hbd'.1.1 hNXmax
      have hspec := kernel_map_plan_next_spec it' hN (by rw [h4]; exact hc)
        (by rw [h3, h4]; exact hfitR) (by rw [h3, h4]; exact hlowL) hcur' hs' hg' hn'
        (fun hseek => by
          have hle := Nat.le_trans (take_next_le_step
            (fun f l _ => layoutFind ((it'.ranges.val.take it'.count.val).map viewOf) f l)
            (placeOr (tablesOf it'.set) (word64 it'.base)) (word64 it'.base) (curOf it'.cursor)) hn'
          obtain ⟨f, hf, hc'⟩ := take_seek _ _ hseek
          have hfl : f.pa < 2 ^ 39 := layoutFind_low (by rw [h3, h4]; exact hlowL) hf
          rw [hc'] at hle
          dsimp only
          rw [hc']
          refine ⟨hle, ?_, rfl⟩
          show gibOf f.pa + 2 ^ 30 < 2 ^ 64
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

/-- **The statement `KernelMap`, with `N` implicit.** `kernel_map` on a
layout that stands for a layout, on a 64-bit `usize`: the set after the
write phase of `Tables.kernelMap` with a plan iterator that stands for its
plan, or its error with the set unchanged. -/
theorem kernel_map_spec (hU : Usize64) {N : Usize} (s : page_tables.Tables N false)
    (layout : page_tables.Layout) (L : Layout) (base : U64) (bits : U8)
    (hL : LayoutRepr layout L) :
    page_tables.kernel_map s layout base bits ⦃ r s' =>
      Writes (fun s' S => tablesOf s' = S) (Stands page_tables.boot.layout.KernelMapPlan.next StepRepr)
        (tableErrorOf · = ·) s r s' ((tablesOf s).kernelMap L (word64 base) (byte bits)) ⦄ := by
  refine spec_mono (kernel_map_set_spec hU s layout L base bits hL) ?_
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
      refine ⟨kernel_map_plan_stands hU s layout L base bits hL hk it hstart ?_, hrepr⟩
      rw [hs']
      show (tablesOf s).used ≤ (tablesOf s').used
      rw [hrepr]
      exact hle

end Krepi.Proofs.PageTables.Refinement
