module

public import Krepi.Proofs.PageTables.Refinement.DirectLemmas
public import Krepi.Proofs.PageTables.Refinement.KernelPlanLemmas
public import Krepi.Proofs.PageTables.Refinement.DirectPlanSpecLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: the plan iterator of `direct_map` stands for its plan

The plan iterator that `direct_map` returns, `DirectMapPlan`, stands for the
plan `mapPlan` of `Tables.directMap`. Each call of `DirectMapPlan::next` is
one call of the cursor on numbers, `Cur.step`, with the leaf search
`directFind` of the saved state of the iterator of the usable ranges
(`direct_map_plan_next_spec`); while the cursor keeps `SearchK` and the
ranges that the state skipped end at or below its `lowB`, that search is the
search `usableFind` of all the usable ranges at every address the call reads
(`step_congr_find`); the leaves of the usable ranges that passed the checks
satisfy `SimOk` with that search (`direct_simOk`); and the simulation
`stands_mapPlan` (`Krepi.Proofs.PageTables.Refinement.PlanSimSpecLemmas`)
turns them into `Stands`.

- `direct_map_plan_stands`: from the success of `Tables.directMap` on a
  well-formed boot memory map and an iterator at its start
  (`DirectMapStart`) on a set whose record of tables in use is at or above
  that of the set before the write phase, `Stands DirectMapPlan.next
  StepRepr` of the plan. The cursor takes a new table only when the plan has
  one, and then its next free table stays at or below the record after the
  write phase, which is at most `N`; so no call overflows, whatever the
  record of the set.
- `direct_map_spec`: the conclusion of the statement `DirectMap`, from
  `direct_map_set_spec` and `direct_map_plan_stands`.
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.PageTables Krepi.Spec.PageTables Krepi.Statements Krepi.Statements.PageTables
open Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

/-- **The plan iterator of `direct_map` stands for its plan.** For a
well-formed boot memory map `P`, a success of `Tables.directMap` with the
plan `plan`, and an iterator at its start (`DirectMapStart`) whose set has a
record of tables in use at or above that of the set before the write phase
(the set that `direct_map` returns has the record after it),
`DirectMapPlan::next` stands for `plan`. -/
theorem direct_map_plan_stands (hU : Usize64) {N : Usize} (s : page_tables.Tables N true)
    (P : Krepi.Spec.Fdt.MemoryPlan) (base : U64) (bits : U8) (hw : P.WellFormed)
    {S : Tables .upper N.val} {plan : Plan}
    (hd : (tablesOf s).directMap P (word64 base) (byte bits) = .ok (S, plan))
    (it : page_tables.DirectMapPlan N) (hstart : DirectMapStart s P base it)
    (hused : s.used.val ≤ it.set.used.val) :
    Stands page_tables.boot.direct.DirectMapPlan.next StepRepr it plan := by
  have hmax := usize_max hU
  have hsl0 := searchList_start hstart
  obtain ⟨hpool, hbase, hcur, hm0, hr0, -, -, -, -⟩ := hstart
  obtain ⟨-, hpw, -⟩ := usable_wf hw
  have hsorted := usable_sorted hw
  have hUs := usable_ranges_ok hw
  have hlow := directMap_ok_low hw hd
  have hok0 := searchOk_start hw hd
  have hM : ∀ b ∈ P.managed, b.Valid := fun b hb => (hw.2.2.2.2.2.2.1 b hb).1.2
  have hRs : ∀ r ∈ P.reservations, r.Nonempty :=
    fun r hr => (Krepi.Proofs.Fdt.reservations_wf hw r hr).1
  -- the specification: the checks pass, and the plan is `mapPlan` of the placed leaves
  cases hp : checkPool N.val (word64 base) (byte bits) with
  | error x => rw [directMap_pool_error (s := tablesOf s) hp] at hd; cases hd
  | ok u =>
  cases u
  cases hfo : (sortByKey (·.start.toNat) P.availableRanges).foldlM
      ((tablesOf s).checkUsableRange (word64 base) (byte bits)) ([], []) with
  | error x => rw [directMap_fold_error (s := tablesOf s) hp hfo] at hd; cases hd
  | ok res =>
  obtain ⟨earlier, leaves⟩ := res
  rw [directMap_fold_ok (s := tablesOf s) hp hfo, tablesOf_used] at hd
  have hassign1 : (assignTables s.used.val leaves.reverse).1 = (allocOf s.used.val leaves).next := rfl
  have hassign2 : (assignTables s.used.val leaves.reverse).2 =
      (allocOf s.used.val leaves).placed.reverse := rfl
  split at hd
  · cases hd
  · rename_i hfit
    simp only [Except.ok.injEq, Prod.mk.injEq] at hd
    obtain ⟨-, hplan⟩ := hd
    rw [← hassign1] at hfit
    rw [← hassign2] at hplan
    subst hplan
    -- the pool
    obtain ⟨hwd, hpf⟩ := checkPool_ok_facts hp
    obtain ⟨hN0, hfits⟩ := (poolFits_iff _ _ _).1 hpf
    have hb := (widthOk_byte_iff bits).1 hwd
    rw [word64_toNat, byte_toNat] at hfits
    have h48 : 2 ^ bits.val ≤ 2 ^ 48 := Nat.pow_le_pow_right (by decide) hb.2
    have hN : 0 < N.val := Nat.pos_of_ne_zero hN0
    simp only [PAGE_SIZE] at hfits
    -- the leaves
    rw [hsorted] at hfo
    obtain ⟨new, hnew, hmap, hplace⟩ := direct_fold (tablesOf s) (word64 base) (byte bits)
      P.availableRanges [] [] (earlier, leaves) hfo
    simp only [List.append_nil] at hnew
    subst hnew
    have hplace' : ∀ x ∈ leaves.reverse, (tablesOf s).place (word64 base) x.1 = .ok x.2 :=
      fun x hx => hplace x (List.mem_reverse.1 hx)
    have hset : tablesOf it.set =
        ({ tablesOf s with used := it.set.used.val } : Tables .upper N.val) := by
      show (⟨poolOf it.set.pool, it.set.used.val⟩ : Tables .upper N.val) =
        ⟨poolOf s.pool, it.set.used.val⟩
      rw [hpool]
    have hSim := direct_simOk hmap hplace' hUs hlow hpw (u' := it.set.used.val)
      (by rw [tablesOf_used]; exact hused)
    rw [← hset, ← hbase] at hSim
    set NX := (assignTables s.used.val leaves.reverse).1 with hNX
    have hnewTT : s.used.val < NX → NX ≤ N.val := fun h => by omega
    -- the next free table of the cursor stays at or below `NX`, a `usize`
    have hNXmax : NX ≤ Usize.max := by
      by_cases h : s.used.val < NX
      · have := hnewTT h; scalar_tac
      · have : NX ≤ s.used.val := by omega
        scalar_tac
    rw [← hbase]
    refine stands_mapPlan (abs := fun it' => curOf it'.cursor)
      (Inv := fun it' => it'.set = it.set ∧ it'.base = it.base ∧
        spansOf it'.ranges.managed = P.managed ∧ spansOf it'.ranges.reservations = P.reservations ∧
        SearchK (curOf it'.cursor) ∧
        ∃ sk, (⟨0, 0⟩ :: P.availableRanges : List Krepi.Spec.Fdt.Span) =
            sk ++ searchList P.managed P.reservations it'.ranges it'.range ∧
          ∀ u ∈ sk, u.endNat ≤ lowB (curOf it'.cursor))
      hSim s.used.val N.val (fun x hx => placeLe_of_place (hplace' x hx)) hnewTT ?_ it
      ⟨rfl, rfl, hm0, hr0, ?_, [], by rw [hsl0]; rfl, fun u hu => absurd hu List.not_mem_nil⟩ ?_
    · rintro it' ⟨h1, h2, hm', hr', hK, sk, hsk, hskb⟩ hbd hbd'
      obtain ⟨⟨-, hbt2, hbt3, hbslot, hbgib⟩, L, hsp⟩ := hbd
      have hok : SearchOk (searchList P.managed P.reservations it'.ranges it'.range) :=
        fun u hu => hok0 u (by rw [hsk]; exact List.mem_append_right _ hu)
      have hfo' := findOk_of_split hSim hsp
      have hlowc := searchK_low hK
      have hfind : ∀ f l p, lowB (curOf it'.cursor) ≤ f →
          directFind P.managed P.reservations it'.ranges it'.range f l p =
            usableFind (P.availableRanges.map spanView) f l p :=
        fun f l p hf => directFind_eq_of_skip hsk hskb f l p hf
      have hstep : ∀ (pl : Found → Place) (b : UInt64),
          (curOf it'.cursor).step (directFind P.managed P.reservations it'.ranges it'.range) pl b =
            (curOf it'.cursor).step (fun f l p => usableFind (P.availableRanges.map spanView) f l p)
              pl b :=
        fun pl b => step_congr_find hlowc (fun l p f hf => (hfo' l p f hf).1) hfind
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
          (directFind P.managed P.reservations it'.ranges it'.range)
          (placeOr (tablesOf it'.set) (word64 it'.base)) (word64 it'.base)).2.next ≤ Usize.max := by
        rw [hstep, h1, h2]
        exact Nat.le_trans hbd'.1.1 hNXmax
      have hspec := direct_map_plan_next_spec it' P.managed P.reservations hN hM hRs hm' hr' hok
        hcur' hs' hg' hn' (fun hseek => by
          have hle := Nat.le_trans (take_next_le_step
            (directFind P.managed P.reservations it'.ranges it'.range)
            (placeOr (tablesOf it'.set) (word64 it'.base)) (word64 it'.base) (curOf it'.cursor)) hn'
          have hfe := hfind (curOf it'.cursor).search.1 (curOf it'.cursor).search.2.1
            (curOf it'.cursor).search.2.2 (by rw [cur_search_frm]; exact hlowc)
          simp only [hfe] at hseek hle ⊢
          obtain ⟨f, hf, hc'⟩ := take_seek _ _ hseek
          have hfl : f.pa < 2 ^ 39 :=
            (hfo' _ _ f (by rw [← cur_search_frm]; exact hf)).2.2.1
          rw [hc'] at hle
          rw [hc']
          refine ⟨hle, ?_⟩
          show gibOf f.pa + 2 ^ 30 < 2 ^ 64
          simp only [gibOf, GIB_SIZE]; omega)
      rw [h1, h2, hstep] at hspec
      refine spec_mono hspec ?_
      rintro ⟨o, it''⟩ ⟨ho, hcur'', e1, e2, em, er, hframe, skipped, hsk2, hskb2⟩
      obtain ⟨hK2, hK3⟩ := searchK_step (base := word64 it.base) hSim hK hsp
      have hK2' : SearchK (curOf it''.cursor) := by rw [hcur'']; exact hK2
      have hK3' : (curOf it''.cursor).gib ≠ (curOf it'.cursor).gib →
          (curOf it'.cursor).frm ≤ lowB (curOf it''.cursor) := by rw [hcur'']; exact hK3
      have hfix : curOf it''.cursor = curOf it'.cursor → it'' = it' := by
        intro hcc
        have hcc' := curOf_inj hcc
        obtain ⟨hr1, hr2⟩ := hframe (by rw [hcc'])
        obtain ⟨a1, a2, a3, a4, a5⟩ := it''
        obtain ⟨b1, b2, b3, b4, b5⟩ := it'
        simp only at e1 e2 hcc' h1 h2 hr1 hr2
        simp only [page_tables.DirectMapPlan.mk.injEq]
        exact ⟨e1.trans h1.symm, e2.trans h2.symm, hcc', hr1, hr2⟩
      refine ⟨optionRel_stepRepr ho, hcur'', ⟨e1, e2, em, er, hK2', ?_⟩, hfix⟩
      by_cases hgc : it''.cursor.gib = it'.cursor.gib
      · obtain ⟨hr1, hr2⟩ := hframe hgc
        have hlb : lowB (curOf it''.cursor) = lowB (curOf it'.cursor) := by
          unfold lowB curOf; rw [hgc]
        exact ⟨sk, by rw [hr1, hr2]; exact hsk, fun u hu => by rw [hlb]; exact hskb u hu⟩
      · have hgc' : (curOf it''.cursor).gib ≠ (curOf it'.cursor).gib :=
          fun h => hgc (UScalar.eq_of_val_eq h)
        have hle := hK3' hgc'
        refine ⟨sk ++ skipped, by rw [hsk, hsk2, List.append_assoc], fun u hu => ?_⟩
        rcases List.mem_append.1 hu with hu | hu
        · exact Nat.le_trans (hskb u hu) (Nat.le_trans hlowc hle)
        · exact Nat.le_trans (hskb2 u hu) hle
    · rw [hcur]
      simp only [curOf, startCursor, phaseOf, no_slot_val]
      exact searchK_start _
    · rw [hcur]
      simp only [curOf, startCursor, phaseOf, no_slot_val]
      rfl

/-- **The statement `DirectMap`, with `N` implicit.** `direct_map` on a map
that stands for a boot memory map that the fdt entries built, on a 64-bit
`usize`: the set after the write phase of `Tables.directMap` with a plan
iterator that stands for its plan, or its error with the set unchanged. -/
theorem direct_map_spec (hU : Usize64) {N : Usize} (s : page_tables.Tables N true)
    (memory : fdt.MemoryPlan) (P : Krepi.Spec.Fdt.MemoryPlan) (base : U64) (bits : U8)
    (hP : MemoryPlanRepr memory P) (hB : Witnesses.TableSets.BuiltPlan P) :
    page_tables.direct_map s memory base bits ⦃ r s' =>
      Writes (fun s' S => tablesOf s' = S)
        (Stands page_tables.boot.direct.DirectMapPlan.next StepRepr)
        (tableErrorOf · = ·) s r s' ((tablesOf s).directMap P (word64 base) (byte bits)) ⦄ := by
  refine spec_mono (direct_map_set_spec s memory P base bits hP hB) ?_
  rintro ⟨r, s'⟩ ⟨hw, hset⟩
  cases hk : (tablesOf s).directMap P (word64 base) (byte bits) with
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
      have hle := directMap_used_le hk
      refine ⟨direct_map_plan_stands hU s P base bits (builtPlan_wellFormed hB) hk it hstart ?_,
        hrepr⟩
      rw [hs']
      show (tablesOf s).used ≤ (tablesOf s').used
      rw [hrepr]
      exact hle

end Krepi.Proofs.PageTables.Refinement
