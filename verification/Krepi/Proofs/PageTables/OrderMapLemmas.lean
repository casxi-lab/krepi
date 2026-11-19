module

public import Krepi.Proofs.PageTables.OrderLemmas
public import Krepi.Proofs.PageTables.MapWriteLemmas
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.WalkLemmas

/-!
# Page tables: the units of the plan of a map

The steps of the plan of a map (`mapPlan`) come in units, each checked
against a well-formed set that holds the tables of the units before it:

- entries after a plan: `lastAt_some`, `get_exec_cases` (an entry after a plan
  is the old one, the value of a store of the plan into it, or 0 after a
  `Zero` of its table), `get_exec_untouched` (an entry of a table that no step
  writes);
- the units: `ukey` (one key for a 1 GiB slot under a new level 2 table and
  one for each 2 MiB slot under a level 2 table of the set, ascending with the
  address), `ukey_gib`, `ukey_eq`, `unitSteps`, and what a unit needs of the
  set before it, `UnitFacts`;
- `held_allOk` (the steps of a 2 MiB slot under a level 2 table of the set
  pass their checks) and `new_allOk` (those of a 1 GiB slot under a new level
  2 table).
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables

variable {r : Region} {N : Nat}

/-! ## Entries after a plan -/

theorem lastAt_some {t i : Nat} {d : UInt64} : ∀ {plan : Plan}, lastAt t i plan = some d →
    Step.store t i d ∈ plan ∨ (Step.zero t ∈ plan ∧ d = 0)
  | [], h => by simp [lastAt] at h
  | x :: rest, h => by
    simp only [lastAt] at h
    cases hr : lastAt t i rest with
    | some d' =>
      rw [hr] at h; simp only [Option.some_or, Option.some.injEq] at h; subst h
      rcases lastAt_some hr with h | ⟨h, h'⟩
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr ⟨List.mem_cons_of_mem _ h, h'⟩
    | none =>
      rw [hr, Option.none_or] at h
      cases x with
      | zero u =>
        simp only [stepAt] at h; split at h
        · rename_i hu; subst hu; simp only [Option.some.injEq] at h; subst h
          exact Or.inr ⟨List.mem_cons_self, rfl⟩
        · cases h
      | store u j e =>
        simp only [stepAt] at h; split at h
        · rename_i hu; obtain ⟨rfl, rfl⟩ := hu; simp only [Option.some.injEq] at h; subst h
          exact Or.inl List.mem_cons_self
        · cases h
      | _ => simp [stepAt] at h

theorem get_exec_cases (plan : Plan) (p : Pool N) (t i : Nat) :
    (plan.exec p).get t i = p.get t i ∨ Step.store t i ((plan.exec p).get t i) ∈ plan ∨
      (Step.zero t ∈ plan ∧ (plan.exec p).get t i = 0) := by
  by_cases ht : t < N
  · by_cases hi : i < ENTRIES
    · rw [get_exec _ _ ht hi]
      cases h : lastAt t i plan with
      | none => exact Or.inl rfl
      | some d =>
        simp only [Option.getD_some]
        rcases lastAt_some h with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
    · left; rw [get_of_ge_entries _ _ (by omega), get_of_ge_entries _ _ (by omega)]
  · left; rw [get_of_ge _ _ (by omega), get_of_ge _ _ (by omega)]

theorem get_exec_untouched {plan : Plan} {p : Pool N} {t : Nat}
    (h : ∀ x ∈ plan, x.writes t = false) (i : Nat) : (plan.exec p).get t i = p.get t i := by
  rcases get_exec_cases plan p t i with e | e | ⟨e, -⟩
  · exact e
  · have := h _ e; simp [Step.writes] at this
  · have := h _ e; simp [Step.writes] at this

private theorem reached_exec_fresh {p : Pool N} {base : UInt64} {T : Nat → Prop} {steps : Plan}
    (hT : ∀ x ∈ steps, ∀ u, x.writes u = true → T u) (hf : ∀ u, T u → u ∉ p.reached base) :
    (steps.exec p).reached base = p.reached base ∧
      (steps.exec p).children base 0 = p.children base 0 :=
  reached_congr fun t ht i _ => by
    rw [get_exec_untouched (fun x hx => ?_) i]
    cases hw : x.writes t
    · rfl
    · exact absurd ht (hf t (hT x hx t hw))

private theorem poolChild_zero {base : UInt64} : poolChild? N base 0 = none := poolChild_none (by decide)

private theorem walked_tableAt {base : UInt64} {c : Nat} (b : Bool) :
    walkedAsWritten b (tableAt base c) = true := by
  simp [walkedAsWritten, tableAt, isPlain_tableDescriptor]

private theorem ok_link {st : PlanState N} {base : UInt64} {bits : UInt8} (hp : PoolOk N base bits)
    {t i c : Nat} (hcN : c < N) (hr : t ∈ st.pool.reached base)
    (ht : t ≠ 0 ∨ ∀ j, j < ENTRIES → walkedAsWritten true (st.pool.get c j) = true)
    (hz : t ∉ st.zeroed) (hv : isValid (st.pool.get t i) = false) (hcz : c ∈ st.zeroed)
    (hcs : c ∉ st.sealed) (hcr : c ∉ st.pool.reached base) (hd : st.dirty = [])
    (hch : ∀ u ∈ st.pool.children base c, u ∈ st.zeroed) :
    okStep base st (.store t i (tableAt base c)) = true := by
  refine ok_store_reached hr (Or.inr (walked_tableAt false)) (Or.inr (walked_tableAt true)) hz hv
    fun c' h => ?_
  rw [poolChild_tableAt hp hcN, Option.some.injEq] at h; subst h
  refine ⟨hcz, hcs, ht, hcr, fun u hu => ⟨?_, by rw [hd]; simp⟩⟩
  rcases List.mem_cons.1 hu with rfl | hu
  · exact hcz
  · exact hch u hu

private theorem foldl_fence_dirty (base : UInt64) (a : Plan) (st : PlanState N) :
    ((a ++ [Step.fence]).foldl (nxt base) st).dirty = [] := by
  rw [List.foldl_append]; rfl

/-! ## The units of a plan -/

/-- The key of the unit of a placed leaf: its 1 GiB slot under a new level 2
table, its 2 MiB slot otherwise, in address order. -/
def ukey (q : Placed) : Nat :=
  if q.new2 then 2 * (q.leaf.gibSlot * ENTRIES) else 2 * q.leaf.blockSlot + 1

/-- The steps of one unit of the plan of a map. -/
def unitSteps (base : UInt64) : List Placed → Plan
  | [] => []
  | q :: rest => if q.new2 then newLevel2Steps base (q :: rest) else heldLevel2Steps base (q :: rest)

private theorem block_gib (a : MapLeaf) : a.blockSlot / ENTRIES = a.gibSlot := by
  simp only [MapLeaf.blockSlot, MapLeaf.gibSlot, BLOCK_SIZE, GIB_SIZE, ENTRIES]; omega

theorem ukey_gib (q : Placed) : ukey q / (2 * ENTRIES) = q.leaf.gibSlot := by
  have := block_gib q.leaf
  unfold ukey; split <;> simp only [ENTRIES] at this ⊢ <;> omega

theorem ukey_eq {q q' : Placed} (h : ukey q = ukey q') :
    q.new2 = q'.new2 ∧ q.leaf.gibSlot = q'.leaf.gibSlot ∧
      (q.new2 = false → q.leaf.blockSlot = q'.leaf.blockSlot) := by
  have hg := (ukey_gib q).symm.trans (h ▸ ukey_gib q')
  unfold ukey at h
  cases hn : q.new2 <;> cases hn' : q'.new2 <;> simp only [hn, hn', ite_true, ite_false,
    Bool.false_eq_true] at h
  · exact ⟨rfl, hg, fun _ => by omega⟩
  · omega
  · omega
  · exact ⟨rfl, hg, fun h => by cases h⟩

/-- What a unit of placed leaves needs of the set before it. -/
structure UnitFacts (S : Tables r N) (base : UInt64) (bits : UInt8) (U : List Placed) : Prop where
  ok : PlacedOk U
  order : U.Pairwise (fun q q' => q.leaf.va.toNat + q.leaf.form.size ≤ q'.leaf.va.toNat)
  desc : ∀ q ∈ U, LeafDesc bits q.leaf
  fresh : ∀ q ∈ U, ∀ c, NewTable q c → S.used ≤ c ∧ c < N
  new2 : ∀ q ∈ U, q.new2 = true → S.entry 0 (index1 q.leaf.va) = 0
  old2 : ∀ q ∈ U, q.new2 = false → S.PointsAt base 0 (index1 q.leaf.va) q.t2 ∧ S.IsLevel2 base q.t2
  new3 : ∀ q ∈ U, q.leaf.form = .page → q.new3 = true → q.new2 = false →
    S.entry q.t2 (index2 q.leaf.va) = 0
  old3 : ∀ q ∈ U, q.leaf.form = .page → q.new3 = false →
    S.PointsAt base q.t2 (index2 q.leaf.va) q.t3 ∧ S.IsLevel3 base q.t3 ∧
      S.entry q.t3 (index3 q.leaf.va) = 0
  block : ∀ q ∈ U, q.leaf.form = .block → q.new2 = false → S.entry q.t2 (index2 q.leaf.va) = 0

private theorem index3_lt_of {a b : MapLeaf} (hb : a.blockSlot = b.blockSlot)
    (h : a.va.toNat + a.form.size ≤ b.va.toNat) : index3 a.va < index3 b.va := by
  have h1 := page_index a.va
  have h2 := page_index b.va
  have := form_size_pos a.form
  have hs : PAGE_SIZE ≤ a.form.size := by cases a.form <;> decide
  simp only [MapLeaf.blockSlot] at hb
  rw [hb] at h1
  simp only [PAGE_SIZE, ENTRIES] at h1 h2 hs
  have : a.va.toNat / 4096 < b.va.toNat / 4096 := by omega
  omega

private theorem index2_lt_of {a b : MapLeaf} (hg : a.gibSlot = b.gibSlot) (h : a.blockSlot < b.blockSlot) :
    index2 a.va < index2 b.va := by
  have h1 := block_index a.va
  have h2 := block_index b.va
  simp only [MapLeaf.blockSlot, MapLeaf.gibSlot] at hg h
  rw [hg] at h1
  omega

/-! ## A unit under a level 2 table of the set -/

section Held

variable {S : Tables r N} {base : UInt64} {bits : UInt8}

theorem held_allOk (hs : S.WellFormed base bits) {q0 : Placed} {rest : List Placed}
    (hu : UnitFacts S base bits (q0 :: rest))
    (hk : ∀ q ∈ q0 :: rest, q.leaf.blockSlot = q0.leaf.blockSlot) (hn : q0.new2 = false)
    {st : PlanState N} (hp : st.pool = S.pool)
    (hz : ∀ c ∈ st.zeroed, c < S.used ∧ c ≠ q0.t2 ∧
      (q0.leaf.form = .page → q0.new3 = false → c ≠ q0.t3))
    (hsl : ∀ c ∈ st.sealed, c < S.used) :
    allOk base st (heldLevel2Steps base (q0 :: rest)) = true := by
  have hq0 : q0 ∈ q0 :: rest := List.mem_cons_self
  have hsame : ∀ q ∈ q0 :: rest, q.leaf.form = q0.leaf.form ∧ q.new3 = q0.new3 ∧ q.t3 = q0.t3 ∧
      q.t2 = q0.t2 ∧ index2 q.leaf.va = index2 q0.leaf.va := fun q hq => by
    obtain ⟨a, b, c⟩ := hu.ok.block q hq q0 hq0 (hk q hq)
    exact ⟨a, b, c, (hu.ok.gib q hq q0 hq0 (gib_of_block (hk q hq))).2, index2_of_block (hk q hq)⟩
  obtain ⟨hpa2, hl2⟩ := hu.old2 q0 hq0 hn
  have ht2r : q0.t2 ∈ st.pool.reached base := by
    rw [hp]; exact (wf_mem_reached hs).2 (wf_level2_lt hl2).1
  have ht20 : q0.t2 ≠ 0 := wf_level2_ne_zero hs hl2
  cases hf : q0.leaf.form with
  | block =>
    have hr : rest = [] := by
      cases rest with
      | nil => rfl
      | cons q rest' =>
        have hq : q ∈ q0 :: q :: rest' := List.mem_cons_of_mem _ List.mem_cons_self
        have := hu.ok.blockOne q0 hq0 q hq (hk q hq).symm hf
        have h' := List.rel_of_pairwise_cons hu.order List.mem_cons_self
        rw [← this] at h'; have := form_size_pos q0.leaf.form; omega
    subst hr
    have hd := hu.desc q0 hq0
    simp only [heldLevel2Steps, hf, List.map_cons, List.map_nil, Placed.store]
    have := leaves_allOk (base := base) [(q0.t2, index2 q0.leaf.va, q0.leaf.desc)] st
      (fun x hx => by
        rw [List.mem_singleton] at hx; subst hx
        refine ⟨ht2r, ht20, fun h => (hz _ h).2.1 rfl, ?_, poolChild_none (leaf_not_plain hd),
          Or.inr ?_⟩
        · rw [hp, ← entry_eq_get, hu.block q0 hq0 hf hn]; decide
        · have := typeBits_of_isReadWriteBlock (hd.2 hf).1
          simp [walkedAsWritten, this]) (List.pairwise_singleton _ _)
    simpa using this
  | page =>
    have hpg : ∀ q ∈ q0 :: rest, q.store = .store q0.t3 (index3 q.leaf.va) q.leaf.desc := fun q hq => by
      obtain ⟨a, -, c, -⟩ := hsame q hq
      simp only [Placed.store, a, hf, c]
    have hmap : (q0 :: rest).map Placed.store =
        ((q0 :: rest).map fun q => (index3 q.leaf.va, q.leaf.desc)).map
          fun x => Step.store q0.t3 x.1 x.2 := by
      rw [List.map_map]; exact List.map_congr_left hpg
    have hord : ((q0 :: rest).map fun q => (index3 q.leaf.va, q.leaf.desc)).Pairwise
        (fun x y => x.1 < y.1) := by
      rw [List.pairwise_map]
      exact hu.order.imp_of_mem fun {a b} ha hb h =>
        index3_lt_of ((hk a ha).trans (hk b hb).symm) h
    have hnone : ∀ q ∈ q0 :: rest, poolChild? N base q.leaf.desc = none := fun q hq =>
      poolChild_none (leaf_not_plain (hu.desc q hq))
    cases h3 : q0.new3 with
    | false =>
      simp only [heldLevel2Steps, hf, h3, Bool.false_eq_true, ite_false]
      rw [hmap, List.map_map]
      obtain ⟨-, hl3, -⟩ := hu.old3 q0 hq0 hf h3
      have h3r : q0.t3 ∈ st.pool.reached base := by
        rw [hp]; exact (wf_mem_reached hs).2 (wf_level3_lt hl3).1
      have := leaves_allOk (base := base)
        ((q0 :: rest).map fun q => (q0.t3, index3 q.leaf.va, q.leaf.desc)) st
        (fun x hx => by
          obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
          obtain ⟨a, b, c, -⟩ := hsame q hq
          refine ⟨h3r, wf_level3_ne_zero hs hl3, fun h => (hz _ h).2.2 hf h3 rfl, ?_, hnone q hq,
            Or.inl ?_⟩
          · obtain ⟨-, -, he⟩ := hu.old3 q hq (a.trans hf) (b.trans h3)
            rw [hp, ← entry_eq_get, ← c, he]; decide
          · rw [hp, wf_mem_children hs]; exact fun h2 => wf_not_level2_level3 hs h2 hl3)
        (by
          rw [List.pairwise_map]
          exact hu.order.imp_of_mem fun {a b} ha hb h =>
            Or.inr (Nat.ne_of_lt (index3_lt_of ((hk a ha).trans (hk b hb).symm) h)))
      simpa [Function.comp_def] using this
    | true =>
      have ht3 := hu.fresh q0 hq0 q0.t3 (Or.inr ⟨hf, h3, rfl⟩)
      have h3r : q0.t3 ∉ S.pool.reached base := fun h => by
        have := (wf_mem_reached hs).1 h; omega
      have ht30 : q0.t3 ≠ 0 := by have := hs.2.1; omega
      have h32 : q0.t3 ≠ q0.t2 := (hu.ok.t3new q0 hq0 q0 hq0 hf h3).2.1
      have hsteps : heldLevel2Steps base (q0 :: rest) =
          (Step.zero q0.t3 :: ((q0 :: rest).map fun q => (index3 q.leaf.va, q.leaf.desc)).map
            fun x => Step.store q0.t3 x.1 x.2) ++ [Step.fence] ++
            [Step.store q0.t2 (index2 q0.leaf.va) (tableAt base q0.t3)] := by
        simp only [heldLevel2Steps, hf, h3, ite_true, level2Entry, hmap, tableAt]; simp
      generalize hxs : ((q0 :: rest).map fun q => (index3 q.leaf.va, q.leaf.desc)) = xs at hsteps hord
      have hxd : ∀ x ∈ xs, poolChild? N base x.2 = none := fun x hx => by
        rw [← hxs] at hx; obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx; exact hnone q hq
      rw [hsteps, allOk_append, allOk_append]
      have hw : ∀ x ∈ (Step.zero q0.t3 :: xs.map fun x => Step.store q0.t3 x.1 x.2) ++ [Step.fence],
          ∀ u, x.writes u = true → u = q0.t3 := by
        intro x hx u hu'
        simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hx
        rcases hx with (rfl | ⟨y, -, rfl⟩) | rfl
        · simp only [Step.writes, beq_iff_eq] at hu'; exact hu'.symm
        · simp only [Step.writes, beq_iff_eq] at hu'; exact hu'.symm
        · cases hu'
      have hrf := reached_exec_fresh (p := S.pool) (base := base) hw fun u hu' => hu' ▸ h3r
      simp only [Bool.and_eq_true]
      refine ⟨⟨?_, rfl⟩, ?_⟩
      · simp only [allOk, Bool.and_eq_true]
        refine ⟨ok_zero (by rw [hp]; exact h3r) fun h => by have := (hz _ h).1; omega, ?_⟩
        refine fill_allOk ht30 xs _ ?_ List.mem_cons_self (fun h => by have := hsl _ h; omega)
          (fun y hy => by rw [nxt_steps] at hy; simp at hy) hord
          (fun x hx c hc => by rw [hxd x hx] at hc; cases hc)
          (hord.imp_of_mem fun {a b} ha _ _ c hc => by rw [hxd a ha] at hc; cases hc)
        show q0.t3 ∉ (st.pool.zeroTable q0.t3).reached base
        rw [hp, (reached_zero_fresh h3r).1]; exact h3r
      · simp only [allOk, Bool.and_true]
        have hpool := foldl_pool base ((Step.zero q0.t3 :: xs.map fun x => Step.store q0.t3 x.1 x.2) ++
          [Step.fence]) st
        rw [hp] at hpool
        refine ok_link hs.1 ht3.2 ?_ (Or.inl ht20) ?_ ?_ ?_ ?_ ?_ (foldl_fence_dirty _ _ _) ?_
        · rw [hpool, hrf.1]; exact (wf_mem_reached hs).2 (wf_level2_lt hl2).1
        · rw [foldl_zeroed]
          rintro (h | h)
          · exact (hz _ h).2.1 rfl
          · exact h32 (hw _ h q0.t2 (by simp [Step.writes])).symm
        · rw [hpool, get_exec_untouched (fun x hx => by
            cases h : x.writes q0.t2
            · rfl
            · exact absurd (hw x hx _ h).symm h32), ← entry_eq_get, hu.new3 q0 hq0 hf h3 hn]
          decide
        · rw [foldl_zeroed]; exact Or.inr (by simp)
        · rw [foldl_sealed]
          rintro (h | ⟨t, i, d, h, hc⟩)
          · have := hsl _ h; omega
          · simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false,
              reduceCtorEq, false_or] at h
            obtain ⟨y, hy, hye⟩ := h
            simp only [Step.store.injEq] at hye
            rw [← hye.2.2, hxd y hy] at hc; cases hc
        · rw [hpool, hrf.1]; exact h3r
        · intro u hu'
          rw [hpool] at hu'
          obtain ⟨j, -, hj⟩ := mem_children.1 hu'
          exfalso
          rcases get_exec_cases _ S.pool q0.t3 j with e | e | ⟨-, e⟩
          · rw [e, ← entry_eq_get, wf_entry_free hs ht3.1, poolChild_zero] at hj; cases hj
          · simp only [List.mem_append, List.mem_cons, List.mem_map, List.not_mem_nil, or_false,
              reduceCtorEq, false_or] at e
            obtain ⟨y, hy, hye⟩ := e
            simp only [Step.store.injEq] at hye
            rw [← hye.2.2, hxd y hy] at hj; cases hj
          · rw [e, poolChild_zero] at hj; cases hj

end Held

/-! ## A unit under a new level 2 table -/

/-- The entry that the level 2 table of a 2 MiB slot takes for its first leaf:
the block, or the table descriptor of the level 3 table of the pages. -/
private def l2val (base : UInt64) (q : Placed) : UInt64 :=
  match q.leaf.form with
  | .block => q.leaf.desc
  | .page => tableAt base q.t3

private theorem level2Entry_flatMap (base : UInt64) {t2 : Nat} : ∀ (Bs : List (List Placed)),
    (∀ Sb ∈ Bs, ∀ q ∈ Sb, q.t2 = t2) →
    Bs.flatMap (level2Entry base) =
      (Bs.filterMap List.head?).map fun q => Step.store t2 (index2 q.leaf.va) (l2val base q)
  | [], _ => rfl
  | [] :: Bs, h => by
    simp only [List.flatMap_cons, List.filterMap_cons, List.head?_nil]
    exact level2Entry_flatMap base Bs fun Sb hSb => h Sb (List.mem_cons_of_mem _ hSb)
  | (q :: rest) :: Bs, h => by
    simp only [List.flatMap_cons, List.filterMap_cons, List.head?_cons, List.map_cons]
    rw [level2Entry_flatMap base Bs fun Sb hSb => h Sb (List.mem_cons_of_mem _ hSb),
      ← h _ List.mem_cons_self q List.mem_cons_self]
    cases hf : q.leaf.form <;> simp [level2Entry, l2val, Placed.store, hf, tableAt]

section New

variable {S : Tables r N} {base : UInt64} {bits : UInt8}

private theorem children_allOk (hs : S.WellFormed base bits) {U : List Placed}
    (hu : UnitFacts S base bits U) (hn : ∀ q ∈ U, q.new2 = true) :
    ∀ (Ss : List (List Placed)), (∀ Sb ∈ Ss, Sb ∈ runsBy (·.leaf.blockSlot) U) →
      Ss.Pairwise (fun Sb Sb' => ∀ x ∈ Sb, ∀ y ∈ Sb', x.leaf.blockSlot < y.leaf.blockSlot) →
      ∀ (st : PlanState N), st.pool.reached base = S.pool.reached base →
      (∀ Sb ∈ Ss, ∀ q ∈ Sb, q.leaf.form = .page → q.t3 ∉ st.zeroed ∧ q.t3 ∉ st.sealed) →
      allOk base st (Ss.flatMap childSteps) = true
  | [], _, _, _, _, _ => rfl
  | Sb :: Ss, hm, hpw, st, hr, hz => by
    rw [List.pairwise_cons] at hpw
    obtain ⟨qb, rest, rfl, hbf⟩ := block_run hu.ok (fun q hq => hq) (hm _ List.mem_cons_self)
    have hqb := (hbf qb List.mem_cons_self).1
    rw [List.flatMap_cons, allOk_append]
    simp only [Bool.and_eq_true]
    cases hf : qb.leaf.form with
    | block =>
      have : childSteps (qb :: rest) = [] := by simp [childSteps, hf]
      rw [this]
      exact ⟨rfl, children_allOk hs hu hn Ss (fun S' h => hm S' (List.mem_cons_of_mem _ h)) hpw.2 _
        hr fun S' h q hq hp => hz S' (List.mem_cons_of_mem _ h) q hq hp⟩
    | page =>
      have h3 := hu.ok.new3 qb hqb (hn qb hqb) hf
      have ht3 := hu.fresh qb hqb qb.t3 (Or.inr ⟨hf, h3, rfl⟩)
      have h3r : qb.t3 ∉ st.pool.reached base := fun h => by
        rw [hr] at h; have := (wf_mem_reached hs).1 h; omega
      have ht30 : qb.t3 ≠ 0 := by have := hs.2.1; omega
      have hsteps : childSteps (qb :: rest) = Step.zero qb.t3 ::
          ((qb :: rest).map fun q => (index3 q.leaf.va, q.leaf.desc)).map
            fun x => Step.store qb.t3 x.1 x.2 := by
        simp only [childSteps, hf, beq_self_eq_true, ite_true, List.map_map]
        congr 1
        exact List.map_congr_left fun q hq => by
          obtain ⟨-, -, a, -, c, -⟩ := hbf q hq
          simp only [Function.comp_apply, Placed.store, a, hf, c]
      have hord : ((qb :: rest).map fun q => (index3 q.leaf.va, q.leaf.desc)).Pairwise
          (fun x y => x.1 < y.1) := by
        rw [List.pairwise_map]
        have hsub : (qb :: rest).Sublist U := by
          have := List.sublist_flatten_of_mem (hm _ List.mem_cons_self)
          rwa [runsBy_flatten] at this
        exact (hu.order.sublist hsub).imp_of_mem fun {a b} ha hb h =>
          index3_lt_of ((hbf a ha).2.1.trans (hbf b hb).2.1.symm) h
      have hxd : ∀ x ∈ ((qb :: rest).map fun q => (index3 q.leaf.va, q.leaf.desc)),
          poolChild? N base x.2 = none := fun x hx => by
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
        exact poolChild_none (leaf_not_plain (hu.desc q (hbf q hq).1))
      have hw : ∀ x ∈ childSteps (qb :: rest), ∀ u, x.writes u = true → u = qb.t3 := by
        intro x hx u hu'
        rw [hsteps] at hx
        rcases List.mem_cons.1 hx with rfl | hx
        · simp only [Step.writes, beq_iff_eq] at hu'; exact hu'.symm
        · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
          simp only [Step.writes, beq_iff_eq] at hu'; exact hu'.symm
      obtain ⟨hz3, hs3⟩ := hz _ List.mem_cons_self qb List.mem_cons_self hf
      refine ⟨?_, ?_⟩
      · rw [hsteps]
        simp only [allOk, Bool.and_eq_true]
        refine ⟨ok_zero h3r hz3, fill_allOk ht30 _ _ ?_ List.mem_cons_self hs3
          (fun y hy => by rw [nxt_steps] at hy; simp at hy) hord
          (fun x hx c hc => by rw [hxd x hx] at hc; cases hc)
          (hord.imp_of_mem fun {a b} ha _ _ c hc => by rw [hxd a ha] at hc; cases hc)⟩
        show qb.t3 ∉ (st.pool.zeroTable qb.t3).reached base
        rw [(reached_zero_fresh h3r).1]; exact h3r
      · refine children_allOk hs hu hn Ss (fun S' h => hm S' (List.mem_cons_of_mem _ h)) hpw.2 _ ?_ ?_
        · rw [foldl_pool, (reached_exec_fresh (T := (· = qb.t3)) hw fun u hu' => hu' ▸ h3r).1, hr]
        · intro S' hS' q hq hp
          obtain ⟨a, b⟩ := hz S' (List.mem_cons_of_mem _ hS') q hq hp
          refine ⟨fun h => ?_, fun h => ?_⟩
          · rcases (foldl_zeroed _ _ _ _).1 h with h | h
            · exact a h
            · have := hw _ h q.t3 (by simp [Step.writes])
              have hq' : q ∈ U := by
                obtain ⟨_, _, rfl, hf'⟩ := block_run hu.ok (fun q hq => hq) (hm S' (List.mem_cons_of_mem _ hS'))
                exact (hf' q hq).1
              have := (hu.ok.t3new q hq' qb hqb hf h3).2.2 hp this.symm
              exact absurd this.symm (Nat.ne_of_lt (hpw.1 S' hS' qb List.mem_cons_self q hq))
          · rcases (foldl_sealed _ _ _ _).1 h with h | ⟨t, i, d, h, hc⟩
            · exact b h
            · rw [hsteps] at h
              rcases List.mem_cons.1 h with h | h
              · cases h
              · obtain ⟨y, hy, hye⟩ := List.mem_map.1 h
                simp only [Step.store.injEq] at hye
                rw [← hye.2.2, hxd y hy] at hc; cases hc

theorem new_allOk (hs : S.WellFormed base bits) {q0 : Placed} {rest : List Placed}
    (hu : UnitFacts S base bits (q0 :: rest)) (hn : ∀ q ∈ q0 :: rest, q.new2 = true)
    (hk : ∀ q ∈ q0 :: rest, q.leaf.gibSlot = q0.leaf.gibSlot)
    {st : PlanState N} (hp : st.pool = S.pool)
    (hz : ∀ c ∈ st.zeroed, c ≠ 0 ∧ c < S.used) (hsl : ∀ c ∈ st.sealed, c < S.used) :
    allOk base st (newLevel2Steps base (q0 :: rest)) = true := by
  have hq0 : q0 ∈ q0 :: rest := List.mem_cons_self
  have hu1 := hs.2.1
  have ht2eq : ∀ q ∈ q0 :: rest, q.t2 = q0.t2 := fun q hq => (hu.ok.gib q hq q0 hq0 (hk q hq)).2
  have ht2 := hu.fresh q0 hq0 q0.t2 (Or.inl ⟨hn q0 hq0, rfl⟩)
  have hBm : ∀ Sb ∈ runsBy (·.leaf.blockSlot) (q0 :: rest), ∀ q ∈ Sb, q ∈ q0 :: rest :=
    fun Sb h q hq => (mem_runsBy _).2 ⟨Sb, h, hq⟩
  have hBp := runsBy_pairwise (·.leaf.blockSlot) (q0 :: rest) (hu.order.imp fun {a b} h => by
    have := form_size_pos a.leaf.form
    exact Nat.div_le_div_right (show a.leaf.va.toNat ≤ b.leaf.va.toNat by omega))
  have hfr : ∀ q ∈ q0 :: rest, q.leaf.form = .page → S.used ≤ q.t3 ∧ q.t3 < N := fun q hq hpg =>
    hu.fresh q hq q.t3 (Or.inr ⟨hpg, hu.ok.new3 q hq (hn q hq) hpg, rfl⟩)
  have h23 : ∀ q ∈ q0 :: rest, q.leaf.form = .page → q0.t2 ≠ q.t3 := fun q hq hpg =>
    (hu.ok.t2new q hq q0 hq0 (hn q0 hq0)).2.2 hpg
  rw [newLevel2Steps_eq, level2Entry_flatMap base _ (fun Sb h q hq => ht2eq q (hBm Sb h q hq))]
  generalize hB : runsBy (·.leaf.blockSlot) (q0 :: rest) = Bs at hBm hBp
  -- the heads of the 2 MiB slots
  have hH : ∀ q ∈ Bs.filterMap List.head?, q ∈ q0 :: rest ∧
      (q.leaf.form = .page → Step.zero q.t3 ∈ Bs.flatMap childSteps) := by
    intro q hq
    obtain ⟨Sb, hSb, hh⟩ := List.mem_filterMap.1 hq
    obtain ⟨qb, rb, rfl, -⟩ := block_run hu.ok (fun q hq => hq) (hB ▸ hSb)
    simp only [List.head?_cons, Option.some.injEq] at hh; subst hh
    exact ⟨hBm _ hSb qb List.mem_cons_self, fun hpg =>
      List.mem_flatMap.2 ⟨_, hSb, mem_childSteps.2 ⟨hpg, Or.inl rfl⟩⟩⟩
  have hHp : (Bs.filterMap List.head?).Pairwise
      (fun q q' => q.leaf.blockSlot < q'.leaf.blockSlot) :=
    hBp.filterMap _ fun Sb Sb' h q hq q' hq' =>
      h q (List.mem_of_mem_head? hq) q' (List.mem_of_mem_head? hq')
  -- the steps before the level 2 table
  have hP1 : ∀ x ∈ Bs.flatMap childSteps, ∃ q ∈ q0 :: rest, q.leaf.form = .page ∧
      (x = .zero q.t3 ∨ x = .store q.t3 (index3 q.leaf.va) q.leaf.desc) := by
    intro x hx
    obtain ⟨Sb, hSb, hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨qb, rb, rfl, hbf⟩ := block_run hu.ok (fun q hq => hq) (hB ▸ hSb)
    obtain ⟨hpg, hx | ⟨q, hq, rfl⟩⟩ := mem_childSteps.1 hx
    · exact ⟨qb, hBm _ hSb qb List.mem_cons_self, hpg, Or.inl hx⟩
    · obtain ⟨-, -, a, -, -⟩ := hbf q hq
      exact ⟨q, hBm _ hSb q hq, a.trans hpg, Or.inr (by simp only [Placed.store, a, hpg])⟩
  have hxd : ∀ q ∈ q0 :: rest, poolChild? N base q.leaf.desc = none := fun q hq =>
    poolChild_none (leaf_not_plain (hu.desc q hq))
  have hl2 : ∀ q ∈ q0 :: rest, ∀ c, poolChild? N base (l2val base q) = some c →
      q.leaf.form = .page ∧ c = q.t3 := by
    intro q hq c hc
    unfold l2val at hc
    cases hf : q.leaf.form <;> rw [hf] at hc
    · rw [poolChild_tableAt hs.1 (hfr q hq hf).2, Option.some.injEq] at hc; exact ⟨rfl, hc.symm⟩
    · rw [hxd q hq] at hc; cases hc
  generalize hP1e : Bs.flatMap childSteps = P1 at hH hP1
  generalize hHe : Bs.filterMap List.head? = H at hH hHp
  have hlist : P1 ++ Step.zero q0.t2 ::
      (H.map fun q => Step.store q0.t2 (index2 q.leaf.va) (l2val base q)) ++
      [Step.fence, Step.store 0 (index1 q0.leaf.va) (tableAt base q0.t2)] =
      (((P1 ++ [Step.zero q0.t2]) ++
        ((H.map fun q => (index2 q.leaf.va, l2val base q)).map fun x => Step.store q0.t2 x.1 x.2)) ++
        [Step.fence]) ++ [Step.store 0 (index1 q0.leaf.va) (tableAt base q0.t2)] := by
    simp [List.map_map, Function.comp_def]
  rw [hlist]
  -- every step before the link writes a new table
  have hW : ∀ x ∈ (((P1 ++ [Step.zero q0.t2]) ++
      ((H.map fun q => (index2 q.leaf.va, l2val base q)).map fun x => Step.store q0.t2 x.1 x.2)) ++
      [Step.fence]), ∀ u, x.writes u = true → S.used ≤ u ∧ u < N := by
    intro x hx u hw
    simp only [List.mem_append, List.mem_singleton, List.map_map, List.mem_map] at hx
    rcases hx with ((hx | rfl) | ⟨q, -, rfl⟩) | rfl
    · obtain ⟨q, hq, hpg, rfl | rfl⟩ := hP1 x hx <;>
      · simp only [Step.writes, beq_iff_eq] at hw; subst hw; exact hfr q hq hpg
    · simp only [Step.writes, beq_iff_eq] at hw; subst hw; exact ht2
    · simp only [Function.comp_apply, Step.writes, beq_iff_eq] at hw; subst hw; exact ht2
    · cases hw
  have hfresh : ∀ u, S.used ≤ u ∧ u < N → u ∉ S.pool.reached base := fun u hu' h => by
    have := (wf_mem_reached hs).1 h; omega
  have hsl' : ∀ (A : Plan) c, (∀ t i d, Step.store t i d ∈ A → poolChild? N base d ≠ some c) →
      c ∈ (A.foldl (nxt base) st).sealed → S.used ≤ c → False := by
    intro A c h1 h2 h3
    rcases (foldl_sealed _ _ _ _).1 h2 with h | ⟨t, i, d, h, hc⟩
    · have := hsl _ h; omega
    · exact h1 t i d h hc
  have hP1s : ∀ t i d, Step.store t i d ∈ P1 → poolChild? N base d = none := fun t i d h => by
    obtain ⟨q, hq, -, h | h⟩ := hP1 _ h
    · cases h
    · simp only [Step.store.injEq] at h; rw [h.2.2]; exact hxd q hq
  have hH2 : ∀ q ∈ H, ∀ c, poolChild? N base (l2val base q) = some c → c = q.t3 ∧
      Step.zero c ∈ P1 ∧ S.used ≤ c ∧ c < N ∧ q0.t2 ≠ c := by
    intro q hq c hc
    obtain ⟨hqU, hz3⟩ := hH q hq
    obtain ⟨hpg, rfl⟩ := hl2 q hqU c hc
    exact ⟨rfl, hz3 hpg, (hfr q hqU hpg).1, (hfr q hqU hpg).2, h23 q hqU hpg⟩
  rw [allOk_append, allOk_append, allOk_append, allOk_append]
  simp only [Bool.and_eq_true]
  have hWs : ∀ (A : Plan), (∀ x ∈ A, ∀ u, x.writes u = true → S.used ≤ u ∧ u < N) →
      (A.foldl (nxt base) st).pool.reached base = S.pool.reached base := fun A hA => by
    rw [foldl_pool, hp]; exact (reached_exec_fresh hA hfresh).1
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, rfl⟩, ?_⟩
  · rw [← hP1e]
    refine children_allOk hs hu hn Bs (fun Sb h => hB ▸ h) hBp st (by rw [hp]) ?_
    intro Sb hSb q hq hpg
    have := hfr q (hBm Sb hSb q hq) hpg
    exact ⟨fun h => by have := (hz _ h).2; omega, fun h => by have := hsl _ h; omega⟩
  · simp only [allOk, Bool.and_true]
    refine ok_zero ?_ fun h => ?_
    · rw [hWs P1 fun x hx => hW x (by simp [hx])]; exact hfresh _ ht2
    · rcases (foldl_zeroed _ _ _ _).1 h with h | h
      · have := (hz _ h).2; omega
      · obtain ⟨q, hq, hpg, h | h⟩ := hP1 _ h
        · simp only [Step.zero.injEq] at h; exact h23 q hq hpg h
        · cases h
  · have ht20 : q0.t2 ≠ 0 := by omega
    refine fill_allOk ht20 _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hWs _ fun x hx => hW x (List.mem_append_left _ (List.mem_append_left _ hx))]
      exact hfresh _ ht2
    · exact (foldl_zeroed _ _ _ _).2 (Or.inr (by simp))
    · refine fun h => hsl' _ _ (fun t i d h hc => ?_) h ht2.1
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at h
      rw [hP1s t i d h] at hc; cases hc
    · intro y hy
      rw [foldl_steps] at hy; simp at hy
    · rw [List.pairwise_map]
      exact hHp.imp_of_mem fun {a b} ha hb h =>
        index2_lt_of ((hk a (hH a ha).1).trans (hk b (hH b hb).1).symm) h
    · intro x hx c hc
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      obtain ⟨-, hz3, hc1, -, hc3⟩ := hH2 q hq c hc
      refine ⟨(foldl_zeroed _ _ _ _).2 (Or.inr (by simp [hz3])), fun h => hsl' _ _ ?_ h hc1,
        fun e => hc3 e.symm⟩
      intro t i d h hc'
      simp only [List.mem_append, List.mem_singleton, reduceCtorEq, or_false] at h
      rw [hP1s t i d h] at hc'; cases hc'
    · rw [List.pairwise_map]
      refine hHp.imp_of_mem fun {a b} ha hb h c hca hcb => ?_
      obtain ⟨rfl, -, -, -, -⟩ := hH2 a ha c hca
      obtain ⟨e, -, -, -, -⟩ := hH2 b hb _ hcb
      have hpa := (hl2 a (hH a ha).1 _ hca).1
      have hpb := (hl2 b (hH b hb).1 _ hcb).1
      have := (hu.ok.t3new a (hH a ha).1 b (hH b hb).1 hpb
        (hu.ok.new3 b (hH b hb).1 (hn b (hH b hb).1) hpb)).2.2 hpa e.symm ▸ h
      omega
  · simp only [allOk, Bool.and_true]
    generalize hA : ((P1 ++ [Step.zero q0.t2]) ++
      ((H.map fun q => (index2 q.leaf.va, l2val base q)).map fun x => Step.store q0.t2 x.1 x.2)) = A
      at hW ⊢
    have hpool := foldl_pool base (A ++ [Step.fence]) st
    rw [hp] at hpool
    have hreach := hWs _ hW
    have hsA : ∀ t i v, Step.store t i v ∈ A ++ [Step.fence] →
        (t = q0.t2 ∧ ∃ q ∈ H, v = l2val base q) ∨
          (∃ q ∈ q0 :: rest, q.leaf.form = .page ∧ t = q.t3 ∧ v = q.leaf.desc) := by
      intro t i v h
      rw [← hA] at h
      simp only [List.mem_append, List.mem_singleton, List.map_map, List.mem_map, reduceCtorEq,
        or_false, Function.comp_apply] at h
      rcases h with h | ⟨q, hq, e⟩
      · obtain ⟨q, hq, hpg, h | h⟩ := hP1 _ h
        · cases h
        · simp only [Step.store.injEq] at h; exact Or.inr ⟨q, hq, hpg, h.1, h.2.2⟩
      · simp only [Step.store.injEq] at e; exact Or.inl ⟨e.1.symm, q, hq, e.2.2.symm⟩
    have hent : ∀ j, (Plan.exec (A ++ [Step.fence]) S.pool).get q0.t2 j = 0 ∨
        ∃ q ∈ H, (Plan.exec (A ++ [Step.fence]) S.pool).get q0.t2 j = l2val base q := by
      intro j
      rcases get_exec_cases (A ++ [Step.fence]) S.pool q0.t2 j with e | e | ⟨-, e⟩
      · rw [e, ← entry_eq_get, wf_entry_free hs ht2.1]; exact Or.inl rfl
      · rcases hsA _ _ _ e with ⟨-, q, hq, e⟩ | ⟨q, hq, hpg, e, -⟩
        · exact Or.inr ⟨q, hq, e⟩
        · exact absurd e (h23 q hq hpg)
      · exact Or.inl e
    refine ok_link hs.1 ht2.2 (zero_mem_reached _ _) (Or.inr fun j _ => ?_) (fun h => ?_) ?_
      ((foldl_zeroed _ _ _ _).2 (Or.inr (by rw [← hA]; simp))) (fun h => ?_) ?_
      (foldl_fence_dirty _ _ _) ?_
    · rw [hpool]
      rcases hent j with e | ⟨q, hq, e⟩ <;> rw [e]
      · decide
      · unfold l2val
        cases hf : q.leaf.form
        · exact walked_tableAt true
        · have := typeBits_of_isReadWriteBlock ((hu.desc q (hH q hq).1).2 hf).1
          simp [walkedAsWritten, this]
    · rcases (foldl_zeroed _ _ _ _).1 h with h | h
      · exact (hz _ h).1 rfl
      · have := (hW _ h 0 rfl).1; omega
    · rw [hpool, get_exec_untouched (fun x hx => ?_), ← entry_eq_get,
        hu.new2 q0 hq0 (hn q0 hq0)]
      · decide
      · cases h : x.writes 0
        · rfl
        · have := (hW x hx 0 h).1; omega
    · refine hsl' _ _ (fun t i d h hc => ?_) h ht2.1
      rcases hsA t i d h with ⟨-, q, hq, rfl⟩ | ⟨q, hq, -, -, rfl⟩
      · exact (hH2 q hq _ hc).2.2.2.2 rfl
      · rw [hxd q hq] at hc; cases hc
    · rw [hreach]; exact hfresh _ ht2
    · intro u hu'
      rw [hpool] at hu'
      obtain ⟨j, -, hj⟩ := mem_children.1 hu'
      rcases hent j with e | ⟨q, hq, e⟩ <;> rw [e] at hj
      · rw [poolChild_zero] at hj; cases hj
      · obtain ⟨-, hz3, -⟩ := hH2 q hq u hj
        exact (foldl_zeroed _ _ _ _).2 (Or.inr (by rw [← hA]; simp [hz3]))

end New

end Krepi.Proofs.PageTables
