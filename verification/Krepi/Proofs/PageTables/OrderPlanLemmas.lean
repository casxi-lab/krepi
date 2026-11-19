module

public import Krepi.Proofs.PageTables.OrderMapLemmas
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.WalkLemmas

/-!
# Page tables: the plan of a map, unit by unit

- `mapPlan_units`: the plan of placed leaves whose tables agree slot by slot
  is the steps of its units (`ukey`, `unitSteps`) and `Sync`;
- prefixes of the leaves of a map: `placedOk_sublist`, `foldl_add_placed`,
  `leafFacts_take`, `assign_take` (the placed leaves of a prefix are the
  prefix of the placed leaves);
- **`mapPlan_inOrder`**: the plan of the leaves of a map that passed their
  checks in a well-formed set passes `Plan.inOrder`, one unit after the
  other, each against the set that the units before it left (`finalSet` of a
  prefix of the leaves, well-formed by `final_wf`), in which its tables are
  new or held as in the set before the map.
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables

variable {r : Region} {N : Nat}

/-! ## Runs -/

section Runs

variable {α : Type}

/-- Nonempty runs of one key each, the keys strictly ascending from one run to
the next. -/
private def AscRuns (key : α → Nat) (Rs : List (List α)) : Prop :=
  (∀ R ∈ Rs, ∃ x xs, R = x :: xs ∧ ∀ y ∈ R, key y = key x) ∧
    Rs.Pairwise (fun R R' => ∀ x ∈ R, ∀ y ∈ R', key x < key y)

private theorem runsBy_run (key : α → Nat) (L : List α) : ∀ (x : α) (xs : List α),
    (∀ y ∈ xs, key y = key x) → (∀ y ∈ L, key x < key y) →
    runsBy key (x :: xs ++ L) = (x :: xs) :: runsBy key L
  | x, [], _, hL => by
    simp only [List.cons_append, List.nil_append, runsBy]
    split
    · rename_i y run runs h
      have hy : y ∈ L := (mem_runsBy key).2 ⟨_, by rw [h]; exact List.mem_cons_self,
        List.mem_cons_self⟩
      have := hL y hy
      simp only [beq_iff_eq, show key x ≠ key y by omega, ite_false, h]
    · rfl
  | x, x' :: xs, hk, hL => by
    have hx' := hk x' List.mem_cons_self
    have ih := runsBy_run key L x' xs
      (fun y hy => (hk y (List.mem_cons_of_mem _ hy)).trans hx'.symm)
      (fun y hy => by rw [hx']; exact hL y hy)
    simp only [List.cons_append] at ih ⊢
    rw [runsBy, ih]
    simp [hx']

private theorem runsBy_asc (key : α → Nat) : ∀ Rs : List (List α), AscRuns key Rs →
    runsBy key Rs.flatten = Rs
  | [], _ => rfl
  | R :: Rs, ⟨h1, h2⟩ => by
    obtain ⟨x, xs, rfl, hk⟩ := h1 _ List.mem_cons_self
    rw [List.pairwise_cons] at h2
    rw [List.flatten_cons, runsBy_run key _ x xs (fun y hy => hk y (List.mem_cons_of_mem _ hy))
      (fun y hy => ?_), runsBy_asc key Rs ⟨fun R hR => h1 R (List.mem_cons_of_mem _ hR), h2.2⟩]
    obtain ⟨R', hR', hy'⟩ := List.mem_flatten.1 hy
    exact h2.1 R' hR' x List.mem_cons_self y hy'

private theorem ascRuns_runsBy (key : α → Nat) (l : List α) (h : l.Pairwise (fun a b => key a ≤ key b)) :
    AscRuns key (runsBy key l) :=
  ⟨runsBy_key key l, runsBy_pairwise key l h⟩

private theorem ascRuns_take (key : α → Nat) {Rs : List (List α)} (h : AscRuns key Rs) (j : Nat) :
    AscRuns key (Rs.take j) :=
  ⟨fun R hR => h.1 R (List.mem_of_mem_take hR), h.2.sublist (List.take_sublist _ _)⟩

end Runs

/-! ## The units of the plan of a map -/

private theorem ukey_lt {q q' : Placed} (hg : q.leaf.gibSlot < q'.leaf.gibSlot) : ukey q < ukey q' := by
  have h1 := ukey_gib q
  have h2 := ukey_gib q'
  apply Nat.lt_of_not_le
  intro h
  have := Nat.div_le_div_right (c := 2 * ENTRIES) h
  omega

theorem mapPlan_units (base : UInt64) {P : List Placed} (hp : PlacedOk P) :
    mapPlan base P = (runsBy ukey P).flatMap (unitSteps base) ++ [.sync] := by
  rw [mapPlan_eq]
  congr 1
  have hf : ∀ R ∈ runsBy (·.leaf.gibSlot) P, ∃ q rest, R = q :: rest ∧
      ∀ q' ∈ R, q' ∈ P ∧ q'.leaf.gibSlot = q.leaf.gibSlot ∧ q'.new2 = q.new2 := fun R hR => by
    obtain ⟨q, rest, rfl, h⟩ := gib_run hp hR
    exact ⟨q, rest, rfl, fun q' hq' => ⟨(h q' hq').1, (h q' hq').2.1, (h q' hq').2.2.1⟩⟩
  let f : List Placed → List (List Placed) := fun R =>
    match R with
    | q :: _ => if q.new2 then [R] else runsBy (·.leaf.blockSlot) R
    | [] => []
  have hflat : ∀ R, (f R).flatten = R := fun R => by
    cases R with
    | nil => rfl
    | cons q rest =>
      simp only [f]
      split
      · simp
      · exact runsBy_flatten _ _
  have hRs : runsBy ukey P = (runsBy (·.leaf.gibSlot) P).flatMap f := by
    have e : ((runsBy (·.leaf.gibSlot) P).flatMap f).flatten = P := by
      have : ∀ Rs : List (List Placed), (Rs.flatMap f).flatten = Rs.flatten := fun Rs => by
        induction Rs with
        | nil => rfl
        | cons R Rs ih => rw [List.flatMap_cons, List.flatten_append, ih, hflat]; rfl
      rw [this]; exact runsBy_flatten _ P
    rw [show runsBy ukey P = runsBy ukey ((runsBy (·.leaf.gibSlot) P).flatMap f).flatten by rw [e]]
    apply runsBy_asc
    refine ⟨fun S hS => ?_, ?_⟩
    · obtain ⟨R, hR, hS⟩ := List.mem_flatMap.1 hS
      obtain ⟨q, rest, rfl, hq⟩ := hf R hR
      simp only [f] at hS
      split at hS
      · rename_i hn
        rw [List.mem_singleton] at hS; subst hS
        refine ⟨q, rest, rfl, fun y hy => ?_⟩
        obtain ⟨-, a, b⟩ := hq y hy
        simp only [ukey, a, b, hn, ite_true]
      · rename_i hn
        obtain ⟨x, xs, rfl, hx⟩ := runsBy_key _ _ S hS
        refine ⟨x, xs, rfl, fun y hy => ?_⟩
        have hy' : y ∈ q :: rest := (mem_runsBy _).2 ⟨_, hS, hy⟩
        have hx' : x ∈ q :: rest := (mem_runsBy _).2 ⟨_, hS, List.mem_cons_self⟩
        simp only [ukey, (hq y hy').2.2, (hq x hx').2.2, hn, hx y hy, Bool.false_eq_true,
          ite_false]
    · rw [List.pairwise_flatMap]
      refine ⟨fun R hR => ?_, (pairwise_runsBy_lt hp).imp_of_mem fun {R R'} hR hR' h => ?_⟩
      · obtain ⟨q, rest, rfl, hq⟩ := hf R hR
        simp only [f]
        split
        · exact List.pairwise_singleton _ _
        · rename_i hn
          have hmono : (q :: rest).Pairwise (fun a b => a.leaf.blockSlot ≤ b.leaf.blockSlot) := by
            have hsub : (q :: rest).Sublist P := by
              have := List.sublist_flatten_of_mem hR
              rwa [runsBy_flatten] at this
            exact (hp.mono.sublist hsub).imp fun h => Nat.div_le_div_right h
          refine (runsBy_pairwise _ _ hmono).imp_of_mem fun {S S'} hS hS' hlt x hx y hy => ?_
          have hx' : x ∈ q :: rest := (mem_runsBy _).2 ⟨_, hS, hx⟩
          have hy' : y ∈ q :: rest := (mem_runsBy _).2 ⟨_, hS', hy⟩
          have := hlt x hx y hy
          simp only [ukey, (hq x hx').2.2, (hq y hy').2.2, hn, Bool.false_eq_true, ite_false]
          omega
      · intro S hS S' hS' x hx y hy
        have hxR : x ∈ R := by
          rw [← hflat R]; exact List.mem_flatten.2 ⟨S, hS, hx⟩
        have hyR : y ∈ R' := by
          rw [← hflat R']; exact List.mem_flatten.2 ⟨S', hS', hy⟩
        exact ukey_lt (h x hxR y hyR)
  rw [hRs, List.flatMap_assoc]
  apply flatMap_congr'
  intro R hR
  obtain ⟨q, rest, rfl, hq⟩ := hf R hR
  simp only [runSteps, f]
  split
  · rename_i hn; simp [unitSteps, hn]
  · rename_i hn
    apply flatMap_congr'
    intro S hS
    obtain ⟨x, xs, rfl, -⟩ := runsBy_key _ _ S hS
    have hx' : x ∈ q :: rest := (mem_runsBy _).2 ⟨_, hS, List.mem_cons_self⟩
    simp only [unitSteps, (hq x hx').2.2, hn, Bool.false_eq_true, ite_false]

/-! ## A prefix of the leaves -/

theorem placedOk_sublist {P Q : List Placed} (hp : PlacedOk P) (h : Q.Sublist P) : PlacedOk Q :=
  ⟨hp.mono.sublist h, fun q hq q' hq' => hp.gib q (h.subset hq) q' (h.subset hq'),
    fun q hq q' hq' => hp.block q (h.subset hq) q' (h.subset hq'),
    fun q hq q' hq' => hp.blockOne q (h.subset hq) q' (h.subset hq'),
    fun q hq => hp.new3 q (h.subset hq), fun q hq q' hq' => hp.t2new q (h.subset hq) q' (h.subset hq'),
    fun q hq q' hq' => hp.t3new q (h.subset hq) q' (h.subset hq')⟩

theorem foldl_add_placed : ∀ (L : List (MapLeaf × Place)) (a : Alloc),
    ∃ Y, (L.foldl Alloc.add a).placed = Y ++ a.placed
  | [], a => ⟨[], rfl⟩
  | (l, p) :: L, a => by
    obtain ⟨q, hq, -⟩ := add_placed a l p
    obtain ⟨Y, hY⟩ := foldl_add_placed L (a.add (l, p))
    exact ⟨Y ++ [q], by rw [List.foldl_cons, hY, hq]; simp⟩

section Prefix

variable {s : Tables r N} {base : UInt64} {bits : UInt8} {leaves : List (MapLeaf × Place)}

theorem leafFacts_take (hl : LeafFacts s base bits leaves) (k : Nat) :
    LeafFacts s base bits (leaves.take k) :=
  ⟨fun lp h => hl.place lp (List.mem_of_mem_take h),
    by rw [List.map_take]; exact hl.order.sublist (List.take_sublist _ _),
    fun lp h => hl.region lp (List.mem_of_mem_take h), fun lp h => hl.align lp (List.mem_of_mem_take h),
    fun lp h => hl.desc lp (List.mem_of_mem_take h)⟩

theorem assign_take (hl : LeafFacts s base bits leaves) {k : Nat} (hk : k ≤ leaves.length) :
    (assignTables s.used (leaves.take k)).2 = (assignTables s.used leaves).2.take k := by
  have hlen : (assignTables s.used (leaves.take k)).2.length = k := by
    have := congrArg List.length
      (assignTables_spec s.used (leaves.take k) (leaves_mono (leafFacts_take hl k))).1
    rw [List.length_map, List.length_map, List.length_take] at this; omega
  obtain ⟨Y, hY⟩ := foldl_add_placed (leaves.drop k)
    ((leaves.take k).foldl Alloc.add ⟨s.used, none, none, []⟩)
  have e : (assignTables s.used leaves).2 = (assignTables s.used (leaves.take k)).2 ++ Y.reverse := by
    conv => lhs; rw [← List.take_append_drop k leaves]
    simp only [assignTables, List.foldl_append, hY, List.reverse_append]
  rw [e, List.take_left' hlen]

private theorem assign_le (hl : LeafFacts s base bits leaves) (k : Nat) :
    (assignTables s.used (leaves.take k)).1 ≤ (assignTables s.used leaves).1 := by
  have sp := assignTables_spec s.used (leaves.take k) (leaves_mono (leafFacts_take hl k))
  have sp' := assignTables_spec s.used leaves (leaves_mono hl)
  apply Nat.le_of_not_lt; intro hc
  have h1 : s.used ≤ (assignTables s.used (leaves.take k)).1 := sp.2.2.1
  have hcov : ∀ c, s.used ≤ c → c < (assignTables s.used (leaves.take k)).1 →
      ∃ q ∈ (assignTables s.used (leaves.take k)).2, NewTable q c := sp.2.2.2.2.1
  have hr : ∀ q ∈ (assignTables s.used leaves).2, ∀ c, NewTable q c →
      s.used ≤ c ∧ c < (assignTables s.used leaves).1 := sp'.2.2.2.1
  obtain ⟨q, hq, hn⟩ := hcov ((assignTables s.used (leaves.take k)).1 - 1) (by omega) (by omega)
  have hsub : (assignTables s.used (leaves.take k)).2.Sublist (assignTables s.used leaves).2 := by
    by_cases hk : k ≤ leaves.length
    · rw [assign_take hl hk]; exact List.take_sublist _ _
    · rw [List.take_of_length_le (by omega)]; exact List.Sublist.refl _
  have := (hr q (hsub.subset hq) _ hn).2
  omega

private theorem ukey_of_block {P : List Placed} (hp : PlacedOk P) {q q' : Placed} (hq : q ∈ P) (hq' : q' ∈ P)
    (h : q.leaf.blockSlot = q'.leaf.blockSlot) : ukey q = ukey q' := by
  have hg := gib_of_block h
  obtain ⟨hn, -⟩ := hp.gib q hq q' hq' hg
  simp only [ukey, hn, hg, h]

private theorem ukey_of_gib {P : List Placed} (hp : PlacedOk P) {q q' : Placed} (hq : q ∈ P) (hq' : q' ∈ P)
    (hg : q.leaf.gibSlot = q'.leaf.gibSlot) (hn : q.new2 = true) : ukey q = ukey q' := by
  obtain ⟨hn', -⟩ := hp.gib q hq q' hq' hg
  simp only [ukey, ← hn', hn, ite_true, hg]

/-- A store of one placed leaf into an entry of the walk of another is a
store of its unit. -/
private theorem wr_ukey (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q q' : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) (hq' : q' ∈ (assignTables s.used leaves).2)
    {t i : Nat} {d : UInt64} (hw : Step.store t i d ∈ writesOf base q')
    (he : (t = 0 ∧ i = index1 q.leaf.va) ∨ (t = q.t2 ∧ i = index2 q.leaf.va) ∨
      (q.leaf.form = .page ∧ t = q.t3 ∧ i = index3 q.leaf.va)) : ukey q' = ukey q := by
  have hok := placed_ok hs hl
  have z2 := placed_t2_ne_zero hs hl hq
  have z2' := placed_t2_ne_zero hs hl hq'
  have hr := (placed_region hl hq).1
  have hr' := (placed_region hl hq').1
  rcases mem_writesOf.1 hw with ⟨hn, he'⟩ | ⟨hpg, -, he'⟩ | he'
  · simp only [Step.store.injEq] at he'; obtain ⟨rfl, rfl, -⟩ := he'
    rcases he with ⟨-, h⟩ | ⟨h, -⟩ | ⟨hp, h, -⟩
    · exact ukey_of_gib hok hq' hq (gib_of_index1 hr' hr h) hn
    · exact absurd h.symm z2
    · exact absurd h.symm (placed_t3_ne_zero hs hl hq hp)
  · simp only [link3, Step.store.injEq] at he'; obtain ⟨rfl, rfl, -⟩ := he'
    rcases he with ⟨h, -⟩ | ⟨h, hi⟩ | ⟨hp, h, -⟩
    · exact absurd h z2'
    · exact ukey_of_block hok hq' hq (slot_of_t2 hs hl hq' hq h hi)
    · exact absurd h (placed_apart hs hl hq' hq hp)
  · simp only [Placed.store] at he'
    cases hf : q'.leaf.form <;> simp only [hf, Step.store.injEq] at he' <;> obtain ⟨rfl, rfl, -⟩ := he'
    · rcases he with ⟨h, -⟩ | ⟨h, -⟩ | ⟨hp, h, -⟩
      · exact absurd h (placed_t3_ne_zero hs hl hq' hf)
      · exact absurd h.symm (placed_apart hs hl hq hq' hf)
      · exact ukey_of_block hok hq' hq (placed_t3eq hs hl hq' hq hf hp h)
    · rcases he with ⟨h, -⟩ | ⟨h, hi⟩ | ⟨hp, h, -⟩
      · exact absurd h z2'
      · exact ukey_of_block hok hq' hq (slot_of_t2 hs hl hq' hq h hi)
      · exact absurd h (placed_apart hs hl hq' hq hp)

/-- Two placed leaves with a new table in common are of one unit. -/
private theorem new_ukey (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q q' : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) (hq' : q' ∈ (assignTables s.used leaves).2) {c : Nat}
    (h : NewTable q c) (h' : NewTable q' c) : ukey q = ukey q' := by
  have hok := placed_ok hs hl
  rcases h with ⟨hn, rfl⟩ | ⟨hp, -, rfl⟩ <;> rcases h' with ⟨-, e⟩ | ⟨hp', -, e⟩
  · exact ukey_of_gib hok hq hq' (placed_t2eq hs hl hq hq' e) hn
  · exact absurd e (placed_apart hs hl hq hq' hp')
  · exact absurd e.symm (placed_apart hs hl hq' hq hp)
  · exact ukey_of_block hok hq hq' (placed_t3eq hs hl hq hq' hp hp' e)

private theorem unitFacts_of (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    (hN : (assignTables s.used leaves).1 ≤ N) {k : Nat} (hk : k ≤ leaves.length) {U : List Placed}
    (hU : U.Sublist (assignTables s.used leaves).2)
    (hlt : ∀ q' ∈ (assignTables s.used leaves).2.take k, ∀ q ∈ U, ukey q' < ukey q) :
    UnitFacts (finalSet s base (leaves.take k)) base bits U := by
  have hok := placed_ok hs hl
  have hlk := leafFacts_take hl k
  have hA := assign_take hl hk
  have sp := assignTables_spec s.used (leaves.take k) (leaves_mono hlk)
  have hle : s.used ≤ (assignTables s.used (leaves.take k)).1 := sp.2.2.1
  have hcov : ∀ c, s.used ≤ c → c < (assignTables s.used (leaves.take k)).1 →
      ∃ q ∈ (assignTables s.used (leaves.take k)).2, NewTable q c := sp.2.2.2.2.1
  have hP : ∀ q ∈ U, q ∈ (assignTables s.used leaves).2 := fun q hq => hU.subset hq
  have hold : ∀ q ∈ U, ∀ t i, ((t = 0 ∧ i = index1 q.leaf.va) ∨ (t = q.t2 ∧ i = index2 q.leaf.va) ∨
      (q.leaf.form = .page ∧ t = q.t3 ∧ i = index3 q.leaf.va)) →
      (finalSet s base (leaves.take k)).entry t i = s.entry t i := by
    intro q hq t i he
    refine final_entry_old hs hlk fun d ⟨q', hq', hw⟩ => ?_
    rw [hA] at hq'
    have := wr_ukey hs hl (hP q hq) (List.mem_of_mem_take hq') hw he
    have := hlt q' hq' q hq; omega
  have hpt : ∀ q ∈ U, ∀ t i c, ((t = 0 ∧ i = index1 q.leaf.va) ∨ (t = q.t2 ∧ i = index2 q.leaf.va)) →
      s.PointsAt base t i c → (finalSet s base (leaves.take k)).PointsAt base t i c := by
    intro q hq t i c he h
    have e := hold q hq t i (he.elim Or.inl (fun h => Or.inr (Or.inl h)))
    refine ⟨h.1, by rw [e]; exact h.2.1, ?_⟩
    rw [e, child_final]; exact child?_mono hle h.2.2
  refine ⟨placedOk_sublist hok hU, (placed_order hl).sublist hU,
    fun q hq => (placed_region hl (hP q hq)).2.2, fun q hq c hc => ?_, fun q hq hn => ?_,
    fun q hq hn => ?_, fun q hq hp h3 hn => ?_, fun q hq hp h3 => ?_, fun q hq hb hn => ?_⟩
  · obtain ⟨h1, h2⟩ := placed_range hl (hP q hq) hc
    refine ⟨Nat.le_of_not_lt fun hlt' => ?_, by omega⟩
    obtain ⟨q', hq', hn'⟩ := hcov c h1 hlt'
    rw [hA] at hq'
    have := new_ukey hs hl (List.mem_of_mem_take hq') (hP q hq) hn' hc
    have := hlt q' hq' q hq; omega
  · rw [hold q hq 0 _ (Or.inl ⟨rfl, rfl⟩)]; exact placed_new2 hs hl (hP q hq) hn
  · have := hpt q hq 0 _ _ (Or.inl ⟨rfl, rfl⟩) (placed_old2 hs hl (hP q hq) hn).1
    exact ⟨this, _, this⟩
  · rw [hold q hq _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩))]; exact (placed_new3 hs hl (hP q hq) hp).2.1 h3 hn
  · obtain ⟨hn, h1, -, h3'⟩ := (placed_new3 hs hl (hP q hq) hp).2.2 h3
    have h2 := hpt q hq _ _ _ (Or.inr ⟨rfl, rfl⟩) h1
    have hl2 := hpt q hq 0 _ _ (Or.inl ⟨rfl, rfl⟩) (placed_old2 hs hl (hP q hq) hn).1
    exact ⟨h2, ⟨q.t2, _, ⟨_, hl2⟩, h2⟩,
      by rw [hold q hq _ _ (Or.inr (Or.inr ⟨hp, rfl, rfl⟩))]; exact h3'⟩
  · rw [hold q hq _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩))]; exact placed_block hs hl (hP q hq) hb hn

end Prefix

private theorem store_ne_sync (q : Placed) : q.store ≠ .sync := by
  simp only [Placed.store]; split <;> simp

private theorem unitSteps_no_sync (base : UInt64) : ∀ (U : List Placed), ∀ x ∈ unitSteps base U, x ≠ .sync
  | [], x, h => by simp [unitSteps] at h
  | q :: rest, x, h => by
    simp only [unitSteps] at h
    split at h
    · rcases mem_newLevel2Steps.1 h with ⟨S, -, hx⟩ | rfl | ⟨S, -, hx⟩ | rfl | rfl
      · cases S with
        | nil => simp [childSteps] at hx
        | cons q0 r0 =>
          obtain ⟨-, rfl | ⟨q', -, rfl⟩⟩ := mem_childSteps.1 hx
          · simp
          · exact store_ne_sync q'
      · simp
      · cases S with
        | nil => simp [level2Entry] at hx
        | cons q0 r0 =>
          rcases mem_level2Entry.1 hx with ⟨-, rfl⟩ | ⟨-, rfl⟩
          · exact store_ne_sync q0
          · simp [link3]
      · simp
      · simp
    · rcases mem_heldLevel2Steps.1 h with ⟨q', -, rfl⟩ | ⟨-, -, rfl | rfl | rfl⟩
      · exact store_ne_sync q'
      · simp
      · simp
      · simp [link3]

section Main

variable {s : Tables r N} {base : UInt64} {bits : UInt8} {leaves : List (MapLeaf × Place)}

/-- **The plan of a map passes `Plan.inOrder`.** -/
theorem mapPlan_inOrder (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    (hN : (assignTables s.used leaves).1 ≤ N) :
    (mapPlan base (assignTables s.used leaves).2).publishesInOrder base s.pool = true := by
  have hok := placed_ok hs hl
  have hu1 := hs.2.1
  have hlenP : (assignTables s.used leaves).2.length = leaves.length := by
    have := congrArg List.length (assignTables_spec s.used leaves (leaves_mono hl)).1
    rwa [List.length_map, List.length_map] at this
  have hmono : (assignTables s.used leaves).2.Pairwise (fun a b => ukey a ≤ ukey b) := by
    refine hok.mono.imp_of_mem fun {a b} ha hb h => ?_
    have hg : a.leaf.gibSlot ≤ b.leaf.gibSlot := Nat.div_le_div_right h
    rcases Nat.lt_or_eq_of_le hg with hg | hg
    · exact Nat.le_of_lt (ukey_lt hg)
    · obtain ⟨hn, -⟩ := hok.gib a ha b hb hg
      have : a.leaf.blockSlot ≤ b.leaf.blockSlot := Nat.div_le_div_right h
      unfold ukey; rw [hn, hg]
      split
      · exact Nat.le_refl _
      · omega
  have hasc := ascRuns_runsBy ukey _ hmono
  generalize hUs : runsBy ukey (assignTables s.used leaves).2 = Us at hasc
  have hflat : Us.flatten = (assignTables s.used leaves).2 := by rw [← hUs, runsBy_flatten]
  have hpre : ∀ pre rest, Us = pre ++ rest →
      pre.flatten.length ≤ leaves.length ∧ pre.flatten.Sublist (assignTables s.used leaves).2 ∧
      (assignTables s.used (leaves.take pre.flatten.length)).2 = pre.flatten ∧
      mapPlan base pre.flatten = pre.flatMap (unitSteps base) ++ [.sync] := by
    intro pre rest h
    have e : (assignTables s.used leaves).2 = pre.flatten ++ rest.flatten := by
      rw [← hflat, h, List.flatten_append]
    have hk : pre.flatten.length ≤ leaves.length := by
      rw [← hlenP, e, List.length_append]; omega
    have hsub : pre.flatten.Sublist (assignTables s.used leaves).2 := by
      rw [e]; exact List.sublist_append_left _ _
    have hasc' : AscRuns ukey pre := by
      have := ascRuns_take ukey hasc pre.length
      rwa [h, List.take_left' rfl] at this
    refine ⟨hk, hsub, by rw [assign_take hl hk, e, List.take_left' rfl], ?_⟩
    rw [mapPlan_units base (placedOk_sublist hok hsub), runsBy_asc ukey pre hasc']
  have key : ∀ rest pre, Us = pre ++ rest → ∀ st : PlanState N,
      st.pool = Plan.exec (pre.flatMap (unitSteps base)) s.pool →
      (∀ c ∈ st.zeroed, ∃ q ∈ pre.flatten, NewTable q c) →
      (∀ c ∈ st.sealed, ∃ q ∈ pre.flatten, NewTable q c) →
      Plan.inOrder base (rest.flatMap (unitSteps base) ++ [.sync]) st = true := by
    intro rest
    induction rest with
    | nil => intro _ _ st _ _ _; rfl
    | cons U rest ih =>
      intro pre h st hp hz hsl
      obtain ⟨hk, -, hA, hmp⟩ := hpre pre (U :: rest) h
      obtain ⟨-, hsub', -, hmp'⟩ := hpre (pre ++ [U]) rest (by rw [h]; simp)
      have hok' := placedOk_sublist hok hsub'
      have hUmem : U ∈ Us := by rw [h]; simp
      obtain ⟨q0, rest0, hU0, hkey⟩ := hasc.1 U hUmem
      have hUsub : U.Sublist (assignTables s.used leaves).2 := by
        rw [← hflat]; exact List.sublist_flatten_of_mem hUmem
      have hlt : ∀ q' ∈ (assignTables s.used leaves).2.take pre.flatten.length, ∀ q ∈ U,
          ukey q' < ukey q := by
        rw [← assign_take hl hk, hA]
        intro q' hq' q hq
        obtain ⟨R, hR, hq'R⟩ := List.mem_flatten.1 hq'
        have hp2 := hasc.2; rw [h] at hp2
        exact (List.pairwise_append.1 hp2).2.2 R hR U List.mem_cons_self q' hq'R q hq
      have huf := unitFacts_of hs hl hN hk hUsub hlt
      have hlk := leafFacts_take hl pre.flatten.length
      have hSwf := final_wf hs hlk (Nat.le_trans (assign_le hl _) hN)
      have hnew : ∀ c, (∃ q ∈ pre.flatten, NewTable q c) →
          s.used ≤ c ∧ c < (finalSet s base (leaves.take pre.flatten.length)).used := by
        rintro c ⟨q, hq, hc⟩
        rw [← hA] at hq
        exact placed_range hlk hq hc
      have hpS : st.pool = (finalSet s base (leaves.take pre.flatten.length)).pool := by
        rw [hp]; simp only [finalSet, hA, hmp, exec_append]; rfl
      rw [List.flatMap_cons, List.append_assoc, inOrder_append _ _ _ _ (unitSteps_no_sync base U)]
      simp only [Bool.and_eq_true]
      have hsteps : ∀ x ∈ unitSteps base U, x ∈ mapPlan base (pre ++ [U]).flatten := fun x hx => by
        rw [hmp']; simp [hx]
      refine ⟨?_, ih (pre ++ [U]) (by rw [h]; simp) _ ?_ ?_ ?_⟩
      · rw [hU0] at huf hkey ⊢
        simp only [unitSteps]
        split
        · rename_i hn
          refine new_allOk hSwf huf (fun q hq => (ukey_eq (hkey q hq)).1.trans hn)
            (fun q hq => (ukey_eq (hkey q hq)).2.1) hpS (fun c hc => ?_) (fun c hc => ?_)
          · have := hnew c (hz c hc); exact ⟨by omega, this.2⟩
          · exact (hnew c (hsl c hc)).2
        · rename_i hn
          have hn' : q0.new2 = false := by simpa using hn
          refine held_allOk hSwf huf
            (fun q hq => (ukey_eq (hkey q hq)).2.2 ((ukey_eq (hkey q hq)).1.trans hn')) hn' hpS
            (fun c hc => ?_) (fun c hc => (hnew c (hsl c hc)).2)
          have hq0 : q0 ∈ (assignTables s.used leaves).2 :=
            hUsub.subset (by rw [hU0]; exact List.mem_cons_self)
          have := hnew c (hz c hc)
          refine ⟨this.2, fun e => ?_, fun hpg h3 e => ?_⟩
          · have := (placed_lt2 hs hl hq0).1 hn'; omega
          · have := (placed_lt3 hs hl hq0 hpg).1 h3; omega
      · rw [foldl_pool, hp, ← exec_append]; simp
      · intro c hc
        rcases (foldl_zeroed _ _ _ _).1 hc with hc | hc
        · obtain ⟨q, hq, hn⟩ := hz c hc; exact ⟨q, by simp [hq], hn⟩
        · exact zero_mapPlan hok' (hsteps _ hc)
      · intro c hc
        rcases (foldl_sealed _ _ _ _).1 hc with hc | ⟨t, i, d, hd, hc⟩
        · obtain ⟨q, hq, hn⟩ := hsl c hc; exact ⟨q, by simp [hq], hn⟩
        · obtain ⟨q, hq, hw⟩ := (mem_mapPlan hok').1 (hsteps _ hd)
          have hqP := hsub'.subset hq
          rcases mem_writesOf.1 hw with ⟨hn, he⟩ | ⟨hpg, hn3, he⟩ | he
          · simp only [Step.store.injEq] at he
            rw [he.2.2, poolChild_tableAt hs.1 (Nat.lt_of_lt_of_le
              (placed_range hl hqP (Or.inl ⟨hn, rfl⟩)).2 hN), Option.some.injEq] at hc
            exact ⟨q, hq, Or.inl ⟨hn, hc.symm⟩⟩
          · simp only [link3, Step.store.injEq] at he
            rw [he.2.2, poolChild_tableAt hs.1 (Nat.lt_of_lt_of_le
              (placed_range hl hqP (Or.inr ⟨hpg, hn3, rfl⟩)).2 hN), Option.some.injEq] at hc
            exact ⟨q, hq, Or.inr ⟨hpg, hn3, hc.symm⟩⟩
          · have hd' : d = q.leaf.desc := by
              simp only [Placed.store] at he; split at he <;> simp_all
            rw [hd', poolChild_none (leaf_not_plain (placed_region hl hqP).2.2)] at hc; cases hc
  unfold Plan.publishesInOrder
  rw [mapPlan_units base hok, hUs]
  exact key Us [] rfl _ rfl (by simp) (by simp)

end Main

end Krepi.Proofs.PageTables
