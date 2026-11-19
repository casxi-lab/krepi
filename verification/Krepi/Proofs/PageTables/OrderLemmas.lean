module

public import Krepi.SpecProperties.PageTables.Properties
public import Krepi.Proofs.PageTables.PoolLemmas
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.WellFormedLemmas

/-!
# Page tables: lemmas about the check of the order of a plan

`Plan.inOrder` taken one step at a time, for plans whose steps are `Zero`,
`Store` and `Fence` up to the last `Sync`:

- the state after one step, `nxt`, the check of one step, `okStep`, and the
  check of a list of steps, `allOk`, with `inOrder_cons`, `inOrder_append`,
  `allOk_append`, `nxt_pool`, `nxt_steps` and the state after a list of
  steps, `foldl_pool`, `foldl_steps`, `foldl_zeroed`, `foldl_sealed`;
- lists: `filterMap_congr'`, `flatMap_congr'`, `contains_iff`;
- the tables that the walk reaches: `poolChild_none`, `poolChild_tableAt`,
  `mem_children`, `mem_reached`, `zero_mem_reached`, `children_sub_reached`,
  `reached_congr` (a change of the entries that keeps the table each entry of
  a reached table points at keeps the reached tables), `reached_store_fresh`
  and `reached_zero_fresh` (a write of a table not reached);
- in a well-formed set: `wf_mem_reached` (the reached tables are those in
  use) and `wf_mem_children` (the tables that the root points at are its
  level 2 tables);
- the checks of one step: `ok_zero` and `ok_store_reached` (a store into a
  reached table);
- runs of steps: `fill_allOk` (stores into a table not reached, after its
  `Zero`, in increasing order of their indices) and `leaves_allOk` (leaves
  into invalid entries of reached tables).
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables

variable {N : Nat}

/-! ## One step at a time -/

/-- The state of the check of the order after one step that is not the last
`Sync`, as `Plan.inOrder` passes it on. -/
def nxt (base : UInt64) (st : PlanState N) (step : Step) : PlanState N :=
  let next : PlanState N := { st with pool := step.exec st.pool, steps := step :: st.steps }
  match step with
  | .zero t => { next with zeroed := t :: st.zeroed, dirty := t :: st.dirty }
  | .store t _ d =>
    { next with dirty := if (st.pool.reached base).contains t then st.dirty else t :: st.dirty,
                sealed := match poolChild? N base d with
                  | some c => c :: st.sealed
                  | none => st.sealed,
                valid := st.valid || isValid d }
  | .fence => { next with dirty := [] }
  | _ => next

/-- The check of one step that is not the last `Sync`, as `Plan.inOrder` makes
it. -/
def okStep (base : UInt64) (st : PlanState N) : Step → Bool
  | .zero t => !(st.pool.reached base).contains t && !st.zeroed.contains t
  | .store t i d =>
    let reached := st.pool.reached base
    let child := poolChild? N base d
    let since := st.steps.takeWhile (· != .zero t)
    (t != 0 || walkedAsWritten false d) &&
    (!(st.pool.children base 0).contains t || walkedAsWritten true d) &&
    (match child with
      | some c => st.zeroed.contains c && !st.sealed.contains c &&
        (t != 0 || (List.range ENTRIES).all fun j => walkedAsWritten true (st.pool.get c j))
      | none => true) &&
    (if reached.contains t then
      !st.zeroed.contains t && !isValid (st.pool.get t i) &&
        match child with
        | some c => !reached.contains c &&
          (c :: st.pool.children base c).all fun u => st.zeroed.contains u && !st.dirty.contains u
        | none => true
    else
      st.zeroed.contains t && !st.sealed.contains t &&
        (since.all fun s => match s with
          | .store u j _ => u != t || j < i
          | _ => true) &&
        match child with
        | some c => since.all fun s => !s.writes c
        | none => true)
  | .fence => true
  | .sync => true
  | .invalidate _ => false

/-- The checks of a list of steps, each on the state that the steps before it
left. -/
def allOk (base : UInt64) : PlanState N → Plan → Bool
  | _, [] => true
  | st, step :: rest => okStep base st step && allOk base (nxt base st step) rest

theorem inOrder_cons (base : UInt64) (st : PlanState N) (step : Step) (rest : Plan)
    (h : step ≠ .sync) :
    Plan.inOrder base (step :: rest) st =
      (okStep base st step && Plan.inOrder base rest (nxt base st step)) := by
  cases step with
  | sync => exact absurd rfl h
  | zero t => cases rest <;> rfl
  | store t i d => cases rest <;> rfl
  | fence => cases rest <;> rfl
  | invalidate v => cases rest <;> rfl

theorem inOrder_append (base : UInt64) : ∀ (steps rest : Plan) (st : PlanState N),
    (∀ x ∈ steps, x ≠ .sync) →
    Plan.inOrder base (steps ++ rest) st =
      (allOk base st steps && Plan.inOrder base rest (steps.foldl (nxt base) st))
  | [], rest, st, _ => by simp [allOk]
  | x :: xs, rest, st, h => by
    rw [List.cons_append, inOrder_cons _ _ _ _ (h x List.mem_cons_self),
      inOrder_append base xs rest _ (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    simp only [allOk, List.foldl_cons, Bool.and_assoc]

theorem allOk_append (base : UInt64) : ∀ (a b : Plan) (st : PlanState N),
    allOk base st (a ++ b) = (allOk base st a && allOk base (a.foldl (nxt base) st) b)
  | [], b, st => by simp [allOk]
  | x :: xs, b, st => by
    simp only [List.cons_append, allOk, List.foldl_cons, allOk_append base xs b, Bool.and_assoc]

theorem nxt_pool (base : UInt64) (st : PlanState N) (step : Step) :
    (nxt base st step).pool = step.exec st.pool := by
  cases step <;> rfl

theorem nxt_steps (base : UInt64) (st : PlanState N) (step : Step) :
    (nxt base st step).steps = step :: st.steps := by
  cases step <;> rfl

theorem foldl_pool (base : UInt64) : ∀ (steps : Plan) (st : PlanState N),
    (steps.foldl (nxt base) st).pool = steps.exec st.pool
  | [], _ => rfl
  | x :: xs, st => by rw [List.foldl_cons, foldl_pool base xs, nxt_pool]; rfl

theorem foldl_steps (base : UInt64) : ∀ (steps : Plan) (st : PlanState N),
    (steps.foldl (nxt base) st).steps = steps.reverse ++ st.steps
  | [], _ => rfl
  | x :: xs, st => by rw [List.foldl_cons, foldl_steps base xs, nxt_steps]; simp

theorem foldl_zeroed (base : UInt64) : ∀ (steps : Plan) (st : PlanState N) (c : Nat),
    c ∈ (steps.foldl (nxt base) st).zeroed ↔ c ∈ st.zeroed ∨ Step.zero c ∈ steps
  | [], _, c => by simp
  | x :: xs, st, c => by
    rw [List.foldl_cons, foldl_zeroed base xs]
    cases x <;> simp [nxt, or_assoc, or_left_comm, eq_comm]

theorem foldl_sealed (base : UInt64) : ∀ (steps : Plan) (st : PlanState N) (c : Nat),
    c ∈ (steps.foldl (nxt base) st).sealed ↔
      c ∈ st.sealed ∨ ∃ t i d, Step.store t i d ∈ steps ∧ poolChild? N base d = some c
  | [], _, c => by simp
  | x :: xs, st, c => by
    rw [List.foldl_cons, foldl_sealed base xs]
    cases x with
    | store t i d =>
      simp only [nxt]
      cases hc : poolChild? N base d with
      | none =>
        simp only [List.mem_cons, Step.store.injEq]
        constructor
        · rintro (h | ⟨t', i', d', h, h'⟩)
          · exact Or.inl h
          · exact Or.inr ⟨t', i', d', Or.inr h, h'⟩
        · rintro (h | ⟨t', i', d', (⟨-, -, rfl⟩ | h), h'⟩)
          · exact Or.inl h
          · rw [hc] at h'; cases h'
          · exact Or.inr ⟨t', i', d', h, h'⟩
      | some c' =>
        simp only [List.mem_cons, Step.store.injEq]
        constructor
        · rintro ((rfl | h) | ⟨t', i', d', h, h'⟩)
          · exact Or.inr ⟨t, i, d, Or.inl ⟨rfl, rfl, rfl⟩, hc⟩
          · exact Or.inl h
          · exact Or.inr ⟨t', i', d', Or.inr h, h'⟩
        · rintro (h | ⟨t', i', d', (⟨-, -, rfl⟩ | h), h'⟩)
          · exact Or.inl (Or.inr h)
          · rw [hc] at h'; exact Or.inl (Or.inl (Option.some.inj h').symm)
          · exact Or.inr ⟨t', i', d', h, h'⟩
    | _ => simp [nxt]

/-! ## The tables that the walk reaches -/

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: rest, h => by
    simp only [List.filterMap_cons]
    rw [h x List.mem_cons_self, filterMap_congr' (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem flatMap_congr' {α β : Type} {f g : α → List β} :
    ∀ {l : List α}, (∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | x :: rest, h => by
    simp only [List.flatMap_cons]
    rw [h x List.mem_cons_self, flatMap_congr' (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem contains_iff {l : List Nat} {a : Nat} : l.contains a = true ↔ a ∈ l := by
  simp

theorem poolChild_none {base d : UInt64} (h : isPlainTableDescriptor d = false) :
    poolChild? N base d = none := by
  simp [poolChild?, h]

private theorem poolChild_some {base d : UInt64} {c : Nat} (h : poolChild? N base d = some c) :
    isPlainTableDescriptor d = true ∧ c < N ∧ c = ((outputAddress d).toNat - base.toNat) / PAGE_SIZE := by
  simp only [poolChild?] at h
  split at h
  · rename_i hc; simp only [Option.some.injEq] at h; subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    exact ⟨hc.1.1, hc.2, rfl⟩
  · cases h

theorem poolChild_tableAt {base : UInt64} {bits : UInt8} (hp : PoolOk N base bits) {c : Nat}
    (hc : c < N) : poolChild? N base (tableAt base c) = some c := by
  simp only [poolChild?]
  rw [outputAddress_tableAt hp hc]
  have : (base.toNat + PAGE_SIZE * c - base.toNat) / PAGE_SIZE = c := by
    simp only [PAGE_SIZE]; omega
  rw [this, tableAt, isPlain_tableDescriptor]
  simp [hc]

theorem mem_children {p : Pool N} {base : UInt64} {t c : Nat} :
    c ∈ p.children base t ↔ ∃ i, i < ENTRIES ∧ poolChild? N base (p.get t i) = some c := by
  simp [Pool.children]

private theorem children_congr {p q : Pool N} {base : UInt64} {t : Nat}
    (h : ∀ i, i < ENTRIES → poolChild? N base (q.get t i) = poolChild? N base (p.get t i)) :
    q.children base t = p.children base t := by
  unfold Pool.children
  exact filterMap_congr' fun i hi => h i (List.mem_range.1 hi)

theorem mem_reached {p : Pool N} {base : UInt64} {c : Nat} :
    c ∈ p.reached base ↔
      c = 0 ∨ c ∈ p.children base 0 ∨ ∃ t2 ∈ p.children base 0, c ∈ p.children base t2 := by
  simp only [Pool.reached, List.mem_cons, List.mem_append, List.mem_flatMap, or_assoc]

theorem zero_mem_reached (p : Pool N) (base : UInt64) : 0 ∈ p.reached base :=
  mem_reached.2 (Or.inl rfl)

theorem children_sub_reached {p : Pool N} {base : UInt64} {c : Nat} (h : c ∈ p.children base 0) :
    c ∈ p.reached base :=
  mem_reached.2 (Or.inr (Or.inl h))

theorem reached_congr {p q : Pool N} {base : UInt64}
    (h : ∀ t ∈ p.reached base, ∀ i, i < ENTRIES →
      poolChild? N base (q.get t i) = poolChild? N base (p.get t i)) :
    q.reached base = p.reached base ∧ q.children base 0 = p.children base 0 := by
  have h0 := children_congr (h 0 (zero_mem_reached p base))
  refine ⟨?_, h0⟩
  unfold Pool.reached
  show 0 :: q.children base 0 ++ (q.children base 0).flatMap (q.children base) =
    0 :: p.children base 0 ++ (p.children base 0).flatMap (p.children base)
  rw [h0, flatMap_congr' fun t ht => children_congr (h t (children_sub_reached ht))]

private theorem reached_fresh {p q : Pool N} {base : UInt64} {t : Nat} (ht : t ∉ p.reached base)
    (hq : ∀ t' i, t' ≠ t → q.get t' i = p.get t' i) :
    q.reached base = p.reached base ∧ q.children base 0 = p.children base 0 :=
  reached_congr fun t' ht' i _ => by rw [hq t' i (fun e => ht (e ▸ ht'))]

theorem reached_store_fresh {p : Pool N} {base : UInt64} {t i : Nat} {d : UInt64}
    (ht : t ∉ p.reached base) :
    (p.store t i d).reached base = p.reached base ∧
      (p.store t i d).children base 0 = p.children base 0 :=
  reached_fresh ht fun t' i' h => by rw [get_store]; simp [h]

theorem reached_zero_fresh {p : Pool N} {base : UInt64} {t : Nat} (ht : t ∉ p.reached base) :
    (p.zeroTable t).reached base = p.reached base ∧
      (p.zeroTable t).children base 0 = p.children base 0 :=
  reached_fresh ht fun t' i' h => by rw [get_zeroTable]; simp [h]

private theorem reached_leaf {p : Pool N} {base : UInt64} {t i : Nat} {d : UInt64}
    (hv : isValid (p.get t i) = false) (hd : poolChild? N base d = none) :
    (p.store t i d).reached base = p.reached base ∧
      (p.store t i d).children base 0 = p.children base 0 := by
  refine reached_congr fun t' _ i' _ => ?_
  rw [get_store]
  split
  · rename_i h; obtain ⟨rfl, rfl, -, -⟩ := h
    rw [hd, poolChild_none]
    cases hp : isPlainTableDescriptor (p.get t' i')
    · rfl
    · rw [isValid_of_isPlain hp] at hv; cases hv
  · rfl

/-! ## In a well-formed set -/

section WellFormed

variable {r : Region} {S : Tables r N} {base : UInt64} {bits : UInt8}

private theorem poolChild_of_child {d : UInt64} {c : Nat} (hp : isPlainTableDescriptor d = true)
    (h : S.child? base d = some c) : poolChild? N base d = some c := by
  simp only [Tables.child?] at h
  simp only [poolChild?, hp, Bool.true_and]
  split at h
  · rename_i hc; simp only [Option.some.injEq] at h; subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    split
    · rfl
    · rename_i hn; exact absurd ⟨hc.1, by omega⟩ hn
  · cases h

private theorem wf_poolChild (hs : S.WellFormed base bits) {t i c : Nat} (ht : S.IsParent base t)
    (hi : i < ENTRIES) : poolChild? N base (S.pool.get t i) = some c ↔ S.PointsAt base t i c := by
  rw [← entry_eq_get]
  constructor
  · intro h
    obtain ⟨hp, -, hc⟩ := poolChild_some h
    have key : ∃ c', S.PointsAt base t i c' := by
      rcases ht with rfl | h2
      · rcases hs.2.2.2.2.1 i hi with h0 | hc'
        · rw [h0] at hp; cases hp
        · exact hc'
      · rcases hs.2.2.2.2.2.1 t h2 i hi with h0 | hc' | ⟨hb, -⟩
        · rw [h0] at hp; cases hp
        · exact hc'
        · rw [isPlain_of_isReadWriteBlock hb] at hp; cases hp
    obtain ⟨c', hc'⟩ := key
    have := poolChild_of_child hc'.2.1 hc'.2.2
    rw [h] at this; cases this; exact hc'
  · intro h; exact poolChild_of_child h.2.1 h.2.2

theorem wf_mem_children (hs : S.WellFormed base bits) {c : Nat} :
    c ∈ S.pool.children base 0 ↔ S.IsLevel2 base c := by
  rw [mem_children]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, (wf_poolChild hs (Or.inl rfl) hi).1 h⟩
  · rintro ⟨i, h⟩; exact ⟨i, h.1, (wf_poolChild hs (Or.inl rfl) h.1).2 h⟩

theorem wf_mem_reached (hs : S.WellFormed base bits) {c : Nat} :
    c ∈ S.pool.reached base ↔ c < S.used := by
  rw [mem_reached]
  constructor
  · rintro (rfl | h | ⟨t2, h2, h⟩)
    · exact hs.2.1
    · exact (wf_level2_lt ((wf_mem_children hs).1 h)).1
    · obtain ⟨i, hi, h⟩ := mem_children.1 h
      exact (pointsAt_lt ((wf_poolChild hs (Or.inr ((wf_mem_children hs).1 h2)) hi).1 h)).1
  · intro hc
    by_cases h0 : c = 0
    · exact Or.inl h0
    obtain ⟨t, i, ht, hp⟩ := hs.2.2.2.2.2.2.2.2.1 c (Nat.pos_of_ne_zero h0) hc
    rcases ht with rfl | h2
    · exact Or.inr (Or.inl ((wf_mem_children hs).2 ⟨i, hp⟩))
    · exact Or.inr (Or.inr ⟨t, (wf_mem_children hs).2 h2,
        mem_children.2 ⟨i, hp.1, (wf_poolChild hs (Or.inr h2) hp.1).2 hp⟩⟩)

end WellFormed

/-! ## The checks of one step -/

section Checks

variable {st : PlanState N} {base : UInt64}

theorem ok_zero {t : Nat} (hr : t ∉ st.pool.reached base) (hz : t ∉ st.zeroed) :
    okStep base st (.zero t) = true := by
  simp [okStep, hr, hz]

theorem ok_store_reached {t i : Nat} {d : UInt64} (hr : t ∈ st.pool.reached base)
    (h1 : t ≠ 0 ∨ walkedAsWritten false d = true)
    (h2 : t ∉ st.pool.children base 0 ∨ walkedAsWritten true d = true)
    (hz : t ∉ st.zeroed) (hv : isValid (st.pool.get t i) = false)
    (hc : ∀ c, poolChild? N base d = some c → c ∈ st.zeroed ∧ c ∉ st.sealed ∧
      (t ≠ 0 ∨ ∀ j, j < ENTRIES → walkedAsWritten true (st.pool.get c j) = true) ∧
      c ∉ st.pool.reached base ∧ ∀ u ∈ c :: st.pool.children base c, u ∈ st.zeroed ∧ u ∉ st.dirty) :
    okStep base st (.store t i d) = true := by
  have hr' : (st.pool.reached base).contains t = true := contains_iff.2 hr
  unfold okStep
  simp only [hr', ite_true]
  have e1 : (t != 0 || walkedAsWritten false d) = true := by
    rcases h1 with h | h
    · simp [h]
    · simp [h]
  have e2 : (!(st.pool.children base 0).contains t || walkedAsWritten true d) = true := by
    rcases h2 with h | h
    · simp [h]
    · simp [h]
  rw [e1, e2]
  cases hch : poolChild? N base d with
  | none => simp [hz, hv]
  | some c =>
    obtain ⟨a, b, c', e, f⟩ := hc c hch
    have g : ((List.range ENTRIES).all fun j => walkedAsWritten true (st.pool.get c j)) = true ∨
        t ≠ 0 := by
      rcases c' with h | h
      · exact Or.inr h
      · exact Or.inl (List.all_eq_true.2 fun j hj => h j (List.mem_range.1 hj))
    have f' := And.intro (f c List.mem_cons_self).2 fun x hx => f x (List.mem_cons_of_mem _ hx)
    rcases g with g | g
    · simpa [a, b, g, hz, hv, e] using f'
    · simpa [a, b, g, hz, hv, e] using f'

private theorem ok_store_fresh {t i : Nat} {d : UInt64} (hr : t ∉ st.pool.reached base) (ht : t ≠ 0)
    (hz : t ∈ st.zeroed) (hs : t ∉ st.sealed)
    (hsince : ∀ x ∈ st.steps.takeWhile (· != .zero t), ∀ u j e, x = .store u j e → u ≠ t ∨ j < i)
    (hc : ∀ c, poolChild? N base d = some c → c ∈ st.zeroed ∧ c ∉ st.sealed ∧
      ∀ x ∈ st.steps.takeWhile (· != .zero t), x.writes c = false) :
    okStep base st (.store t i d) = true := by
  have hr' : (st.pool.reached base).contains t = false := by
    cases h : (st.pool.reached base).contains t
    · rfl
    · exact absurd (contains_iff.1 h) hr
  have hch : (st.pool.children base 0).contains t = false := by
    cases h : (st.pool.children base 0).contains t
    · rfl
    · exact absurd (children_sub_reached (contains_iff.1 h)) hr
  have hzc : st.zeroed.contains t = true := contains_iff.2 hz
  have hsc : st.sealed.contains t = false := by
    cases h : st.sealed.contains t
    · rfl
    · exact absurd (contains_iff.1 h) hs
  have ht0 : (t != 0) = true := by simp [ht]
  unfold okStep
  simp only [hr', hch, Bool.false_eq_true, ite_false, hzc, hsc, ht0, Bool.true_or, Bool.not_false,
    Bool.true_and, Bool.not_true, Bool.and_eq_true, List.all_eq_true]
  have hall : ∀ x ∈ st.steps.takeWhile (· != .zero t), (match x with
      | .store u j _ => u != t || decide (j < i)
      | _ => true) = true := by
    intro x hx
    cases x with
    | store u j e =>
      rcases hsince _ hx u j e rfl with h | h
      · simp [h]
      · simp [h]
    | _ => rfl
  cases hcd : poolChild? N base d with
  | none => exact ⟨rfl, hall, rfl⟩
  | some c =>
    obtain ⟨a, b, f⟩ := hc c hcd
    refine ⟨?_, hall, ?_⟩
    · simp [a, b]
    · simp only [List.all_eq_true]
      intro x hx; simp [f x hx]

end Checks

/-! ## Runs of steps -/

private theorem takeWhile_cons_store {t u j : Nat} {e : UInt64} (l : Plan) :
    (Step.store u j e :: l).takeWhile (· != .zero t) =
      .store u j e :: l.takeWhile (· != .zero t) := by
  simp

theorem fill_allOk {base : UInt64} {t : Nat} (ht : t ≠ 0) :
    ∀ (xs : List (Nat × UInt64)) (st : PlanState N),
      t ∉ st.pool.reached base → t ∈ st.zeroed → t ∉ st.sealed →
      (∀ x ∈ st.steps.takeWhile (· != .zero t), ∃ j e, x = .store t j e ∧ ∀ y ∈ xs, j < y.1) →
      xs.Pairwise (fun x y => x.1 < y.1) →
      (∀ x ∈ xs, ∀ c, poolChild? N base x.2 = some c → c ∈ st.zeroed ∧ c ∉ st.sealed ∧ c ≠ t) →
      xs.Pairwise (fun x y => ∀ c, poolChild? N base x.2 = some c → poolChild? N base y.2 ≠ some c) →
      allOk base st (xs.map fun x => Step.store t x.1 x.2) = true
  | [], _, _, _, _, _, _, _, _ => rfl
  | x :: xs, st, hr, hz, hs, hsince, hpw, hc, hlk => by
    rw [List.pairwise_cons] at hpw hlk
    simp only [List.map_cons, allOk, Bool.and_eq_true]
    refine ⟨ok_store_fresh hr ht hz hs ?_ ?_, ?_⟩
    · intro y hy u j e hye
      obtain ⟨j', e', rfl, hlt⟩ := hsince y hy
      simp only [Step.store.injEq] at hye
      obtain ⟨-, rfl, -⟩ := hye
      exact Or.inr (hlt x List.mem_cons_self)
    · intro c hcx
      obtain ⟨a, b, c'⟩ := hc x List.mem_cons_self c hcx
      refine ⟨a, b, fun y hy => ?_⟩
      obtain ⟨j', e', rfl, -⟩ := hsince y hy
      simp [Step.writes, Ne.symm c']
    · refine fill_allOk ht xs _ ?_ hz ?_ ?_ hpw.2 ?_ hlk.2
      · rw [nxt_pool]
        show t ∉ (st.pool.store t x.1 x.2).reached base
        rw [(reached_store_fresh hr).1]; exact hr
      · simp only [nxt]
        cases hcx : poolChild? N base x.2 with
        | none => exact hs
        | some c =>
          intro h
          rcases List.mem_cons.1 h with h | h
          · exact (hc x List.mem_cons_self c hcx).2.2 h.symm
          · exact hs h
      · intro y hy
        rw [nxt_steps, takeWhile_cons_store] at hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨x.1, x.2, rfl, fun z hz => hpw.1 z hz⟩
        · obtain ⟨j, e, h1, h2⟩ := hsince y hy
          exact ⟨j, e, h1, fun z hz => h2 z (List.mem_cons_of_mem _ hz)⟩
      · intro y hy c hcy
        obtain ⟨a, b, c'⟩ := hc y (List.mem_cons_of_mem _ hy) c hcy
        refine ⟨a, ?_, c'⟩
        simp only [nxt]
        cases hcx : poolChild? N base x.2 with
        | none => exact b
        | some c'' =>
          intro h
          rcases List.mem_cons.1 h with h | h
          · subst h; exact hlk.1 y hy c hcx hcy
          · exact b h

theorem leaves_allOk {base : UInt64} :
    ∀ (xs : List (Nat × Nat × UInt64)) (st : PlanState N),
      (∀ x ∈ xs, x.1 ∈ st.pool.reached base ∧ x.1 ≠ 0 ∧ x.1 ∉ st.zeroed ∧
        isValid (st.pool.get x.1 x.2.1) = false ∧ poolChild? N base x.2.2 = none ∧
        (x.1 ∉ st.pool.children base 0 ∨ walkedAsWritten true x.2.2 = true)) →
      xs.Pairwise (fun x y => x.1 ≠ y.1 ∨ x.2.1 ≠ y.2.1) →
      allOk base st (xs.map fun x => Step.store x.1 x.2.1 x.2.2) = true
  | [], _, _, _ => rfl
  | x :: xs, st, hx, hpw => by
    rw [List.pairwise_cons] at hpw
    obtain ⟨a, b, c, d, e, f⟩ := hx x List.mem_cons_self
    simp only [List.map_cons, allOk, Bool.and_eq_true]
    refine ⟨ok_store_reached a (Or.inl b) f c d (fun c' h => by rw [e] at h; cases h), ?_⟩
    have hrc := reached_leaf (base := base) (t := x.1) (i := x.2.1) d e
    refine leaves_allOk xs _ (fun y hy => ?_) hpw.2
    obtain ⟨a', b', c', d', e', f'⟩ := hx y (List.mem_cons_of_mem _ hy)
    have hp : (nxt base st (Step.store x.1 x.2.1 x.2.2)).pool = st.pool.store x.1 x.2.1 x.2.2 := rfl
    have hz : (nxt base st (Step.store x.1 x.2.1 x.2.2)).zeroed = st.zeroed := rfl
    rw [hp, hz, hrc.1, hrc.2, get_store]
    refine ⟨a', b', c', ?_, e', f'⟩
    rw [ite_of_neg]; · exact d'
    rintro ⟨h1, h2, -⟩
    rcases hpw.1 y hy with h | h
    · exact h h1.symm
    · exact h h2.symm

end Krepi.Proofs.PageTables
