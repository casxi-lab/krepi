module

public import Krepi.SpecProperties.PageTables.Properties
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.PoolLemmas
import Krepi.Proofs.PageTables.WellFormedLemmas
import Krepi.Proofs.PageTables.WalkLemmas
import Krepi.Proofs.PageTables.MapCheckLemmas
import Krepi.Proofs.PageTables.OrderPlanLemmas
import Krepi.Proofs.PageTables.Mapping

/-!
# Page tables: proofs about the kernel tables

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about the kernel tables, whose type is
exactly that statement: that no frame is mapped writable and executable,
that the direct map is unchanged after boot, and that the kernel tables are
written only with empty entries.

`directMapUnchangedAfterBoot` and `kernelTablesOnlyFilled` are proved: once
the MMU is on, `kernel_map`, `direct_map` and turning the MMU on are not
enabled and the other transactions write neither the direct map's set nor
the MMU; a plan that keeps the order of `Plan.inOrder` from a well-formed
set writes only invalid entries (`Plan.fillsOnly`), and so keeps every
valid entry. `noWritableExecutable` is still planned: its proof is `sorry`,
and `verification/statements.json` registers it as `planned`. Mathlib is
imported so that the gate counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.PageTables.Kernel

open Krepi.SpecProperties.PageTables
open Krepi.Spec.PageTables
open Krepi.Proofs.PageTables
open Krepi.Proofs.Fdt (except_bind_ok except_jp_ok)

public theorem noWritableExecutable : NoWritableExecutable := by
  sorry

/-! ## The direct map after boot -/

private theorem withOwnership_sets {E X : Nat} {ε α : Type} {tok : OwnershipToken}
    {s s' : Shared E X} {f : Ownership E X → Except ε (Ownership E X × α)} {a : α}
    (h : s.withOwnership tok f = some (.ok (s', a))) :
    s'.lowerKernel = s.lowerKernel ∧ s'.directMap = s.directMap ∧ s'.mmuOn = s.mmuOn := by
  unfold Shared.withOwnership at h
  cases ho : s.ownership with
  | none => rw [ho] at h; cases h
  | some t =>
    rw [ho] at h
    cases hf : f t with
    | error e => simp [hf, Except.map] at h
    | ok r =>
      simp only [hf, Option.map_some, Except.map, Option.some.injEq, Except.ok.injEq,
        Prod.mk.injEq] at h
      rw [← h.1]; exact ⟨rfl, rfl, rfl⟩

private theorem newOwnership_sets {E X : Nat} {tok : OwnershipToken} {s s' : Shared E X}
    {arena : UInt64} {banks : List PhysRange} {ex : List Exclusion}
    (h : s.newOwnership tok arena banks ex = some (.ok s')) :
    s'.lowerKernel = s.lowerKernel ∧ s'.directMap = s.directMap ∧ s'.mmuOn = s.mmuOn := by
  unfold Shared.newOwnership at h
  cases ho : s.ownership with
  | some _ => rw [ho] at h; cases h
  | none =>
    rw [ho] at h
    cases hf : (Ownership.new arena banks ex : Except OwnershipError (Ownership E X)) with
    | error e => simp [hf, Except.map] at h
    | ok t =>
      simp only [hf, Except.map, Option.some.injEq, Except.ok.injEq] at h
      rw [← h]; exact ⟨rfl, rfl, rfl⟩

private theorem run_on {E X : Nat} (cfg : Config) (txn : Txn) (s : Shared E X)
    (h : s.mmuOn = true) :
    (txn.run cfg s).1.directMap = s.directMap ∧ (txn.run cfg s).1.mmuOn = true := by
  cases txn <;> simp only [Txn.run, Shared.buildKernelMap, Shared.buildDirectMap, Shared.enable,
    Shared.fillKernel, h, ite_true, Option.getD_none]
  all_goals try exact ⟨trivial, trivial⟩
  all_goals split
  all_goals try exact ⟨rfl, h⟩
  all_goals rename_i heq
  · simp only [Except.map, Option.some.injEq] at heq
    split at heq
    · cases heq
    · simp only [Except.ok.injEq, Prod.mk.injEq] at heq; rw [← heq.1]; exact ⟨rfl, rfl⟩
  · obtain ⟨-, a, b⟩ := newOwnership_sets heq; exact ⟨a, b.trans h⟩
  all_goals obtain ⟨-, a, b⟩ := withOwnership_sets heq; exact ⟨a, b.trans h⟩

public theorem directMapUnchangedAfterBoot : DirectMapUnchangedAfterBoot := by
  intro E X cfg s txns h
  induction txns generalizing s with
  | nil => exact ⟨rfl, h⟩
  | cons txn rest ih =>
    simp only [runAll, List.foldl_cons] at ih ⊢
    obtain ⟨h1, h2⟩ := run_on cfg txn s h
    obtain ⟨h3, h4⟩ := ih _ h2
    exact ⟨h3.trans h1, h4⟩

/-! ## Plans that fill invalid entries -/

section Fills

variable {N : Nat}

/-- What the check of the order keeps of the tables that no walk reaches: a
table not zeroed has no valid entry, and a zeroed one has valid entries only
where a step since its `Zero` stored. -/
private def Good (base : UInt64) (st : PlanState N) : Prop :=
  (∀ t, t ∉ st.pool.reached base → t ∉ st.zeroed → ∀ i, isValid (st.pool.get t i) = false) ∧
  ∀ t, t ∉ st.pool.reached base → t ∈ st.zeroed → ∀ i, isValid (st.pool.get t i) = true →
    ∃ d, Step.store t i d ∈ st.steps.takeWhile (· != .zero t)

private theorem reached_store_mono {p : Pool N} {base : UInt64} {t i : Nat} {d : UInt64}
    (hv : isValid (p.get t i) = false) {c : Nat} (hc : c ∈ p.reached base) :
    c ∈ (p.store t i d).reached base := by
  have hch : ∀ {t' c'}, c' ∈ p.children base t' → c' ∈ (p.store t i d).children base t' := by
    intro t' c' h
    obtain ⟨j, hj, hjc⟩ := mem_children.1 h
    refine mem_children.2 ⟨j, hj, ?_⟩
    rw [get_store]
    split
    · rename_i he; obtain ⟨rfl, rfl, -⟩ := he
      rw [poolChild_none] at hjc
      · cases hjc
      · cases hp : isPlainTableDescriptor (p.get t' j)
        · rfl
        · rw [isValid_of_isPlain hp] at hv; cases hv
    · exact hjc
  rcases mem_reached.1 hc with rfl | h | ⟨t2, h2, h⟩
  · exact zero_mem_reached _ _
  · exact children_sub_reached (hch h)
  · exact mem_reached.2 (Or.inr (Or.inr ⟨t2, hch h2, hch h⟩))

private theorem store_reached_inv {base : UInt64} {st : PlanState N} {t i : Nat} {d : UInt64}
    (h : okStep base st (.store t i d) = true) (hr : t ∈ st.pool.reached base) :
    isValid (st.pool.get t i) = false := by
  have hr' : (st.pool.reached base).contains t = true := contains_iff.2 hr
  cases hv : isValid (st.pool.get t i)
  · rfl
  · simp only [okStep, hr', ite_true, hv, Bool.not_true, Bool.false_and, Bool.and_false] at h
    cases h

private theorem store_fresh_inv {base : UInt64} {st : PlanState N} {t i : Nat} {d : UInt64}
    (h : okStep base st (.store t i d) = true) (hr : t ∉ st.pool.reached base) :
    t ∈ st.zeroed ∧ ∀ x ∈ st.steps.takeWhile (· != .zero t), ∀ u j e, x = .store u j e →
      u ≠ t ∨ j < i := by
  have hr' : (st.pool.reached base).contains t = false := by
    cases h' : (st.pool.reached base).contains t
    · rfl
    · exact absurd (contains_iff.1 h') hr
  simp only [okStep, hr', Bool.false_eq_true, ite_false, Bool.and_eq_true, List.all_eq_true] at h
  refine ⟨contains_iff.1 h.2.1.1.1, fun x hx u j e hxe => ?_⟩
  have := h.2.1.2 x hx
  subst hxe
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at this
  exact this

private theorem inOrder_fills {base : UInt64} :
    ∀ (plan : Plan) (st : PlanState N), Plan.inOrder base plan st = true → Good base st →
      plan.fillsOnly st.pool = true
  | [], _, _, _ => rfl
  | [.sync], _, _, _ => rfl
  | .sync :: x :: rest, st, h, hg => by
    have h' : Plan.inOrder base (x :: rest) (nxt base st .sync) = true := h
    simp only [Plan.fillsOnly, Bool.true_and]
    refine inOrder_fills (x :: rest) (nxt base st .sync) h'
      ⟨fun t ht hz i => hg.1 t ht hz i, fun t ht hz i hv => ?_⟩
    obtain ⟨d, hd⟩ := hg.2 t ht hz i hv
    exact ⟨d, by rw [nxt_steps]; simp [hd]⟩
  | .zero t :: rest, st, h, hg => by
    rw [inOrder_cons _ _ _ _ (by simp), Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    simp only [okStep, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, contains_iff] at h1
    obtain ⟨hr, hz⟩ := h1
    have hrr := reached_zero_fresh (p := st.pool) (base := base) hr
    simp only [Plan.fillsOnly, Bool.and_eq_true, List.all_eq_true]
    refine ⟨fun i _ => by simp [hg.1 t hr hz i], inOrder_fills rest _ h2 ⟨?_, ?_⟩⟩
    · intro t' ht' hz' i
      simp only [nxt, List.mem_cons, not_or] at hz'
      have ht'' : t' ∉ st.pool.reached base := by
        have : (nxt base st (.zero t)).pool = st.pool.zeroTable t := rfl
        rwa [this, hrr.1] at ht'
      show isValid ((st.pool.zeroTable t).get t' i) = false
      rw [get_zeroTable, ite_of_neg hz'.1]; exact hg.1 t' ht'' hz'.2 i
    · intro t' ht' hz' i hv
      have hp : (nxt base st (.zero t)).pool = st.pool.zeroTable t := rfl
      rw [hp, hrr.1] at ht'
      rw [hp, get_zeroTable] at hv
      by_cases e : t' = t
      · rw [ite_of_pos e] at hv; cases hv
      · rw [ite_of_neg e] at hv
        simp only [nxt, List.mem_cons, e, false_or] at hz'
        obtain ⟨d, hd⟩ := hg.2 t' ht' hz' i hv
        exact ⟨d, by rw [nxt_steps]; simp [hd, Ne.symm e]⟩
  | .store t i d :: rest, st, h, hg => by
    rw [inOrder_cons _ _ _ _ (by simp), Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    simp only [Plan.fillsOnly, Bool.and_eq_true, Bool.not_eq_true']
    have hp : (nxt base st (.store t i d)).pool = st.pool.store t i d := rfl
    have hz : (nxt base st (.store t i d)).zeroed = st.zeroed := rfl
    have hsteps := nxt_steps base st (.store t i d)
    by_cases hr : t ∈ st.pool.reached base
    · have hv := store_reached_inv h1 hr
      refine ⟨hv, inOrder_fills rest _ h2 ⟨fun t' ht' hz' j => ?_, fun t' ht' hz' j hv' => ?_⟩⟩
      · rw [hp] at ht' ⊢; rw [hz] at hz'
        have ht'' : t' ∉ st.pool.reached base := fun h => ht' (reached_store_mono hv h)
        have hne : t' ≠ t := fun e => ht'' (e ▸ hr)
        rw [get_store, ite_of_neg (fun h => hne h.1)]; exact hg.1 t' ht'' hz' j
      · rw [hp] at ht' hv'; rw [hz] at hz'
        have ht'' : t' ∉ st.pool.reached base := fun h => ht' (reached_store_mono hv h)
        have hne : t' ≠ t := fun e => ht'' (e ▸ hr)
        rw [get_store, ite_of_neg (fun h => hne h.1)] at hv'
        obtain ⟨d', hd'⟩ := hg.2 t' ht'' hz' j hv'
        exact ⟨d', by rw [hsteps]; simp [hd']⟩
    · obtain ⟨hzt, hsince⟩ := store_fresh_inv h1 hr
      have hv : isValid (st.pool.get t i) = false := by
        cases hv : isValid (st.pool.get t i)
        · rfl
        · obtain ⟨d', hd'⟩ := hg.2 t hr hzt i hv
          rcases hsince _ hd' t i d' rfl with h' | h'
          · exact absurd rfl h'
          · exact absurd h' (Nat.lt_irrefl _)
      have hrr := reached_store_fresh (p := st.pool) (base := base) (i := i) (d := d) hr
      refine ⟨hv, inOrder_fills rest _ h2 ⟨fun t' ht' hz' j => ?_, fun t' ht' hz' j hv' => ?_⟩⟩
      · rw [hp, hrr.1] at ht'; rw [hz] at hz'
        have hne : t' ≠ t := fun e => hz' (e ▸ hzt)
        rw [hp, get_store, ite_of_neg (fun h => hne h.1)]; exact hg.1 t' ht' hz' j
      · rw [hp, hrr.1] at ht'; rw [hz] at hz'; rw [hp, get_store] at hv'
        split at hv'
        · rename_i he; obtain ⟨rfl, rfl, -⟩ := he
          exact ⟨d, by rw [hsteps]; simp⟩
        · obtain ⟨d', hd'⟩ := hg.2 t' ht' hz' j hv'
          exact ⟨d', by rw [hsteps]; simp [hd']⟩
  | .fence :: rest, st, h, hg => by
    rw [inOrder_cons _ _ _ _ (by simp), Bool.and_eq_true] at h
    simp only [Plan.fillsOnly, Bool.true_and]
    refine inOrder_fills rest (nxt base st .fence) h.2
      ⟨fun t ht hz i => hg.1 t ht hz i, fun t ht hz i hv => ?_⟩
    obtain ⟨d, hd⟩ := hg.2 t ht hz i hv
    exact ⟨d, by rw [nxt_steps]; simp [hd]⟩
  | .invalidate _ :: rest, st, h, _ => by
    rw [inOrder_cons _ _ _ _ (by simp)] at h; simp [okStep] at h

private theorem fills_keep {t i : Nat} : ∀ (plan : Plan) (p : Pool N), plan.fillsOnly p = true →
    isValid (p.get t i) = true → (plan.exec p).get t i = p.get t i
  | [], _, _, _ => rfl
  | step :: rest, p, h, hv => by
    simp only [Plan.fillsOnly, Bool.and_eq_true] at h
    have e : (step.exec p).get t i = p.get t i := by
      cases step with
      | zero u =>
        simp only [Step.exec, get_zeroTable]
        split
        · rename_i hu; subst hu
          have := h.1
          simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true'] at this
          by_cases hi : i < ENTRIES
          · rw [this i hi] at hv; cases hv
          · rw [get_of_ge_entries _ _ (by omega)] at hv; cases hv
        · rfl
      | store u j e =>
        simp only [Step.exec, get_store]
        split
        · rename_i he; obtain ⟨rfl, rfl, -⟩ := he
          have := h.1; simp only [Bool.not_eq_true'] at this; rw [this] at hv; cases hv
        · rfl
      | fence => rfl
      | sync => rfl
      | invalidate _ => simp at h
    rw [exec_cons, fills_keep rest _ h.2 (e ▸ hv), e]

end Fills

private theorem set_write {r : Region} {N : Nat} {T T' : Tables r N} {base : UInt64} {bits : UInt8}
    {plan : Plan} (hT : T.WellFormed base bits) (hp : T'.pool = T.pool)
    (ho : plan.publishesInOrder base T.pool = true) :
    plan.fillsOnly T.pool = true ∧
      ∀ t i, isValid (T.entry t i) = true → (T'.apply plan).entry t i = T.entry t i := by
  have hf : plan.fillsOnly T.pool = true := by
    refine inOrder_fills plan _ ho ⟨fun t ht _ i => ?_, fun t _ hz => by cases hz⟩
    have : T.used ≤ t := Nat.le_of_not_lt fun h => ht ((wf_mem_reached hT).2 h)
    show isValid (T.pool.get t i) = false
    rw [← entry_eq_get, wf_entry_free hT this]; decide
  refine ⟨hf, fun t i hv => ?_⟩
  rw [entry_eq_get] at hv
  rw [entry_eq_get, entry_eq_get]
  show (plan.exec T'.pool).get t i = _
  rw [hp]; exact fills_keep plan _ hf hv

private theorem mapPage_pool {r : Region} {N : Nat} {s s' : Tables r N} {v p base : UInt64}
    {k : Kind} {bits : UInt8} {plan : Plan} (h : s.mapPage v p k base bits = .ok (s', plan)) :
    s'.pool = s.pool := by
  unfold Tables.mapPage at h
  obtain ⟨-, -, h⟩ := except_bind_ok.1 h
  obtain ⟨-, -, h⟩ := except_bind_ok.1 h
  obtain ⟨w, -, h⟩ := except_bind_ok.1 h
  rcases w with _ | ⟨t2, e2⟩
  · obtain ⟨-, h⟩ := except_jp_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]
  · dsimp only at h
    split at h
    · obtain ⟨-, h⟩ := except_jp_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]
    · split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · split at h
        next =>
          split at h
          next => simp [throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at h
          next =>
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            rw [← h.1]
        next => simp [throw, throwThe, MonadExceptOf.throw] at h

private theorem map_ok {ε α β : Type} {f : α → β} {e : Except ε α} {b : β}
    (h : Except.map f e = .ok b) : ∃ a, e = .ok a ∧ b = f a := by
  cases e with
  | error _ => simp [Except.map] at h
  | ok a => simp only [Except.map, Except.ok.injEq] at h; exact ⟨a, rfl, h.symm⟩

public theorem kernelTablesOnlyFilled : KernelTablesOnlyFilled := by
  intro E X cfg s txn hs
  obtain ⟨hl, hd, -⟩ := hs
  have keep : ∀ (s' : Shared E X), s'.lowerKernel = s.lowerKernel → s'.directMap = s.directMap →
      (∀ t i, isValid (s.lowerKernel.entry t i) = true →
        s'.lowerKernel.entry t i = s.lowerKernel.entry t i) ∧
      (∀ t i, isValid (s.directMap.entry t i) = true →
        s'.directMap.entry t i = s.directMap.entry t i) := fun s' h1 h2 =>
    ⟨fun t i _ => by rw [h1], fun t i _ => by rw [h2]⟩
  cases txn with
  | kernelMap layout =>
    simp only [Txn.run]
    split
    · rename_i s' plan heq
      unfold Shared.buildKernelMap at heq
      split at heq
      · cases heq
      · obtain ⟨⟨t, pl⟩, h1, h2⟩ := map_ok (Option.some.inj heq)
        simp only [Prod.mk.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2
        obtain ⟨leaves, hlf, -, hN, hplan, hpool⟩ := kernelMap_facts hl h1
        obtain ⟨hf, hk⟩ := set_write hl hpool (hplan ▸ mapPlan_inOrder hl hlf hN)
        exact ⟨hk, fun _ _ _ => rfl, fun plan' h => by
          simp only [Option.some.injEq] at h; subst h; exact hf⟩
    · exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ h => by cases h⟩
  | directMap memory =>
    simp only [Txn.run]
    split
    · rename_i s' plan heq
      unfold Shared.buildDirectMap at heq
      split at heq
      · cases heq
      · obtain ⟨⟨t, pl⟩, h1, h2⟩ := map_ok (Option.some.inj heq)
        simp only [Prod.mk.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2
        obtain ⟨leaves, hlf, -, hN, -, hplan, hpool⟩ := directMap_facts hd h1
        obtain ⟨hf, hk⟩ := set_write hd hpool (hplan ▸ mapPlan_inOrder hd hlf hN)
        exact ⟨fun _ _ _ => rfl, hk, fun plan' h => by
          simp only [Option.some.injEq] at h; subst h; exact hf⟩
    · exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ h => by cases h⟩
  | fill v p k =>
    simp only [Txn.run]
    split
    · rename_i s' plan heq
      unfold Shared.fillKernel at heq
      split at heq
      · obtain ⟨⟨t, pl⟩, h1, h2⟩ := map_ok (Option.some.inj heq)
        simp only [Prod.mk.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2
        obtain ⟨hf, hk⟩ := set_write hl (mapPage_pool h1)
          (Mapping.plansPublishInOrder.1 _ _ _ _ _ _ _ _ _ _ hl h1)
        exact ⟨hk, fun _ _ _ => rfl, fun plan' h => by
          simp only [Option.some.injEq] at h; subst h; exact hf⟩
      · cases heq
    · exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ h => by cases h⟩
  | enable =>
    simp only [Txn.run, Shared.enable]
    split <;> exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ h => by cases h⟩
  | newOwnership arena banks ex =>
    simp only [Txn.run]
    split
    · rename_i heq; obtain ⟨a, b, -⟩ := newOwnership_sets heq
      exact ⟨(keep _ a b).1, (keep _ a b).2, fun _ h => by cases h⟩
    · exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ h => by cases h⟩
  | _ =>
    simp only [Txn.run, Shared.allocate]
    split
    · rename_i heq; obtain ⟨a, b, -⟩ := withOwnership_sets heq
      exact ⟨(keep _ a b).1, (keep _ a b).2, fun _ h => by cases h⟩
    · exact ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ h => by cases h⟩

end Krepi.Proofs.PageTables.Kernel
