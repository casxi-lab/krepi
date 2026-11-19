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
import Krepi.Proofs.PageTables.Tables
import Krepi.Proofs.PageTables.EntryLemmas
import Krepi.Proofs.PageTables.ListLemmas
import Krepi.Proofs.PageTables.CloneWalkLemmas
import Krepi.Proofs.Fdt.Plan

/-!
# Page tables: proofs about the kernel tables

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about the kernel tables, whose type is
exactly that statement: that no frame is mapped writable and executable,
that the direct map is unchanged after boot, and that the kernel tables are
written only with empty entries.

Every theorem here is proved. Once the MMU is on, `kernel_map`, `direct_map`
and turning the MMU on are not enabled and the other transactions write
neither the direct map's set nor the MMU; a plan that keeps the order of
`Plan.inOrder` from a well-formed set writes only invalid entries
(`Plan.fillsOnly`), and so keeps every valid entry.

For W^X, every shared state that the transactions reach from the boot keeps
an invariant: each kernel set is well-formed or still the set of the boot;
an executable leaf of the lower kernel set maps a page of the text of the
layout, and a page of the text is mapped there only with `ReadExecute`
(the ranges of `kernel_map` share no page, and the fills follow
`WxPremises`); and each leaf of the direct map's set is `ReadWrite` and maps a
page of a usable range of a boot memory map, which shares no page with its
boot storage and so with the text. The leaves of a copy of the lower kernel
set are leaves of that set (`Krepi.Proofs.PageTables.CloneWalkLemmas`).
The conjunct of `WxPremises` that `direct_map` runs at most once is not
used; that `kernel_map` runs at most once is: a second, refused layout could
otherwise make an executable fill of a page that the first maps writable
satisfy the rules of the fills. Mathlib is imported so that the gate counts
the heartbeats of each theorem.
-/

namespace Krepi.Proofs.PageTables.Kernel

open Krepi.SpecProperties.PageTables
open Krepi.Spec.PageTables
open Krepi.Proofs.PageTables
open Krepi.Proofs.Fdt (except_bind_ok except_jp_ok)

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
        obtain ⟨leaves, hlf, -, hN, hplan, hpool, -⟩ := kernelMap_facts hl h1
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
        obtain ⟨leaves, hlf, -, hN, -, hplan, hpool, -⟩ := directMap_facts hd h1
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
        obtain ⟨-, -, -, -, -, -, -, hpool⟩ := mapPage_single hl h1
        obtain ⟨hf, hk⟩ := set_write hl hpool
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

/-! ## No frame mapped writable and executable -/

section Wx

/-- A set of the boot, `Tables::new` on zero storage, maps nothing. -/
private theorem new_M {r : Region} {N : Nat} {base v : UInt64} {l : Leaf} :
    ¬ (Tables.new (Pool.zero N) : Tables r N).M base v l := by
  have h0 : ∀ i, isValid ((Tables.new (Pool.zero N) : Tables r N).entry 0 i) = false := by
    intro i; rw [entry_eq_get]; simp [Tables.new, Pool.zero, Pool.get, Table.zero, isValid_zero]
  have hw2 : ∀ {w}, (Tables.new (Pool.zero N) : Tables r N).walk2 base v = .ok (some w) → False := by
    intro w hw
    rcases walk2_ok.1 hw with ⟨-, h⟩ | ⟨_, hv, -⟩
    · cases h
    · rw [h0] at hv; cases hv
  rintro ⟨-, -, ⟨t2, t3, d, hw, -⟩ | ⟨t2, d, hw, -⟩⟩
  · obtain ⟨e2, h, -⟩ := walk_ok_level3.1 hw; exact hw2 h
  · exact hw2 (walk_ok_block.1 hw).1

/-- A set that the transactions reach: well-formed, or the set of the boot,
which stays so while its pool is not one that the contract admits. -/
private def SetOk {r : Region} {N : Nat} (T : Tables r N) (base : UInt64) (bits : UInt8) : Prop :=
  T.WellFormed base bits ∨ T = Tables.new (Pool.zero N)

private theorem setOk_wf {r : Region} {N : Nat} {T : Tables r N} {base : UInt64} {bits : UInt8}
    (h : SetOk T base bits) (hp : PoolOk N base bits) : T.WellFormed base bits := by
  rcases h with h | rfl
  · exact h
  · exact Tables.newWellFormed r N base bits hp

/-- What W^X needs of each leaf of the lower kernel set, for the layouts `Ls`
of the transactions: an executable leaf maps a page of the text, and a page
of the text is mapped only with `ReadExecute`. -/
private def LowerOk (Ls : List Layout) (T : Tables .lower KERNEL_TABLES) (base : UInt64) : Prop :=
  ∀ v l, T.M base v l →
    (l.kind.attributes.executable = true → ∃ L ∈ Ls, L.text l.pa.toNat = true) ∧
    ∀ L ∈ Ls, L.text l.pa.toNat = true → l.kind = .readExecute

/-- What W^X needs of each leaf of the direct map's set, for the boot memory
maps `Bs` of the transactions: it is `ReadWrite` and maps a page of a usable
range of one of them. -/
private def DirectOk (Bs : List Krepi.Spec.Fdt.MemoryPlan) (T : Tables .upper DIRECT_MAP_TABLES)
    (base : UInt64) : Prop :=
  ∀ v l, T.M base v l → l.kind = .readWrite ∧ ∃ B ∈ Bs, ∃ u ∈ B.availableRanges,
    u.start.toNat ≤ l.pa.toNat ∧ l.pa.toNat < u.endNat

/-- The invariant of the shared states that the transactions reach. -/
private def Inv {E X : Nat} (Ls : List Layout) (Bs : List Krepi.Spec.Fdt.MemoryPlan) (cfg : Config)
    (s : Shared E X) : Prop :=
  SetOk s.lowerKernel cfg.lowerBase cfg.bits ∧ SetOk s.directMap cfg.directBase cfg.bits ∧
    LowerOk Ls s.lowerKernel cfg.lowerBase ∧ DirectOk Bs s.directMap cfg.directBase

/-- What `WxPremises` gives a transaction of the list. -/
private def TxnOk (Ls : List Layout) (Bs : List Krepi.Spec.Fdt.MemoryPlan) : Txn → Prop
  | .kernelMap layout => layout ∈ Ls
  | .directMap memory => memory ∈ Bs
  | .fill _ p k => (k.attributes.executable = true → ∃ L ∈ Ls, L.text p.toNat = true) ∧
      ∀ L ∈ Ls, L.text p.toNat = true → k = .readExecute
  | _ => True

/-- The page at `q` of a range of `count` pages from `pa`. -/
private theorem mem_layoutPages (k : Kind) : ∀ (count pa q : Nat), pa % PAGE_SIZE = 0 →
    q % PAGE_SIZE = 0 → pa ≤ q → q + PAGE_SIZE ≤ pa + count * PAGE_SIZE →
    ∃ x ∈ layoutPages k count pa, x.pa = UInt64.ofNat q
  | 0, pa, q, _, _, h1, h2 => by simp only [PAGE_SIZE] at h2; omega
  | count + 1, pa, q, hpa, hq, h1, h2 => by
    simp only [layoutPages]
    by_cases he : q = pa
    · exact ⟨_, List.mem_cons_self, by rw [he]⟩
    · obtain ⟨x, hx, hxq⟩ := mem_layoutPages k count (pa + PAGE_SIZE) q
        (by simp only [PAGE_SIZE] at hpa ⊢; omega) hq
        (by simp only [PAGE_SIZE] at hpa hq ⊢; omega) (by rw [Nat.add_mul] at h2; omega)
      exact ⟨x, List.mem_cons_of_mem _ hx, hxq⟩

private theorem layout_exec {k : Kind} (h : layoutKinds.contains k = true)
    (he : k.attributes.executable = true) : k = .readExecute := by
  revert h he; cases k <;> decide

/-- `kernel_map` keeps the facts of W^X of the lower kernel set: each new leaf
is a page of a range of the layout with the kind of the range, and the ranges
share no page. -/
private theorem kernelMap_ok {Ls : List Layout} {T T' : Tables .lower KERNEL_TABLES}
    {layout : Layout} {base : UInt64} {bits : UInt8} {plan : Plan} (hT : SetOk T base bits)
    (hlo : LowerOk Ls T base) (hmem : layout ∈ Ls) (huniq : ∀ L ∈ Ls, L = layout)
    (h : T.kernelMap layout base bits = .ok (T', plan)) :
    SetOk (T'.apply plan) base bits ∧ LowerOk Ls (T'.apply plan) base := by
  have hp : PoolOk KERNEL_TABLES base bits := by
    unfold Tables.kernelMap at h
    obtain ⟨_, hc, -⟩ := except_bind_ok.1 h
    exact checkPool_ok.1 hc
  have hw := setOk_wf hT hp
  obtain ⟨leaves, hlf, happ, hN, -, -, hmap, hok⟩ := kernelMap_facts hw h
  refine ⟨Or.inl (happ ▸ final_wf hw hlf hN), fun v l hm => ?_⟩
  rw [happ] at hm
  rcases final_M hw hlf hN hm with hold | ⟨q, hq, -, -, -, hpg, -⟩
  · exact hlo v l hold
  obtain ⟨pl, hqm, -⟩ := placed_leaf hlf hq
  have hx : q.leaf ∈ leaves.map Prod.fst := List.mem_map.2 ⟨_, hqm, rfl⟩
  have hx' := hx
  rw [hmap] at hx'
  obtain ⟨j, hj, hxj⟩ := List.mem_flatMap.1 hx'
  obtain ⟨hs1, hs2, hs3, hva, hform, hdesc⟩ := (rangePages_spec (hok j hj)).1 _ hxj
  obtain ⟨hpa, hkind⟩ := hpg hform
  have h48 : ∀ j ∈ sortByKey (·.range.start.toNat) layout.ranges, j.range.endNat < 2 ^ 48 :=
    fun j hj => by have := (hok j hj).2.2.1; simp only [VA_LIMIT] at this; omega
  have hlpa : l.pa = q.leaf.pa := by
    rw [hpa, hdesc, outputAddress_descriptor, outputAddress_of_aligned hs3 (by have := h48 j hj; omega)]
  have hlk : l.kind = j.kind := by
    rw [hdesc, ofPage_descriptor] at hkind; exact (Option.some.inj hkind).symm
  have hjL : j ∈ layout.ranges := (sortByKey_perm _ _).subset hj
  rw [hlpa]
  refine ⟨fun hx => ⟨layout, hmem, ?_⟩, fun L hL ht => ?_⟩
  · have hre : j.kind = .readExecute := layout_exec j.named (hlk ▸ hx)
    refine List.any_eq_true.2 ⟨j, hjL, ?_⟩
    simp only [hre, Bool.and_eq_true, beq_self_eq_true, decide_eq_true_eq, true_and]
    exact ⟨hs1, hs2⟩
  · rw [huniq L hL] at ht
    obtain ⟨j0, hj0, hc⟩ := List.any_eq_true.1 ht
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨hre, h1⟩, h2⟩ := hc
    have hj0' : j0 ∈ sortByKey (·.range.start.toNat) layout.ranges :=
      (sortByKey_perm _ _).symm.subset hj0
    obtain ⟨o1, o2, -, -⟩ := hok j0 hj0'
    obtain ⟨y, hy, hyq⟩ := mem_layoutPages j0.kind (j0.range.len.toNat / PAGE_SIZE)
      j0.range.start.toNat q.leaf.pa.toNat o1 hs3 h1
      (by simp only [PhysRange.endNat, PAGE_SIZE] at o1 o2 h2 ⊢; omega)
    obtain ⟨-, -, -, hyva, hyf, hyd⟩ := (rangePages_spec (hok j0 hj0')).1 y hy
    have hyp : y.pa = q.leaf.pa := by rw [hyq, UInt64.ofNat_toNat]
    have hy' : y ∈ leaves.map Prod.fst := by
      rw [hmap]; exact List.mem_flatMap.2 ⟨j0, hj0', hy⟩
    have hyx : y = q.leaf := by
      rcases pairwise_mem hlf.order hy' hx with e | e | e
      · exact e
      · rw [hyva, hyp, ← hva] at e; have := form_size_pos y.form; omega
      · rw [hyva, hyp, ← hva] at e; have := form_size_pos q.leaf.form; omega
    have := congrArg MapLeaf.desc hyx
    rw [hyd, hdesc, hyp] at this
    rw [hlk, ← descriptor_kind_inj this, hre]

/-- `direct_map` keeps the facts of W^X of the direct map's set: each new
leaf is a `ReadWrite` page or block of a usable range of the boot memory map. -/
private theorem directMap_ok {Bs : List Krepi.Spec.Fdt.MemoryPlan}
    {T T' : Tables .upper DIRECT_MAP_TABLES} {memory : Krepi.Spec.Fdt.MemoryPlan} {base : UInt64}
    {bits : UInt8} {plan : Plan} (hT : SetOk T base bits) (hdo : DirectOk Bs T base)
    (hmem : memory ∈ Bs) (h : T.directMap memory base bits = .ok (T', plan)) :
    SetOk (T'.apply plan) base bits ∧ DirectOk Bs (T'.apply plan) base := by
  have hp : PoolOk DIRECT_MAP_TABLES base bits := by
    unfold Tables.directMap at h
    obtain ⟨_, hc, -⟩ := except_bind_ok.1 h
    exact checkPool_ok.1 hc
  have hw := setOk_wf hT hp
  obtain ⟨leaves, hlf, happ, hN, -, -, -, hmap, hok⟩ := directMap_facts hw h
  refine ⟨Or.inl (happ ▸ final_wf hw hlf hN), fun v l hm => ?_⟩
  rw [happ] at hm
  rcases final_M hw hlf hN hm with hold | ⟨q, hq, -, -, hfm, hpg, hbk⟩
  · exact hdo v l hold
  obtain ⟨pl, hqm, -⟩ := placed_leaf hlf hq
  have hx : q.leaf ∈ leaves.map Prod.fst := List.mem_map.2 ⟨_, hqm, rfl⟩
  rw [hmap] at hx
  obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.1 hx
  obtain ⟨hs1, hs2, -, hal, hpage, hblock⟩ := (usableLeaves_spec (hok u hu)).1 _ hxu
  have hlim := (hok u hu).2.2.1
  have huB : u ∈ memory.availableRanges := (sortByKey_perm _ _).subset hu
  have hsz := form_size_pos q.leaf.form
  cases hf : q.leaf.form with
  | page =>
    obtain ⟨hpa, hkind⟩ := hpg hf
    rw [hpage hf, ofPage_descriptor] at hkind
    rw [hf] at hal hs2
    rw [hpage hf, outputAddress_descriptor,
      outputAddress_of_aligned hal (by simp only [VA_LIMIT, Form.size] at hlim hs2 ⊢; omega)] at hpa
    refine ⟨(Option.some.inj hkind).symm, memory, hmem, u, huB, ?_, ?_⟩ <;> rw [hpa]
    · exact hs1
    · simp only [Form.size, PAGE_SIZE] at hs2; omega
  | block =>
    obtain ⟨hpa, hkind⟩ := hbk hf
    rw [hf] at hal hs2
    rw [hblock hf, blockAddress_blockDescriptor,
      blockAddress_of_aligned hal (by simp only [VA_LIMIT, Form.size] at hlim hs2 ⊢; omega)] at hpa
    have hmod : v.toNat % BLOCK_SIZE < BLOCK_SIZE := Nat.mod_lt _ (by decide)
    refine ⟨hkind, memory, hmem, u, huB, ?_, ?_⟩ <;> rw [hpa]
    · omega
    · simp only [Form.size] at hs2; omega

/-- A fill keeps the facts of W^X of the lower kernel set: its one leaf is a
page of its kind, whose rules `WxPremises` states. -/
private theorem fill_ok {Ls : List Layout} {T T' : Tables .lower KERNEL_TABLES} {v p : UInt64}
    {k : Kind} {base : UInt64} {bits : UInt8} {plan : Plan} (hT : SetOk T base bits)
    (hlo : LowerOk Ls T base)
    (hk : (k.attributes.executable = true → ∃ L ∈ Ls, L.text p.toNat = true) ∧
      ∀ L ∈ Ls, L.text p.toNat = true → k = .readExecute)
    (h : T.mapPage v p k base bits = .ok (T', plan)) :
    SetOk (T'.apply plan) base bits ∧ LowerOk Ls (T'.apply plan) base := by
  have hp : PoolOk KERNEL_TABLES base bits := by
    unfold Tables.mapPage at h
    obtain ⟨_, hc, -⟩ := except_bind_ok.1 h
    obtain ⟨-, h2, -, h4, h5⟩ := checkEntry_ok.1 hc
    exact ⟨h2, h4, h5⟩
  have hw := setOk_wf hT hp
  obtain ⟨pl, hlf, happ, hN, -, hpa, hpb, -⟩ := mapPage_single hw h
  refine ⟨Or.inl (happ ▸ final_wf hw hlf hN), fun v' l hm => ?_⟩
  rw [happ] at hm
  rcases final_M hw hlf hN hm with hold | ⟨q, hq, -, -, -, hpg, -⟩
  · exact hlo v' l hold
  obtain ⟨pl', hqm, -⟩ := placed_leaf hlf hq
  rw [List.mem_singleton, Prod.mk.injEq] at hqm
  obtain ⟨hql, -⟩ := hqm
  obtain ⟨hpa', hkind⟩ := hpg (by rw [hql])
  rw [hql, ofPage_descriptor] at hkind
  rw [hql, outputAddress_descriptor,
    outputAddress_of_aligned hpa (Nat.lt_of_lt_of_le hpb (pool_ok_facts hp).2.2.2)] at hpa'
  rw [hpa', ← Option.some.inj hkind]
  exact hk

private theorem map_some_ok {ε α β : Type} {f : α → β} {e : Except ε α} {b : β}
    (h : some (Except.map f e) = some (.ok b)) : ∃ a, e = .ok a ∧ b = f a :=
  map_ok (Option.some.inj h)

/-- One transaction keeps the invariant. -/
private theorem inv_step {E X : Nat} {Ls : List Layout} {Bs : List Krepi.Spec.Fdt.MemoryPlan}
    (huniq : ∀ L ∈ Ls, ∀ L' ∈ Ls, L = L') (cfg : Config) (txn : Txn) (s : Shared E X)
    (ht : TxnOk Ls Bs txn) (hs : Inv Ls Bs cfg s) : Inv Ls Bs cfg (txn.run cfg s).1 := by
  obtain ⟨hl, hd, hlo, hdo⟩ := hs
  cases txn with
  | kernelMap layout =>
    simp only [Txn.run]
    split
    · rename_i s' plan heq
      unfold Shared.buildKernelMap at heq
      split at heq
      · cases heq
      · obtain ⟨⟨t, pl⟩, h1, h2⟩ := map_some_ok heq
        simp only [Prod.mk.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2
        obtain ⟨a, b⟩ := kernelMap_ok hl hlo ht (fun L hL => huniq L hL layout ht) h1
        exact ⟨a, hd, b, hdo⟩
    · exact ⟨hl, hd, hlo, hdo⟩
  | directMap memory =>
    simp only [Txn.run]
    split
    · rename_i s' plan heq
      unfold Shared.buildDirectMap at heq
      split at heq
      · cases heq
      · obtain ⟨⟨t, pl⟩, h1, h2⟩ := map_some_ok heq
        simp only [Prod.mk.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2
        obtain ⟨a, b⟩ := directMap_ok hd hdo ht h1
        exact ⟨hl, a, hlo, b⟩
    · exact ⟨hl, hd, hlo, hdo⟩
  | fill v p k =>
    simp only [Txn.run]
    split
    · rename_i s' plan heq
      unfold Shared.fillKernel at heq
      split at heq
      · obtain ⟨⟨t, pl⟩, h1, h2⟩ := map_some_ok heq
        simp only [Prod.mk.injEq] at h2; obtain ⟨rfl, rfl⟩ := h2
        obtain ⟨a, b⟩ := fill_ok hl hlo ht h1
        exact ⟨a, hd, b, hdo⟩
      · cases heq
    · exact ⟨hl, hd, hlo, hdo⟩
  | enable =>
    simp only [Txn.run, Shared.enable]
    split <;> exact ⟨hl, hd, hlo, hdo⟩
  | newOwnership arena banks ex =>
    simp only [Txn.run]
    split
    · rename_i heq; obtain ⟨a, b, -⟩ := newOwnership_sets heq
      unfold Inv; rw [a, b]; exact ⟨hl, hd, hlo, hdo⟩
    · exact ⟨hl, hd, hlo, hdo⟩
  | _ =>
    simp only [Txn.run, Shared.allocate]
    split
    · rename_i heq; obtain ⟨a, b, -⟩ := withOwnership_sets heq
      unfold Inv; rw [a, b]; exact ⟨hl, hd, hlo, hdo⟩
    · exact ⟨hl, hd, hlo, hdo⟩

private theorem inv_run {E X : Nat} {Ls : List Layout} {Bs : List Krepi.Spec.Fdt.MemoryPlan}
    (huniq : ∀ L ∈ Ls, ∀ L' ∈ Ls, L = L') (cfg : Config) :
    ∀ (txns : List Txn) (s : Shared E X), (∀ t ∈ txns, TxnOk Ls Bs t) → Inv Ls Bs cfg s →
      Inv Ls Bs cfg (runAll cfg txns s)
  | [], _, _, hs => hs
  | txn :: rest, s, ht, hs => by
    simp only [runAll, List.foldl_cons]
    exact inv_run huniq cfg rest _ (fun t h => ht t (List.mem_cons_of_mem _ h))
      (inv_step huniq cfg txn s (ht txn List.mem_cons_self) hs)

/-- The text of a layout and a usable range of a well-formed boot memory map
share no page when each `ReadExecute` range of the layout lies in a span of
its boot storage. -/
private theorem text_not_usable {L : Layout} {B : Krepi.Spec.Fdt.MemoryPlan} (hB : B.WellFormed)
    (hboot : ∀ j ∈ L.ranges, j.kind = .readExecute →
      ∃ b ∈ B.boot, b.start.toNat ≤ j.range.start.toNat ∧ j.range.endNat ≤ b.endNat)
    {q : Nat} (ht : L.text q = true) {u : Krepi.Spec.Fdt.Span} (hu : u ∈ B.availableRanges)
    (h1 : u.start.toNat ≤ q) (h2 : q < u.endNat) : False := by
  obtain ⟨j, hj, hc⟩ := List.any_eq_true.1 ht
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨hre, hj1⟩, hj2⟩ := hc
  obtain ⟨b, hb, hb1, hb2⟩ := hboot j hj hre
  have hno := (Krepi.Proofs.Fdt.Plan.usableRangesExact B hB).1 u hu |>.2 b
    (List.mem_append_left _ hb)
  simp only [Krepi.Spec.Fdt.Span.touches, Krepi.Spec.Fdt.Span.overlaps, Bool.and_eq_false_iff,
    bne_eq_false_iff_eq, decide_eq_false_iff_not, Nat.not_lt] at hno
  simp only [PhysRange.endNat, Krepi.Spec.Fdt.Span.endNat, PAGE_SIZE] at hj2 hb2 h2 hno ⊢
  rcases hno with (hz | hz) | hz | hz
  · have := congrArg UInt64.toNat hz; simp only [UInt64.toNat_zero] at this; omega
  · have := congrArg UInt64.toNat hz; simp only [UInt64.toNat_zero] at this; omega
  · omega
  · omega

/-- W^X of the two kernel sets from the facts of their leaves. -/
private theorem wx_kernel {Ls : List Layout} {Bs : List Krepi.Spec.Fdt.MemoryPlan}
    {A : Tables .lower KERNEL_TABLES} {D : Tables .upper DIRECT_MAP_TABLES} {a d : UInt64}
    (hlo : LowerOk Ls A a) (hdo : DirectOk Bs D d) (hB : ∀ B ∈ Bs, B.WellFormed)
    (hboot : ∀ L ∈ Ls, ∀ B ∈ Bs, ∀ j ∈ L.ranges, j.kind = .readExecute →
      ∃ b ∈ B.boot, b.start.toNat ≤ j.range.start.toNat ∧ j.range.endNat ≤ b.endNat) :
    WxFree [⟨.lower, _, A, a⟩, ⟨.upper, _, D, d⟩] := by
  rintro q ⟨⟨w1, hw1, v1, l1, hm1, hq1, hwr⟩, ⟨w2, hw2, v2, l2, hm2, hq2, hex⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw1 hw2
  obtain ⟨L, hL, ht⟩ : ∃ L ∈ Ls, L.text q = true := by
    rcases hw2 with rfl | rfl
    · rw [← hq2]; exact (hlo v2 l2 hm2).1 hex
    · rw [(hdo v2 l2 hm2).1] at hex; exact absurd hex (by decide)
  rcases hw1 with rfl | rfl
  · rw [(hlo v1 l1 hm1).2 L hL (hq1 ▸ ht)] at hwr; exact absurd hwr (by decide)
  · obtain ⟨-, B, hBm, u, hu, h1, h2⟩ := hdo v1 l1 hm1
    exact text_not_usable (hB B hBm) (hboot L hL B hBm) ht hu (hq1 ▸ h1) (hq1 ▸ h2)

/-- A set whose leaves are all leaves of a set of a list adds no frame to the
list. -/
private theorem wx_cons {w : SetView} {ks : List SetView}
    (hk : ∃ w' ∈ ks, ∀ v l, w.set.M w.base v l → w'.set.M w'.base v l) (h : WxFree ks) :
    WxFree (w :: ks) := by
  obtain ⟨w', hw', hM⟩ := hk
  have hmf : ∀ pred q, MapsFrame (w :: ks) pred q → MapsFrame ks pred q := by
    rintro pred q ⟨x, hx, v, l, hm, hq, hp⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨w', hw', v, l, hM v l hm, hq, hp⟩
    · exact ⟨x, hx, v, l, hm, hq, hp⟩
  exact fun q ⟨h1, h2⟩ => h q ⟨hmf _ q h1, hmf _ q h2⟩

end Wx

public theorem noWritableExecutable : NoWritableExecutable := by
  refine ⟨fun k => by cases k <;> decide, fun E X cfg txns hP => ?_⟩
  obtain ⟨hL, -, hB, hboot, hfill⟩ := hP
  have huniq : ∀ L ∈ txns.filterMap Txn.layout?, ∀ L' ∈ txns.filterMap Txn.layout?, L = L' := by
    generalize txns.filterMap Txn.layout? = Ls at hL ⊢
    intro L h1 L' h2
    rcases Ls with _ | ⟨x, _ | ⟨y, Ls⟩⟩
    · cases h1
    · rw [List.mem_singleton] at h1 h2; rw [h1, h2]
    · simp at hL
  have htx : ∀ t ∈ txns, TxnOk (txns.filterMap Txn.layout?) (txns.filterMap Txn.memory?) t := by
    intro t ht
    cases t with
    | kernelMap layout => exact List.mem_filterMap.2 ⟨_, ht, rfl⟩
    | directMap memory => exact List.mem_filterMap.2 ⟨_, ht, rfl⟩
    | fill v p k => exact hfill v p k ht
    | _ => trivial
  have hinv := inv_run huniq cfg txns (Shared.initial E X) htx
    ⟨Or.inr rfl, Or.inr rfl, fun _ _ h => absurd h new_M, fun _ _ h => absurd h new_M⟩
  obtain ⟨hl, -, hlo, hdo⟩ := hinv
  refine ⟨wx_kernel hlo hdo hB hboot, fun C base C' plan hz hcl => ?_⟩
  obtain ⟨-, hp, -⟩ := clone_facts hz hcl
  exact wx_cons ⟨_, List.mem_cons_self, fun v l hm => clone_M (setOk_wf hl hp) hz hcl hm⟩
    (wx_kernel hlo hdo hB hboot)

end Krepi.Proofs.PageTables.Kernel
