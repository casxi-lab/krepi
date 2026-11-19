module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.BitLemmas

/-!
# Page tables: lemmas about pools, plans and table pointers

Lemmas about the pool of a table set and the execution of a write plan on
it, for every proof that reads a pool after a plan:

- `ite_of_pos` and `ite_of_neg`, the branches of an `if`;
- entries: `entry_eq_get` (`Tables.entry` is `Pool.get`), `zero_get`,
  `get_of_ge`, `get_of_ge_entries`, `pool_ext` (two pools with the same
  entries are equal);
- one step: `get_store` and `get_zeroTable`, the entries after a `Store`
  and a `Zero`;
- plans: `stepAt` and `lastAt`, the value that a step and the last step of a
  plan that writes an entry give it; `get_exec` (an entry after a plan is
  the value of the last step that writes it, or the entry before), with
  `exec_cons`, `exec_append`, `lastAt_append` and `lastAt_zeros`;
- pools that the contract admits: `pool_ok_facts`;
- table pointers: `child?_some` (a pointer reaches a table in use),
  `child?_mono` (it keeps its table when the record grows),
  `tableAddress_toNat`, `outputAddress_tableAt` and `child?_tableAt` (the
  table descriptor of a table in use points at it).
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables

variable {r : Region} {N : Nat}

theorem ite_of_neg {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

theorem ite_of_pos {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem zero_get (i : Nat) (h : i < ENTRIES) : Table.zero[i] = 0 := by
  simp [Table.zero]

theorem entry_eq_get (s : Tables r N) (t i : Nat) : s.entry t i = s.pool.get t i := by
  unfold Tables.entry Tables.table Pool.get
  by_cases ht : t < N <;> by_cases hi : i < ENTRIES <;> simp [ht, hi, Table.zero]

theorem get_of_ge (p : Pool N) {t : Nat} (i : Nat) (h : N ≤ t) : p.get t i = 0 := by
  simp [Pool.get, show ¬ t < N by omega]

theorem get_of_ge_entries (p : Pool N) (t : Nat) {i : Nat} (h : ENTRIES ≤ i) : p.get t i = 0 := by
  simp [Pool.get, show ¬ i < ENTRIES by omega]

theorem get_store (p : Pool N) (t i : Nat) (d : UInt64) (t' i' : Nat) :
    (p.store t i d).get t' i' =
      if t' = t ∧ i' = i ∧ t < N ∧ i < ENTRIES then d else p.get t' i' := by
  unfold Pool.store
  by_cases ht : t < N
  · by_cases hi : i < ENTRIES
    · simp only [ht, hi, dite_true, Pool.get]
      by_cases ht' : t' < N <;> by_cases hi' : i' < ENTRIES <;>
        simp [ht', hi', Vector.getElem_set] <;> grind
    · simp [ht, hi]
  · simp [ht]

theorem get_zeroTable (p : Pool N) (t t' i' : Nat) :
    (p.zeroTable t).get t' i' = if t' = t then 0 else p.get t' i' := by
  unfold Pool.zeroTable Pool.get
  by_cases ht : t < N
  · simp only [ht, dite_true]
    by_cases ht' : t' < N
    · by_cases hi' : i' < ENTRIES
      · by_cases he : t' = t
        · subst he; simp [ht', hi', Table.zero]
        · simp [ht', hi', he, Ne.symm he]
      · simp [ht', hi']
    · simp [ht']
  · by_cases he : t' = t
    · subst he; simp [ht]
    · simp [ht, he]

theorem pool_ext {p q : Pool N} (h : ∀ t i, t < N → i < ENTRIES → p.get t i = q.get t i) : p = q := by
  apply Vector.ext; intro t ht
  apply Vector.ext; intro i hi
  have := h t i ht hi
  simpa [Pool.get, ht, hi] using this

/-! ## Plans -/

def stepAt (t i : Nat) : Step → Option UInt64
  | .zero t' => if t' = t then some 0 else none
  | .store t' i' d => if t' = t ∧ i' = i then some d else none
  | _ => none

def lastAt (t i : Nat) : Plan → Option UInt64
  | [] => none
  | step :: rest => (lastAt t i rest).or (stepAt t i step)

theorem exec_nil (p : Pool N) : Plan.exec [] p = p := rfl
theorem exec_cons (step : Step) (rest : Plan) (p : Pool N) :
    Plan.exec (step :: rest) p = Plan.exec rest (step.exec p) := rfl
theorem exec_append (a b : Plan) (p : Pool N) : Plan.exec (a ++ b) p = Plan.exec b (Plan.exec a p) := by
  simp [Plan.exec, List.foldl_append]

theorem get_step (step : Step) (p : Pool N) {t i : Nat} (ht : t < N) (hi : i < ENTRIES) :
    (step.exec p).get t i = (stepAt t i step).getD (p.get t i) := by
  cases step with
  | zero t' => simp only [Step.exec, get_zeroTable, stepAt]; by_cases h : t = t' <;> simp [h, eq_comm]
  | store t' i' d =>
    simp only [Step.exec, get_store, stepAt]
    by_cases h : t = t' ∧ i = i'
    · obtain ⟨rfl, rfl⟩ := h; simp [ht, hi]
    · have : ¬ (t' = t ∧ i' = i) := fun ⟨a, b⟩ => h ⟨a.symm, b.symm⟩
      simp only [this, ite_false, Option.getD_none]
      simp only [show ¬ (t = t' ∧ i = i' ∧ t' < N ∧ i' < ENTRIES) from fun ⟨a, b, _⟩ => h ⟨a, b⟩, ite_false]
  | fence => rfl
  | sync => rfl
  | invalidate v => rfl

theorem get_exec (plan : Plan) (p : Pool N) {t i : Nat} (ht : t < N) (hi : i < ENTRIES) :
    (plan.exec p).get t i = (lastAt t i plan).getD (p.get t i) := by
  induction plan generalizing p with
  | nil => rfl
  | cons step rest ih =>
    rw [exec_cons, ih, get_step _ _ ht hi, lastAt]
    cases lastAt t i rest <;> cases stepAt t i step <;> rfl

theorem lastAt_append (t i : Nat) (a b : Plan) : lastAt t i (a ++ b) = (lastAt t i b).or (lastAt t i a) := by
  induction a with
  | nil => simp [lastAt]
  | cons step rest ih => simp [lastAt, ih, Option.or_assoc]

theorem lastAt_zeros (t i : Nat) (l : List Nat) :
    lastAt t i (l.map Step.zero) = if t ∈ l then some 0 else none := by
  induction l with
  | nil => simp [lastAt]
  | cons a rest ih =>
    simp only [List.map_cons, lastAt, ih, stepAt, List.mem_cons]
    by_cases h : t ∈ rest
    · simp [h]
    · by_cases ha : a = t
      · subst ha; simp [h]
      · simp [h, ha, Ne.symm ha]

theorem pool_ok_facts {N : Nat} {base : UInt64} {bits : UInt8} (h : PoolOk N base bits) :
    base.toNat % PAGE_SIZE = 0 ∧ 0 < N ∧ base.toNat + PAGE_SIZE * N ≤ 2 ^ bits.toNat ∧
      2 ^ bits.toNat ≤ 2 ^ 48 := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [widthOk, MIN_BITS, MAX_BITS, Bool.and_eq_true] at h2
  have h2' : bits.toNat ≤ 48 := of_decide_eq_true h2.2
  simp only [poolFits, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h3
  exact ⟨h1, Nat.pos_of_ne_zero h3.1, h3.2, Nat.pow_le_pow_right (by decide) h2'⟩

theorem child?_some {s : Tables r N} {base d : UInt64} {c : Nat} (h : s.child? base d = some c) :
    c < s.used ∧ c < N := by
  simp only [Tables.child?] at h
  split at h
  · rename_i hc; simp only [Option.some.injEq] at h; subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc; omega
  · simp at h

theorem child?_mono {s : Tables r N} {base d : UInt64} {c u : Nat} (hu : s.used ≤ u)
    (h : s.child? base d = some c) : ({ s with used := u } : Tables r N).child? base d = some c := by
  simp only [Tables.child?] at h ⊢
  split at h
  · rename_i hc; simp only [Option.some.injEq] at h; subst h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    split
    · rfl
    · rename_i hn; exact absurd ⟨by omega, by omega⟩ hn
  · simp at h

theorem tableAddress_toNat {base : UInt64} {c : Nat} (h : base.toNat + PAGE_SIZE * c < 2 ^ 64) :
    (tableAddress base c).toNat = base.toNat + PAGE_SIZE * c := by
  simp only [tableAddress, UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h

theorem outputAddress_tableAt {base : UInt64} {bits : UInt8} (hp : PoolOk N base bits) {c : Nat}
    (hc : c < N) : (outputAddress (tableAt base c)).toNat = base.toNat + PAGE_SIZE * c := by
  obtain ⟨h1, -, h3, h4⟩ := pool_ok_facts hp
  have hlt : base.toNat + PAGE_SIZE * c < 2 ^ 48 := by
    have : PAGE_SIZE * c < PAGE_SIZE * N := Nat.mul_lt_mul_of_pos_left hc (by decide)
    omega
  have hta := tableAddress_toNat (base := base) (c := c) (by omega)
  rw [tableAt, outputAddress_tableDescriptor, outputAddress_of_aligned]
  · exact hta
  · rw [hta]; simp only [PAGE_SIZE] at h1 ⊢; omega
  · rw [hta]; exact hlt

theorem child?_tableAt {s : Tables r N} {base : UInt64} {bits : UInt8} (hp : PoolOk N base bits)
    {c : Nat} (hc : c < s.used) (hcN : c < N) : s.child? base (tableAt base c) = some c := by
  simp only [Tables.child?]
  rw [outputAddress_tableAt hp hcN]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have : (base.toNat + PAGE_SIZE * c - base.toNat) / PAGE_SIZE = c := by
    simp only [PAGE_SIZE]; omega
  rw [this]
  split
  · rfl
  · rename_i hn; exact absurd ⟨by omega, by omega⟩ hn

end Krepi.Proofs.PageTables
