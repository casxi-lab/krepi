module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.ListLemmas
public import Mathlib.Data.List.Nodup
public import Krepi.Proofs.PageTables.PoolLemmas

/-!
# Page tables: lemmas about the copy of the kernel tables

What the checks of `Tables.cloneKernelFrom` tell about its source, and the
entries of the target after its plan:

- `table_toList_eq`: the entries of a table as a list are its entries by
  index;
- `kidOf`, the table that a valid entry points at, with `walkRoot_ok` (from
  private steps for each level of the walk): a walk of the source that
  succeeds met only table descriptors at levels 1 and 2 and only copyable
  leaves at level 3, and the tables that it reached are the root, then each
  level 2 table followed by its level 3 tables, without duplicates;
- `copyValue`, the descriptor that the copy stores for an entry, with
  `lastAt_copyStores` and `lastAt_flatMap_range`, the last store of the plan
  of the copy into an entry;
- for the target: `copyable_facts` (a copyable leaf is a page descriptor of a
  kind and no table descriptor), `child?_index` (the index that a pointer
  gives), `mem_kids` and `kids_inj` (the tables that the valid entries of a
  table point at, and the entries that point at one of them) and
  `disjoint_of_pairwise`.
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables
open Krepi.Proofs.Fdt (except_bind_ok)

variable {r : Region} {N : Nat}

theorem table_toList_eq (s : Tables r N) (t : Nat) :
    (s.table t).toList = (List.range ENTRIES).map (s.entry t) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [Vector.getElem_toList, List.getElem_map, List.getElem_range, Tables.entry]
    simp [show i < ENTRIES by simpa using h1]

/-- The table that a valid entry of the source points at. -/
def kidOf (src : Tables r N) (sb d : UInt64) : Option Nat :=
  if isValid d then src.child? sb d else none

section Walk

variable (src : Tables r N) (sb : UInt64) (bits : UInt8)

private theorem reach_ok {d : UInt64} {st st' : Visit} {t : Nat} (h : src.reach sb d st = .ok (t, st')) :
    isPlainTableDescriptor d = true ∧ src.child? sb d = some t ∧ t ∉ st.reached ∧
      st' = { st with reached := st.reached ++ [t] } := by
  unfold Tables.reach at h
  obtain ⟨hp, h⟩ := Krepi.Proofs.Fdt.except_jp_ok h
  cases hc : src.child? sb d with
  | none => rw [hc] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some t' =>
    rw [hc] at h
    obtain ⟨hm, h⟩ := Krepi.Proofs.Fdt.except_jp_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simpa using hp, rfl, fun h' => hm (by simpa using h'), rfl⟩

private theorem checkLeaves_ok : ∀ {ds : List UInt64} {u : Unit}, checkLeaves bits ds = .ok u →
    ∀ d ∈ ds, isValid d = true → copyableLeaf bits d = true
  | [], _, _ => by simp
  | d :: rest, u, h => by
    unfold checkLeaves at h
    by_cases hb : (isValid d && !copyableLeaf bits d) = true
    · simp [hb, throw, throwThe, MonadExceptOf.throw] at h
    · simp only [hb, Bool.false_eq_true, ite_false] at h
      intro e he hv
      rcases List.mem_cons.1 he with rfl | he
      · simpa [hv] using hb
      · exact checkLeaves_ok h e he hv

private theorem walkLevel2_ok : ∀ {ds : List UInt64} {st st' : Visit},
    src.walkLevel2 sb bits ds st = .ok st' →
      (∀ d ∈ ds, isValid d = true → isPlainTableDescriptor d = true ∧ ∃ c,
        src.child? sb d = some c ∧
        ∀ e ∈ (src.table c).toList, isValid e = true → copyableLeaf bits e = true) ∧
      st'.reached = st.reached ++ ds.filterMap (kidOf src sb) ∧
      st'.leaves = st.leaves ++ ds.filterMap (kidOf src sb) ∧
      (st.reached.Nodup → st'.reached.Nodup)
  | [], st, st', h => by
    simp only [Tables.walkLevel2, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | d :: rest, st, st', h => by
    unfold Tables.walkLevel2 at h
    by_cases hv : isValid d = true
    · simp only [hv, Bool.not_true, Bool.false_eq_true, ite_false] at h
      obtain ⟨⟨t3, st1⟩, hr, h⟩ := except_bind_ok.1 h
      obtain ⟨u, hcl, h⟩ := except_bind_ok.1 h
      obtain ⟨hp, hc, hn, rfl⟩ := reach_ok src sb hr
      obtain ⟨ih1, ih2, ih3, ih4⟩ := walkLevel2_ok h
      have hk : kidOf src sb d = some t3 := by simp [kidOf, hv, hc]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro e he hve
        rcases List.mem_cons.1 he with rfl | he
        · exact ⟨hp, t3, hc, checkLeaves_ok bits hcl⟩
        · exact ih1 e he hve
      · rw [ih2, List.filterMap_cons, hk]; simp
      · rw [ih3, List.filterMap_cons, hk]; simp
      · intro hnd
        apply ih4
        exact List.nodup_append.2 ⟨hnd, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, fun a ha b hb => by
          rw [List.mem_singleton] at hb; subst hb; exact fun h => hn (h ▸ ha)⟩
    · simp only [hv, Bool.not_false, ite_true] at h
      obtain ⟨ih1, ih2, ih3, ih4⟩ := walkLevel2_ok h
      have hk : kidOf src sb d = none := by simp [kidOf, hv]
      refine ⟨?_, ?_, ?_, ih4⟩
      · intro e he hve
        rcases List.mem_cons.1 he with rfl | he
        · exact absurd hve hv
        · exact ih1 e he hve
      · rw [ih2, List.filterMap_cons, hk]
      · rw [ih3, List.filterMap_cons, hk]

theorem walkRoot_ok : ∀ {ds : List UInt64} {st st' : Visit},
    src.walkRoot sb bits ds st = .ok st' →
      (∀ d ∈ ds, isValid d = true → isPlainTableDescriptor d = true ∧ ∃ c,
        src.child? sb d = some c ∧
        ∀ e ∈ (src.table c).toList, isValid e = true → isPlainTableDescriptor e = true ∧ ∃ c',
          src.child? sb e = some c' ∧
          ∀ f ∈ (src.table c').toList, isValid f = true → copyableLeaf bits f = true) ∧
      st'.reached = st.reached ++ (ds.filterMap (kidOf src sb)).flatMap
        (fun c => c :: (src.table c).toList.filterMap (kidOf src sb)) ∧
      st'.leaves = st.leaves ++ (ds.filterMap (kidOf src sb)).flatMap
        (fun c => (src.table c).toList.filterMap (kidOf src sb)) ∧
      (st.reached.Nodup → st'.reached.Nodup)
  | [], st, st', h => by
    simp only [Tables.walkRoot, pure, Except.pure, Except.ok.injEq] at h
    subst h; simp
  | d :: rest, st, st', h => by
    unfold Tables.walkRoot at h
    by_cases hv : isValid d = true
    · simp only [hv, Bool.not_true, Bool.false_eq_true, ite_false] at h
      obtain ⟨⟨t2, st1⟩, hr, h1⟩ := except_bind_ok.1 h
      obtain ⟨st2, hw2, h2⟩ := except_bind_ok.1 h1
      obtain ⟨hp, hc, hn, rfl⟩ := reach_ok src sb hr
      obtain ⟨j1, j2, j3, j4⟩ := walkLevel2_ok src sb bits hw2
      obtain ⟨ih1, ih2, ih3, ih4⟩ := walkRoot_ok h2
      have hk : kidOf src sb d = some t2 := by simp [kidOf, hv, hc]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro e he hve
        rcases List.mem_cons.1 he with rfl | he
        · exact ⟨hp, t2, hc, j1⟩
        · exact ih1 e he hve
      · rw [ih2, j2, List.filterMap_cons, hk]; simp
      · rw [ih3, j3, List.filterMap_cons, hk]; simp
      · intro hnd
        apply ih4; apply j4
        exact List.nodup_append.2 ⟨hnd, List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, fun a ha b hb => by
          rw [List.mem_singleton] at hb; subst hb; exact fun h => hn (h ▸ ha)⟩
    · simp only [hv, Bool.not_false, ite_true] at h
      obtain ⟨ih1, ih2, ih3, ih4⟩ := walkRoot_ok h
      have hk : kidOf src sb d = none := by simp [kidOf, hv]
      refine ⟨?_, ?_, ?_, ih4⟩
      · intro e he hve
        rcases List.mem_cons.1 he with rfl | he
        · exact absurd hve hv
        · exact ih1 e he hve
      · rw [ih2, List.filterMap_cons, hk]
      · rw [ih3, List.filterMap_cons, hk]

end Walk

/-! ## The plan of the copy -/

/-- The descriptor that the copy stores for a valid entry `d` of the source:
`d` itself in a level 3 table, otherwise the table descriptor of the
target's table of the index that `d` points at. -/
def copyValue (sb base : UInt64) (leaf : Bool) (d : UInt64) : UInt64 :=
  if leaf then d
  else tableDescriptor (tableAddress base (((outputAddress d).toNat - sb.toNat) / PAGE_SIZE))

theorem lastAt_copyStores (t i : Nat) (sb base : UInt64) (leaf : Bool) (t' : Nat) :
    ∀ (l : List UInt64) (i0 : Nat), lastAt t i (copyStores sb base leaf t' l i0) =
      if t' = t ∧ i0 ≤ i then
        (l[i - i0]?).bind fun d => if isValid d then some (copyValue sb base leaf d) else none
      else none
  | [], i0 => by simp [copyStores, lastAt]
  | d :: rest, i0 => by
    have ih := lastAt_copyStores t i sb base leaf t' rest (i0 + 1)
    have hstep : lastAt t i (copyStores sb base leaf t' (d :: rest) i0) =
        (lastAt t i (copyStores sb base leaf t' rest (i0 + 1))).or
          (if isValid d ∧ t' = t ∧ i0 = i then some (copyValue sb base leaf d) else none) := by
      simp only [copyStores]
      by_cases hv : isValid d = true
      · simp only [hv, Bool.not_true, Bool.false_eq_true, ite_false, lastAt, stepAt, true_and]
        rfl
      · simp [hv]
    rw [hstep, ih]
    by_cases ht : t' = t
    · by_cases hlt : i0 < i
      · have h1 : i - i0 = (i - (i0 + 1)) + 1 := by omega
        simp [ht, show i0 + 1 ≤ i by omega, show i0 ≤ i by omega, show i0 ≠ i by omega, h1]
      · by_cases heq : i0 = i
        · subst heq; simp [ht, show ¬ i0 + 1 ≤ i0 by omega]
        · simp [ht, show ¬ i0 + 1 ≤ i by omega, show ¬ i0 ≤ i by omega, heq]
    · simp [ht]

theorem lastAt_flatMap_range (t i : Nat) (f : Nat → Plan)
    (hf : ∀ t', t' ≠ t → lastAt t i (f t') = none) :
    ∀ n, lastAt t i ((List.range n).flatMap f) = if t < n then lastAt t i (f t) else none
  | 0 => by simp [lastAt]
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, lastAt_append, lastAt_flatMap_range t i f hf n]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    by_cases hn : n = t
    · subst hn; simp [Nat.lt_irrefl]
    · rw [hf n hn]
      by_cases htn : t < n
      · simp [htn, show t < n + 1 by omega]
      · simp [htn, show ¬ t < n + 1 by omega]

/-! ## Facts for the target -/

theorem copyable_facts {bits : UInt8} {d : UInt64} (h : copyableLeaf bits d = true) :
    isPlainTableDescriptor d = false ∧ (∃ k, d = descriptor k (outputAddress d)) ∧
      (outputAddress d).toNat < 2 ^ bits.toNat := by
  simp only [copyableLeaf, Bool.and_eq_true, List.any_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨k, -, hk⟩, hb⟩ := h
  refine ⟨?_, ⟨k, hk.symm⟩, hb⟩
  rw [← hk, isPlain_descriptor]

theorem child?_index {s : Tables r N} {base d : UInt64} {c : Nat} (h : s.child? base d = some c) :
    c = ((outputAddress d).toNat - base.toNat) / PAGE_SIZE := by
  simp only [Tables.child?] at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

theorem mem_kids {src : Tables r N} {sb : UInt64} {t c : Nat} :
    c ∈ ((List.range ENTRIES).map (src.entry t)).filterMap (kidOf src sb) ↔
      ∃ i, i < ENTRIES ∧ isValid (src.entry t i) = true ∧ src.child? sb (src.entry t i) = some c := by
  simp only [List.mem_filterMap, List.mem_map, List.mem_range, kidOf]
  constructor
  · rintro ⟨d, ⟨i, hi, rfl⟩, h⟩
    by_cases hv : isValid (src.entry t i) = true
    · exact ⟨i, hi, hv, by simpa [hv] using h⟩
    · simp [hv] at h
  · rintro ⟨i, hi, hv, hc⟩
    exact ⟨_, ⟨i, hi, rfl⟩, by simp [hv, hc]⟩

theorem kids_inj {src : Tables r N} {sb : UInt64} {t : Nat}
    (hn : (((List.range ENTRIES).map (src.entry t)).filterMap (kidOf src sb)).Nodup)
    {i j c : Nat} (hi : i < ENTRIES) (hj : j < ENTRIES)
    (hci : isValid (src.entry t i) = true ∧ src.child? sb (src.entry t i) = some c)
    (hcj : isValid (src.entry t j) = true ∧ src.child? sb (src.entry t j) = some c) : i = j := by
  rw [List.filterMap_map] at hn
  exact filterMap_nodup_inj (c := c) List.nodup_range hn (List.mem_range.2 hi) (List.mem_range.2 hj)
    (by simp [kidOf, hci.1, hci.2]) (by simp [kidOf, hcj.1, hcj.2])

theorem disjoint_of_pairwise {α β : Type} {g : α → List β} {l : List α}
    (h : l.Pairwise (fun a b => (g a).Disjoint (g b))) :
    ∀ {a b}, a ∈ l → b ∈ l → a ≠ b → (g a).Disjoint (g b) := by
  induction l with
  | nil => intro a b ha; simp at ha
  | cons x xs ih =>
    intro a b ha hb hab
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · exact absurd rfl hab
    · exact h.1 b hb'
    · exact List.disjoint_comm.1 (h.1 a ha')
    · exact ih h.2 ha' hb' hab

end Krepi.Proofs.PageTables
