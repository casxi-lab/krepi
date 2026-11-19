module

public import Krepi.Proofs.PageTables.MapPlanLemmas
import Mathlib.Util.CountHeartbeats
import Mathlib.Data.List.Basic

/-!
# Page tables: lemmas about the new tables of a map

What `assignTables` gives the leaves of `kernel_map` and `direct_map`, from
the fold of `Alloc.add` over the leaves in ascending address order: the new
tables are taken one for each key, a 1 GiB slot of a leaf whose root entry is
invalid or a 2 MiB slot of a page without a level 3 table, in the order in
which the leaves first need them, and the table of a key is the record plus
its position in that order.

- the two stages of `Alloc.add`: `stage2`, `stage3`, `add_eq`, `cacheStep`
  (the cached table or the next free index), `stage2_root`, `stage3_new`;
- the invariant of one level, `LevelInv`, and of the fold, `AllocInv`, which
  each leaf keeps (private steps);
- `Matches` (the tables of a placed leaf as its place gives them) and
  `add_placed`;
- `assignTables_spec`: the placed leaves are the leaves, each with the tables
  of its place; the new tables are the indices from the record up to the next
  free index, each the new table of a leaf; two new level 2 tables are equal
  exactly when their 1 GiB slots are, two new level 3 tables exactly when
  their 2 MiB slots are, and no new level 2 table is a new level 3 table.
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables

/-- The level 2 table of one more leaf, as `Alloc.add` takes it. -/
def stage2 (a : Alloc) (l : MapLeaf) : Place → Nat × Bool × Alloc
  | .root =>
    match a.level2 with
    | some (g, t) => if g == l.gibSlot then (t, true, a)
      else (a.next, true, { a with next := a.next + 1, level2 := some (l.gibSlot, a.next) })
    | none => (a.next, true, { a with next := a.next + 1, level2 := some (l.gibSlot, a.next) })
  | .level2 t2 => (t2, false, a)
  | .level3 t2 _ => (t2, false, a)

/-- The level 3 table of one more leaf, as `Alloc.add` takes it. -/
def stage3 (a : Alloc) (l : MapLeaf) (p : Place) : Nat × Bool × Alloc :=
  match l.form, p with
  | .block, _ => (0, false, a)
  | .page, .level3 _ t3 => (t3, false, a)
  | .page, _ =>
    match a.level3 with
    | some (b, t) => if b == l.blockSlot then (t, true, a)
      else (a.next, true, { a with next := a.next + 1, level3 := some (l.blockSlot, a.next) })
    | none => (a.next, true, { a with next := a.next + 1, level3 := some (l.blockSlot, a.next) })

theorem add_eq (a : Alloc) (l : MapLeaf) (p : Place) :
    a.add (l, p) =
      { (stage3 (stage2 a l p).2.2 l p).2.2 with
        placed := ⟨l, (stage2 a l p).1, (stage2 a l p).2.1, (stage3 (stage2 a l p).2.2 l p).1,
          (stage3 (stage2 a l p).2.2 l p).2.1⟩ :: (stage3 (stage2 a l p).2.2 l p).2.2.placed } := by
  simp only [Alloc.add]
  cases p <;> rfl

/-- The table of one slot from the cache of the last new table: the cached
table when the slot is the cached one, else the next free index. -/
def cacheStep (c : Option (Nat × Nat)) (slot next : Nat) : Nat × Option (Nat × Nat) × Nat :=
  match c with
  | some (g, t) => if g == slot then (t, c, next) else (next, some (slot, next), next + 1)
  | none => (next, some (slot, next), next + 1)

theorem stage2_root (a : Alloc) (l : MapLeaf) :
    stage2 a l .root = ((cacheStep a.level2 l.gibSlot a.next).1, true,
      { a with next := (cacheStep a.level2 l.gibSlot a.next).2.2,
               level2 := (cacheStep a.level2 l.gibSlot a.next).2.1 }) := by
  obtain ⟨n, l2, l3, pl⟩ := a
  simp only [stage2, cacheStep]
  cases l2 with
  | none => rfl
  | some gt => obtain ⟨g, t⟩ := gt; simp only; split <;> simp_all

theorem stage3_new (a : Alloc) (l : MapLeaf) (p : Place) (hf : l.form = .page)
    (hp : ∀ t2 t3, p ≠ .level3 t2 t3) :
    stage3 a l p = ((cacheStep a.level3 l.blockSlot a.next).1, true,
      { a with next := (cacheStep a.level3 l.blockSlot a.next).2.2,
               level3 := (cacheStep a.level3 l.blockSlot a.next).2.1 }) := by
  obtain ⟨n, l2, l3, pl⟩ := a
  simp only [stage3, cacheStep, hf]
  cases p with
  | level3 t2 t3 => exact absurd rfl (hp t2 t3)
  | _ =>
    cases l3 with
    | none => rfl
    | some gt => obtain ⟨g, t⟩ := gt; simp only; split <;> simp_all

/-- What the cache and the keys of one level tell about the placed leaves:
the new table of a leaf is the table of its key, the position of the key in
the order in which the tables were taken; the cache holds the latest key; and
each key is that of a leaf. -/
def LevelInv (used : Nat) (keys : List (Nat × Nat)) (tag : Nat) (c : Option (Nat × Nat))
    (isNew : Placed → Prop) (tab slot : Placed → Nat) (P : List Placed) : Prop :=
  (∀ q ∈ P, isNew q → (tag, slot q) ∈ keys ∧ tab q = used + keys.idxOf (tag, slot q)) ∧
  (∀ g t, c = some (g, t) → (tag, g) ∈ keys ∧ t = used + keys.idxOf (tag, g) ∧
    ∀ g', (tag, g') ∈ keys → g' ≤ g) ∧
  (∀ g, (tag, g) ∈ keys → ∃ q ∈ P, isNew q ∧ slot q = g) ∧
  (c = none → ∀ g, (tag, g) ∉ keys)

private theorem levelInv_other {used tag : Nat} {keys : List (Nat × Nat)} {c : Option (Nat × Nat)}
    {isNew : Placed → Prop} {tab slot : Placed → Nat} {P : List Placed} {k : Nat × Nat}
    (h : LevelInv used keys tag c isNew tab slot P) (hk : k.1 ≠ tag) :
    LevelInv used (keys ++ [k]) tag c isNew tab slot P := by
  have hm : ∀ g, (tag, g) ∈ keys ++ [k] ↔ (tag, g) ∈ keys := by
    intro g; simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (h | h)
      · exact h
      · exact absurd (congrArg Prod.fst h).symm hk
    · exact Or.inl
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun q hq hn => ?_, fun g t hc => ?_, fun g hg => h3 g ((hm g).1 hg), fun hc g => ?_⟩
  · obtain ⟨a, b⟩ := h1 q hq hn
    exact ⟨(hm _).2 a, by rw [List.idxOf_append_of_mem a]; exact b⟩
  · obtain ⟨a, b, d⟩ := h2 g t hc
    exact ⟨(hm _).2 a, by rw [List.idxOf_append_of_mem a]; exact b, fun g' hg' => d g' ((hm g').1 hg')⟩
  · rw [hm]; exact h4 hc g

private theorem levelInv_old {used tag : Nat} {keys : List (Nat × Nat)} {c : Option (Nat × Nat)}
    {isNew : Placed → Prop} {tab slot : Placed → Nat} {P : List Placed} {q : Placed}
    (h : LevelInv used keys tag c isNew tab slot P) (hq : ¬ isNew q) :
    LevelInv used keys tag c isNew tab slot (q :: P) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun q' hq' hn => ?_, h2, fun g hg => ?_, h4⟩
  · rcases List.mem_cons.1 hq' with rfl | hq'
    · exact absurd hn hq
    · exact h1 q' hq' hn
  · obtain ⟨q', hq', a, b⟩ := h3 g hg
    exact ⟨q', List.mem_cons_of_mem _ hq', a, b⟩

/-- One step of a level: the leaf takes the table of its slot, the cached one
or the next free index, and the keys grow by its key when it is new. -/
private theorem levelInv_step {used tag : Nat} {keys : List (Nat × Nat)} {c : Option (Nat × Nat)}
    {isNew : Placed → Prop} {tab slot : Placed → Nat} {P : List Placed} {q : Placed} {next : Nat}
    (h : LevelInv used keys tag c isNew tab slot P) (hnext : next = used + keys.length)
    (hord : ∀ g, (tag, g) ∈ keys → g ≤ slot q) (hq : isNew q)
    (ht : tab q = (cacheStep c (slot q) next).1) :
    ∃ keys', (keys' = keys ∨ ((tag, slot q) ∉ keys ∧ keys' = keys ++ [(tag, slot q)])) ∧
      (cacheStep c (slot q) next).2.2 = used + keys'.length ∧
      (keys' = keys → (cacheStep c (slot q) next).2.2 = next) ∧
      (keys' ≠ keys → tab q = next) ∧
      LevelInv used keys' tag (cacheStep c (slot q) next).2.1 isNew tab slot (q :: P) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  by_cases hin : (tag, slot q) ∈ keys
  · -- the slot already has its table: the cache holds it
    obtain ⟨g, t, hc, hg⟩ : ∃ g t, c = some (g, t) ∧ g = slot q := by
      cases hc : c with
      | none => exact absurd hin (h4 hc _)
      | some gt =>
        obtain ⟨g, t⟩ := gt
        obtain ⟨q', -, -, hq'⟩ := h3 _ hin
        have := (h2 g t hc).2.2 (slot q) hin
        have := hord g (h2 g t hc).1
        exact ⟨g, t, rfl, by omega⟩
    subst hg
    have hcs : cacheStep c (slot q) next = (t, c, next) := by simp [cacheStep, hc]
    rw [hcs] at ht ⊢
    obtain ⟨a, b, d⟩ := h2 _ t hc
    refine ⟨keys, Or.inl rfl, hnext, fun _ => rfl, fun h => absurd rfl h, ?_, ?_, ?_, ?_⟩
    · intro q' hq' hn
      rcases List.mem_cons.1 hq' with rfl | hq'
      · exact ⟨hin, by rw [ht]; exact b⟩
      · exact h1 q' hq' hn
    · exact h2
    · intro g' hg'
      obtain ⟨q', hq', a', b'⟩ := h3 g' hg'
      exact ⟨q', List.mem_cons_of_mem _ hq', a', b'⟩
    · exact h4
  · have hcs : cacheStep c (slot q) next = (next, some (slot q, next), next + 1) := by
      cases hc : c with
      | none => rfl
      | some gt =>
        obtain ⟨g, t⟩ := gt
        have hg : g ≠ slot q := fun e => hin (e ▸ (h2 g t hc).1)
        simp [cacheStep, hg]
    rw [hcs] at ht ⊢
    have hmem : ∀ k, k ∈ keys ++ [(tag, slot q)] ↔ k ∈ keys ∨ k = (tag, slot q) := by
      intro k; simp
    have hidx : (keys ++ [(tag, slot q)]).idxOf (tag, slot q) = keys.length := by
      rw [List.idxOf_append_of_notMem hin]; simp
    refine ⟨keys ++ [(tag, slot q)], Or.inr ⟨hin, rfl⟩, by simp [hnext]; omega,
      fun h => absurd (congrArg List.length h) (by simp), fun _ => ht, ?_, ?_, ?_, ?_⟩
    · intro q' hq' hn
      rcases List.mem_cons.1 hq' with rfl | hq'
      · exact ⟨(hmem _).2 (Or.inr rfl), by rw [ht, hidx, hnext]⟩
      · obtain ⟨a, b⟩ := h1 q' hq' hn
        exact ⟨(hmem _).2 (Or.inl a), by rw [List.idxOf_append_of_mem a]; exact b⟩
    · intro g t hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      refine ⟨(hmem _).2 (Or.inr rfl), by rw [hidx, hnext], fun g' hg' => ?_⟩
      rcases (hmem _).1 hg' with hg' | hg'
      · exact hord g' hg'
      · simp only [Prod.mk.injEq] at hg'; omega
    · intro g hg
      rcases (hmem _).1 hg with hg | hg
      · obtain ⟨q', hq', a', b'⟩ := h3 g hg
        exact ⟨q', List.mem_cons_of_mem _ hq', a', b'⟩
      · simp only [Prod.mk.injEq] at hg
        exact ⟨q, List.mem_cons_self, hq, hg.2.symm⟩
    · intro hc; cases hc

/-- The invariant of the fold of `Alloc.add` from the record `used`, with the
keys of the new tables in the order in which they were taken. -/
structure AllocInv (used : Nat) (keys : List (Nat × Nat)) (a : Alloc) : Prop where
  next : a.next = used + keys.length
  tags : ∀ k ∈ keys, k.1 = 2 ∨ k.1 = 3
  inv2 : LevelInv used keys 2 a.level2 (fun q => q.new2 = true) (·.t2) (·.leaf.gibSlot) a.placed
  inv3 : LevelInv used keys 3 a.level3 (fun q => q.leaf.form = .page ∧ q.new3 = true) (·.t3)
    (·.leaf.blockSlot) a.placed
  cover : ∀ c, used ≤ c → c < a.next → ∃ q ∈ a.placed, NewTable q c

private theorem stage2_level3 (a : Alloc) (l : MapLeaf) (p : Place) : (stage2 a l p).2.2.level3 = a.level3 := by
  cases p with
  | root => rw [stage2_root]
  | _ => rfl

private theorem stage2_placed (a : Alloc) (l : MapLeaf) (p : Place) : (stage2 a l p).2.2.placed = a.placed := by
  cases p with
  | root => rw [stage2_root]
  | _ => rfl

private theorem stage3_placed (a : Alloc) (l : MapLeaf) (p : Place) : (stage3 a l p).2.2.placed = a.placed := by
  simp only [stage3]; split
  · rfl
  · rfl
  · split
    · split <;> rfl
    · rfl

private theorem allocInv_add {used : Nat} {keys : List (Nat × Nat)} {a : Alloc} (h : AllocInv used keys a)
    (l : MapLeaf) (p : Place) (hord : ∀ q ∈ a.placed, q.leaf.va.toNat ≤ l.va.toNat) :
    ∃ keys', AllocInv used keys' (a.add (l, p)) := by
  rw [add_eq]
  generalize hq : (⟨l, (stage2 a l p).1, (stage2 a l p).2.1, (stage3 (stage2 a l p).2.2 l p).1,
    (stage3 (stage2 a l p).2.2 l p).2.1⟩ : Placed) = q
  have hql : q.leaf = l := by rw [← hq]
  have hqt2 : q.t2 = (stage2 a l p).1 := by rw [← hq]
  have hqn2 : q.new2 = (stage2 a l p).2.1 := by rw [← hq]
  have hqt3 : q.t3 = (stage3 (stage2 a l p).2.2 l p).1 := by rw [← hq]
  have hqn3 : q.new3 = (stage3 (stage2 a l p).2.2 l p).2.1 := by rw [← hq]
  generalize ha1 : (stage2 a l p).2.2 = a1 at hqt3 hqn3 ⊢
  have ha1l3 : a1.level3 = a.level3 := by rw [← ha1, stage2_level3]
  -- stage 2
  obtain ⟨keys1, hk1, hn1, hfresh1, hinv2, hinv3, hcov1⟩ : ∃ keys1,
      (keys1 = keys ∨ keys1 = keys ++ [(2, l.gibSlot)]) ∧ a1.next = used + keys1.length ∧
      (a1.next ≠ a.next → q.new2 = true ∧ q.t2 = a.next ∧ a1.next = a.next + 1) ∧
      LevelInv used keys1 2 a1.level2 (fun q => q.new2 = true) (·.t2) (·.leaf.gibSlot) (q :: a.placed) ∧
      LevelInv used keys1 3 a1.level3 (fun q => q.leaf.form = .page ∧ q.new3 = true) (·.t3)
        (·.leaf.blockSlot) a.placed ∧
      (a1.next = a.next ∨ a1.next = a.next + 1) := by
    cases p with
    | root =>
      rw [stage2_root] at ha1 hqt2 hqn2
      subst ha1
      have hord2 : ∀ g, (2, g) ∈ keys → g ≤ (fun q : Placed => q.leaf.gibSlot) q := by
        intro g hg
        obtain ⟨q', hq', -, rfl⟩ := h.inv2.2.2.1 g hg
        simp only [hql, MapLeaf.gibSlot]; exact Nat.div_le_div_right (hord q' hq')
      have hgs : (fun q : Placed => q.leaf.gibSlot) q = l.gibSlot := by simp [hql]
      obtain ⟨keys', hk, hn, hsame, hfresh, hinv⟩ :=
        levelInv_step h.inv2 h.next hord2 hqn2 (by simp only [hgs]; exact hqt2)
      simp only [hql] at hk hn hsame hfresh hinv
      refine ⟨keys', ?_, hn, ?_, hinv, ?_, ?_⟩
      · rcases hk with hk | ⟨-, hk⟩
        · exact Or.inl hk
        · exact Or.inr hk
      · intro hne
        refine ⟨hqn2, ?_, ?_⟩
        · apply hfresh; intro e; exact hne (hsame e)
        · rcases hk with rfl | ⟨-, rfl⟩
          · exact absurd (hsame rfl) hne
          · rw [hn, h.next]; simp; omega
      · rcases hk with rfl | ⟨-, rfl⟩
        · exact h.inv3
        · exact levelInv_other h.inv3 (by simp)
      · rcases hk with rfl | ⟨-, rfl⟩
        · exact Or.inl (hsame rfl)
        · right; rw [hn, h.next]; simp; omega
    | level2 t2 =>
      simp only [stage2] at ha1 hqn2 hqt2; subst ha1
      exact ⟨keys, Or.inl rfl, h.next, fun h => absurd rfl h,
        levelInv_old h.inv2 (by simp [hqn2]), h.inv3, Or.inl rfl⟩
    | level3 t2 t3 =>
      simp only [stage2] at ha1 hqn2 hqt2; subst ha1
      exact ⟨keys, Or.inl rfl, h.next, fun h => absurd rfl h,
        levelInv_old h.inv2 (by simp [hqn2]), h.inv3, Or.inl rfl⟩
  have htags1 : ∀ k ∈ keys1, k.1 = 2 ∨ k.1 = 3 := by
    rcases hk1 with rfl | rfl
    · exact h.tags
    · intro k hk; rcases List.mem_append.1 hk with hk | hk
      · exact h.tags k hk
      · simp at hk; simp [hk]
  have hcov : ∀ c, used ≤ c → c < a1.next → ∃ q' ∈ q :: a.placed, NewTable q' c := by
    intro c h1 h2
    by_cases hc : c < a.next
    · obtain ⟨q', hq', hn⟩ := h.cover c h1 hc
      exact ⟨q', List.mem_cons_of_mem _ hq', hn⟩
    · have hne : a1.next ≠ a.next := by omega
      obtain ⟨hn2, ht2, hn⟩ := hfresh1 hne
      exact ⟨q, List.mem_cons_self, Or.inl ⟨hn2, by omega⟩⟩
  have hpl : a1.placed = a.placed := by rw [← ha1, stage2_placed]
  rw [← hpl] at hinv2 hinv3 hcov
  cases hf : l.form with
  | block =>
    have h3 : stage3 a1 l p = (0, false, a1) := by simp only [stage3, hf]
    rw [h3] at hqt3 hqn3 ⊢
    refine ⟨keys1, ⟨hn1, htags1, hinv2, ?_, ?_⟩⟩
    · exact levelInv_old hinv3 (by simp [hql, hf])
    · exact hcov
  | page =>
    by_cases hp3 : ∃ t2 t3, p = .level3 t2 t3
    · obtain ⟨t2, t3, rfl⟩ := hp3
      have h3 : stage3 a1 l (.level3 t2 t3) = (t3, false, a1) := by simp only [stage3, hf]
      rw [h3] at hqt3 hqn3 ⊢
      refine ⟨keys1, ⟨hn1, htags1, hinv2, ?_, ?_⟩⟩
      · exact levelInv_old hinv3 (by simp [hqn3])
      · exact hcov
    · have hp3' : ∀ t2 t3, p ≠ .level3 t2 t3 := fun t2 t3 e => hp3 ⟨t2, t3, e⟩
      rw [stage3_new a1 l p hf hp3'] at hqt3 hqn3 ⊢
      have hord3 : ∀ g, (3, g) ∈ keys1 → g ≤ (fun q : Placed => q.leaf.blockSlot) q := by
        intro g hg
        obtain ⟨q', hq', -, rfl⟩ := hinv3.2.2.1 g hg
        simp only [hql, MapLeaf.blockSlot]; exact Nat.div_le_div_right (hord q' (hpl ▸ hq'))
      obtain ⟨keys', hk, hn, hsame, hfresh, hinv⟩ :=
        levelInv_step hinv3 hn1 hord3 (q := q) ⟨by rw [hql, hf], hqn3⟩
          (by simp only [hql]; exact hqt3)
      simp only [hql] at hk hn hsame hfresh hinv
      refine ⟨keys', ⟨hn, ?_, ?_, ?_, ?_⟩⟩
      · rcases hk with rfl | ⟨-, rfl⟩
        · exact htags1
        · intro k hk; rcases List.mem_append.1 hk with hk | hk
          · exact htags1 k hk
          · simp at hk; simp [hk]
      · rcases hk with rfl | ⟨-, rfl⟩
        · exact hinv2
        · exact levelInv_other hinv2 (by simp)
      · exact hinv
      · intro c h1 h2
        by_cases hc : c < a1.next
        · exact hcov c h1 hc
        · rcases hk with rfl | ⟨-, rfl⟩
          · exact absurd (hsame rfl ▸ h2) hc
          · have ht := hfresh (fun e => by simpa using congrArg List.length e)
            have : c = a1.next := by rw [hn, hn1] at h2; simp at h2; omega
            exact ⟨q, List.mem_cons_self, Or.inr ⟨by rw [hql, hf], hqn3, by rw [this, ht]⟩⟩

/-- The tables of a placed leaf as its place gives them. -/
def Matches (q : Placed) : Place → Prop
  | .root => q.new2 = true ∧ (q.leaf.form = .page → q.new3 = true)
  | .level2 t2 => q.new2 = false ∧ q.t2 = t2 ∧ (q.leaf.form = .page → q.new3 = true)
  | .level3 t2 t3 => q.new2 = false ∧ q.t2 = t2 ∧ (q.leaf.form = .page → q.new3 = false ∧ q.t3 = t3)

theorem add_placed (a : Alloc) (l : MapLeaf) (p : Place) :
    ∃ q, (a.add (l, p)).placed = q :: a.placed ∧ q.leaf = l ∧ Matches q p := by
  rw [add_eq]
  refine ⟨⟨l, (stage2 a l p).1, (stage2 a l p).2.1, (stage3 (stage2 a l p).2.2 l p).1,
    (stage3 (stage2 a l p).2.2 l p).2.1⟩, by simp only [stage3_placed, stage2_placed], rfl, ?_⟩
  cases p with
  | root =>
    simp only [Matches, stage2_root, true_and]
    intro hf; rw [stage3_new _ _ _ hf (fun _ _ h => by cases h)]
  | level2 t2 =>
    simp only [Matches, stage2, true_and]
    intro hf; rw [stage3_new _ _ _ hf (fun _ _ h => by cases h)]
  | level3 t2 t3 =>
    simp only [Matches, stage2, true_and]
    cases hf : l.form <;> simp [stage3, hf]

private theorem foldl_placed (L : List (MapLeaf × Place)) : ∀ (a : Alloc),
    (L.foldl Alloc.add a).placed.map (·.leaf) = (L.map Prod.fst).reverse ++ a.placed.map (·.leaf) ∧
    ∀ q ∈ (L.foldl Alloc.add a).placed, q ∈ a.placed ∨ ∃ p, (q.leaf, p) ∈ L ∧ Matches q p := by
  induction L with
  | nil => intro a; simp
  | cons x rest ih =>
    intro a
    obtain ⟨l, p⟩ := x
    obtain ⟨q, hq, hql, hm⟩ := add_placed a l p
    obtain ⟨h1, h2⟩ := ih (a.add (l, p))
    simp only [List.foldl_cons]
    refine ⟨by rw [h1, hq]; simp [hql], fun q' hq' => ?_⟩
    rcases h2 q' hq' with h | ⟨p', hp', hm'⟩
    · rw [hq] at h
      rcases List.mem_cons.1 h with rfl | h
      · exact Or.inr ⟨p, by rw [hql]; exact List.mem_cons_self, hm⟩
      · exact Or.inl h
    · exact Or.inr ⟨p', List.mem_cons_of_mem _ hp', hm'⟩

private theorem allocInv_foldl (used : Nat) : ∀ (L : List (MapLeaf × Place)) (keys : List (Nat × Nat))
    (a : Alloc), AllocInv used keys a → (∀ lp ∈ L, ∀ q ∈ a.placed, q.leaf.va.toNat ≤ lp.1.va.toNat) →
    (L.map Prod.fst).Pairwise (fun x y => x.va.toNat ≤ y.va.toNat) →
    ∃ keys', AllocInv used keys' (L.foldl Alloc.add a)
  | [], keys, a, h, _, _ => ⟨keys, h⟩
  | (l, p) :: rest, keys, a, h, hord, hpw => by
    rw [List.map_cons, List.pairwise_cons] at hpw
    obtain ⟨keys1, h1⟩ := allocInv_add h l p (hord (l, p) List.mem_cons_self)
    obtain ⟨q, hq, hql, -⟩ := add_placed a l p
    refine allocInv_foldl used rest keys1 _ h1 (fun lp hlp q' hq' => ?_) hpw.2
    rw [hq] at hq'
    rcases List.mem_cons.1 hq' with rfl | hq'
    · rw [hql]; exact hpw.1 _ (List.mem_map.2 ⟨lp, hlp, rfl⟩)
    · exact hord lp (List.mem_cons_of_mem _ hlp) q' hq'

/-- What `assignTables` gives: the new tables of the placed leaves are the
indices from `used` up to `next`, one for each 1 GiB slot of a leaf whose root
entry is invalid and one for each 2 MiB slot of a page without a level 3
table, the level 2 tables apart from the level 3 tables. -/
theorem assignTables_spec (used : Nat) (L : List (MapLeaf × Place))
    (hpw : (L.map Prod.fst).Pairwise (fun x y => x.va.toNat ≤ y.va.toNat)) :
    let r := assignTables used L
    r.2.map (·.leaf) = L.map Prod.fst ∧ (∀ q ∈ r.2, ∃ p, (q.leaf, p) ∈ L ∧ Matches q p) ∧
    used ≤ r.1 ∧ (∀ q ∈ r.2, ∀ c, NewTable q c → used ≤ c ∧ c < r.1) ∧
    (∀ c, used ≤ c → c < r.1 → ∃ q ∈ r.2, NewTable q c) ∧
    (∀ q ∈ r.2, ∀ q' ∈ r.2, q.new2 = true → q'.new2 = true →
      (q.t2 = q'.t2 ↔ q.leaf.gibSlot = q'.leaf.gibSlot)) ∧
    (∀ q ∈ r.2, ∀ q' ∈ r.2, q.leaf.form = .page → q.new3 = true → q'.leaf.form = .page →
      q'.new3 = true → (q.t3 = q'.t3 ↔ q.leaf.blockSlot = q'.leaf.blockSlot)) ∧
    (∀ q ∈ r.2, ∀ q' ∈ r.2, q.new2 = true → q'.leaf.form = .page → q'.new3 = true → q.t2 ≠ q'.t3) := by
  intro r
  have h0 : AllocInv used [] ⟨used, none, none, []⟩ :=
    ⟨rfl, by simp, ⟨by simp, by simp, by simp, by simp⟩, ⟨by simp, by simp, by simp, by simp⟩,
      fun c h1 h2 => absurd h2 (by simp; omega)⟩
  obtain ⟨keys, h⟩ := allocInv_foldl used L [] _ h0 (by simp) hpw
  obtain ⟨hpl, hm⟩ := foldl_placed L ⟨used, none, none, []⟩
  have hr1 : r.1 = (L.foldl Alloc.add ⟨used, none, none, []⟩).next := rfl
  have hr2 : ∀ q, q ∈ r.2 ↔ q ∈ (L.foldl Alloc.add ⟨used, none, none, []⟩).placed := by
    intro q; simp [r, assignTables]
  have ht2 := h.inv2.1
  have ht3 := h.inv3.1
  have hlt : ∀ k ∈ keys, used + keys.idxOf k < r.1 := by
    intro k hk; rw [hr1, h.next]; have := List.idxOf_lt_length_of_mem hk; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [r, assignTables, List.map_reverse, hpl]; simp
  · intro q hq
    rcases hm q ((hr2 q).1 hq) with h | h
    · simp at h
    · exact h
  · rw [hr1, h.next]; omega
  · intro q hq c hc
    rw [hr2] at hq
    rcases hc with ⟨hn, rfl⟩ | ⟨hp, hn, rfl⟩
    · obtain ⟨a, b⟩ := ht2 q hq hn; simp only at a b; rw [b]; exact ⟨by omega, hlt _ a⟩
    · obtain ⟨a, b⟩ := ht3 q hq ⟨hp, hn⟩; simp only at a b; rw [b]; exact ⟨by omega, hlt _ a⟩
  · intro c h1 h2
    obtain ⟨q, hq, hn⟩ := h.cover c h1 h2
    exact ⟨q, (hr2 q).2 hq, hn⟩
  · intro q hq q' hq' hn hn'
    rw [hr2] at hq hq'
    obtain ⟨a, b⟩ := ht2 q hq hn
    obtain ⟨a', b'⟩ := ht2 q' hq' hn'
    simp only at a b a' b'
    rw [b, b', Nat.add_left_cancel_iff, List.idxOf_inj a]; simp
  · intro q hq q' hq' hp hn hp' hn'
    rw [hr2] at hq hq'
    obtain ⟨a, b⟩ := ht3 q hq ⟨hp, hn⟩
    obtain ⟨a', b'⟩ := ht3 q' hq' ⟨hp', hn'⟩
    simp only at a b a' b'
    rw [b, b', Nat.add_left_cancel_iff, List.idxOf_inj a]; simp
  · intro q hq q' hq' hn hp' hn' he
    rw [hr2] at hq hq'
    obtain ⟨a, b⟩ := ht2 q hq hn
    obtain ⟨a', b'⟩ := ht3 q' hq' ⟨hp', hn'⟩
    simp only at a b a' b'
    rw [b, b', Nat.add_left_cancel_iff, List.idxOf_inj a] at he
    simp at he

end Krepi.Proofs.PageTables
