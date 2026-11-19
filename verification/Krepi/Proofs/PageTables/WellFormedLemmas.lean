module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.PoolLemmas

/-!
# Page tables: lemmas about well-formed table sets

What `Tables.WellFormed` tells about the entries of a set, and the elementary
changes of a set that keep it well-formed, from which the proofs of the write
entries are put together:

- the tables of a well-formed set: `pointsAt_lt`, `wf_level2_ne_zero`,
  `wf_level3_ne_zero`, `wf_not_level2_level3` (no table is at both levels),
  `wf_level2_lt`, `wf_level3_lt`, `wf_entry_free` (an entry of a table not
  in use is 0) and `wf_plain_child` (every table descriptor in the pool points
  at a table in use);
- zero tables: `table_eq_zero`, `entry_of_table_zero`;
- the set of a zero pool with the root alone in use: `wf_zero`;
- a leaf, a block of a level 2 table or a page of a level 3 table, written
  into or cleared from an entry that holds no table descriptor:
  `wf_setLeaf`;
- a new table, the table of the record, linked into a free entry of the root
  or of a level 2 table: `wf_link`.
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables

variable {r : Region} {N : Nat}

theorem pointsAt_lt {s : Tables r N} {base : UInt64} {t i c : Nat} (h : s.PointsAt base t i c) :
    c < s.used ∧ c < N := child?_some h.2.2

theorem entry_of_table_zero {s : Tables r N} {t : Nat} (h : s.table t = Table.zero) (i : Nat) :
    s.entry t i = 0 := by
  unfold Tables.entry; rw [h]; split <;> simp [Table.zero]

theorem table_eq_zero {s : Tables r N} {t : Nat} (h : ∀ i, i < ENTRIES → s.pool.get t i = 0) :
    s.table t = Table.zero := by
  unfold Tables.table
  split
  · rename_i ht
    apply Vector.ext; intro i hi
    have := h i hi
    simp only [Pool.get, ht, hi, dite_true] at this
    simp [this, Table.zero]
  · rfl

section WellFormed

variable {s : Tables r N} {base : UInt64} {bits : UInt8}

theorem wf_level2_ne_zero (hs : s.WellFormed base bits) {t : Nat} (h : s.IsLevel2 base t) :
    t ≠ 0 := by
  rintro rfl
  obtain ⟨i, hi⟩ := h
  exact hs.2.2.2.2.2.2.2.1 0 i (Or.inl rfl) hi

theorem wf_level3_ne_zero (hs : s.WellFormed base bits) {t : Nat} (h : s.IsLevel3 base t) :
    t ≠ 0 := by
  rintro rfl
  obtain ⟨t2, i, h2, hi⟩ := h
  exact hs.2.2.2.2.2.2.2.1 t2 i (Or.inr h2) hi

theorem wf_not_level2_level3 (hs : s.WellFormed base bits) {t : Nat} (h2 : s.IsLevel2 base t)
    (h3 : s.IsLevel3 base t) : False := by
  obtain ⟨i, hi⟩ := h2
  obtain ⟨t2, j, h22, hj⟩ := h3
  have := (hs.2.2.2.2.2.2.2.2.2 0 i t2 j t (Or.inl rfl) (Or.inr h22) hi hj).1
  exact wf_level2_ne_zero hs h22 this.symm

theorem wf_level2_lt {t : Nat} (h : s.IsLevel2 base t) : t < s.used ∧ t < N := by
  obtain ⟨i, hi⟩ := h; exact pointsAt_lt hi

theorem wf_level3_lt {t : Nat} (h : s.IsLevel3 base t) : t < s.used ∧ t < N := by
  obtain ⟨_, _, _, hi⟩ := h; exact pointsAt_lt hi

theorem wf_entry_free (hs : s.WellFormed base bits) {t : Nat} (ht : s.used ≤ t) (i : Nat) :
    s.entry t i = 0 := by
  by_cases htN : t < N
  · exact entry_of_table_zero (hs.2.2.2.1 t ht htN) i
  · rw [entry_eq_get, get_of_ge _ _ (by omega)]

theorem wf_plain_child (hs : s.WellFormed base bits) {t i : Nat}
    (hp : isPlainTableDescriptor (s.entry t i) = true) :
    ∃ c, s.PointsAt base t i c := by
  have hs0 := hs
  obtain ⟨-, h1, -, -, hroot, hl2, hl3, -, hall, -⟩ := hs
  have hi : i < ENTRIES := by
    apply Nat.lt_of_not_le; intro hi
    rw [entry_eq_get, get_of_ge_entries _ _ hi] at hp; exact absurd hp (by decide)
  by_cases ht0 : t = 0
  · subst ht0
    rcases hroot i hi with h | h
    · rw [h] at hp; exact absurd hp (by decide)
    · exact h
  by_cases htu : t < s.used
  · obtain ⟨t', i', hpar, hpt⟩ := hall t (by omega) htu
    rcases hpar with rfl | h2
    · rcases hl2 t ⟨i', hpt⟩ i hi with h | h | ⟨h, -⟩
      · rw [h] at hp; exact absurd hp (by decide)
      · exact h
      · rw [isPlain_of_isReadWriteBlock h] at hp; exact absurd hp (by decide)
    · rcases hl3 t ⟨t', i', h2, hpt⟩ i hi with h | ⟨⟨k, hk⟩, -⟩
      · rw [h] at hp; exact absurd hp (by decide)
      · rw [hk, isPlain_descriptor] at hp; exact absurd hp (by decide)
  · rw [wf_entry_free hs0 (by omega)] at hp; exact absurd hp (by decide)

end WellFormed

/-! ## The set of a zero pool -/

theorem not_pointsAt_of_zero {s : Tables r N} {base : UInt64} {t i c : Nat}
    (h : s.entry t i = 0) : ¬ s.PointsAt base t i c := by
  rintro ⟨-, hp, -⟩; rw [h] at hp; exact absurd hp (by decide)

theorem wf_zero {s : Tables r N} {base : UInt64} {bits : UInt8} (hp : PoolOk N base bits)
    (hz : ∀ t i, s.pool.get t i = 0) (hu : s.used = 1) : s.WellFormed base bits := by
  have he : ∀ t i, s.entry t i = 0 := fun t i => by rw [entry_eq_get, hz]
  have hn : ∀ t i c, ¬ s.PointsAt base t i c := fun t i c => not_pointsAt_of_zero (he t i)
  have hN := (pool_ok_facts hp).2.1
  refine ⟨hp, by omega, by omega, fun t _ _ => table_eq_zero fun i _ => hz t i,
    fun i _ => Or.inl (he 0 i), fun t ⟨i, h⟩ => absurd h (hn _ _ _),
    fun t ⟨_, _, _, h⟩ => absurd h (hn _ _ _), fun t i _ h => hn _ _ _ h,
    fun c h1 h2 => by omega, fun t i _ _ _ _ _ h => absurd h (hn _ _ _)⟩

/-! ## Elementary changes -/

/-- The entries of a set after one store into the entry `i` of table `t`. -/
theorem entry_store {s : Tables r N} {u t i : Nat} {d : UInt64} (ht : t < N) (hi : i < ENTRIES)
    (t' i' : Nat) :
    (⟨s.pool.store t i d, u⟩ : Tables r N).entry t' i' =
      if t' = t ∧ i' = i then d else s.entry t' i' := by
  rw [entry_eq_get, entry_eq_get, get_store]
  by_cases h : t' = t ∧ i' = i
  · simp [h, ht, hi]
  · simp only [h, ite_false]
    rw [ite_of_neg]; exact fun ⟨a, b, _⟩ => h ⟨a, b⟩

theorem wf_setLeaf {s : Tables r N} {base : UInt64} {bits : UInt8} (hs : s.WellFormed base bits)
    {t i : Nat} {d : UInt64} (ht0 : t ≠ 0) (htu : t < s.used) (hi : i < ENTRIES)
    (hold : isPlainTableDescriptor (s.entry t i) = false)
    (hnew : isPlainTableDescriptor d = false)
    (h2 : s.IsLevel2 base t → d = 0 ∨
      (isReadWriteBlock d = true ∧ (blockAddress d).toNat < 2 ^ bits.toNat))
    (h3 : s.IsLevel3 base t → d = 0 ∨
      ((∃ k, d = descriptor k (outputAddress d)) ∧ (outputAddress d).toNat < 2 ^ bits.toNat)) :
    (⟨s.pool.store t i d, s.used⟩ : Tables r N).WellFormed base bits := by
  have htN : t < N := Nat.lt_of_lt_of_le htu hs.2.2.1
  obtain ⟨hp, h1, hN, hz, hroot, hl2, hl3, hno, hall, huniq⟩ := hs
  have hent := entry_store (s := s) (u := s.used) (d := d) htN hi
  have hpa : ∀ t' i' c, (⟨s.pool.store t i d, s.used⟩ : Tables r N).PointsAt base t' i' c ↔
      s.PointsAt base t' i' c := by
    intro t' i' c
    unfold Tables.PointsAt
    rw [hent]
    by_cases h : t' = t ∧ i' = i
    · obtain ⟨rfl, rfl⟩ := h; simp [hold, hnew]
    · simp only [h, ite_false]; rfl
  have hL2 : ∀ x, (⟨s.pool.store t i d, s.used⟩ : Tables r N).IsLevel2 base x ↔ s.IsLevel2 base x :=
    fun x => by simp only [Tables.IsLevel2, hpa]
  have hL3 : ∀ x, (⟨s.pool.store t i d, s.used⟩ : Tables r N).IsLevel3 base x ↔ s.IsLevel3 base x :=
    fun x => by simp only [Tables.IsLevel3, hL2, hpa]
  have hPar : ∀ x, (⟨s.pool.store t i d, s.used⟩ : Tables r N).IsParent base x ↔
      s.IsParent base x := fun x => by simp only [Tables.IsParent, hL2]
  refine ⟨hp, h1, hN, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t' ht' ht'N
    have ht'' : s.used ≤ t' := ht'
    apply table_eq_zero; intro i' hi'
    rw [← entry_eq_get, hent, ite_of_neg (by omega)]
    exact entry_of_table_zero (hz t' ht' ht'N) i'
  · intro i' hi'
    rw [hent, ite_of_neg (by omega)]
    rcases hroot i' hi' with h | ⟨c, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, (hpa 0 i' c).2 h⟩
  · intro x hx i' hi'
    rw [hL2] at hx
    rw [hent]
    by_cases h : x = t ∧ i' = i
    · obtain ⟨rfl, rfl⟩ := h
      simp only [and_self, ite_true]
      rcases h2 hx with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · simp only [h, ite_false]
      rcases hl2 x hx i' hi' with h' | ⟨c, h'⟩ | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl ⟨c, (hpa x i' c).2 h'⟩)
      · exact Or.inr (Or.inr h')
  · intro x hx i' hi'
    rw [hL3] at hx
    rw [hent]
    by_cases h : x = t ∧ i' = i
    · obtain ⟨rfl, rfl⟩ := h
      simp only [and_self, ite_true]
      exact h3 hx
    · simp only [h, ite_false]
      exact hl3 x hx i' hi'
  · intro t' i' ht' h
    exact hno t' i' ((hPar t').1 ht') ((hpa _ _ _).1 h)
  · intro c hc1 hc2
    obtain ⟨t', i', hpar, h⟩ := hall c hc1 hc2
    exact ⟨t', i', (hPar t').2 hpar, (hpa _ _ _).2 h⟩
  · intro t1 i1 t2 i2 c hp1 hp2 ha hb
    exact huniq t1 i1 t2 i2 c ((hPar t1).1 hp1) ((hPar t2).1 hp2) ((hpa _ _ _).1 ha) ((hpa _ _ _).1 hb)

theorem wf_link {s : Tables r N} {base : UInt64} {bits : UInt8} (hs : s.WellFormed base bits)
    {t i : Nat} (ht : t = 0 ∨ s.IsLevel2 base t) (hi : i < ENTRIES) (h0 : s.entry t i = 0)
    (hu : s.used < N) :
    (⟨s.pool.store t i (tableAt base s.used), s.used + 1⟩ : Tables r N).WellFormed base bits := by
  have hs0 := hs
  obtain ⟨hp, h1, hN, hz, hroot, hl2, hl3, hno, hall, huniq⟩ := hs
  have htu : t < s.used := by
    rcases ht with rfl | h
    · omega
    · exact (wf_level2_lt h).1
  have htN : t < N := by omega
  let s' : Tables r N := ⟨s.pool.store t i (tableAt base s.used), s.used + 1⟩
  have hent : ∀ t' i', s'.entry t' i' = if t' = t ∧ i' = i then tableAt base s.used
      else s.entry t' i' := entry_store htN hi
  have hfree : ∀ j c, ¬ s.PointsAt base s.used j c :=
    fun j c => not_pointsAt_of_zero (wf_entry_free hs0 (Nat.le_refl _) j)
  have hnt : ∀ c, ¬ s.PointsAt base t i c := fun c => not_pointsAt_of_zero h0
  have hpa : ∀ t' i' c, s'.PointsAt base t' i' c ↔
      (t' = t ∧ i' = i ∧ c = s.used) ∨ s.PointsAt base t' i' c := by
    intro t' i' c
    by_cases h : t' = t ∧ i' = i
    · obtain ⟨rfl, rfl⟩ := h
      have hc : s'.child? base (tableAt base s.used) = some s.used :=
        child?_tableAt hp (Nat.lt_succ_self _) hu
      have he' : s'.entry t' i' = tableAt base s.used := by rw [hent]; simp
      unfold Tables.PointsAt
      rw [he', hc]
      constructor
      · rintro ⟨-, -, hc'⟩
        exact Or.inl ⟨rfl, rfl, (Option.some.inj hc').symm⟩
      · rintro (⟨-, -, rfl⟩ | h)
        · exact ⟨hi, isPlain_tableDescriptor _, rfl⟩
        · exact absurd h (hnt c)
    · have hiff : s'.PointsAt base t' i' c ↔ s.PointsAt base t' i' c := by
        simp only [Tables.PointsAt, hent, h, ite_false]
        constructor
        · rintro ⟨hi', hpl, hc⟩
          obtain ⟨c', hc'⟩ := wf_plain_child hs0 hpl
          have := child?_mono (u := s.used + 1) (Nat.le_succ _) hc'.2.2
          have hcc : c' = c := Option.some.inj (this.symm.trans hc)
          subst hcc; exact hc'
        · rintro ⟨hi', hpl, hc⟩
          exact ⟨hi', hpl, child?_mono (Nat.le_succ _) hc⟩
      rw [hiff]
      constructor
      · exact Or.inr
      · rintro (⟨a, b, -⟩ | h')
        · exact absurd ⟨a, b⟩ h
        · exact h'
  have hL2 : ∀ x, s'.IsLevel2 base x ↔ (t = 0 ∧ x = s.used) ∨ s.IsLevel2 base x := by
    intro x
    simp only [Tables.IsLevel2, hpa]
    constructor
    · rintro ⟨i', ⟨a, -, c⟩ | h⟩
      · exact Or.inl ⟨a.symm, c⟩
      · exact Or.inr ⟨i', h⟩
    · rintro (⟨a, c⟩ | ⟨i', h⟩)
      · exact ⟨i, Or.inl ⟨a.symm, rfl, c⟩⟩
      · exact ⟨i', Or.inr h⟩
  have hL3 : ∀ x, s'.IsLevel3 base x ↔ (t ≠ 0 ∧ x = s.used) ∨ s.IsLevel3 base x := by
    intro x
    simp only [Tables.IsLevel3, hL2, hpa]
    constructor
    · rintro ⟨t2, i2, ⟨-, rfl⟩ | h2, ⟨a, -, c⟩ | h⟩
      · omega
      · exact absurd h (hfree _ _)
      · subst a; exact Or.inl ⟨wf_level2_ne_zero hs0 h2, c⟩
      · exact Or.inr ⟨t2, i2, h2, h⟩
    · rintro (⟨a, c⟩ | ⟨t2, i2, h2, h⟩)
      · rcases ht with b | b
        · exact absurd b a
        · exact ⟨t, i, Or.inr b, Or.inl ⟨rfl, rfl, c⟩⟩
      · exact ⟨t2, i2, Or.inr h2, Or.inr h⟩
  have hPar : ∀ x i' c, s'.IsParent base x → s.PointsAt base x i' c → s.IsParent base x := by
    rintro x i' c (h | h) hx
    · exact Or.inl h
    · rcases (hL2 x).1 h with ⟨-, rfl⟩ | h
      · exact absurd hx (hfree _ _)
      · exact Or.inr h
  have htPar : s'.IsParent base t := by
    rcases ht with h | h
    · exact Or.inl h
    · exact Or.inr ((hL2 t).2 (Or.inr h))
  refine ⟨hp, Nat.le_add_left 1 s.used, Nat.succ_le_of_lt hu, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t' ht' ht'N
    have ht'' : s.used + 1 ≤ t' := ht'
    apply table_eq_zero; intro i' hi'
    rw [← entry_eq_get, hent, ite_of_neg (by omega)]
    exact entry_of_table_zero (hz t' (by omega) ht'N) i'
  · intro i' hi'
    by_cases h : 0 = t ∧ i' = i
    · exact Or.inr ⟨s.used, (hpa 0 i' _).2 (Or.inl ⟨h.1, h.2, rfl⟩)⟩
    · rw [hent, ite_of_neg h]
      rcases hroot i' hi' with h' | ⟨c, h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨c, (hpa 0 i' c).2 (Or.inr h')⟩
  · intro x hx i' hi'
    rcases (hL2 x).1 hx with ⟨-, rfl⟩ | hx
    · left; rw [hent, ite_of_neg (by omega)]; exact wf_entry_free hs0 (Nat.le_refl _) i'
    · by_cases h : x = t ∧ i' = i
      · exact Or.inr (Or.inl ⟨s.used, (hpa x i' _).2 (Or.inl ⟨h.1, h.2, rfl⟩)⟩)
      · rw [hent, ite_of_neg h]
        rcases hl2 x hx i' hi' with h' | ⟨c, h'⟩ | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl ⟨c, (hpa x i' c).2 (Or.inr h')⟩)
        · exact Or.inr (Or.inr h')
  · intro x hx i' hi'
    rcases (hL3 x).1 hx with ⟨-, rfl⟩ | hx3
    · left; rw [hent, ite_of_neg (by omega)]; exact wf_entry_free hs0 (Nat.le_refl _) i'
    · have hxt : x ≠ t := by
        rintro rfl
        rcases ht with h | h
        · exact wf_level3_ne_zero hs0 hx3 h
        · exact wf_not_level2_level3 hs0 h hx3
      rw [hent, ite_of_neg (fun h => hxt h.1)]
      exact hl3 x hx3 i' hi'
  · intro t' i' ht' h
    rcases (hpa t' i' 0).1 h with ⟨-, -, h⟩ | h
    · omega
    · exact hno t' i' (hPar t' i' 0 ht' h) h
  · intro c hc1 hc2
    by_cases hc : c = s.used
    · exact ⟨t, i, htPar, (hpa t i c).2 (Or.inl ⟨rfl, rfl, hc⟩)⟩
    · obtain ⟨t', i', hpar, h⟩ := hall c hc1 (by
        have : c < s.used + 1 := hc2
        omega)
      refine ⟨t', i', ?_, (hpa _ _ _).2 (Or.inr h)⟩
      rcases hpar with h' | h'
      · exact Or.inl h'
      · exact Or.inr ((hL2 t').2 (Or.inr h'))
  · intro t1 i1 t2 i2 c hp1 hp2 ha hb
    rcases (hpa _ _ _).1 ha with ⟨a1, a2, a3⟩ | ha <;>
      rcases (hpa _ _ _).1 hb with ⟨b1, b2, b3⟩ | hb
    · exact ⟨a1.trans b1.symm, a2.trans b2.symm⟩
    · subst a3; exact absurd (pointsAt_lt hb).1 (Nat.lt_irrefl _)
    · subst b3; exact absurd (pointsAt_lt ha).1 (Nat.lt_irrefl _)
    · exact huniq t1 i1 t2 i2 c (hPar _ _ _ hp1 ha) (hPar _ _ _ hp2 hb) ha hb

theorem link_pointsAt {s : Tables r N} {base : UInt64} {bits : UInt8} (hp : PoolOk N base bits)
    {t i : Nat} (ht : t < N) (hi : i < ENTRIES) (hu : s.used < N) :
    (⟨s.pool.store t i (tableAt base s.used), s.used + 1⟩ : Tables r N).PointsAt base t i s.used := by
  refine ⟨hi, ?_, ?_⟩ <;> rw [entry_store ht hi, ite_of_pos ⟨rfl, rfl⟩]
  · exact isPlain_tableDescriptor _
  · exact child?_tableAt hp (Nat.lt_succ_self _) hu

theorem pointsAt_store_of_ne {s : Tables r N} {base d : UInt64} {t i t' i' c u : Nat}
    (ht : t < N) (hi : i < ENTRIES) (hu : s.used ≤ u) (h : s.PointsAt base t' i' c)
    (hne : ¬ (t' = t ∧ i' = i)) :
    (⟨s.pool.store t i d, u⟩ : Tables r N).PointsAt base t' i' c := by
  obtain ⟨hi', hp, hc⟩ := h
  refine ⟨hi', ?_, ?_⟩ <;> rw [entry_store ht hi, ite_of_neg hne]
  · exact hp
  · exact child?_mono (s := s) hu hc

end Krepi.Proofs.PageTables
