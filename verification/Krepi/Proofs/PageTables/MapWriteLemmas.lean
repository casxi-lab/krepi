module

public import Krepi.Proofs.PageTables.MapLeavesLemmas
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.WalkLemmas
import Krepi.Proofs.PageTables.BitLemmas

/-!
# Page tables: the set after the write phase of a map

The set that `kernel_map` and `direct_map` leave once the plan of their
placed leaves has run (`finalSet`), for leaves that passed their checks in a
well-formed set (`LeafFacts`):

- the stores of the plan, `Wr` (those that a placed leaf needs; privately:
  two stores into one entry agree, a store is into a free entry of a table
  below the next free index, and a store of a table descriptor links a new
  table);
- the entries after the plan: `final_entry_wr` and `final_entry_old`;
- the tables after the plan: `NewT2`, `NewT3`, `leaf_not_plain`,
  `child_final`, `final_pointsAt` (a table descriptor of the set after the map
  is a link of a new table or one of the set before it), `final_level2` and
  `final_level3` (the level 2 and level 3 tables after the map are those
  before it and the new ones);
- **`final_wf`**: the set after the map is well-formed, from private steps
  for the parents, the entries and the uniqueness of the tables;
- `placed_path` (the walk of a placed leaf reaches its tables) and
  **`final_M`**: every leaf of the abstract mapping after the map is one of
  the set before it or lies in a placed leaf, with its descriptor.

Small facts: `placed_t2_ne_zero`, `placed_t3_ne_zero`, `slot_of_t2`.
`final_entry_wr`, `final_pointsAt`, `final_level2`, `final_level3` and
`placed_path` are not used by another module yet; they are stated for the
abstract mapping and the slots after a map.
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables

variable {r : Region} {N : Nat}

/-- A store of the plan of placed leaves: one that a placed leaf needs. -/
def Wr (base : UInt64) (placed : List Placed) (t i : Nat) (d : UInt64) : Prop :=
  ∃ q ∈ placed, Step.store t i d ∈ writesOf base q

private theorem wr_cases {base : UInt64} {placed : List Placed} {t i : Nat} {d : UInt64}
    (h : Wr base placed t i d) :
    (∃ q ∈ placed, q.new2 = true ∧ t = 0 ∧ i = index1 q.leaf.va ∧ d = tableAt base q.t2) ∨
    (∃ q ∈ placed, q.leaf.form = .page ∧ q.new3 = true ∧ t = q.t2 ∧ i = index2 q.leaf.va ∧
      d = tableAt base q.t3) ∨
    (∃ q ∈ placed, q.leaf.form = .page ∧ t = q.t3 ∧ i = index3 q.leaf.va ∧ d = q.leaf.desc) ∨
    (∃ q ∈ placed, q.leaf.form = .block ∧ t = q.t2 ∧ i = index2 q.leaf.va ∧ d = q.leaf.desc) := by
  obtain ⟨q, hq, hw⟩ := h
  rcases mem_writesOf.1 hw with ⟨hn, he⟩ | ⟨hp, hn, he⟩ | he
  · simp only [Step.store.injEq] at he
    exact Or.inl ⟨q, hq, hn, he.1, he.2.1, he.2.2⟩
  · simp only [link3, Step.store.injEq] at he
    exact Or.inr (Or.inl ⟨q, hq, hp, hn, he.1, he.2.1, he.2.2⟩)
  · simp only [Placed.store] at he
    cases hf : q.leaf.form <;> simp only [hf, Step.store.injEq] at he
    · exact Or.inr (Or.inr (Or.inl ⟨q, hq, hf, he.1, he.2.1, he.2.2⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨q, hq, hf, he.1, he.2.1, he.2.2⟩))

section Final

variable {s : Tables r N} {base : UInt64} {bits : UInt8} {leaves : List (MapLeaf × Place)}

theorem placed_t2_ne_zero (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) : q.t2 ≠ 0 := by
  cases hn : q.new2
  · exact wf_level2_ne_zero hs (placed_old2 hs hl hq hn).2
  · have := (placed_lt2 hs hl hq).2 hn; have := hs.2.1; omega

theorem placed_t3_ne_zero (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) (hp : q.leaf.form = .page) : q.t3 ≠ 0 := by
  cases hn : q.new3
  · exact wf_level3_ne_zero hs ((placed_new3 hs hl hq hp).2.2 hn).2.2.1
  · have := (placed_lt3 hs hl hq hp).2 hn; have := hs.2.1; omega

theorem slot_of_t2 (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q q' : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) (hq' : q' ∈ (assignTables s.used leaves).2)
    (ht : q.t2 = q'.t2) (hi : index2 q.leaf.va = index2 q'.leaf.va) :
    q.leaf.blockSlot = q'.leaf.blockSlot := by
  have hg := placed_t2eq hs hl hq hq' ht
  simp only [MapLeaf.blockSlot, MapLeaf.gibSlot] at hg ⊢
  rw [block_index, block_index, hg, hi]

private theorem va_of_page {a b : MapLeaf} (hb : a.blockSlot = b.blockSlot) (hi : index3 a.va = index3 b.va)
    (ha : a.va.toNat % PAGE_SIZE = 0) (hb' : b.va.toNat % PAGE_SIZE = 0) : a.va = b.va := by
  have h1 := page_index a.va
  have h2 := page_index b.va
  simp only [MapLeaf.blockSlot] at hb
  rw [hb, hi] at h1
  apply UInt64.toNat_inj.1
  simp only [PAGE_SIZE] at h1 h2 ha hb'
  omega

/-- Two stores of the plan into one entry agree. -/
private theorem wr_fun (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {t i : Nat}
    {d d' : UInt64} (h : Wr base (assignTables s.used leaves).2 t i d)
    (h' : Wr base (assignTables s.used leaves).2 t i d') : d = d' := by
  have hok := placed_ok hs hl
  rcases wr_cases h with ⟨q, hq, hn, rfl, rfl, rfl⟩ | ⟨q, hq, hp, hn, rfl, rfl, rfl⟩ |
      ⟨q, hq, hp, rfl, rfl, rfl⟩ | ⟨q, hq, hp, rfl, rfl, rfl⟩ <;>
    rcases wr_cases h' with ⟨q', hq', hn', ht, hi, rfl⟩ | ⟨q', hq', hp', hn', ht, hi, rfl⟩ |
      ⟨q', hq', hp', ht, hi, rfl⟩ | ⟨q', hq', hp', ht, hi, rfl⟩
  · have hg := gib_of_index1 (placed_region hl hq).1 (placed_region hl hq').1 hi
    rw [(hok.gib q hq q' hq' hg).2]
  · exact absurd ht.symm (placed_t2_ne_zero hs hl hq')
  · exact absurd ht.symm (placed_t3_ne_zero hs hl hq' hp')
  · exact absurd ht.symm (placed_t2_ne_zero hs hl hq')
  · exact absurd ht (placed_t2_ne_zero hs hl hq)
  · have hb := slot_of_t2 hs hl hq hq' ht hi
    rw [(hok.block q hq q' hq' hb).2.2]
  · exact absurd ht (placed_apart hs hl hq hq' hp')
  · have hb := slot_of_t2 hs hl hq hq' ht hi
    have := (hok.block q hq q' hq' hb).1; rw [hp, hp'] at this; cases this
  · exact absurd ht (placed_t3_ne_zero hs hl hq hp)
  · exact absurd ht.symm (placed_apart hs hl hq' hq hp)
  · have hb := placed_t3eq hs hl hq hq' hp hp' ht
    have hv := va_of_page hb hi (by have := (placed_region hl hq).2.1; rwa [hp] at this)
      (by have := (placed_region hl hq').2.1; rwa [hp'] at this)
    rcases placed_distinct hl hq hq' with rfl | h | h
    · rfl
    · rw [hv, hp] at h; simp only [Form.size, PAGE_SIZE] at h; omega
    · rw [hv, hp'] at h; simp only [Form.size, PAGE_SIZE] at h; omega
  · exact absurd ht.symm (placed_apart hs hl hq' hq hp)
  · exact absurd ht (placed_t2_ne_zero hs hl hq)
  · have hb := slot_of_t2 hs hl hq hq' ht hi
    have := (hok.block q hq q' hq' hb).1; rw [hp, hp'] at this; cases this
  · exact absurd ht (placed_apart hs hl hq hq' hp')
  · have hb := slot_of_t2 hs hl hq hq' ht hi
    rw [placed_blockOne hl hq hq' hb hp]

/-- The set after the write phase of a map and its plan. -/
def finalSet (s : Tables r N) (base : UInt64) (leaves : List (MapLeaf × Place)) : Tables r N :=
  ⟨(mapPlan base (assignTables s.used leaves).2).exec s.pool, (assignTables s.used leaves).1⟩

private theorem wr_facts (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {t i : Nat}
    {d : UInt64} (h : Wr base (assignTables s.used leaves).2 t i d) :
    t < (assignTables s.used leaves).1 ∧ i < ENTRIES ∧ (t < s.used → s.entry t i = 0) := by
  have hle : s.used ≤ (assignTables s.used leaves).1 := by
    have := (assignTables_spec s.used leaves (leaves_mono hl)).2.2.1; exact this
  have h1 := hs.2.1
  rcases wr_cases h with ⟨q, hq, hn, rfl, rfl, rfl⟩ | ⟨q, hq, hp, hn, rfl, rfl, rfl⟩ |
      ⟨q, hq, hp, rfl, rfl, rfl⟩ | ⟨q, hq, hp, rfl, rfl, rfl⟩
  · exact ⟨by omega, index1_lt _, fun _ => placed_new2 hs hl hq hn⟩
  · refine ⟨?_, index2_lt _, fun hlt => ?_⟩
    · cases hn2 : q.new2
      · have := (placed_lt2 hs hl hq).1 hn2; omega
      · exact (placed_range hl hq (Or.inl ⟨hn2, rfl⟩)).2
    · cases hn2 : q.new2
      · exact (placed_new3 hs hl hq hp).2.1 hn hn2
      · have := (placed_lt2 hs hl hq).2 hn2; omega
  · refine ⟨?_, index3_lt _, fun hlt => ?_⟩
    · cases hn3 : q.new3
      · have := (placed_lt3 hs hl hq hp).1 hn3; omega
      · exact (placed_range hl hq (Or.inr ⟨hp, hn3, rfl⟩)).2
    · cases hn3 : q.new3
      · exact ((placed_new3 hs hl hq hp).2.2 hn3).2.2.2
      · have := (placed_lt3 hs hl hq hp).2 hn3; omega
  · refine ⟨?_, index2_lt _, fun hlt => ?_⟩
    · cases hn2 : q.new2
      · have := (placed_lt2 hs hl hq).1 hn2; omega
      · exact (placed_range hl hq (Or.inl ⟨hn2, rfl⟩)).2
    · cases hn2 : q.new2
      · exact placed_block hs hl hq hp hn2
      · have := (placed_lt2 hs hl hq).2 hn2; omega

theorem final_entry_wr (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    (hN : (assignTables s.used leaves).1 ≤ N) {t i : Nat} {d : UInt64}
    (h : Wr base (assignTables s.used leaves).2 t i d) : (finalSet s base leaves).entry t i = d := by
  have hok := placed_ok hs hl
  obtain ⟨ht, hi, -⟩ := wr_facts hs hl h
  rw [entry_eq_get]
  exact get_exec_store (by omega) hi (pairwise_mapPlan hok base)
    (fun d' hd' => wr_fun hs hl ((mem_mapPlan hok).1 hd') h) ((mem_mapPlan hok).2 h)

theorem final_entry_old (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {t i : Nat}
    (h : ∀ d, ¬ Wr base (assignTables s.used leaves).2 t i d) :
    (finalSet s base leaves).entry t i = s.entry t i := by
  have hok := placed_ok hs hl
  rw [entry_eq_get, entry_eq_get]
  by_cases ht : t < N
  · by_cases hi : i < ENTRIES
    · refine get_exec_old ht hi (fun hz => ?_) (fun d hd => h d ((mem_mapPlan hok).1 hd))
      obtain ⟨q, hq, hn⟩ := zero_mapPlan hok hz
      rw [← entry_eq_get]; exact wf_entry_free hs (placed_range hl hq hn).1 i
    · rw [get_of_ge_entries _ _ (by omega), get_of_ge_entries _ _ (by omega)]
  · rw [get_of_ge _ _ (by omega), get_of_ge _ _ (by omega)]

/-- A new level 2 table of the placed leaves. -/
def NewT2 (placed : List Placed) (c : Nat) : Prop := ∃ q ∈ placed, q.new2 = true ∧ q.t2 = c

/-- A new level 3 table of the placed leaves. -/
def NewT3 (placed : List Placed) (c : Nat) : Prop :=
  ∃ q ∈ placed, q.leaf.form = .page ∧ q.new3 = true ∧ q.t3 = c

private theorem tableAt_inj {base : UInt64} {bits : UInt8} (hp : PoolOk N base bits) {c c' : Nat} (hc : c < N)
    (hc' : c' < N) (h : tableAt base c = tableAt base c') : c = c' := by
  have := congrArg (fun d => (outputAddress d).toNat) h
  simp only [outputAddress_tableAt hp hc, outputAddress_tableAt hp hc'] at this
  simp only [PAGE_SIZE] at this; omega

theorem leaf_not_plain {bits : UInt8} {l : MapLeaf} (h : LeafDesc bits l) :
    isPlainTableDescriptor l.desc = false := by
  cases hf : l.form
  · obtain ⟨⟨k, hk⟩, -⟩ := h.1 hf; rw [hk, isPlain_descriptor]
  · exact isPlain_of_isReadWriteBlock (h.2 hf).1

theorem child_final (d : UInt64) : (finalSet s base leaves).child? base d =
    ({ s with used := (assignTables s.used leaves).1 } : Tables r N).child? base d := rfl

private theorem placed_t2_lt (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) : q.t2 < (assignTables s.used leaves).1 := by
  have hle : s.used ≤ (assignTables s.used leaves).1 := by
    have := (assignTables_spec s.used leaves (leaves_mono hl)).2.2.1; exact this
  cases hn2 : q.new2
  · have := (placed_lt2 hs hl hq).1 hn2; omega
  · exact (placed_range hl hq (Or.inl ⟨hn2, rfl⟩)).2

private theorem placed_t3_lt (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) (hp : q.leaf.form = .page) :
    q.t3 < (assignTables s.used leaves).1 := by
  have hle : s.used ≤ (assignTables s.used leaves).1 := by
    have := (assignTables_spec s.used leaves (leaves_mono hl)).2.2.1; exact this
  cases hn3 : q.new3
  · have := (placed_lt3 hs hl hq hp).1 hn3; omega
  · exact (placed_range hl hq (Or.inr ⟨hp, hn3, rfl⟩)).2

/-- A store of a table descriptor of the plan is the link of a new table. -/
private theorem wr_table (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    (hN : (assignTables s.used leaves).1 ≤ N) {t i c : Nat} (hc : c < N)
    (h : Wr base (assignTables s.used leaves).2 t i (tableAt base c)) :
    (∃ q ∈ (assignTables s.used leaves).2, q.new2 = true ∧ t = 0 ∧ i = index1 q.leaf.va ∧ c = q.t2) ∨
    (∃ q ∈ (assignTables s.used leaves).2, q.leaf.form = .page ∧ q.new3 = true ∧ t = q.t2 ∧
      i = index2 q.leaf.va ∧ c = q.t3) := by
  rcases wr_cases h with ⟨q, hq, hn, ht, hi, he⟩ | ⟨q, hq, hp, hn, ht, hi, he⟩ |
      ⟨q, hq, hp, ht, hi, he⟩ | ⟨q, hq, hp, ht, hi, he⟩
  · have := placed_t2_lt hs hl hq
    exact Or.inl ⟨q, hq, hn, ht, hi, tableAt_inj hs.1 hc (by omega) he⟩
  · have := placed_t3_lt hs hl hq hp
    exact Or.inr ⟨q, hq, hp, hn, ht, hi, tableAt_inj hs.1 hc (by omega) he⟩
  · have := leaf_not_plain (placed_region hl hq).2.2
    rw [← he, tableAt, isPlain_tableDescriptor] at this; cases this
  · have := leaf_not_plain (placed_region hl hq).2.2
    rw [← he, tableAt, isPlain_tableDescriptor] at this; cases this

theorem final_pointsAt (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    (hN : (assignTables s.used leaves).1 ≤ N) {t i c : Nat} :
    (finalSet s base leaves).PointsAt base t i c ↔
      (Wr base (assignTables s.used leaves).2 t i (tableAt base c) ∧ s.used ≤ c ∧
        c < (assignTables s.used leaves).1) ∨
      ((∀ d, ¬ Wr base (assignTables s.used leaves).2 t i d) ∧ s.PointsAt base t i c) := by
  have hle : s.used ≤ (assignTables s.used leaves).1 := by
    have := (assignTables_spec s.used leaves (leaves_mono hl)).2.2.1; exact this
  constructor
  · rintro ⟨hi, hpl, hc⟩
    by_cases hw : ∃ d, Wr base (assignTables s.used leaves).2 t i d
    · obtain ⟨d, hd⟩ := hw
      rw [final_entry_wr hs hl hN hd] at hpl hc
      rw [child_final] at hc
      rcases wr_cases hd with ⟨q, hq, hn, ht, hi', he⟩ | ⟨q, hq, hp, hn, ht, hi', he⟩ |
          ⟨q, hq, hp, ht, hi', he⟩ | ⟨q, hq, hp, ht, hi', he⟩
      · have hlt := placed_t2_lt hs hl hq
        rw [he, child?_tableAt hs.1 (s := { s with used := _ }) hlt (by omega)] at hc
        cases hc
        exact Or.inl ⟨he ▸ hd, (placed_range hl hq (Or.inl ⟨hn, rfl⟩)).1, hlt⟩
      · have hlt := placed_t3_lt hs hl hq hp
        rw [he, child?_tableAt hs.1 (s := { s with used := _ }) hlt (by omega)] at hc
        cases hc
        exact Or.inl ⟨he ▸ hd, (placed_range hl hq (Or.inr ⟨hp, hn, rfl⟩)).1, hlt⟩
      · rw [he, leaf_not_plain (placed_region hl hq).2.2] at hpl; cases hpl
      · rw [he, leaf_not_plain (placed_region hl hq).2.2] at hpl; cases hpl
    · have hw' : ∀ d, ¬ Wr base (assignTables s.used leaves).2 t i d := fun d h => hw ⟨d, h⟩
      rw [final_entry_old hs hl hw'] at hpl hc
      obtain ⟨c0, hc0⟩ := wf_plain_child hs hpl
      have := child?_mono (s := s) hle hc0.2.2
      rw [child_final, this] at hc
      cases hc
      exact Or.inr ⟨hw', hc0⟩
  · rintro (⟨hw, h1, h2⟩ | ⟨hw, hpa⟩)
    · refine ⟨(wr_facts hs hl hw).2.1, ?_, ?_⟩ <;> rw [final_entry_wr hs hl hN hw]
      · exact isPlain_tableDescriptor _
      · rw [child_final]; exact child?_tableAt hs.1 (s := { s with used := _ }) h2 (by omega)
    · obtain ⟨hi, hpl, hc⟩ := hpa
      refine ⟨hi, ?_, ?_⟩ <;> rw [final_entry_old hs hl hw]
      · exact hpl
      · rw [child_final]; exact child?_mono (s := s) hle hc

private theorem not_wr_of_lt (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {t i : Nat}
    (ht : t < s.used) (hne : s.entry t i ≠ 0) : ∀ d, ¬ Wr base (assignTables s.used leaves).2 t i d :=
  fun _ hw => hne ((wr_facts hs hl hw).2.2 ht)

theorem final_level2 (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    (hN : (assignTables s.used leaves).1 ≤ N) {t : Nat} :
    (finalSet s base leaves).IsLevel2 base t ↔ s.IsLevel2 base t ∨ NewT2 (assignTables s.used leaves).2 t := by
  constructor
  · rintro ⟨i, h⟩
    rcases (final_pointsAt hs hl hN).1 h with ⟨hw, -, h2⟩ | ⟨-, hp⟩
    · rcases wr_table hs hl hN (by omega) hw with ⟨q, hq, hn, -, -, rfl⟩ | ⟨q, hq, -, -, ht, -, -⟩
      · exact Or.inr ⟨q, hq, hn, rfl⟩
      · exact absurd ht.symm (placed_t2_ne_zero hs hl hq)
    · exact Or.inl ⟨i, hp⟩
  · rintro (⟨i, hp⟩ | ⟨q, hq, hn, rfl⟩)
    · exact ⟨i, (final_pointsAt hs hl hN).2 (Or.inr ⟨not_wr_of_lt hs hl (by have := hs.2.1; omega)
        (pointsAt_ne_zero hp), hp⟩)⟩
    · obtain ⟨h1, h2⟩ := placed_range hl hq (Or.inl ⟨hn, rfl⟩)
      exact ⟨index1 q.leaf.va, (final_pointsAt hs hl hN).2 (Or.inl
        ⟨⟨q, hq, mem_writesOf.2 (Or.inl ⟨hn, rfl⟩)⟩, h1, h2⟩)⟩

private theorem placed_lvl2 (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) :
    s.IsLevel2 base q.t2 ∨ NewT2 (assignTables s.used leaves).2 q.t2 := by
  cases hn : q.new2
  · exact Or.inl (placed_old2 hs hl hq hn).2
  · exact Or.inr ⟨q, hq, hn, rfl⟩

private theorem placed_lvl3 (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) (hp : q.leaf.form = .page) :
    s.IsLevel3 base q.t3 ∨ NewT3 (assignTables s.used leaves).2 q.t3 := by
  cases hn : q.new3
  · exact Or.inl ((placed_new3 hs hl hq hp).2.2 hn).2.2.1
  · exact Or.inr ⟨q, hq, hp, hn, rfl⟩

theorem final_level3 (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    (hN : (assignTables s.used leaves).1 ≤ N) {t : Nat} :
    (finalSet s base leaves).IsLevel3 base t ↔ s.IsLevel3 base t ∨ NewT3 (assignTables s.used leaves).2 t := by
  constructor
  · rintro ⟨t2, i, h2, h⟩
    rcases (final_pointsAt hs hl hN).1 h with ⟨hw, -, hc⟩ | ⟨-, hp⟩
    · rcases wr_table hs hl hN (by omega) hw with ⟨q, hq, hn, rfl, -, -⟩ | ⟨q, hq, hp, hn, -, -, rfl⟩
      · rcases (final_level2 hs hl hN).1 h2 with h2 | ⟨q', hq', -, ht⟩
        · exact absurd rfl (wf_level2_ne_zero hs h2)
        · exact absurd ht (placed_t2_ne_zero hs hl hq')
      · exact Or.inr ⟨q, hq, hp, hn, rfl⟩
    · rcases (final_level2 hs hl hN).1 h2 with h2 | ⟨q', hq', hn', rfl⟩
      · exact Or.inl ⟨t2, i, h2, hp⟩
      · have := wf_entry_free hs (placed_range hl hq' (Or.inl ⟨hn', rfl⟩)).1 i
        exact absurd this (pointsAt_ne_zero hp)
  · rintro (⟨t2, i, h2, hp⟩ | ⟨q, hq, hp, hn, rfl⟩)
    · refine ⟨t2, i, (final_level2 hs hl hN).2 (Or.inl h2), (final_pointsAt hs hl hN).2 (Or.inr ⟨?_, hp⟩)⟩
      exact not_wr_of_lt hs hl (wf_level2_lt h2).1 (pointsAt_ne_zero hp)
    · obtain ⟨h1, h2⟩ := placed_range hl hq (Or.inr ⟨hp, hn, rfl⟩)
      exact ⟨q.t2, index2 q.leaf.va, (final_level2 hs hl hN).2 (placed_lvl2 hs hl hq),
        (final_pointsAt hs hl hN).2 (Or.inl ⟨⟨q, hq, mem_writesOf.2 (Or.inr (Or.inl ⟨hp, hn, rfl⟩))⟩,
          h1, h2⟩)⟩

private theorem lvl_excl (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {t : Nat}
    (h2 : s.IsLevel2 base t ∨ NewT2 (assignTables s.used leaves).2 t)
    (h3 : s.IsLevel3 base t ∨ NewT3 (assignTables s.used leaves).2 t) : False := by
  rcases h2 with h2 | ⟨q, hq, hn, rfl⟩ <;> rcases h3 with h3 | ⟨q', hq', hp', hn', ht⟩
  · exact wf_not_level2_level3 hs h2 h3
  · have := (wf_level2_lt h2).1; have := (placed_lt3 hs hl hq' hp').2 hn'; omega
  · have := (wf_level3_lt h3).1; have := (placed_lt2 hs hl hq).2 hn; omega
  · exact placed_apart hs hl hq hq' hp' ht.symm

private theorem final_parent (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    (hN : (assignTables s.used leaves).1 ≤ N) {t i c : Nat} (ht : (finalSet s base leaves).IsParent base t)
    (hp : s.PointsAt base t i c) : s.IsParent base t := by
  rcases ht with rfl | ht
  · exact Or.inl rfl
  · rcases (final_level2 hs hl hN).1 ht with ht | ⟨q, hq, hn, rfl⟩
    · exact Or.inr ht
    · exact absurd (wf_entry_free hs (placed_range hl hq (Or.inl ⟨hn, rfl⟩)).1 i) (pointsAt_ne_zero hp)

private theorem final_level2_entry (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    (hN : (assignTables s.used leaves).1 ≤ N) {t : Nat} (ht : (finalSet s base leaves).IsLevel2 base t)
    {i : Nat} (hi : i < ENTRIES) :
    (finalSet s base leaves).entry t i = 0 ∨ (∃ c, (finalSet s base leaves).PointsAt base t i c) ∨
      (isReadWriteBlock ((finalSet s base leaves).entry t i) = true ∧
        (blockAddress ((finalSet s base leaves).entry t i)).toNat < 2 ^ bits.toNat) := by
  have h2 := (final_level2 hs hl hN).1 ht
  by_cases hw : ∃ d, Wr base (assignTables s.used leaves).2 t i d
  · obtain ⟨d, hd⟩ := hw
    rw [final_entry_wr hs hl hN hd]
    rcases wr_cases hd with ⟨q, hq, hn, rfl, -, -⟩ | ⟨q, hq, hp, hn, rfl, -, rfl⟩ |
        ⟨q, hq, hp, rfl, -, -⟩ | ⟨q, hq, hp, rfl, -, rfl⟩
    · rcases h2 with h2 | ⟨q', hq', -, ht'⟩
      · exact absurd rfl (wf_level2_ne_zero hs h2)
      · exact absurd ht' (placed_t2_ne_zero hs hl hq')
    · obtain ⟨h1, h2⟩ := placed_range hl hq (Or.inr ⟨hp, hn, rfl⟩)
      exact Or.inr (Or.inl ⟨q.t3, (final_pointsAt hs hl hN).2 (Or.inl ⟨hd, h1, h2⟩)⟩)
    · exact (lvl_excl hs hl h2 (placed_lvl3 hs hl hq hp)).elim
    · exact Or.inr (Or.inr ((placed_region hl hq).2.2.2 hp))
  · have hw' : ∀ d, ¬ Wr base (assignTables s.used leaves).2 t i d := fun d h => hw ⟨d, h⟩
    rw [final_entry_old hs hl hw']
    rcases h2 with h2 | ⟨q, hq, hn, rfl⟩
    · rcases hs.2.2.2.2.2.1 t h2 i hi with h | ⟨c, hc⟩ | h
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨c, (final_pointsAt hs hl hN).2 (Or.inr ⟨hw', hc⟩)⟩)
      · exact Or.inr (Or.inr h)
    · exact Or.inl (wf_entry_free hs (placed_range hl hq (Or.inl ⟨hn, rfl⟩)).1 i)

private theorem final_level3_entry (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    (hN : (assignTables s.used leaves).1 ≤ N) {t : Nat} (ht : (finalSet s base leaves).IsLevel3 base t)
    {i : Nat} (hi : i < ENTRIES) :
    (finalSet s base leaves).entry t i = 0 ∨
      ((∃ k, (finalSet s base leaves).entry t i =
          descriptor k (outputAddress ((finalSet s base leaves).entry t i))) ∧
        (outputAddress ((finalSet s base leaves).entry t i)).toNat < 2 ^ bits.toNat) := by
  have h3 := (final_level3 hs hl hN).1 ht
  by_cases hw : ∃ d, Wr base (assignTables s.used leaves).2 t i d
  · obtain ⟨d, hd⟩ := hw
    rw [final_entry_wr hs hl hN hd]
    rcases wr_cases hd with ⟨q, hq, hn, rfl, -, -⟩ | ⟨q, hq, hp, hn, rfl, -, rfl⟩ |
        ⟨q, hq, hp, rfl, -, rfl⟩ | ⟨q, hq, hp, rfl, -, rfl⟩
    · rcases h3 with h3 | ⟨q', hq', hp', -, ht'⟩
      · exact absurd rfl (wf_level3_ne_zero hs h3)
      · exact absurd ht' (placed_t3_ne_zero hs hl hq' hp')
    · exact (lvl_excl hs hl (placed_lvl2 hs hl hq) h3).elim
    · exact Or.inr ((placed_region hl hq).2.2.1 hp)
    · exact (lvl_excl hs hl (placed_lvl2 hs hl hq) h3).elim
  · have hw' : ∀ d, ¬ Wr base (assignTables s.used leaves).2 t i d := fun d h => hw ⟨d, h⟩
    rw [final_entry_old hs hl hw']
    rcases h3 with h3 | ⟨q, hq, hp, hn, rfl⟩
    · exact hs.2.2.2.2.2.2.1 t h3 i hi
    · exact Or.inl (wf_entry_free hs (placed_range hl hq (Or.inr ⟨hp, hn, rfl⟩)).1 i)

private theorem final_uniq (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    (hN : (assignTables s.used leaves).1 ≤ N) {t i t' i' c : Nat}
    (hp : (finalSet s base leaves).IsParent base t) (hp' : (finalSet s base leaves).IsParent base t')
    (ha : (finalSet s base leaves).PointsAt base t i c) (hb : (finalSet s base leaves).PointsAt base t' i' c) :
    t = t' ∧ i = i' := by
  have hok := placed_ok hs hl
  rcases (final_pointsAt hs hl hN).1 ha with ⟨hw, h1, h2⟩ | ⟨-, ha'⟩ <;>
    rcases (final_pointsAt hs hl hN).1 hb with ⟨hw', h1', h2'⟩ | ⟨-, hb'⟩
  · rcases wr_table hs hl hN (by omega) hw with ⟨q, hq, hn, rfl, rfl, rfl⟩ | ⟨q, hq, hpg, hn, rfl, rfl, rfl⟩ <;>
      rcases wr_table hs hl hN (by omega) hw' with ⟨q', hq', hn', rfl, rfl, hc⟩ |
        ⟨q', hq', hpg', hn', rfl, rfl, hc⟩
    · exact ⟨rfl, index1_of_gib (placed_t2eq hs hl hq hq' hc)⟩
    · exact absurd hc (placed_apart hs hl hq hq' hpg')
    · exact absurd hc.symm (placed_apart hs hl hq' hq hpg)
    · have hb := placed_t3eq hs hl hq hq' hpg hpg' hc
      exact ⟨(hok.gib q hq q' hq' (gib_of_block hb)).2, index2_of_block hb⟩
  · have := (pointsAt_lt hb').1; omega
  · have := (pointsAt_lt ha').1; omega
  · exact hs.2.2.2.2.2.2.2.2.2 _ _ _ _ _ (final_parent hs hl hN hp ha') (final_parent hs hl hN hp' hb') ha' hb'

/-- **The write phase of a map keeps a set well-formed.** -/
theorem final_wf (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    (hN : (assignTables s.used leaves).1 ≤ N) : (finalSet s base leaves).WellFormed base bits := by
  have hle : s.used ≤ (assignTables s.used leaves).1 := by
    have := (assignTables_spec s.used leaves (leaves_mono hl)).2.2.1; exact this
  have hu1 := hs.2.1
  refine ⟨hs.1, by simp only [finalSet]; omega, hN, ?_, ?_, fun t ht i hi => final_level2_entry hs hl hN ht hi,
    fun t ht i hi => final_level3_entry hs hl hN ht hi, ?_, ?_,
    fun t i t' i' c hp hp' ha hb => final_uniq hs hl hN hp hp' ha hb⟩
  · intro t ht htN
    apply table_eq_zero; intro i hi
    rw [← entry_eq_get, final_entry_old hs hl (fun d hw => ?_)]
    · exact wf_entry_free hs (by simp only [finalSet] at ht; omega) i
    · have := (wr_facts hs hl hw).1; simp only [finalSet] at ht; omega
  · intro i hi
    by_cases hw : ∃ d, Wr base (assignTables s.used leaves).2 0 i d
    · obtain ⟨d, hd⟩ := hw
      rcases wr_cases hd with ⟨q, hq, hn, -, -, rfl⟩ | ⟨q, hq, -, -, h0, -, -⟩ |
          ⟨q, hq, hp, h0, -, -⟩ | ⟨q, hq, -, h0, -, -⟩
      · obtain ⟨h1, h2⟩ := placed_range hl hq (Or.inl ⟨hn, rfl⟩)
        exact Or.inr ⟨q.t2, (final_pointsAt hs hl hN).2 (Or.inl ⟨hd, h1, h2⟩)⟩
      · exact absurd h0.symm (placed_t2_ne_zero hs hl hq)
      · exact absurd h0.symm (placed_t3_ne_zero hs hl hq hp)
      · exact absurd h0.symm (placed_t2_ne_zero hs hl hq)
    · have hw' : ∀ d, ¬ Wr base (assignTables s.used leaves).2 0 i d := fun d h => hw ⟨d, h⟩
      rw [final_entry_old hs hl hw']
      rcases hs.2.2.2.2.1 i hi with h | ⟨c, hc⟩
      · exact Or.inl h
      · exact Or.inr ⟨c, (final_pointsAt hs hl hN).2 (Or.inr ⟨hw', hc⟩)⟩
  · intro t i ht h
    rcases (final_pointsAt hs hl hN).1 h with ⟨-, h1, -⟩ | ⟨-, hp⟩
    · omega
    · exact hs.2.2.2.2.2.2.2.1 t i (final_parent hs hl hN ht hp) hp
  · intro c hc1 hc2
    simp only [finalSet] at hc2
    by_cases hc : c < s.used
    · obtain ⟨t, i, ht, hp⟩ := hs.2.2.2.2.2.2.2.2.1 c hc1 hc
      have htu : t < s.used := by rcases ht with rfl | ht; · omega
                                  exact (wf_level2_lt ht).1
      refine ⟨t, i, ?_, (final_pointsAt hs hl hN).2 (Or.inr ⟨not_wr_of_lt hs hl htu (pointsAt_ne_zero hp), hp⟩)⟩
      rcases ht with rfl | ht
      · exact Or.inl rfl
      · exact Or.inr ((final_level2 hs hl hN).2 (Or.inl ht))
    · have := (assignTables_spec s.used leaves (leaves_mono hl)).2.2.2.2.1
      obtain ⟨q, hq, hn⟩ := this c (by omega) hc2
      rcases hn with ⟨hn, rfl⟩ | ⟨hp, hn, rfl⟩
      · exact ⟨0, index1 q.leaf.va, Or.inl rfl, (final_pointsAt hs hl hN).2 (Or.inl
          ⟨⟨q, hq, mem_writesOf.2 (Or.inl ⟨hn, rfl⟩)⟩, by omega, hc2⟩)⟩
      · exact ⟨q.t2, index2 q.leaf.va, Or.inr ((final_level2 hs hl hN).2 (placed_lvl2 hs hl hq)),
          (final_pointsAt hs hl hN).2 (Or.inl
            ⟨⟨q, hq, mem_writesOf.2 (Or.inr (Or.inl ⟨hp, hn, rfl⟩))⟩, by omega, hc2⟩)⟩

/-- The walk of a placed leaf in the set after the map reaches its tables. -/
theorem placed_path (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    (hN : (assignTables s.used leaves).1 ≤ N) {q : Placed} (hq : q ∈ (assignTables s.used leaves).2) :
    (finalSet s base leaves).PointsAt base 0 (index1 q.leaf.va) q.t2 ∧
      (q.leaf.form = .page → (finalSet s base leaves).PointsAt base q.t2 (index2 q.leaf.va) q.t3) := by
  have hu1 := hs.2.1
  refine ⟨?_, fun hp => ?_⟩
  · cases hn : q.new2
    · have hpa := (placed_old2 hs hl hq hn).1
      exact (final_pointsAt hs hl hN).2 (Or.inr ⟨not_wr_of_lt hs hl (by omega) (pointsAt_ne_zero hpa), hpa⟩)
    · obtain ⟨h1, h2⟩ := placed_range hl hq (Or.inl ⟨hn, rfl⟩)
      exact (final_pointsAt hs hl hN).2 (Or.inl ⟨⟨q, hq, mem_writesOf.2 (Or.inl ⟨hn, rfl⟩)⟩, h1, h2⟩)
  · cases hn : q.new3
    · obtain ⟨hn2, hpa, -, -⟩ := (placed_new3 hs hl hq hp).2.2 hn
      exact (final_pointsAt hs hl hN).2 (Or.inr ⟨not_wr_of_lt hs hl ((placed_lt2 hs hl hq).1 hn2)
        (pointsAt_ne_zero hpa), hpa⟩)
    · obtain ⟨h1, h2⟩ := placed_range hl hq (Or.inr ⟨hp, hn, rfl⟩)
      exact (final_pointsAt hs hl hN).2 (Or.inl
        ⟨⟨q, hq, mem_writesOf.2 (Or.inr (Or.inl ⟨hp, hn, rfl⟩))⟩, h1, h2⟩)

/-- The leaves of the set after the map: those of the set before it, and those
of the placed leaves. -/
theorem final_M (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    (hN : (assignTables s.used leaves).1 ≤ N) {v : UInt64} {l : Leaf}
    (h : (finalSet s base leaves).M base v l) :
    s.M base v l ∨ ∃ q ∈ (assignTables s.used leaves).2, q.leaf.va.toNat ≤ v.toNat ∧
      v.toNat < q.leaf.va.toNat + q.leaf.form.size ∧ l.form = q.leaf.form ∧
      (q.leaf.form = .page → l.pa = outputAddress q.leaf.desc ∧ Kind.ofPage q.leaf.desc = some l.kind) ∧
      (q.leaf.form = .block →
        l.pa.toNat = (blockAddress q.leaf.desc).toNat + v.toNat % BLOCK_SIZE ∧ l.kind = .readWrite) := by
  have hs' := final_wf hs hl hN
  have hu1 := hs.2.1
  obtain ⟨hreg, hal, ⟨t2, t3, d, hw, htb, hk, hpa, hfm⟩ | ⟨t2, d, hw, hrw, hkd, hfm, hpa⟩⟩ := h
  · obtain ⟨e2, hw2, -, -, -, -⟩ := walk_ok_level3.1 hw
    have hp1 := (wf_walk2_some hs' hw2).1
    obtain ⟨hl2, hp2, hl3, hd⟩ := wf_walk_level3 hs' hw
    by_cases hW : ∃ d', Wr base (assignTables s.used leaves).2 t3 (index3 v) d'
    · obtain ⟨d', hd'⟩ := hW
      have hdd := (final_entry_wr hs hl hN hd').symm.trans hd.symm
      rcases wr_cases hd' with ⟨q, hq, -, rfl, -, -⟩ | ⟨q, hq, -, -, rfl, -, -⟩ |
          ⟨q, hq, hp, rfl, hi3, rfl⟩ | ⟨q, hq, -, rfl, -, -⟩
      · rcases (final_level3 hs hl hN).1 hl3 with h3 | ⟨q', hq', hp', -, ht'⟩
        · exact absurd rfl (wf_level3_ne_zero hs h3)
        · exact absurd ht' (placed_t3_ne_zero hs hl hq' hp')
      · exact (lvl_excl hs hl (placed_lvl2 hs hl hq) ((final_level3 hs hl hN).1 hl3)).elim
      · obtain ⟨hq1, hq2⟩ := placed_path hs hl hN hq
        obtain ⟨e2, e2'⟩ := final_uniq hs hl hN (Or.inr hl2)
          (Or.inr ((final_level2 hs hl hN).2 (placed_lvl2 hs hl hq))) hp2 (hq2 hp)
        subst e2
        have e1 := (final_uniq hs hl hN (Or.inl rfl) (Or.inl rfl) hp1 hq1).2
        obtain ⟨hreg', hal', -⟩ := placed_region hl hq
        rw [hp] at hal'
        have hg := gib_of_index1 hreg hreg' e1
        have hb : v.toNat / BLOCK_SIZE = q.leaf.va.toNat / BLOCK_SIZE := by
          rw [block_index, block_index, hg, e2']
        have hpg := page_index v
        have hpg' := page_index q.leaf.va
        rw [hb, hi3] at hpg
        simp only [Form.size, PAGE_SIZE] at hal hal' hpg hpg' ⊢
        refine Or.inr ⟨q, hq, by omega, by rw [hp]; simp only; omega,
          by rw [hfm, hp], fun _ => ⟨by rw [hpa, hdd], by rw [hdd]; exact hk⟩, fun hb' => ?_⟩
        rw [hp] at hb'; cases hb'
      · exact (lvl_excl hs hl (placed_lvl2 hs hl hq) ((final_level3 hs hl hN).1 hl3)).elim
    · have hW' : ∀ d', ¬ Wr base (assignTables s.used leaves).2 t3 (index3 v) d' :=
        fun d' h => hW ⟨d', h⟩
      rw [final_entry_old hs hl hW'] at hd
      have hold2 : s.PointsAt base t2 (index2 v) t3 := by
        rcases (final_pointsAt hs hl hN).1 hp2 with ⟨-, h1, -⟩ | ⟨-, h⟩
        · rw [hd, wf_entry_free hs h1] at htb; exact absurd htb (by decide)
        · exact h
      have hold1 : s.PointsAt base 0 (index1 v) t2 := by
        rcases (final_pointsAt hs hl hN).1 hp1 with ⟨-, h1, -⟩ | ⟨-, h⟩
        · exact absurd (wf_entry_free hs h1 _) (pointsAt_ne_zero hold2)
        · exact h
      refine Or.inl ⟨hreg, hal, Or.inl ⟨t2, t3, d, ?_, htb, hk, hpa, hfm⟩⟩
      refine walk_ok_level3.2 ⟨s.entry t2 (index2 v), walk2_ok.2 (Or.inr ⟨t2, isValid_of_isPlain hold1.2.1,
        hold1.2.2, rfl⟩), isValid_of_isPlain hold2.2.1, ?_, hold2.2.2, hd⟩
      rw [typeBits_of_isPlain hold2.2.1]; decide
  · obtain ⟨hw2, hv, hbk⟩ := walk_ok_block.1 hw
    obtain ⟨hp1, hl2, hd⟩ := wf_walk2_some hs' hw2
    by_cases hW : ∃ d', Wr base (assignTables s.used leaves).2 t2 (index2 v) d'
    · obtain ⟨d', hd'⟩ := hW
      have hdd := (final_entry_wr hs hl hN hd').symm.trans hd.symm
      rcases wr_cases hd' with ⟨q, hq, -, rfl, -, -⟩ | ⟨q, hq, -, -, rfl, -, rfl⟩ |
          ⟨q, hq, hp, rfl, -, -⟩ | ⟨q, hq, hp, rfl, hi2, rfl⟩
      · rcases (final_level2 hs hl hN).1 hl2 with h2 | ⟨q', hq', -, ht'⟩
        · exact absurd rfl (wf_level2_ne_zero hs h2)
        · exact absurd ht' (placed_t2_ne_zero hs hl hq')
      · have := isPlain_of_isReadWriteBlock hrw
        rw [← hdd, tableAt, isPlain_tableDescriptor] at this; cases this
      · exact (lvl_excl hs hl ((final_level2 hs hl hN).1 hl2) (placed_lvl3 hs hl hq hp)).elim
      · have e1 := (final_uniq hs hl hN (Or.inl rfl) (Or.inl rfl) hp1 (placed_path hs hl hN hq).1).2
        obtain ⟨hreg', hal', -⟩ := placed_region hl hq
        rw [hp] at hal'
        have hg := gib_of_index1 hreg hreg' e1
        have hb : v.toNat / BLOCK_SIZE = q.leaf.va.toNat / BLOCK_SIZE := by
          rw [block_index, block_index, hg, hi2]
        simp only [Form.size, BLOCK_SIZE] at hal' hb ⊢
        refine Or.inr ⟨q, hq, by omega, by rw [hp]; simp only; omega,
          by rw [hfm, hp], fun hp' => ?_, fun _ => ⟨by rw [hpa, hdd]; simp only [BLOCK_SIZE], hkd⟩⟩
        rw [hp] at hp'; cases hp'
    · have hW' : ∀ d', ¬ Wr base (assignTables s.used leaves).2 t2 (index2 v) d' :=
        fun d' h => hW ⟨d', h⟩
      rw [final_entry_old hs hl hW'] at hd
      have hold1 : s.PointsAt base 0 (index1 v) t2 := by
        rcases (final_pointsAt hs hl hN).1 hp1 with ⟨-, h1, -⟩ | ⟨-, h⟩
        · rw [hd, wf_entry_free hs h1] at hv; exact absurd hv (by decide)
        · exact h
      refine Or.inl ⟨hreg, hal, Or.inr ⟨t2, d, ?_, hrw, hkd, hfm, hpa⟩⟩
      exact walk_ok_block.2 ⟨walk2_ok.2 (Or.inr ⟨t2, isValid_of_isPlain hold1.2.1, hold1.2.2,
        by rw [hd]⟩), hv, hbk⟩

end Final

end Krepi.Proofs.PageTables
