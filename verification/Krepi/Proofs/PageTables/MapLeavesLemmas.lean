module

public import Krepi.Proofs.PageTables.AssignLemmas
public import Krepi.Proofs.PageTables.WellFormedLemmas
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.WalkLemmas
import Krepi.Proofs.PageTables.BitLemmas

/-!
# Page tables: lemmas about the placed leaves of a map

What the checks of `kernel_map` and `direct_map` tell about the leaves of a
map in a well-formed set (`LeafFacts`: each leaf in its place, in the region,
aligned, with a descriptor that the set takes, the leaves in address order),
and what follows for the tables of their placed leaves:

- `PlaceSpec` and `place_spec`: the entries of the walk of a leaf in its
  place;
- slots: `gib_of_index1`, `block_index`, `page_index` (from the private
  `gib_index`: the 1 GiB slot of an address of a region is its root index
  past the first slot of the region);
- `pointsAt_inj`, `pointsAt_ne_zero`, `pairwise_mem`, `form_size_pos`;
- `LeafDesc`, `LeafFacts`;
- the placed leaves of `assignTables`: `leaves_mono`, `placed_order`,
  `placed_leaf`, `placed_new2`, `placed_old2`, `placed_new3`,
  `placed_block` (the entries that a leaf writes in a table of the set are
  free, and the tables that it does not take new are the tables of its
  walk), `placed_range`, `placed_lt2`, `placed_lt3` (new tables lie at or
  above the record, the others below), `placed_region`, `placed_t2eq`,
  `placed_t3eq` (one table, one slot), `placed_apart` (a level 2 table is no
  level 3 table), `placed_distinct`, `placed_blockOne` and `placed_ok` (the
  placed leaves are `PlacedOk`: one slot, one table, by private steps).
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables

variable {r : Region} {N : Nat}

/-- What the walk of a leaf tells about its place in a well-formed set. -/
def PlaceSpec (s : Tables r N) (base : UInt64) (l : MapLeaf) : Place → Prop
  | .root => s.entry 0 (index1 l.va) = 0
  | .level2 t2 => s.PointsAt base 0 (index1 l.va) t2 ∧ s.IsLevel2 base t2 ∧ s.entry t2 (index2 l.va) = 0
  | .level3 t2 t3 => l.form = .page ∧ s.PointsAt base 0 (index1 l.va) t2 ∧ s.IsLevel2 base t2 ∧
    s.PointsAt base t2 (index2 l.va) t3 ∧ s.IsLevel3 base t3 ∧ s.entry t3 (index3 l.va) = 0

theorem place_spec {s : Tables r N} {base : UInt64} {bits : UInt8} (hs : s.WellFormed base bits)
    {l : MapLeaf} {p : Place} (h : s.place base l = .ok p) : PlaceSpec s base l p := by
  unfold Tables.place at h
  cases hw : s.walk2 base l.va with
  | error e => rw [hw] at h; cases h
  | ok w =>
    rw [hw] at h
    rcases w with _ | ⟨t2, e2⟩
    · simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h; exact wf_walk2_none hs hw
    · obtain ⟨hpt, hl2, he2⟩ := wf_walk2_some hs hw
      subst he2
      cases hf : l.form <;> cases hv : isValid (s.entry t2 (index2 l.va))
      · simp only [hf, hv, bind, Except.bind, pure, Except.pure, Bool.not_false, ite_true,
          Except.ok.injEq] at h
        subst h; exact ⟨hpt, hl2, wf_level2_invalid hs hl2 (index2_lt _) hv⟩
      · cases hb : (typeBits (s.entry t2 (index2 l.va)) == BLOCK)
        · cases hc : s.child? base (s.entry t2 (index2 l.va)) with
          | none =>
            simp [hf, hv, hb, hc, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
          | some t3 =>
            cases hv3 : isValid (s.entry t3 (index3 l.va)) <;>
              simp [hf, hv, hb, hc, hv3, bind, Except.bind, pure, Except.pure, throw, throwThe,
                MonadExceptOf.throw] at h
            subst h
            obtain ⟨hp3, hl3⟩ := wf_level2_table hs hl2 (index2_lt _) hv hb hc
            exact ⟨hf, hpt, hl2, hp3, hl3, wf_level3_invalid hs hl3 (index3_lt _) hv3⟩
        · simp [hf, hv, hb, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
      · simp only [hf, hv, bind, Except.bind, pure, Except.pure, Bool.not_false, ite_true,
          Except.ok.injEq] at h
        subst h; exact ⟨hpt, hl2, wf_level2_invalid hs hl2 (index2_lt _) hv⟩
      · simp only [hf, hv, bind, Except.bind, pure, Except.pure, Bool.not_true, Bool.false_eq_true,
          ite_false] at h
        split at h <;> simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## Slots in a region -/

private theorem gib_index {v : UInt64} (hv : r.holds v = true) :
    v.toNat / GIB_SIZE = r.first / GIB_SIZE + index1 v := by
  have hlt := v.toNat_lt
  cases r with
  | lower =>
    simp only [Region.holds, VA_LIMIT] at hv
    have : v.toNat < 549755813888 := of_decide_eq_true hv
    simp only [Region.first, index1, GIB_SIZE, ENTRIES]; omega
  | upper =>
    simp only [Region.holds, decide_eq_true_eq] at hv
    have hD : DIRECT_BASE.toNat = 2 ^ 30 * (2 ^ 34 - 512) := by decide
    simp only [Region.first, index1, GIB_SIZE, ENTRIES]
    rw [hD] at hv ⊢
    generalize v.toNat = x at hv hlt ⊢
    omega

theorem gib_of_index1 {a b : UInt64} (ha : r.holds a = true) (hb : r.holds b = true)
    (h : index1 a = index1 b) : a.toNat / GIB_SIZE = b.toNat / GIB_SIZE := by
  rw [gib_index ha, gib_index hb, h]

theorem block_index (a : UInt64) : a.toNat / BLOCK_SIZE = a.toNat / GIB_SIZE * ENTRIES + index2 a := by
  simp only [index2, BLOCK_SIZE, GIB_SIZE, ENTRIES]; omega

theorem page_index (a : UInt64) : a.toNat / PAGE_SIZE = a.toNat / BLOCK_SIZE * ENTRIES + index3 a := by
  simp only [index3, BLOCK_SIZE, PAGE_SIZE, ENTRIES]; omega

/-! ## Two pointers -/

theorem pointsAt_inj {s : Tables r N} {base : UInt64} {t i c c' : Nat}
    (h : s.PointsAt base t i c) (h' : s.PointsAt base t i c') : c = c' := by
  have := h.2.2.symm.trans h'.2.2; simpa using this

theorem pointsAt_ne_zero {s : Tables r N} {base : UInt64} {t i c : Nat} (h : s.PointsAt base t i c) :
    s.entry t i ≠ 0 := by
  intro e; have := h.2.1; rw [e, isPlain_zero] at this; cases this

theorem pairwise_mem {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R → ∀ {a b}, a ∈ l → b ∈ l → a = b ∨ R a b ∨ R b a
  | [], _, _, _, ha, _ => absurd ha (by simp)
  | x :: rest, h, a, b, ha, hb => by
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.1 ha with h1 | h1 <;> rcases List.mem_cons.1 hb with h2 | h2
    · exact Or.inl (h1.trans h2.symm)
    · subst h1; exact Or.inr (Or.inl (h.1 b h2))
    · subst h2; exact Or.inr (Or.inr (h.1 a h1))
    · exact pairwise_mem h.2 h1 h2

/-! ## The leaves of a map and their tables -/

/-- The descriptor of a leaf as the set takes it: a page descriptor of a kind
below $2^{\mathrm{bits}}$, or the block descriptor of `ReadWrite` below it. -/
def LeafDesc (bits : UInt8) (l : MapLeaf) : Prop :=
  (l.form = .page → (∃ k, l.desc = descriptor k (outputAddress l.desc)) ∧
    (outputAddress l.desc).toNat < 2 ^ bits.toNat) ∧
  (l.form = .block → isReadWriteBlock l.desc = true ∧ (blockAddress l.desc).toNat < 2 ^ bits.toNat)

/-- The leaves of a map that passed their checks, in address order: each in
its place in the set, in the region, aligned to its form, with a descriptor
that the set takes, and each ending at or before the next. -/
structure LeafFacts (s : Tables r N) (base : UInt64) (bits : UInt8) (leaves : List (MapLeaf × Place)) :
    Prop where
  place : ∀ lp ∈ leaves, s.place base lp.1 = .ok lp.2
  order : (leaves.map Prod.fst).Pairwise (fun a b => a.va.toNat + a.form.size ≤ b.va.toNat)
  region : ∀ lp ∈ leaves, r.holds lp.1.va = true
  align : ∀ lp ∈ leaves, lp.1.va.toNat % lp.1.form.size = 0
  desc : ∀ lp ∈ leaves, LeafDesc bits lp.1

theorem form_size_pos (f : Form) : 0 < f.size := by cases f <;> decide

section Placed

variable {s : Tables r N} {base : UInt64} {bits : UInt8} {leaves : List (MapLeaf × Place)}

theorem leaves_mono (hl : LeafFacts s base bits leaves) :
    (leaves.map Prod.fst).Pairwise (fun x y => x.va.toNat ≤ y.va.toNat) :=
  hl.order.imp fun h => by omega

theorem placed_order (hl : LeafFacts s base bits leaves) :
    (assignTables s.used leaves).2.Pairwise
      (fun q q' => q.leaf.va.toNat + q.leaf.form.size ≤ q'.leaf.va.toNat) := by
  have := hl.order
  rw [← (assignTables_spec s.used leaves (leaves_mono hl)).1, List.pairwise_map] at this
  exact this

theorem placed_leaf (hl : LeafFacts s base bits leaves) {q : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) : ∃ p, (q.leaf, p) ∈ leaves ∧ Matches q p := by
  have := (assignTables_spec s.used leaves (leaves_mono hl)).2.1
  exact this q hq

private theorem placed_place (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) :
    ∃ p, (q.leaf, p) ∈ leaves ∧ Matches q p ∧ PlaceSpec s base q.leaf p := by
  obtain ⟨p, hp, hmq⟩ := placed_leaf hl hq
  have h : s.place base q.leaf = .ok p := hl.place (q.leaf, p) hp
  exact ⟨p, hp, hmq, place_spec hs h⟩

theorem placed_new2 (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) (hn : q.new2 = true) :
    s.entry 0 (index1 q.leaf.va) = 0 := by
  obtain ⟨p, -, hmq, hsp⟩ := placed_place hs hl hq
  cases p with
  | root => exact hsp
  | level2 _ => exact absurd (hn.symm.trans hmq.1) (by decide)
  | level3 _ _ => exact absurd (hn.symm.trans hmq.1) (by decide)

theorem placed_old2 (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) (hn : q.new2 = false) :
    s.PointsAt base 0 (index1 q.leaf.va) q.t2 ∧ s.IsLevel2 base q.t2 := by
  obtain ⟨p, -, hmq, hsp⟩ := placed_place hs hl hq
  cases p with
  | root => exact absurd (hn.symm.trans hmq.1) (by decide)
  | level2 t2 => rw [hmq.2.1]; exact ⟨hsp.1, hsp.2.1⟩
  | level3 t2 t3 => rw [hmq.2.1]; exact ⟨hsp.2.1, hsp.2.2.1⟩

theorem placed_new3 (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) (hp : q.leaf.form = .page) :
    (q.new2 = true → q.new3 = true) ∧
    (q.new3 = true → q.new2 = false → s.entry q.t2 (index2 q.leaf.va) = 0) ∧
    (q.new3 = false → q.new2 = false ∧ s.PointsAt base q.t2 (index2 q.leaf.va) q.t3 ∧
      s.IsLevel3 base q.t3 ∧ s.entry q.t3 (index3 q.leaf.va) = 0) := by
  obtain ⟨p, -, hmq, hsp⟩ := placed_place hs hl hq
  cases p with
  | root => exact ⟨fun _ => hmq.2 hp, fun _ hn => absurd (hn.symm.trans hmq.1) (by decide),
      fun h3 => absurd (h3.symm.trans (hmq.2 hp)) (by decide)⟩
  | level2 t2 => exact ⟨fun hn => absurd (hn.symm.trans hmq.1) (by decide),
      fun _ _ => by rw [hmq.2.1]; exact hsp.2.2,
      fun h3 => absurd (h3.symm.trans (hmq.2.2 hp)) (by decide)⟩
  | level3 t2 t3 =>
    exact ⟨fun hn => absurd (hn.symm.trans hmq.1) (by decide),
      fun h3 => absurd (h3.symm.trans (hmq.2.2 hp).1) (by decide),
      fun _ => ⟨hmq.1, by rw [hmq.2.1, (hmq.2.2 hp).2]; exact ⟨hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩⟩⟩

theorem placed_block (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) (hb : q.leaf.form = .block) (hn : q.new2 = false) :
    s.entry q.t2 (index2 q.leaf.va) = 0 := by
  obtain ⟨p, -, hmq, hsp⟩ := placed_place hs hl hq
  cases p with
  | root => exact absurd (hn.symm.trans hmq.1) (by decide)
  | level2 t2 => rw [hmq.2.1]; exact hsp.2.2
  | level3 t2 t3 => exact absurd (hb.symm.trans hsp.1) (by decide)

theorem placed_range (hl : LeafFacts s base bits leaves) {q : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) {c : Nat} (hc : NewTable q c) :
    s.used ≤ c ∧ c < (assignTables s.used leaves).1 := by
  have := (assignTables_spec s.used leaves (leaves_mono hl)).2.2.2.1
  exact this q hq c hc

theorem placed_lt2 (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) : (q.new2 = false → q.t2 < s.used) ∧
      (q.new2 = true → s.used ≤ q.t2) := by
  refine ⟨fun hn => (wf_level2_lt (placed_old2 hs hl hq hn).2).1, fun hn => ?_⟩
  exact (placed_range hl hq (Or.inl ⟨hn, rfl⟩)).1

theorem placed_lt3 (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) (hp : q.leaf.form = .page) :
    (q.new3 = false → q.t3 < s.used) ∧ (q.new3 = true → s.used ≤ q.t3) := by
  refine ⟨fun hn => (wf_level3_lt ((placed_new3 hs hl hq hp).2.2 hn).2.2.1).1, fun hn => ?_⟩
  exact (placed_range hl hq (Or.inr ⟨hp, hn, rfl⟩)).1

theorem placed_region (hl : LeafFacts s base bits leaves) {q : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) :
    r.holds q.leaf.va = true ∧ q.leaf.va.toNat % q.leaf.form.size = 0 ∧ LeafDesc bits q.leaf := by
  obtain ⟨p, hp, -⟩ := placed_leaf hl hq
  exact ⟨hl.region _ hp, hl.align _ hp, hl.desc _ hp⟩

theorem placed_t2eq (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q q' : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) (hq' : q' ∈ (assignTables s.used leaves).2)
    (he : q.t2 = q'.t2) : q.leaf.gibSlot = q'.leaf.gibSlot := by
  have h1 := placed_lt2 hs hl hq
  have h2 := placed_lt2 hs hl hq'
  cases hn : q.new2 <;> cases hn' : q'.new2
  · have := hs.2.2.2.2.2.2.2.2.2 0 _ 0 _ _ (Or.inl rfl) (Or.inl rfl) (placed_old2 hs hl hq hn).1
      (he ▸ (placed_old2 hs hl hq' hn').1)
    exact gib_of_index1 (placed_region hl hq).1 (placed_region hl hq').1 this.2
  · have := h1.1 hn; have := h2.2 hn'; omega
  · have := h1.2 hn; have := h2.1 hn'; omega
  · have := (assignTables_spec s.used leaves (leaves_mono hl)).2.2.2.2.2.1
    exact (this q hq q' hq' hn hn').1 he

private theorem placed_parent (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) (hp : q.leaf.form = .page) (hn : q.new3 = false) :
    s.IsParent base q.t2 :=
  Or.inr (placed_old2 hs hl hq ((placed_new3 hs hl hq hp).2.2 hn).1).2

theorem placed_t3eq (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q q' : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) (hq' : q' ∈ (assignTables s.used leaves).2)
    (hp : q.leaf.form = .page) (hp' : q'.leaf.form = .page) (he : q.t3 = q'.t3) :
    q.leaf.blockSlot = q'.leaf.blockSlot := by
  have h1 := placed_lt3 hs hl hq hp
  have h2 := placed_lt3 hs hl hq' hp'
  cases hn : q.new3 <;> cases hn' : q'.new3
  · obtain ⟨-, a, -, -⟩ := (placed_new3 hs hl hq hp).2.2 hn
    obtain ⟨-, a', -, -⟩ := (placed_new3 hs hl hq' hp').2.2 hn'
    obtain ⟨e2, e2'⟩ := hs.2.2.2.2.2.2.2.2.2 _ _ _ _ _ (placed_parent hs hl hq hp hn)
      (placed_parent hs hl hq' hp' hn') a (he ▸ a')
    have hg := placed_t2eq hs hl hq hq' e2
    simp only [MapLeaf.blockSlot]
    rw [block_index, block_index, e2']
    simp only [MapLeaf.gibSlot] at hg; rw [hg]
  · have := h1.1 hn; have := h2.2 hn'; omega
  · have := h1.2 hn; have := h2.1 hn'; omega
  · have := (assignTables_spec s.used leaves (leaves_mono hl)).2.2.2.2.2.2.1
    exact (this q hq q' hq' hp hn hp' hn').1 he

theorem placed_apart (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q q' : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) (hq' : q' ∈ (assignTables s.used leaves).2)
    (hp' : q'.leaf.form = .page) : q.t2 ≠ q'.t3 := by
  intro he
  have h1 := placed_lt2 hs hl hq
  have h2 := placed_lt3 hs hl hq' hp'
  cases hn : q.new2 <;> cases hn' : q'.new3
  · exact wf_not_level2_level3 hs (placed_old2 hs hl hq hn).2
      (he ▸ ((placed_new3 hs hl hq' hp').2.2 hn').2.2.1)
  · have := h1.1 hn; have := h2.2 hn'; omega
  · have := h1.2 hn; have := h2.1 hn'; omega
  · have := (assignTables_spec s.used leaves (leaves_mono hl)).2.2.2.2.2.2.2
    exact this q hq q' hq' hn hp' hn' he

private theorem placed_gib (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {q q' : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) (hq' : q' ∈ (assignTables s.used leaves).2)
    (hg : q.leaf.gibSlot = q'.leaf.gibSlot) : q.new2 = q'.new2 ∧ q.t2 = q'.t2 := by
  have hi : index1 q.leaf.va = index1 q'.leaf.va := index1_of_gib hg
  cases hn : q.new2 <;> cases hn' : q'.new2
  · exact ⟨rfl, pointsAt_inj (placed_old2 hs hl hq hn).1 (hi ▸ (placed_old2 hs hl hq' hn').1)⟩
  · exact absurd (hi ▸ placed_new2 hs hl hq' hn') (pointsAt_ne_zero (placed_old2 hs hl hq hn).1)
  · exact absurd (hi ▸ placed_new2 hs hl hq hn : s.entry 0 (index1 q'.leaf.va) = 0)
      (pointsAt_ne_zero (placed_old2 hs hl hq' hn').1)
  · have := (assignTables_spec s.used leaves (leaves_mono hl)).2.2.2.2.2.1
    exact ⟨rfl, (this q hq q' hq' hn hn').2 hg⟩

theorem placed_distinct (hl : LeafFacts s base bits leaves) {q q' : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) (hq' : q' ∈ (assignTables s.used leaves).2) :
    q = q' ∨ q.leaf.va.toNat + q.leaf.form.size ≤ q'.leaf.va.toNat ∨
      q'.leaf.va.toNat + q'.leaf.form.size ≤ q.leaf.va.toNat :=
  pairwise_mem (placed_order hl) hq hq'

theorem placed_blockOne (hl : LeafFacts s base bits leaves) {q q' : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) (hq' : q' ∈ (assignTables s.used leaves).2)
    (hb : q.leaf.blockSlot = q'.leaf.blockSlot) (hf : q.leaf.form = .block) : q = q' := by
  have ha : q.leaf.va.toNat % BLOCK_SIZE = 0 := by
    have := (placed_region hl hq).2.1; rwa [hf] at this
  rcases placed_distinct hl hq hq' with h | h | h
  · exact h
  · rw [hf] at h
    simp only [MapLeaf.blockSlot, Form.size, BLOCK_SIZE] at hb h
    have : (q.leaf.va.toNat + 2097152) / 2097152 ≤ q'.leaf.va.toNat / 2097152 := Nat.div_le_div_right h
    omega
  · have := form_size_pos q'.leaf.form
    simp only [MapLeaf.blockSlot, BLOCK_SIZE] at hb ha
    omega

theorem placed_ok (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) :
    PlacedOk (assignTables s.used leaves).2 := by
  refine ⟨(placed_order hl).imp fun h => by omega, fun q hq q' hq' hg => placed_gib hs hl hq hq' hg,
    fun q hq q' hq' hb => ?_, fun q hq q' hq' hb hf => placed_blockOne hl hq hq' hb hf,
    fun q hq hn hp => (placed_new3 hs hl hq hp).1 hn, fun q hq q' hq' hn' => ?_,
    fun q hq q' hq' hp' hn' => ?_⟩
  · by_cases heq : q = q'
    · subst heq; exact ⟨rfl, rfl, rfl⟩
    cases hf : q.leaf.form
    · cases hf' : q'.leaf.form
      · obtain ⟨hn, ht⟩ := placed_gib hs hl hq hq' (gib_of_block hb)
        have hi := index2_of_block hb
        have k := placed_new3 hs hl hq hf
        have k' := placed_new3 hs hl hq' hf'
        cases h3 : q.new3 <;> cases h3' : q'.new3
        · exact ⟨rfl, rfl, pointsAt_inj (k.2.2 h3).2.1 (ht ▸ hi ▸ (k'.2.2 h3').2.1)⟩
        · exfalso
          have := k'.2.1 h3' (hn ▸ (k.2.2 h3).1)
          rw [← ht, ← hi] at this
          exact pointsAt_ne_zero (k.2.2 h3).2.1 this
        · exfalso
          have := k.2.1 h3 (hn.symm ▸ (k'.2.2 h3').1)
          rw [ht, hi] at this
          exact pointsAt_ne_zero (k'.2.2 h3').2.1 this
        · have := (assignTables_spec s.used leaves (leaves_mono hl)).2.2.2.2.2.2.1
          exact ⟨rfl, rfl, (this q hq q' hq' hf h3 hf' h3').2 hb⟩
      · exact absurd (placed_blockOne hl hq' hq hb.symm hf').symm heq
    · exact absurd (placed_blockOne hl hq hq' hb hf) heq
  · refine ⟨fun e => ?_, fun e => placed_t2eq hs hl hq hq' e.symm, fun hp e => placed_apart hs hl hq' hq hp e⟩
    have := (placed_lt2 hs hl hq').2 hn'; have := hs.2.1; omega
  · refine ⟨fun e => ?_, fun e => placed_apart hs hl hq hq' hp' e.symm,
      fun hp e => placed_t3eq hs hl hq hq' hp hp' e.symm⟩
    have := (placed_lt3 hs hl hq' hp').2 hn'; have := hs.2.1; omega

end Placed

end Krepi.Proofs.PageTables
