module

public import Krepi.Proofs.PageTables.MapWriteLemmas
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.WalkLemmas
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.WellFormedLemmas
import Krepi.Proofs.PageTables.PoolLemmas

/-!
# Page tables: the abstract mapping after a map

$M$, $G$ and $P$ of the set that a map leaves once its plan has run
(`finalSet`), against those of the set before it, for leaves that passed
their checks in a well-formed set (`LeafFacts`):

- slots of a region: `eq_of_index` and `blk_of_index` (an address of a
  region is determined by its indices, and a 2 MiB-aligned one is the block
  of any address with its root and level 2 indices);
- the walk of any set: `walk2_of_pointsAt` (the walk through a table
  descriptor of the root), `M_unique` ($M$ is a function), `G_of_M` and
  `P_of_M` (a mapped page has its 1 GiB slot in $G$, and a page leaf its
  2 MiB slot in $P$);
- the set after a map: `final_old_M` and `final_new_M`, and
  **`final_M_iff`** ($M'$ is $M$ and the pages of the leaves of the map),
  `leaf_unmapped` (no page of a leaf of the map is in the domain of $M$),
  **`final_G_iff`** and **`final_P_iff`** ($G'$ adds the 1 GiB slots of the
  leaves and $P'$ the 2 MiB slots of the page leaves).

Private steps: an address inside a leaf lies in the region of the leaf and
has its root and level 2 indices; the slots `gib` and `blk` of an address of
a region; the walk through two table descriptors and to a block; the table
descriptors and the nonzero entries of the tables in use stay after a map
(`not_wr_of_lt`); and the placed leaves of a map are its leaves.
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables

variable {r : Region} {N : Nat}

/-! ## Slots of a region -/

private theorem holds_of_block {a v : UInt64} (ha : r.holds a = true) (hal : a.toNat % BLOCK_SIZE = 0)
    (h1 : a.toNat ≤ v.toNat) (h2 : v.toNat < a.toNat + BLOCK_SIZE) : r.holds v = true := by
  cases r with
  | lower =>
    simp only [Region.holds, VA_LIMIT] at ha ⊢
    have ha' : a.toNat < 549755813888 := of_decide_eq_true ha
    simp only [BLOCK_SIZE] at hal h2
    exact decide_eq_true (by omega)
  | upper =>
    simp only [Region.holds, decide_eq_true_eq] at ha ⊢
    exact Nat.le_trans ha h1

private theorem same_block {a v : UInt64} {f : Form} (hal : a.toNat % f.size = 0)
    (h1 : a.toNat ≤ v.toNat) (h2 : v.toNat < a.toNat + f.size) :
    index1 v = index1 a ∧ index2 v = index2 a := by
  simp only [index1, index2, GIB_SIZE, BLOCK_SIZE, ENTRIES]
  generalize a.toNat = x at hal h1 h2
  generalize v.toNat = y at h1 h2
  cases f <;> simp only [Form.size, PAGE_SIZE, BLOCK_SIZE] at hal h2 <;> omega

theorem eq_of_index {a b : UInt64} (ha : r.holds a = true) (hb : r.holds b = true)
    (h1 : index1 a = index1 b) (h2 : index2 a = index2 b) (h3 : index3 a = index3 b)
    (hpa : a.toNat % PAGE_SIZE = 0) (hpb : b.toNat % PAGE_SIZE = 0) : a = b := by
  have hg := gib_of_index1 ha hb h1
  have hk : a.toNat / BLOCK_SIZE = b.toNat / BLOCK_SIZE := by rw [block_index, block_index, hg, h2]
  have hp : a.toNat / PAGE_SIZE = b.toNat / PAGE_SIZE := by rw [page_index, page_index, hk, h3]
  apply UInt64.toNat_inj.1
  generalize a.toNat = x at hpa hp
  generalize b.toNat = y at hpb hp
  simp only [PAGE_SIZE] at hpa hpb hp
  omega

private theorem toNat_down (a : UInt64) (m : Nat) :
    (UInt64.ofNat (a.toNat / m * m)).toNat = a.toNat / m * m :=
  UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) a.toNat_lt)

theorem blk_of_index {a b : UInt64} (ha : r.holds a = true) (hb : r.holds b = true)
    (h1 : index1 a = index1 b) (h2 : index2 a = index2 b) (hal : b.toNat % BLOCK_SIZE = 0) :
    b = blk a := by
  have hg := gib_of_index1 ha hb h1
  have hk : a.toNat / BLOCK_SIZE = b.toNat / BLOCK_SIZE := by rw [block_index, block_index, hg, h2]
  apply UInt64.toNat_inj.1
  rw [blk, toNat_down, hk]
  generalize b.toNat = y at hal
  simp only [BLOCK_SIZE] at hal ⊢
  omega

private theorem gib_of_index {a g : UInt64} (ha : r.holds a = true) (hg : r.holds g = true)
    (h1 : index1 a = index1 g) (hal : g.toNat % GIB_SIZE = 0) : g = gib a := by
  have hk := gib_of_index1 ha hg h1
  apply UInt64.toNat_inj.1
  rw [gib, toNat_down, hk]
  generalize g.toNat = y at hal
  simp only [GIB_SIZE] at hal ⊢
  omega

private theorem blk_facts {a : UInt64} (ha : r.holds a = true) :
    r.holds (blk a) = true ∧ (blk a).toNat % BLOCK_SIZE = 0 ∧ index1 (blk a) = index1 a ∧
      index2 (blk a) = index2 a := by
  have hb : (blk a).toNat = a.toNat / BLOCK_SIZE * BLOCK_SIZE := toNat_down a BLOCK_SIZE
  refine ⟨?_, by rw [hb]; exact Nat.mul_mod_left _ _, ?_, ?_⟩
  · cases r with
    | lower =>
      simp only [Region.holds, VA_LIMIT, hb] at ha ⊢
      have ha' : a.toNat < 549755813888 := of_decide_eq_true ha
      refine decide_eq_true ?_
      generalize a.toNat = x at ha' ⊢
      simp only [BLOCK_SIZE]; omega
    | upper =>
      simp only [Region.holds, decide_eq_true_eq, hb] at ha ⊢
      have hD : DIRECT_BASE.toNat % BLOCK_SIZE = 0 := by decide
      generalize DIRECT_BASE.toNat = D at hD ha ⊢
      generalize a.toNat = x at ha ⊢
      simp only [BLOCK_SIZE] at hD ⊢; omega
  · simp only [index1, hb]
    generalize a.toNat = x
    simp only [GIB_SIZE, BLOCK_SIZE, ENTRIES]; omega
  · simp only [index2, hb]
    generalize a.toNat = x
    simp only [BLOCK_SIZE, ENTRIES]; omega

private theorem gib_facts {a : UInt64} (ha : r.holds a = true) :
    r.holds (gib a) = true ∧ (gib a).toNat % GIB_SIZE = 0 ∧ index1 (gib a) = index1 a := by
  have hb : (gib a).toNat = a.toNat / GIB_SIZE * GIB_SIZE := toNat_down a GIB_SIZE
  refine ⟨?_, by rw [hb]; exact Nat.mul_mod_left _ _, ?_⟩
  · cases r with
    | lower =>
      simp only [Region.holds, VA_LIMIT, hb] at ha ⊢
      have ha' : a.toNat < 549755813888 := of_decide_eq_true ha
      refine decide_eq_true ?_
      generalize a.toNat = x at ha' ⊢
      simp only [GIB_SIZE]; omega
    | upper =>
      simp only [Region.holds, decide_eq_true_eq, hb] at ha ⊢
      have hD : DIRECT_BASE.toNat % GIB_SIZE = 0 := by decide
      generalize DIRECT_BASE.toNat = D at hD ha ⊢
      generalize a.toNat = x at ha ⊢
      simp only [GIB_SIZE] at hD ⊢; omega
  · simp only [index1, hb]
    generalize a.toNat = x
    simp only [GIB_SIZE, ENTRIES]; omega

/-! ## The walk of a set -/

section Walk

variable {s : Tables r N} {base : UInt64}

theorem walk2_of_pointsAt {v : UInt64} {c : Nat} (h : s.PointsAt base 0 (index1 v) c) :
    s.walk2 base v = .ok (some (c, s.entry c (index2 v))) :=
  walk2_ok.2 (Or.inr ⟨c, isValid_of_isPlain h.2.1, h.2.2, rfl⟩)

private theorem walk_of_pointsAt {v : UInt64} {t2 t3 : Nat} (h1 : s.PointsAt base 0 (index1 v) t2)
    (h2 : s.PointsAt base t2 (index2 v) t3) :
    s.walk base v = .ok (.level3 t2 t3 (s.entry t3 (index3 v))) :=
  walk_ok_level3.2 ⟨_, walk2_of_pointsAt h1, isValid_of_isPlain h2.2.1,
    by rw [typeBits_of_isPlain h2.2.1]; decide, h2.2.2, rfl⟩

private theorem walk_of_block {v : UInt64} {t2 : Nat} (h1 : s.PointsAt base 0 (index1 v) t2)
    (h2 : isReadWriteBlock (s.entry t2 (index2 v)) = true) :
    s.walk base v = .ok (.block t2 (s.entry t2 (index2 v))) :=
  walk_ok_block.2 ⟨walk2_of_pointsAt h1, by rw [isValid, typeBits_of_isReadWriteBlock h2]; decide,
    by rw [typeBits_of_isReadWriteBlock h2]; rfl⟩

private theorem walk2_congr {a b : UInt64} (h1 : index1 a = index1 b) (h2 : index2 a = index2 b) :
    s.walk2 base a = s.walk2 base b := by
  unfold Tables.walk2; rw [h1, h2]

/-- $M$ is a function: two leaves of one address are equal. -/
theorem M_unique {v : UInt64} {l l' : Leaf} (h : s.M base v l) (h' : s.M base v l') : l = l' := by
  obtain ⟨-, -, ⟨t2, t3, d, hw, -, hk, hpa, hf⟩ | ⟨t2, d, hw, -, hk, hf, hpa⟩⟩ := h <;>
    obtain ⟨-, -, ⟨t2', t3', d', hw', -, hk', hpa', hf'⟩ | ⟨t2', d', hw', -, hk', hf', hpa'⟩⟩ := h' <;>
    rw [hw] at hw' <;> simp only [Except.ok.injEq, reduceCtorEq, Reach.level3.injEq,
      Reach.block.injEq] at hw'
  · obtain ⟨-, -, rfl⟩ := hw'
    rw [hk] at hk'
    cases l; cases l'
    simp only [Option.some.injEq, Leaf.mk.injEq] at hk' hpa hpa' hf hf' ⊢
    exact ⟨hpa.trans hpa'.symm, hk', hf.trans hf'.symm⟩
  · obtain ⟨-, rfl⟩ := hw'
    cases l; cases l'
    simp only [Leaf.mk.injEq] at hk hk' hf hf' hpa hpa' ⊢
    exact ⟨UInt64.toNat_inj.1 (hpa.trans hpa'.symm), hk.trans hk'.symm, hf.trans hf'.symm⟩

/-- A mapped page has its 1 GiB slot in $G$. -/
theorem G_of_M {v : UInt64} {l : Leaf} (h : s.M base v l) : s.G base (gib v) := by
  obtain ⟨hreg, -, hcase⟩ := h
  obtain ⟨g1, g2, g3⟩ := gib_facts hreg
  have hw2 : ∃ t2 e2, s.walk2 base v = .ok (some (t2, e2)) := by
    rcases hcase with ⟨t2, t3, d, hw, -⟩ | ⟨t2, d, hw, -⟩
    · obtain ⟨e2, hw2, -⟩ := walk_ok_level3.1 hw; exact ⟨t2, e2, hw2⟩
    · exact ⟨t2, d, (walk_ok_block.1 hw).1⟩
  obtain ⟨t2, e2, hw2⟩ := hw2
  rcases walk2_ok.1 hw2 with ⟨-, hn⟩ | ⟨c, hv, hc, -⟩
  · cases hn
  · refine ⟨g1, g2, c, _, walk2_ok.2 (Or.inr ⟨c, ?_, ?_, rfl⟩)⟩ <;> rw [g3]
    · exact hv
    · exact hc

/-- A page leaf of $M$ has its 2 MiB slot in $P$. -/
theorem P_of_M {v : UInt64} {l : Leaf} (h : s.M base v l) (hf : l.form = .page) :
    s.P base (blk v) := by
  obtain ⟨hreg, -, ⟨t2, t3, d, hw, -⟩ | ⟨t2, d, hw, -, -, hf', -⟩⟩ := h
  · obtain ⟨b1, b2, b3, b4⟩ := blk_facts hreg
    obtain ⟨e2, hw2, hv, hb, hc, -⟩ := walk_ok_level3.1 hw
    exact ⟨b1, b2, t2, t3, _, walk_ok_level3.2 ⟨e2, by rw [walk2_congr b3 b4]; exact hw2, hv, hb, hc, rfl⟩⟩
  · rw [hf] at hf'; cases hf'

end Walk

/-! ## The set after a map -/

section Final

variable {s : Tables r N} {base : UInt64} {bits : UInt8} {leaves : List (MapLeaf × Place)}

private theorem final_old_pointsAt (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    (hN : (assignTables s.used leaves).1 ≤ N) {t i c : Nat} (h : s.PointsAt base t i c) :
    (finalSet s base leaves).PointsAt base t i c := by
  have ht : t < s.used := by
    apply Nat.lt_of_not_le; intro ht
    exact pointsAt_ne_zero h (wf_entry_free hs ht i)
  exact (final_pointsAt hs hl hN).2 (Or.inr ⟨not_wr_of_lt hs hl ht (pointsAt_ne_zero h), h⟩)

private theorem final_old_entry (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves) {t i : Nat}
    (ht : t < s.used) (hne : s.entry t i ≠ 0) : (finalSet s base leaves).entry t i = s.entry t i :=
  final_entry_old hs hl (not_wr_of_lt hs hl ht hne)

private theorem placed_of_leaf (hl : LeafFacts s base bits leaves) {x : MapLeaf}
    (hx : x ∈ leaves.map Prod.fst) : ∃ q ∈ (assignTables s.used leaves).2, q.leaf = x := by
  rw [← (assignTables_spec s.used leaves (leaves_mono hl)).1] at hx
  exact List.mem_map.1 hx

private theorem leaf_of_placed (hl : LeafFacts s base bits leaves) {q : Placed}
    (hq : q ∈ (assignTables s.used leaves).2) : q.leaf ∈ leaves.map Prod.fst := by
  rw [← (assignTables_spec s.used leaves (leaves_mono hl)).1]
  exact List.mem_map_of_mem hq

theorem final_old_M (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    (hN : (assignTables s.used leaves).1 ≤ N) {v : UInt64} {l : Leaf} (h : s.M base v l) :
    (finalSet s base leaves).M base v l := by
  obtain ⟨hreg, hal, ⟨t2, t3, d, hw, htb, hk, hpa, hfm⟩ | ⟨t2, d, hw, hrw, hkd, hfm, hpa⟩⟩ := h
  · obtain ⟨e2, hw2, -⟩ := walk_ok_level3.1 hw
    have hp1 := (wf_walk2_some hs hw2).1
    obtain ⟨-, hp2, -, hd⟩ := wf_walk_level3 hs hw
    subst hd
    have hne : s.entry t3 (index3 v) ≠ 0 := by
      intro h0; rw [h0] at htb; exact absurd htb (by decide)
    have he := final_old_entry hs hl (pointsAt_lt hp2).1 hne
    refine ⟨hreg, hal, Or.inl ⟨t2, t3, _, ?_, htb, hk, hpa, hfm⟩⟩
    rw [← he]
    exact walk_of_pointsAt (final_old_pointsAt hs hl hN hp1) (final_old_pointsAt hs hl hN hp2)
  · obtain ⟨hw2, hv, -⟩ := walk_ok_block.1 hw
    obtain ⟨hp1, -, hd⟩ := wf_walk2_some hs hw2
    subst hd
    have hne : s.entry t2 (index2 v) ≠ 0 := by
      intro h0; rw [h0] at hv; exact absurd hv (by decide)
    have he := final_old_entry hs hl (pointsAt_lt hp1).1 hne
    refine ⟨hreg, hal, Or.inr ⟨t2, _, ?_, hrw, hkd, hfm, hpa⟩⟩
    rw [← he]
    exact walk_of_block (final_old_pointsAt hs hl hN hp1) (by rw [he]; exact hrw)

theorem final_new_M (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    (hN : (assignTables s.used leaves).1 ≤ N) {x : MapLeaf} (hx : x ∈ leaves.map Prod.fst)
    {v : UInt64} (hal : v.toNat % PAGE_SIZE = 0) (h1 : x.va.toNat ≤ v.toNat)
    (h2 : v.toNat < x.va.toNat + x.form.size) {l : Leaf} (hf : l.form = x.form)
    (hpg : x.form = .page → l.pa = outputAddress x.desc ∧ Kind.ofPage x.desc = some l.kind)
    (hbk : x.form = .block →
      l.pa.toNat = (blockAddress x.desc).toNat + v.toNat % BLOCK_SIZE ∧ l.kind = .readWrite) :
    (finalSet s base leaves).M base v l := by
  obtain ⟨q, hq, rfl⟩ := placed_of_leaf hl hx
  obtain ⟨hreg, hva, hd⟩ := placed_region hl hq
  obtain ⟨i1, i2⟩ := same_block hva h1 h2
  have hpath := placed_path hs hl hN hq
  cases hfm : q.leaf.form with
  | page =>
    have hv : v = q.leaf.va := by
      rw [hfm] at hva h2
      apply UInt64.toNat_inj.1
      simp only [Form.size, PAGE_SIZE] at hva h2 hal
      omega
    subst hv
    have hent : (finalSet s base leaves).entry q.t3 (index3 q.leaf.va) = q.leaf.desc :=
      final_entry_wr hs hl hN ⟨q, hq, mem_writesOf.2 (Or.inr (Or.inr (by
        simp only [Placed.store, hfm])))⟩
    obtain ⟨⟨k, hk⟩, -⟩ := hd.1 hfm
    obtain ⟨hpa, hkd⟩ := hpg hfm
    refine ⟨hreg, hal, Or.inl ⟨q.t2, q.t3, _, walk_of_pointsAt hpath.1 (hpath.2 hfm), ?_, ?_, ?_, ?_⟩⟩
    · rw [hent, hk]; exact typeBits_descriptor _ _
    · rw [hent]; exact hkd
    · rw [hent]; exact hpa
    · rw [hf, hfm]
  | block =>
    have hp1 := hpath.1
    rw [← i1] at hp1
    have hent : (finalSet s base leaves).entry q.t2 (index2 q.leaf.va) = q.leaf.desc :=
      final_entry_wr hs hl hN ⟨q, hq, mem_writesOf.2 (Or.inr (Or.inr (by
        simp only [Placed.store, hfm])))⟩
    rw [← i2] at hent
    obtain ⟨hrw, -⟩ := hd.2 hfm
    obtain ⟨hpa, hkd⟩ := hbk hfm
    rw [hfm] at hva h2
    refine ⟨holds_of_block hreg hva h1 h2, hal, Or.inr ⟨q.t2, _,
      walk_of_block hp1 (by rw [hent]; exact hrw), by rw [hent]; exact hrw, hkd, by rw [hf, hfm],
      by rw [hent]; exact hpa⟩⟩

/-- **The abstract mapping after a map**: the leaves of the set before it
and the pages of the leaves of the map. -/
theorem final_M_iff (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    (hN : (assignTables s.used leaves).1 ≤ N) {v : UInt64} {l : Leaf} :
    (finalSet s base leaves).M base v l ↔ s.M base v l ∨ ∃ x ∈ leaves.map Prod.fst,
      v.toNat % PAGE_SIZE = 0 ∧ x.va.toNat ≤ v.toNat ∧ v.toNat < x.va.toNat + x.form.size ∧
      l.form = x.form ∧
      (x.form = .page → l.pa = outputAddress x.desc ∧ Kind.ofPage x.desc = some l.kind) ∧
      (x.form = .block →
        l.pa.toNat = (blockAddress x.desc).toNat + v.toNat % BLOCK_SIZE ∧ l.kind = .readWrite) := by
  constructor
  · intro h
    have hal := h.2.1
    rcases final_M hs hl hN h with h | ⟨q, hq, h1, h2, h3, h4, h5⟩
    · exact Or.inl h
    · exact Or.inr ⟨q.leaf, leaf_of_placed hl hq, hal, h1, h2, h3, h4, h5⟩
  · rintro (h | ⟨x, hx, hal, h1, h2, h3, h4, h5⟩)
    · exact final_old_M hs hl hN h
    · exact final_new_M hs hl hN hx hal h1 h2 h3 h4 h5

/-- No page of a leaf of a map is in the domain of $M$ of the set before
it. -/
theorem leaf_unmapped (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    {x : MapLeaf} (hx : x ∈ leaves.map Prod.fst) {v : UInt64} (hal : v.toNat % PAGE_SIZE = 0)
    (h1 : x.va.toNat ≤ v.toNat) (h2 : v.toNat < x.va.toNat + x.form.size) (l : Leaf) :
    ¬ s.M base v l := by
  obtain ⟨lp, hlp, rfl⟩ := List.mem_map.1 hx
  obtain ⟨i1, i2⟩ := same_block (hl.align lp hlp) h1 h2
  have key : ∀ w, s.walk2 base v = .ok w → (∀ t2 e2, w = some (t2, e2) → isValid e2 = false) →
      ¬ s.M base v l := by
    rintro w hw hinv ⟨-, -, ⟨t2, t3, d, hw3, -⟩ | ⟨t2, d, hwb, -⟩⟩
    · obtain ⟨e2, hw2, hv, -⟩ := walk_ok_level3.1 hw3
      rw [hw, Except.ok.injEq] at hw2
      rw [hinv t2 e2 hw2] at hv; exact absurd hv (by decide)
    · obtain ⟨hw2, hv, -⟩ := walk_ok_block.1 hwb
      rw [hw, Except.ok.injEq] at hw2
      rw [hinv t2 d hw2] at hv; exact absurd hv (by decide)
  have hsp := place_spec hs (hl.place lp hlp)
  generalize lp.2 = p at hsp
  cases p with
  | root =>
    refine key none (walk2_ok.2 (Or.inl ⟨?_, rfl⟩)) (fun _ _ h => by cases h)
    rw [i1, hsp]; decide
  | level2 t2 =>
    refine key _ (walk2_of_pointsAt (by rw [i1]; exact hsp.1)) (fun t e h => ?_)
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [i2, hsp.2.2]; decide
  | level3 t2 t3 =>
    obtain ⟨hpg, hp1, -, hp2, -, h0⟩ := hsp
    have hv : v = lp.1.va := by
      have := hl.align lp hlp
      rw [hpg] at this h2
      apply UInt64.toNat_inj.1
      simp only [Form.size, PAGE_SIZE] at this h2 hal
      omega
    subst hv
    rintro ⟨-, -, ⟨t2', t3', d, hw3, htb, -⟩ | ⟨t2', d, hwb, -⟩⟩
    · rw [walk_of_pointsAt hp1 hp2, Except.ok.injEq, Reach.level3.injEq] at hw3
      obtain ⟨-, -, rfl⟩ := hw3
      rw [h0] at htb; exact absurd htb (by decide)
    · rw [walk_of_pointsAt hp1 hp2] at hwb; cases hwb

/-- **$G$ after a map**: that of the set before it and the 1 GiB slots of
the leaves. -/
theorem final_G_iff (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    (hN : (assignTables s.used leaves).1 ≤ N) {g : UInt64} :
    (finalSet s base leaves).G base g ↔ s.G base g ∨ ∃ x ∈ leaves.map Prod.fst, g = gib x.va := by
  have huniq := (final_wf hs hl hN).2.2.2.2.2.2.2.2.2
  constructor
  · rintro ⟨hreg, hal, t2, e2, hw⟩
    have hp := (wf_walk2_some (final_wf hs hl hN) hw).1
    rcases (final_level2 hs hl hN).1 ⟨_, hp⟩ with ⟨j, hj⟩ | ⟨q, hq, -, rfl⟩
    · obtain ⟨-, rfl⟩ := huniq _ _ _ _ _ (Or.inl rfl) (Or.inl rfl) (final_old_pointsAt hs hl hN hj) hp
      exact Or.inl ⟨hreg, hal, _, _, walk2_of_pointsAt hj⟩
    · obtain ⟨-, e⟩ := huniq _ _ _ _ _ (Or.inl rfl) (Or.inl rfl) (placed_path hs hl hN hq).1 hp
      exact Or.inr ⟨q.leaf, leaf_of_placed hl hq, gib_of_index (placed_region hl hq).1 hreg e hal⟩
  · rintro (⟨hreg, hal, t2, e2, hw⟩ | ⟨x, hx, rfl⟩)
    · have hp := (wf_walk2_some hs hw).1
      exact ⟨hreg, hal, _, _, walk2_of_pointsAt (final_old_pointsAt hs hl hN hp)⟩
    · obtain ⟨q, hq, rfl⟩ := placed_of_leaf hl hx
      obtain ⟨g1, g2, g3⟩ := gib_facts (placed_region hl hq).1
      exact ⟨g1, g2, _, _, walk2_of_pointsAt (by rw [g3]; exact (placed_path hs hl hN hq).1)⟩

/-- **$P$ after a map**: that of the set before it and the 2 MiB slots of
the page leaves. -/
theorem final_P_iff (hs : s.WellFormed base bits) (hl : LeafFacts s base bits leaves)
    (hN : (assignTables s.used leaves).1 ≤ N) {b : UInt64} :
    (finalSet s base leaves).P base b ↔
      s.P base b ∨ ∃ x ∈ leaves.map Prod.fst, x.form = .page ∧ b = blk x.va := by
  have hs' := final_wf hs hl hN
  have huniq := hs'.2.2.2.2.2.2.2.2.2
  constructor
  · rintro ⟨hreg, hal, t2, t3, d, hw⟩
    obtain ⟨e2, hw2, -⟩ := walk_ok_level3.1 hw
    have hp1 := (wf_walk2_some hs' hw2).1
    obtain ⟨hl2, hp2, hl3, -⟩ := wf_walk_level3 hs' hw
    rcases (final_level3 hs hl hN).1 hl3 with ⟨t2', i, ⟨j, hj⟩, hp'⟩ | ⟨q, hq, hpg, -, rfl⟩
    · obtain ⟨rfl, rfl⟩ := huniq _ _ _ _ _ (Or.inr ((final_level2 hs hl hN).2 (Or.inl ⟨j, hj⟩)))
        (Or.inr hl2) (final_old_pointsAt hs hl hN hp') hp2
      obtain ⟨-, rfl⟩ := huniq _ _ _ _ _ (Or.inl rfl) (Or.inl rfl) (final_old_pointsAt hs hl hN hj) hp1
      exact Or.inl ⟨hreg, hal, _, _, _, walk_of_pointsAt hj hp'⟩
    · obtain ⟨hq1, hq2⟩ := placed_path hs hl hN hq
      obtain ⟨rfl, e2⟩ := huniq _ _ _ _ _ (Or.inr ⟨_, hq1⟩) (Or.inr hl2) (hq2 hpg) hp2
      obtain ⟨-, e1⟩ := huniq _ _ _ _ _ (Or.inl rfl) (Or.inl rfl) hq1 hp1
      exact Or.inr ⟨q.leaf, leaf_of_placed hl hq, hpg,
        blk_of_index (placed_region hl hq).1 hreg e1 e2 hal⟩
  · rintro (⟨hreg, hal, t2, t3, d, hw⟩ | ⟨x, hx, hpg, rfl⟩)
    · obtain ⟨e2, hw2, -⟩ := walk_ok_level3.1 hw
      have hp1 := (wf_walk2_some hs hw2).1
      obtain ⟨-, hp2, -, -⟩ := wf_walk_level3 hs hw
      exact ⟨hreg, hal, _, _, _,
        walk_of_pointsAt (final_old_pointsAt hs hl hN hp1) (final_old_pointsAt hs hl hN hp2)⟩
    · obtain ⟨q, hq, rfl⟩ := placed_of_leaf hl hx
      obtain ⟨b1, b2, b3, b4⟩ := blk_facts (placed_region hl hq).1
      obtain ⟨hq1, hq2⟩ := placed_path hs hl hN hq
      exact ⟨b1, b2, _, _, _, walk_of_pointsAt (by rw [b3]; exact hq1) (by rw [b4]; exact hq2 hpg)⟩

end Final

end Krepi.Proofs.PageTables
