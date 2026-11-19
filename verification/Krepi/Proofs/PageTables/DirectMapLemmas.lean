module

public import Krepi.Proofs.PageTables.CountLemmas
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.LeavesLemmas
import Krepi.Proofs.PageTables.WalkLemmas
import Krepi.Proofs.PageTables.ListLemmas

/-!
# Page tables: the pages that `direct_map` maps

The abstract mapping of the direct map's set after `direct_map`, page by
page, against the usable ranges of its boot memory map:

- `usableLeaves_cover`: every page of a usable range lies in a leaf of the
  range, its page leaf or a block leaf that holds it (from the runs of
  `usableLeaves_eq`, or one run of pages when no block fits; privately, the
  members of `pageRun` and `blockRun`);
- `directMap_M_of_usable`: after `direct_map`, every page of a usable range
  is below $2^{39}$ and mapped at its direct address, `ReadWrite`, to itself
  (the walk of the set after the map reaches the placed leaf that holds it,
  `placed_path` and `final_entry_wr`);
- `directMap_M_usable`: after `direct_map`, a page of the abstract mapping is
  one of the set before it or a page of a usable range (`final_M`).
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables Krepi.SpecProperties.PageTables

/-- `omega` after the sizes are written as their values. -/
local macro "size_omega" : tactic =>
  `(tactic| (simp only [PAGE_SIZE, BLOCK_SIZE, directFuel, ENTRIES] at *; omega))

private theorem mem_pageRun : ∀ (k pa j : Nat), j < k → directPage (pa + j * PAGE_SIZE) ∈ pageRun pa k
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, pa, 0, _ => by simp [pageRun]
  | k + 1, pa, j + 1, h => by
    have := mem_pageRun k (pa + PAGE_SIZE) j (by omega)
    rw [show pa + PAGE_SIZE + j * PAGE_SIZE = pa + (j + 1) * PAGE_SIZE by
      simp only [PAGE_SIZE]; omega] at this
    exact List.mem_cons_of_mem _ this

private theorem mem_blockRun : ∀ (k pa j : Nat), j < k → directBlock (pa + j * BLOCK_SIZE) ∈ blockRun pa k
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, pa, 0, _ => by simp [blockRun]
  | k + 1, pa, j + 1, h => by
    have := mem_blockRun k (pa + BLOCK_SIZE) j (by omega)
    rw [show pa + BLOCK_SIZE + j * BLOCK_SIZE = pa + (j + 1) * BLOCK_SIZE by
      simp only [BLOCK_SIZE]; omega] at this
    exact List.mem_cons_of_mem _ this

/-- Every page of a usable range lies in a leaf of the range: its page leaf,
or a block leaf that holds it. -/
theorem usableLeaves_cover {bits : UInt8} {u : Krepi.Spec.Fdt.Span} (hu : UsableOk bits u)
    {q : Nat} (hq : q % PAGE_SIZE = 0) (h1 : u.start.toNat ≤ q) (h2 : q + PAGE_SIZE ≤ u.endNat) :
    directPage q ∈ usableLeaves u ∨
      ∃ b, directBlock b ∈ usableLeaves u ∧ b % BLOCK_SIZE = 0 ∧ b ≤ q ∧ q < b + BLOCK_SIZE := by
  obtain ⟨ha, he, -, -⟩ := hu
  generalize hA : u.start.toNat = a at ha h1
  generalize hE : u.endNat = e at he h2
  obtain ⟨b0, hb0⟩ : ∃ b0, b0 = (a + BLOCK_SIZE - 1) / BLOCK_SIZE * BLOCK_SIZE := ⟨_, rfl⟩
  by_cases hb : b0 ≤ e
  · obtain ⟨e0, he0⟩ : ∃ e0, e0 = e / BLOCK_SIZE * BLOCK_SIZE := ⟨_, rfl⟩
    rw [usableLeaves_eq a e ((b0 - a) / PAGE_SIZE) ((e0 - b0) / BLOCK_SIZE) ((e - e0) / PAGE_SIZE)
      hA hE (fun j hj => by size_omega) (by size_omega) (fun j hj => by size_omega) (by size_omega)
      (by size_omega)]
    by_cases hq1 : q < b0
    · left
      have := mem_pageRun ((b0 - a) / PAGE_SIZE) a ((q - a) / PAGE_SIZE) (by size_omega)
      rw [show a + (q - a) / PAGE_SIZE * PAGE_SIZE = q by size_omega] at this
      exact List.mem_append_left _ (List.mem_append_left _ this)
    by_cases hq2 : q < e0
    · right
      have := mem_blockRun ((e0 - b0) / BLOCK_SIZE) (a + (b0 - a) / PAGE_SIZE * PAGE_SIZE)
        ((q - b0) / BLOCK_SIZE) (by size_omega)
      exact ⟨_, List.mem_append_left _ (List.mem_append_right _ this), by size_omega, by size_omega,
        by size_omega⟩
    · left
      have := mem_pageRun ((e - e0) / PAGE_SIZE)
        (a + (b0 - a) / PAGE_SIZE * PAGE_SIZE + (e0 - b0) / BLOCK_SIZE * BLOCK_SIZE)
        ((q - e0) / PAGE_SIZE) (by size_omega)
      rw [show a + (b0 - a) / PAGE_SIZE * PAGE_SIZE + (e0 - b0) / BLOCK_SIZE * BLOCK_SIZE +
        (q - e0) / PAGE_SIZE * PAGE_SIZE = q by size_omega] at this
      exact List.mem_append_right _ this
  · left
    unfold usableLeaves
    rw [hA, hE, show directFuel (e - a) = (directFuel (e - a) - (e - a) / PAGE_SIZE) +
      (e - a) / PAGE_SIZE by size_omega, directLeaves_pages _ _ _ (fun j hj => by size_omega) (by size_omega)]
    have := mem_pageRun ((e - a) / PAGE_SIZE) a ((q - a) / PAGE_SIZE) (by size_omega)
    rw [show a + (q - a) / PAGE_SIZE * PAGE_SIZE = q by size_omega] at this
    exact List.mem_append_left _ this

private theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (UInt64.ofNat n).toNat = n := by
  rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt h

/-- After `direct_map`, every page of a usable range of its boot memory map
is below $2^{39}$ and mapped at its direct address, `ReadWrite`, to itself. -/
theorem directMap_M_of_usable {N : Nat} {s s₁ : Tables .upper N} {B : Krepi.Spec.Fdt.MemoryPlan}
    {base : UInt64} {bits : UInt8} {plan : Plan} (hs : s.WellFormed base bits)
    (h : s.directMap B base bits = .ok (s₁, plan)) {u : Krepi.Spec.Fdt.Span}
    (hu : u ∈ B.availableRanges) {q : Nat} (hq : q % PAGE_SIZE = 0) (h1 : u.start.toNat ≤ q)
    (h2 : q + PAGE_SIZE ≤ u.endNat) :
    q < VA_LIMIT ∧
      ∃ f, (s₁.apply plan).M base (DIRECT_BASE ||| UInt64.ofNat q) ⟨UInt64.ofNat q, .readWrite, f⟩ := by
  obtain ⟨leaves, hlf, happ, hN, -, -, -, hmap, hok⟩ := directMap_facts hs h
  have hu' : u ∈ sortByKey (·.start.toNat) B.availableRanges := (sortByKey_perm _ _).symm.subset hu
  have hlim := (hok u hu').2.2.1
  have hqv : q < VA_LIMIT := by simp only [PAGE_SIZE] at h2; omega
  have hqn : (UInt64.ofNat q).toNat = q := toNat_ofNat_lt (by simp only [VA_LIMIT] at hqv; omega)
  have hv : (DIRECT_BASE ||| UInt64.ofNat q).toNat = DIRECT_BASE.toNat + q := by
    rw [direct_or (by rw [hqn]; exact hqv), hqn]
  have hD : DIRECT_BASE.toNat % GIB_SIZE = 0 := by decide
  have hreg : Region.upper.holds (DIRECT_BASE ||| UInt64.ofNat q) = true := by
    simp only [Region.holds, decide_eq_true_eq, hv]; exact Nat.le_add_right _ _
  have hal : (DIRECT_BASE ||| UInt64.ofNat q).toNat % PAGE_SIZE = 0 := by
    rw [hv]; generalize DIRECT_BASE.toNat = D at hD; simp only [GIB_SIZE, PAGE_SIZE] at hD hq ⊢
    omega
  have hplaced : ∀ x ∈ usableLeaves u, ∃ p ∈ (assignTables s.used leaves).2, p.leaf = x := by
    intro x hx
    have hx' : x ∈ leaves.map Prod.fst := by rw [hmap]; exact List.mem_flatMap.2 ⟨u, hu', hx⟩
    rw [← (assignTables_spec s.used leaves (leaves_mono hlf)).1] at hx'
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx'
    exact ⟨p, hp, rfl⟩
  refine ⟨hqv, ?_⟩
  rw [happ]
  rcases usableLeaves_cover (hok u hu') hq h1 h2 with hx | ⟨b, hx, hb1, hb2, hb3⟩
  · obtain ⟨p, hp, hpx⟩ := hplaced _ hx
    have hform : p.leaf.form = .page := by rw [hpx]; rfl
    have hva : p.leaf.va = DIRECT_BASE ||| UInt64.ofNat q := by rw [hpx]; rfl
    have hdesc : p.leaf.desc = descriptor .readWrite (UInt64.ofNat q) := by rw [hpx]; rfl
    obtain ⟨hp1, hp2⟩ := placed_path hs hlf hN hp
    have hp2 := hp2 hform
    have hent : (finalSet s base leaves).entry p.t3 (index3 p.leaf.va) = p.leaf.desc :=
      final_entry_wr hs hlf hN ⟨p, hp, mem_writesOf.2 (Or.inr (Or.inr (by
        simp only [Placed.store, hform])))⟩
    rw [hva] at hp1 hp2 hent
    rw [hdesc] at hent
    refine ⟨.page, hreg, hal, Or.inl ⟨p.t2, p.t3, _, walk_ok_level3.2 ⟨_, walk2_ok.2 (Or.inr
      ⟨p.t2, isValid_of_isPlain hp1.2.1, hp1.2.2, rfl⟩), isValid_of_isPlain hp2.2.1,
      by rw [typeBits_of_isPlain hp2.2.1]; decide, hp2.2.2, rfl⟩, ?_, ?_, ?_, rfl⟩⟩
    · rw [hent]; exact typeBits_descriptor _ _
    · rw [hent]; exact ofPage_descriptor _ _
    · rw [hent, outputAddress_descriptor, outputAddress_of_aligned (by rw [hqn]; exact hq)
        (by rw [hqn]; simp only [VA_LIMIT] at hqv; omega)]
  · obtain ⟨p, hp, hpx⟩ := hplaced _ hx
    have hbv : b < VA_LIMIT := by omega
    have hbn : (UInt64.ofNat b).toNat = b := toNat_ofNat_lt (by simp only [VA_LIMIT] at hbv; omega)
    have hform : p.leaf.form = .block := by rw [hpx]; rfl
    have hva : (p.leaf.va).toNat = DIRECT_BASE.toNat + b := by
      rw [hpx]; show (DIRECT_BASE ||| UInt64.ofNat b).toNat = _
      rw [direct_or (by rw [hbn]; exact hbv), hbn]
    have hdesc : p.leaf.desc = blockDescriptor (UInt64.ofNat b) := by rw [hpx]; rfl
    have hp1 := (placed_path hs hlf hN hp).1
    have hent : (finalSet s base leaves).entry p.t2 (index2 p.leaf.va) = p.leaf.desc :=
      final_entry_wr hs hlf hN ⟨p, hp, mem_writesOf.2 (Or.inr (Or.inr (by
        simp only [Placed.store, hform])))⟩
    have hi1 : index1 (DIRECT_BASE ||| UInt64.ofNat q) = index1 p.leaf.va := by
      unfold index1; rw [hv, hva]
      have key : (DIRECT_BASE.toNat + q) / GIB_SIZE = (DIRECT_BASE.toNat + b) / GIB_SIZE := by
        generalize DIRECT_BASE.toNat = D at hD
        simp only [GIB_SIZE, BLOCK_SIZE] at hD hb1 hb2 hb3 ⊢
        omega
      rw [key]
    have hi2 : index2 (DIRECT_BASE ||| UInt64.ofNat q) = index2 p.leaf.va := by
      unfold index2; rw [hv, hva]
      have key : (DIRECT_BASE.toNat + q) / BLOCK_SIZE = (DIRECT_BASE.toNat + b) / BLOCK_SIZE := by
        generalize DIRECT_BASE.toNat = D at hD
        simp only [GIB_SIZE, BLOCK_SIZE] at hD hb1 hb2 hb3 ⊢
        omega
      rw [key]
    rw [← hi1] at hp1
    rw [← hi2, hdesc] at hent
    refine ⟨.block, hreg, hal, Or.inr ⟨p.t2, _, walk_ok_block.2 ⟨walk2_ok.2 (Or.inr
      ⟨p.t2, isValid_of_isPlain hp1.2.1, hp1.2.2, rfl⟩), ?_, ?_⟩, ?_, rfl, rfl, ?_⟩⟩
    · rw [hent]; simp [isValid, typeBits_blockDescriptor, BLOCK]
    · rw [hent, typeBits_blockDescriptor]; rfl
    · rw [hent]; exact isReadWriteBlock_blockDescriptor _
    · rw [hent, blockAddress_blockDescriptor, blockAddress_of_aligned (by rw [hbn]; exact hb1)
        (by rw [hbn]; simp only [VA_LIMIT] at hbv; omega), hbn, hqn, hv]
      generalize DIRECT_BASE.toNat = D at hD
      simp only [GIB_SIZE, BLOCK_SIZE] at hD hb1 hb3 ⊢
      omega

/-- After `direct_map`, a page of the abstract mapping is one of the set
before it, or one of a usable range of its boot memory map. -/
theorem directMap_M_usable {N : Nat} {s s₁ : Tables .upper N} {B : Krepi.Spec.Fdt.MemoryPlan}
    {base : UInt64} {bits : UInt8} {plan : Plan} (hs : s.WellFormed base bits)
    (h : s.directMap B base bits = .ok (s₁, plan)) {v : UInt64} {l : Leaf}
    (hm : (s₁.apply plan).M base v l) :
    s.M base v l ∨ ∃ u ∈ B.availableRanges, u.start.toNat ≤ l.pa.toNat ∧
      l.pa.toNat + PAGE_SIZE ≤ u.endNat := by
  obtain ⟨leaves, hlf, happ, hN, -, -, -, hmap, hok⟩ := directMap_facts hs h
  have hvp := hm.2.1
  rw [happ] at hm
  rcases final_M hs hlf hN hm with hold | ⟨q, hq, h1, h2, -, hpg, hbk⟩
  · exact Or.inl hold
  obtain ⟨pl, hqm, -⟩ := placed_leaf hlf hq
  have hx : q.leaf ∈ leaves.map Prod.fst := List.mem_map.2 ⟨_, hqm, rfl⟩
  rw [hmap] at hx
  obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.1 hx
  obtain ⟨hs1, hs2, hdl⟩ := (usableLeaves_spec (hok u hu)).1 _ hxu
  have hlim := (hok u hu).2.2.1
  have hva' := directLeaf_va hdl (by have := form_size_pos q.leaf.form; omega)
  obtain ⟨-, hal, hpage, hblock⟩ := hdl
  refine Or.inr ⟨u, (sortByKey_perm _ _).subset hu, ?_⟩
  cases hf : q.leaf.form with
  | page =>
    obtain ⟨hpa, -⟩ := hpg hf
    rw [hf] at hal hs2
    rw [hpage hf, outputAddress_descriptor,
      outputAddress_of_aligned hal (by simp only [VA_LIMIT, Form.size] at hlim hs2 ⊢; omega)] at hpa
    rw [hpa]
    simp only [Form.size] at hs2
    exact ⟨hs1, hs2⟩
  | block =>
    obtain ⟨hpa, -⟩ := hbk hf
    rw [hf] at hal hs2 h2
    rw [hblock hf, blockAddress_blockDescriptor,
      blockAddress_of_aligned hal (by simp only [VA_LIMIT, Form.size] at hlim hs2 ⊢; omega)] at hpa
    have hD : DIRECT_BASE.toNat % BLOCK_SIZE = 0 := by decide
    rw [hpa]
    rw [hva'] at h1 h2
    generalize DIRECT_BASE.toNat = D at hD h1 h2
    simp only [Form.size, BLOCK_SIZE, PAGE_SIZE] at hD hal hs2 h1 h2 hvp ⊢
    omega

end Krepi.Proofs.PageTables
