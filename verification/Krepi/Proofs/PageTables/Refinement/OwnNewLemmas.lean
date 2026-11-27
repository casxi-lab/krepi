module

public import Krepi.Statements.PageTables.Ownership
public import Krepi.Proofs.PageTables.Refinement.WalkLemmas
public import Krepi.Proofs.PageTables.Refinement.OwnNewSpecLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: refinement of `Ownership::new`, `owner` and `stats`

The triples of the generated functions of the page ownership table that
build it, read the owner of a page and count its statistics, each a
`@[step]` lemma.

- Pages and ranges: `holds_page_spec`, `touches_page_spec`, with
  `holdsPage_repr` and `touchesPage_repr` (the tests of the specification on
  ranges that stand for ranges).
- The owner of a page: `in_banks_spec`, `holding_extent_spec`,
  `rank_spec`, `precedes_spec`, `first_excluder_spec`,
  `holding_owner_spec`, `ownership_owner_spec` (the statement
  `OwnershipOwner` without its premises).
- Statistics: `extent_stats_spec`, `ownership_stats_spec` (the statement
  `OwnershipStats` without its premise `Usize64`).
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.PageTables Krepi.Spec.PageTables Krepi.Statements Krepi.Statements.PageTables
open Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

/-! ## Pages -/

/-- `holds_page(range, page)` of a range whose end fits in 64 bits: the page
of 4 KiB at `page` lies in the range. -/
@[step] theorem holds_page_spec (r : page_tables.PhysRange) (page : U64)
    (h : r.start.val + r.len.val < 2 ^ 64) :
    page_tables.ownership.holds_page r page ⦃ b =>
      b = decide (r.start.val ≤ page.val ∧ page.val + 4096 ≤ r.start.val + r.len.val) ⦄ := by
  unfold page_tables.ownership.holds_page
  simp only [page_size_eq]
  step*

theorem holdsPage_repr {r : page_tables.PhysRange} {R : PhysRange} (h : PhysRangeRepr r R)
    (q : Nat) :
    R.holdsPage q = decide (r.start.val ≤ q ∧ q + 4096 ≤ r.start.val + r.len.val) := by
  rw [PhysRange.holdsPage, physRange_start h, physRange_endNat h, Bool.decide_and]; rfl

/-- `touches_page(range, page)` of a range whose end fits in 64 bits, for a
page that does not end past $2^{64}$: the range shares an address with the
page of 4 KiB at `page`. -/
@[step] theorem touches_page_spec (r : page_tables.PhysRange) (page : U64)
    (h : r.start.val + r.len.val < 2 ^ 64) (hp : page.val + 4095 < 2 ^ 64) :
    page_tables.ownership.touches_page r page ⦃ b =>
      b = decide (r.start.val < page.val + 4096 ∧ page.val < r.start.val + r.len.val) ⦄ := by
  unfold page_tables.ownership.touches_page
  simp only [page_size_eq]
  step*

theorem touchesPage_repr {r : page_tables.PhysRange} {R : PhysRange} (h : PhysRangeRepr r R)
    (q : Nat) :
    R.touchesPage q = decide (r.start.val < q + 4096 ∧ q < r.start.val + r.len.val) := by
  rw [PhysRange.touchesPage, physRange_start h, physRange_endNat h, Bool.decide_and]; rfl

/-! ## The owner of a page -/

/-- `in_banks(banks, count, page)`: whether one of the first `count` banks
holds the page, for banks that stand for the banks `Bs`. -/
@[step] theorem in_banks_spec {E : Usize} (banks : Aeneas.Std.Array page_tables.PhysRange E)
    (count : Usize) (page : U64) (Bs : List PhysRange)
    (hB : ListRel PhysRangeRepr (banks.val.take count.val) Bs) (hc : count.val ≤ E.val) :
    page_tables.ownership.in_banks banks count page ⦃ b =>
      b = Bs.any (·.holdsPage page.val) ⦄ := by
  have hc' : count.val ≤ banks.val.length := by rw [banks.property]; exact hc
  have hlen : Bs.length = count.val := by
    have := listRel_length hB; rw [List.length_take, banks.property] at this; omega
  unfold page_tables.ownership.in_banks page_tables.ownership.in_banks_loop
  apply loop.spec_decr_nat (measure := fun (i : Usize) => count.val - i.val)
    (inv := fun (i : Usize) => i.val ≤ count.val ∧
      (Bs.drop i.val).any (·.holdsPage page.val) = Bs.any (·.holdsPage page.val))
  · rintro i ⟨hi, hinv⟩
    unfold page_tables.ownership.in_banks_loop.body
    step*
    · obtain ⟨_, hr⟩ := own_listRel_take_getElem hB hc' i.val (by scalar_tac)
      rw [← pr_post] at hr
      exact physRange_fits hr
    · obtain ⟨hm, hr⟩ := own_listRel_take_getElem hB hc' i.val (by scalar_tac)
      rw [← pr_post] at hr
      rw [← hinv, any_drop_cons hm, holdsPage_repr hr, ← b_post, ‹b = true›, Bool.true_or]
    · obtain ⟨hm, hr⟩ := own_listRel_take_getElem hB hc' i.val (by scalar_tac)
      rw [← pr_post] at hr
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [← hinv, any_drop_cons (l := Bs) (i := i.val) hm, index1_post, holdsPage_repr hr, ← b_post,
        (Bool.not_eq_true _).mp ‹¬b = true›, Bool.false_or]
    · have : i.val = Bs.length := by scalar_tac
      rw [← hinv, this, List.drop_length, List.any_nil]
  · exact ⟨by simp, by simp⟩

/-- `holding_extent(extents, count, page)`: the index of the first of the
first `count` extents that holds the page, for extents that stand for the
extents `L`. -/
@[step] theorem holding_extent_spec {E : Usize} (extents : Aeneas.Std.Array page_tables.Extent E)
    (count : Usize) (page : U64) (L : List Extent)
    (hL : ListRel ExtentRepr (extents.val.take count.val) L) (hc : count.val ≤ E.val) :
    page_tables.ownership.holding_extent extents count page ⦃ o =>
      (o.bind fun i => L[i.val]?) = L.find? (·.range.holdsPage page.val) ∧
        ∀ i ∈ o, i.val < count.val ⦄ := by
  have hc' : count.val ≤ extents.val.length := by rw [extents.property]; exact hc
  have hlen : L.length = count.val := by
    have := listRel_length hL; rw [List.length_take, extents.property] at this; omega
  unfold page_tables.ownership.holding_extent page_tables.ownership.holding_extent_loop
  apply loop.spec_decr_nat (measure := fun (i : Usize) => count.val - i.val)
    (inv := fun (i : Usize) => i.val ≤ count.val ∧
      (L.drop i.val).find? (·.range.holdsPage page.val) = L.find? (·.range.holdsPage page.val))
  · rintro i ⟨hi, hinv⟩
    unfold page_tables.ownership.holding_extent_loop.body
    step*
    · obtain ⟨_, hr⟩ := own_listRel_take_getElem hL hc' i.val (by scalar_tac)
      rw [← e_post] at hr
      exact physRange_fits hr.1
    · obtain ⟨hm, hr⟩ := own_listRel_take_getElem hL hc' i.val (by scalar_tac)
      rw [← e_post] at hr
      have hp : L[i.val].range.holdsPage page.val = true := by
        rw [holdsPage_repr hr.1, ← b_post]; exact ‹b = true›
      refine ⟨?_, fun j hj => ?_⟩
      · rw [Option.bind_some, ← hinv, own_find?_drop_true hm hp, List.getElem?_eq_getElem hm]
      · rw [Option.mem_some_iff] at hj; subst hj; scalar_tac
    · obtain ⟨hm, hr⟩ := own_listRel_take_getElem hL hc' i.val (by scalar_tac)
      rw [← e_post] at hr
      have hp : L[i.val].range.holdsPage page.val = false := by
        rw [holdsPage_repr hr.1, ← b_post]; exact (Bool.not_eq_true _).mp ‹¬b = true›
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [← hinv, own_find?_drop_false hm hp, index1_post]
    · have : i.val = L.length := by scalar_tac
      rw [← hinv, this, List.drop_length]
      exact ⟨rfl, fun j hj => absurd hj (by simp)⟩
  · exact ⟨by simp, by simp⟩

/-- `rank(excluder)`: the rank of `rankOf`. -/
@[step] theorem rank_spec (x : page_tables.Excluder) :
    page_tables.ownership.rank x ⦃ r => r.val = rankOf (excluderOf x) ⦄ := by
  unfold page_tables.ownership.rank
  cases x <;> exact spec_of_eq rfl rfl

/-- `precedes(excluder, first)`: whether the excluder comes before the first
one found, in the order of `rankOf`. -/
@[step] theorem precedes_spec (x : page_tables.Excluder) (first : Option page_tables.Excluder) :
    page_tables.ownership.precedes x first ⦃ b =>
      b = match first with
        | none => true
        | some o => decide (rankOf (excluderOf x) < rankOf (excluderOf o)) ⦄ := by
  unfold page_tables.ownership.precedes
  cases first with
  | none => exact spec_of_eq rfl rfl
  | some o => step*

/-- `first_excluder(records, count, page)`: the first owner, in the order of
`rankOf`, of the first `count` exclusion records that touch the page, for
records that stand for the exclusions `Xs` and a page that does not end past
$2^{64}$. -/
@[step] theorem first_excluder_spec {X : Usize}
    (records : Aeneas.Std.Array page_tables.Exclusion X) (count : Usize) (page : U64)
    (Xs : List Exclusion) (hX : ListRel ExclusionRepr (records.val.take count.val) Xs)
    (hc : count.val ≤ X.val) (hp : page.val + 4095 < 2 ^ 64) :
    page_tables.ownership.first_excluder records count page ⦃ o =>
      o.map excluderOf = firstExcluder Xs page.val ⦄ := by
  have hc' : count.val ≤ records.val.length := by rw [records.property]; exact hc
  have hlen : Xs.length = count.val := by
    have := listRel_length hX; rw [List.length_take, records.property] at this; omega
  unfold page_tables.ownership.first_excluder page_tables.ownership.first_excluder_loop
  apply loop.spec_decr_nat
    (measure := fun (x : Option page_tables.Excluder × Usize) => count.val - x.2.val)
    (inv := fun (x : Option page_tables.Excluder × Usize) => x.2.val ≤ count.val ∧
      minEx (x.1.map excluderOf) (firstExcluder (Xs.drop x.2.val) page.val) =
        firstExcluder Xs page.val)
  · rintro ⟨first, i⟩ ⟨hi, hinv⟩
    dsimp only at hi hinv
    unfold page_tables.ownership.first_excluder_loop.body
    step*
    · obtain ⟨_, hr⟩ := own_listRel_take_getElem hX hc' i.val (by scalar_tac)
      rw [← record_post] at hr
      exact physRange_fits hr.1
    · obtain ⟨hm, hr⟩ := own_listRel_take_getElem hX hc' i.val (by scalar_tac)
      rw [← record_post] at hr
      have ht : Xs[i.val].range.touchesPage page.val = b := by rw [touchesPage_repr hr.1, b_post]
      have hstep := own_firstExcluder_drop hm page.val
      rw [ht, hr.2] at hstep
      have hic : i.val < count.val := by scalar_tac
      by_cases hb : b = true
      · simp only [hb, ↓reduceIte] at hstep ⊢
        step*
        by_cases hx : x = true
        · simp only [hx, ↓reduceIte]
          step*
          refine ⟨by omega, ?_, by omega⟩
          rw [index1_post, ← hinv, hstep, ← minEx_assoc]
          congr 1
          cases first with
          | none => rfl
          | some o =>
            have h1 := hx
            rw [x_post] at h1
            simp only [decide_eq_true_eq] at h1
            simp only [Option.map_some, minEx, h1, ↓reduceIte]
        · simp only [hx, Bool.false_eq_true, ↓reduceIte]
          step*
          refine ⟨by omega, ?_, by omega⟩
          rw [index1_post, ← hinv, hstep, ← minEx_assoc]
          congr 1
          cases first with
          | none => exact absurd x_post (by simpa using hx)
          | some o =>
            have h1 := hx
            rw [x_post] at h1
            simp only [decide_eq_true_eq] at h1
            simp only [Option.map_some, minEx, h1, ↓reduceIte]
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, minEx_none_left] at hstep ⊢
        step*
    · have : i.val = Xs.length := by scalar_tac
      rw [← hinv, this, List.drop_length, firstExcluder_nil, minEx_none_right]
  · exact ⟨by simp, by simp [minEx]⟩

/-- `Holding::owner()`: the owner of the pages of the holding. -/
@[step] theorem holding_owner_spec (h : page_tables.Holding) :
    page_tables.ownership.Holding.owner h ⦃ o => ownerOf o = (holdingOf h).owner ⦄ := by
  unfold page_tables.ownership.Holding.owner
  cases h <;> exact spec_of_eq rfl rfl

/-- `Ownership::owner(address)`: the owner of the page of the address,
`Ownership.owner`, for a table that stands for `T`. -/
@[step] theorem ownership_owner_spec {E X : Usize} (t : page_tables.Ownership E X)
    (T : Ownership E.val X.val) (h : OwnershipRepr t T) (address : U64) :
    page_tables.ownership.Ownership.owner t address ⦃ o =>
      o.map ownerOf = T.owner (word64 address) ⦄ := by
  obtain ⟨hb, he, hx, ha, hbanks, hext, hexcl, hcnt⟩ := h
  have he' : t.extent_count.val ≤ t.extents.val.length := by rw [t.extents.property]; exact he
  unfold page_tables.ownership.Ownership.owner
  simp only [page_size_eq]
  step*
  all_goals
    have hpg : page.val = (word64 address).toNat / 4096 * 4096 := by
      rw [page_post, i1_post, own_and_not_4095 address i (by rw [i_post]), word64_toNat]
    have hown : T.owner (word64 address) = T.ownerOf page.val := by
      rw [Ownership.owner, pageDown, hpg]; rfl
  · have := u64_lt address
    rw [hpg, word64_toNat]; omega
  · have hfind : T.extents.find? (·.range.holdsPage page.val) = none := by
      rw [← o_post, ‹o = none›]; rfl
    simp only [hown, Ownership.ownerOf, hfind, ← b_post, ‹b = true›, ↓reduceIte, ← o1_post,
      ‹o1 = none›, Option.map_none]
  · have hfind : T.extents.find? (·.range.holdsPage page.val) = none := by
      rw [← o_post, ‹o = none›]; rfl
    simp only [hown, Ownership.ownerOf, hfind, ← b_post, ‹b = true›, ↓reduceIte, ← o1_post,
      ‹o1 = some excluder›, Option.map_some]
    rfl
  · have hfind : T.extents.find? (·.range.holdsPage page.val) = none := by
      rw [← o_post, ‹o = none›]; rfl
    simp only [hown, Ownership.ownerOf, hfind, ← b_post, (Bool.not_eq_true _).mp ‹¬b = true›,
      Bool.false_eq_true, ↓reduceIte, Option.map_none]
  · obtain ⟨hm, hr⟩ := own_listRel_take_getElem hext he' index.val
      (o_post1 index (by rw [‹o = some index›]; rfl))
    rw [← e_post] at hr
    have hfind : T.extents.find? (·.range.holdsPage page.val) = some T.extents[index.val] := by
      rw [← o_post, ‹o = some index›, Option.bind_some, List.getElem?_eq_getElem hm]
    simp only [hown, Ownership.ownerOf, hfind, Option.map_some, o1_post, hr.2.2]

/-! ## Statistics -/

/-- The loop of `extent_stats`: from the counters of the extents before
`index`, those of all extents, for extents that stand for the extents `L`
whose lengths from `index` on sum with `m` to less than $2^{64}$. -/
theorem extent_stats_loop_spec {E : Usize} (extents : Aeneas.Std.Array page_tables.Extent E)
    (count : Usize) (L : List Extent) (hL : ListRel ExtentRepr (extents.val.take count.val) L)
    (hc : count.val ≤ E.val) (S : Stats) (c cap : Nat)
    (m f a : U64) (n k : Usize) (big : U64) (index : Usize) (hidx : index.val ≤ count.val)
    (hinv : (L.drop index.val).foldl statsStep
      ⟨m.val, f.val, a.val, n.val, k.val, big.val, c, cap⟩ = S)
    (hsum : m.val + ((L.drop index.val).map (·.range.len.toNat)).sum < 2 ^ 64)
    (hf : f.val ≤ m.val) (ha : a.val ≤ m.val) (hn : n.val + k.val ≤ index.val) :
    page_tables.ownership.extent_stats_loop extents count m f a n k big index ⦃ r =>
      r.1.val = S.managed ∧ r.2.1.val = S.free ∧ r.2.2.1.val = S.allocated ∧
      r.2.2.2.1.val = S.allocations ∧ r.2.2.2.2.1.val = S.freeExtents ∧
      r.2.2.2.2.2.val = S.largestFree ⦄ := by
  have hc' : count.val ≤ extents.val.length := by rw [extents.property]; exact hc
  have hlen : L.length = count.val := by
    have := listRel_length hL; rw [List.length_take, extents.property] at this; omega
  unfold page_tables.ownership.extent_stats_loop
  apply loop.spec_decr_nat
    (measure := fun (x : U64 × U64 × U64 × Usize × Usize × U64 × Usize) =>
      count.val - x.2.2.2.2.2.2.val)
    (inv := fun (x : U64 × U64 × U64 × Usize × Usize × U64 × Usize) =>
      x.2.2.2.2.2.2.val ≤ count.val ∧
      (L.drop x.2.2.2.2.2.2.val).foldl statsStep
        ⟨x.1.val, x.2.1.val, x.2.2.1.val, x.2.2.2.1.val, x.2.2.2.2.1.val, x.2.2.2.2.2.1.val, c,
          cap⟩ = S ∧
      x.1.val + ((L.drop x.2.2.2.2.2.2.val).map (·.range.len.toNat)).sum < 2 ^ 64 ∧
      x.2.1.val ≤ x.1.val ∧ x.2.2.1.val ≤ x.1.val ∧
      x.2.2.2.1.val + x.2.2.2.2.1.val ≤ x.2.2.2.2.2.2.val)
  · rintro ⟨m, f, a, n, k, big, i⟩ ⟨hi, hinv, hsum, hf, ha, hn⟩
    dsimp only at hi hinv hsum hf ha hn
    unfold page_tables.ownership.extent_stats_loop.body
    step*
    · obtain ⟨hm, hr⟩ := own_listRel_take_getElem hL hc' i.val (by scalar_tac)
      rw [← e_post] at hr
      have hle : e.range.len.val = L[i.val].range.len.toNat := (physRange_len hr.1).symm
      simp only [own_sum_drop hm] at hsum
      rw [u64_max_eq]; omega
    · obtain ⟨hm, hr⟩ := own_listRel_take_getElem hL hc' i.val (by scalar_tac)
      rw [← e_post] at hr
      have hle : e.range.len.val = L[i.val].range.len.toNat := (physRange_len hr.1).symm
      simp only [own_sum_drop hm] at hsum
      rw [own_foldl_drop hm] at hinv
      have hic : i.val < count.val := by scalar_tac
      by_cases hb : b = true
      · have hfree : L[i.val].holding = .free := by
          have h1 : (holdingOf e.holding == Holding.free) = true := b_post ▸ hb
          rw [hr.2.2]; exact beq_iff_eq.mp h1
        rw [statsStep_free hfree] at hinv
        simp only [hb, ↓reduceIte]
        step*
        by_cases hbig : e.range.len > big
        · have hbig' : big.val < e.range.len.val := hbig
          have hmax : max big.val L[i.val].range.len.toNat = e.range.len.val := by
            rw [← hle]; exact Nat.max_eq_right (Nat.le_of_lt hbig')
          simp only [hbig, ↓reduceIte]
          step*
          rw [index1_post]
          refine ⟨by omega, ?_, by omega, by omega, by omega, by omega, by omega⟩
          rw [← hinv]
          congr 1
          simp only [Stats.mk.injEq, hmax, and_true, true_and]
          refine ⟨by omega, by omega, by omega⟩
        · have hbig' : ¬ big.val < e.range.len.val := hbig
          have hmax : max big.val L[i.val].range.len.toNat = big.val := by
            rw [← hle]; exact Nat.max_eq_left (Nat.le_of_not_lt hbig')
          simp only [hbig, ↓reduceIte]
          step*
          rw [index1_post]
          refine ⟨by omega, ?_, by omega, by omega, by omega, by omega, by omega⟩
          rw [← hinv]
          congr 1
          simp only [Stats.mk.injEq, hmax, and_true, true_and]
          refine ⟨by omega, by omega, by omega⟩
      · have hheld : L[i.val].holding ≠ .free := by
          have h1 : ¬ (holdingOf e.holding == Holding.free) = true := b_post ▸ hb
          rw [hr.2.2]; exact fun h => h1 (beq_iff_eq.mpr h)
        rw [statsStep_held hheld] at hinv
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        step*
        rw [index1_post]
        refine ⟨by omega, ?_, by omega, by omega, by omega, by omega, by omega⟩
        rw [← hinv]
        congr 1
        simp only [Stats.mk.injEq, and_true, true_and]
        refine ⟨by omega, by omega, by omega⟩
    · have : i.val = L.length := by scalar_tac
      rw [this, List.drop_length, List.foldl_nil] at hinv
      subst hinv
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨hidx, hinv, hsum, hf, ha, hn⟩

/-- `extent_stats(extents, count)`: the statistics of the first `count`
extents, for extents that stand for the extents `L`, whose lengths sum to
less than $2^{64}$. -/
@[step] theorem extent_stats_spec {E : Usize} (extents : Aeneas.Std.Array page_tables.Extent E)
    (count : Usize) (L : List Extent) (hL : ListRel ExtentRepr (extents.val.take count.val) L)
    (hc : count.val ≤ E.val) (hsum : (L.map (·.range.len.toNat)).sum < 2 ^ 64) :
    page_tables.ownership.extent_stats extents count ⦃ s =>
      StatsRepr s (L.foldl statsStep ⟨0, 0, 0, 0, 0, 0, L.length, E.val⟩) ⦄ := by
  have hlen : L.length = count.val := by
    have := listRel_length hL; rw [List.length_take, extents.property] at this; omega
  have hfix := foldl_statsStep_fixed L ⟨0, 0, 0, 0, 0, 0, L.length, E.val⟩
  unfold page_tables.ownership.extent_stats
  refine WP.spec_bind (extent_stats_loop_spec extents count L hL hc
    (L.foldl statsStep ⟨0, 0, 0, 0, 0, 0, L.length, E.val⟩) L.length E.val 0#u64 0#u64
    0#u64 0#usize 0#usize 0#u64 0#usize (by simp) (by simp) (by simpa using hsum) (le_refl _)
    (le_refl _) (by simp)) ?_
  rintro ⟨r1, r2, r3, r4, r5, r6⟩ ⟨h1, h2, h3, h4, h5, h6⟩
  refine spec_of_eq rfl ?_
  exact ⟨h1.symm, h2.symm, h3.symm, h4.symm, h5.symm, h6.symm, hfix.1.trans hlen,
    hfix.2⟩

/-- `Ownership::stats()`: the statistics of `Ownership.stats`, for a table
that stands for a well-formed table `T`. -/
@[step] theorem ownership_stats_spec {E X : Usize} (t : page_tables.Ownership E X)
    (T : Ownership E.val X.val) (h : OwnershipRepr t T) (hw : T.WellFormed) :
    page_tables.ownership.Ownership.stats t ⦃ s => StatsRepr s T.stats ⦄ := by
  obtain ⟨hb, he, hx, ha, hbanks, hext, hexcl, hcnt⟩ := h
  obtain ⟨-, -, -, -, -, -, hpair, -, -⟩ := hw
  have hsum : (T.extents.map (·.range.len.toNat)).sum < 2 ^ 64 := by
    have := extents_len_sum_lt T.extents 0 hpair (fun _ _ => Nat.zero_le _) (by norm_num)
    simpa using this
  unfold page_tables.ownership.Ownership.stats
  refine spec_mono (extent_stats_spec t.extents t.extent_count T.extents hext he hsum) ?_
  intro s hs
  rw [stats_eq_foldl]
  exact hs

end Krepi.Proofs.PageTables.Refinement
