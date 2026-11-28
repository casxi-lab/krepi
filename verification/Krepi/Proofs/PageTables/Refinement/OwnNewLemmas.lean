module

public import Krepi.Statements.PageTables.Ownership
public import Krepi.Proofs.PageTables.Refinement.WalkLemmas
public import Krepi.Proofs.PageTables.Refinement.OwnNewSpecLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: refinement of `Ownership::new`, `owner` and `stats`

The triples of the generated functions of the page ownership table that
build it, read the owner of a page and count its statistics, each a
`@[step]` lemma, so that a mutant of a callee fails the proof of the callee
alone. Each holds without the premise `Usize64`; the loops are proved with
`loop.spec_decr_nat` and an invariant that the answer from the current state
is the answer from the start.

- Pages and ranges: `holds_page_spec`, `touches_page_spec`, with
  `own_holdsPage_repr`, `own_touchesPage_repr`, `own_onPages_repr` and
  `own_overlaps_repr` (the tests of the specification on ranges that stand
  for ranges).
- The owner of a page: `in_banks_spec`, `holding_extent_spec`, `rank_spec`,
  `precedes_spec`, `first_excluder_spec`, `holding_owner_spec` and
  `ownership_owner_spec` (the statement `OwnershipOwner` without its
  premises `Usize64` and `Ownership.Invariant`).
- Statistics: `extent_stats_loop_spec`, `extent_stats_spec` and
  `ownership_stats_spec` (the statement `OwnershipStats` for a well-formed
  table).
- The checks of `Ownership::new`: `on_pages_spec`, `overlaps_later_spec`,
  `any_overlap_spec`; the exclusion records, `copy_exclusions_spec`; the
  banks in address order, `insert_bank_loop_spec`, `insert_bank_spec` and
  `sort_banks_spec`; the free extents, `cut_spec` (against `cutNat`, which
  is `Exclusion.cut` by `cut_eq_cutNat`), `cuts_at_spec` (with `own_val_ite`,
  the value of a choice between two words),
  `bank_extents_loop_spec`, `bank_extents_spec` and `initial_extents_spec`;
  and `ownership_new_spec` (the statement `OwnershipNew` without its premise
  `Usize64`).
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

theorem own_holdsPage_repr {r : page_tables.PhysRange} {R : PhysRange} (h : PhysRangeRepr r R)
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

theorem own_touchesPage_repr {r : page_tables.PhysRange} {R : PhysRange} (h : PhysRangeRepr r R)
    (q : Nat) :
    R.touchesPage q = decide (r.start.val < q + 4096 ∧ q < r.start.val + r.len.val) := by
  rw [PhysRange.touchesPage, physRange_start h, physRange_endNat h, Bool.decide_and]; rfl

/-! ## The owner of a page -/

/-- `in_banks(banks, count, page)`: whether one of the first `count` banks
holds the page, for a count within the array whose first `count` banks stand
for the banks `Bs`. -/
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
      rw [← hinv, any_drop_cons hm, own_holdsPage_repr hr, ← b_post, ‹b = true›, Bool.true_or]
    · obtain ⟨hm, hr⟩ := own_listRel_take_getElem hB hc' i.val (by scalar_tac)
      rw [← pr_post] at hr
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [← hinv, any_drop_cons (l := Bs) (i := i.val) hm, index1_post, own_holdsPage_repr hr,
        ← b_post,
        (Bool.not_eq_true _).mp ‹¬b = true›, Bool.false_or]
    · have : i.val = Bs.length := by scalar_tac
      rw [← hinv, this, List.drop_length, List.any_nil]
  · exact ⟨by simp, by simp⟩

/-- `holding_extent(extents, count, page)`: the index of the first of the
first `count` extents that holds the page, for a count within the array whose
first `count` extents stand for the extents `L`. -/
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
        rw [own_holdsPage_repr hr.1, ← b_post]; exact ‹b = true›
      refine ⟨?_, fun j hj => ?_⟩
      · rw [Option.bind_some, ← hinv, own_find?_drop_true hm hp, List.getElem?_eq_getElem hm]
      · rw [Option.mem_some_iff] at hj; subst hj; scalar_tac
    · obtain ⟨hm, hr⟩ := own_listRel_take_getElem hL hc' i.val (by scalar_tac)
      rw [← e_post] at hr
      have hp : L[i.val].range.holdsPage page.val = false := by
        rw [own_holdsPage_repr hr.1, ← b_post]; exact (Bool.not_eq_true _).mp ‹¬b = true›
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
`rankOf`, of the first `count` exclusion records that touch the page, for a
count within the array whose first `count` records stand for the exclusions
`Xs`, and a page that does not end past $2^{64}$. -/
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
      have ht : Xs[i.val].range.touchesPage page.val = b := by
        rw [own_touchesPage_repr hr.1, b_post]
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

/-- The loop of `extent_stats` from `index`, for a count within the array
whose first `count` extents stand for the extents `L`, and `index` at most
`count`: counters `m`, `f`, `a`, `n`, `k`, `big` whose statistics, folded over
the extents from `index` on, are `S`, with `f` and `a` at most `m`, `n + k`
at most `index`, and `m` with the lengths of the extents from `index` on
below $2^{64}$, give the counters of `S`. -/
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
extents, for a count within the array whose first `count` extents stand for
the extents `L`, whose lengths sum to less than $2^{64}$. -/
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

/-! ## The checks of `Ownership::new` -/

theorem own_onPages_repr {r : page_tables.PhysRange} {R : PhysRange} (h : PhysRangeRepr r R) :
    R.onPages = (r.start.val % 4096 == 0 && (r.start.val + r.len.val) % 4096 == 0) := by
  rw [PhysRange.onPages, physRange_start h, physRange_endNat h]; rfl

theorem own_overlaps_repr {r o : page_tables.PhysRange} {R O : PhysRange} (hr : PhysRangeRepr r R)
    (ho : PhysRangeRepr o O) :
    R.overlaps O =
      decide (r.start.val < o.start.val + o.len.val ∧ o.start.val < r.start.val + r.len.val) := by
  rw [PhysRange.overlaps, physRange_start hr, physRange_start ho, physRange_endNat hr,
    physRange_endNat ho, Bool.decide_and]

/-- `on_pages(banks)`: whether every bank starts and ends on a page boundary,
for banks that stand for the banks `Bs`. -/
@[step] theorem on_pages_spec (banks : Slice page_tables.PhysRange) (Bs : List PhysRange)
    (hB : ListRel PhysRangeRepr banks.val Bs) :
    page_tables.ownership.on_pages banks ⦃ b => b = Bs.all (·.onPages) ⦄ := by
  have hlen : Bs.length = banks.length := (listRel_length hB).symm
  unfold page_tables.ownership.on_pages page_tables.ownership.on_pages_loop
  apply loop.spec_decr_nat (measure := fun (i : Usize) => banks.length - i.val)
    (inv := fun (i : Usize) => i.val ≤ banks.length ∧
      (Bs.drop i.val).all (·.onPages) = Bs.all (·.onPages))
  · rintro i ⟨hi, hinv⟩
    unfold page_tables.ownership.on_pages_loop.body
    simp only [page_size_eq]
    step*
    · have hil : i.val < Bs.length := by scalar_tac
      have hr := own_listRel_getElem hB i.val (by scalar_tac) hil
      rw [← pr_post] at hr
      have h0 : i1.val ≠ 0 := bne_zero_iff.1 ‹_›
      have h1 : (pr.start.val % 4096 == 0) = false := by
        rw [beq_eq_false_iff_ne]; omega
      rw [← hinv, own_all_drop hil, own_onPages_repr hr, h1, Bool.false_and, Bool.false_and]
    · have hil : i.val < Bs.length := by scalar_tac
      have hr := own_listRel_getElem hB i.val (by scalar_tac) hil
      rw [← pr_post] at hr
      exact physRange_fits hr
    · have hil : i.val < Bs.length := by scalar_tac
      have hr := own_listRel_getElem hB i.val (by scalar_tac) hil
      rw [← pr_post] at hr
      have h0 : i1.val = 0 := not_bne_zero_iff.1 ‹_›
      have h0' : i3.val ≠ 0 := bne_zero_iff.1 ‹_›
      have h1 : (pr.start.val % 4096 == 0) = true := by rw [beq_iff_eq]; omega
      have h2 : ((pr.start.val + pr.len.val) % 4096 == 0) = false := by
        rw [beq_eq_false_iff_ne]; omega
      rw [← hinv, own_all_drop hil, own_onPages_repr hr, h1, h2, Bool.true_and, Bool.false_and]
    · have hil : i.val < Bs.length := by scalar_tac
      have hr := own_listRel_getElem hB i.val (by scalar_tac) hil
      rw [← pr_post] at hr
      have h0 : i1.val = 0 := not_bne_zero_iff.1 ‹_›
      have h0' : i3.val = 0 := not_bne_zero_iff.1 ‹_›
      have h1 : (pr.start.val % 4096 == 0) = true := by rw [beq_iff_eq]; omega
      have h2 : ((pr.start.val + pr.len.val) % 4096 == 0) = true := by
        rw [beq_iff_eq]; omega
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [index1_post, ← hinv, own_all_drop hil, own_onPages_repr hr, h1, h2, Bool.true_and,
        Bool.true_and]
    · rw [← hinv, show i.val = Bs.length by scalar_tac, List.drop_length, List.all_nil]
  · exact ⟨by simp, by simp⟩

/-- `overlaps_later(banks, index)`: whether the bank of index `index`
overlaps a later one, for banks that stand for the banks `Bs`. -/
@[step] theorem overlaps_later_spec (banks : Slice page_tables.PhysRange) (index : Usize)
    (Bs : List PhysRange) (hB : ListRel PhysRangeRepr banks.val Bs) (hi : index.val < Bs.length) :
    page_tables.ownership.overlaps_later banks index ⦃ b =>
      b = (Bs.drop (index.val + 1)).any Bs[index.val].overlaps ⦄ := by
  have hlen : Bs.length = banks.length := (listRel_length hB).symm
  unfold page_tables.ownership.overlaps_later page_tables.ownership.overlaps_later_loop
  step*
  apply loop.spec_decr_nat (measure := fun (j : Usize) => banks.length - j.val)
    (inv := fun (j : Usize) => index.val < j.val ∧ j.val ≤ banks.length ∧
      (Bs.drop j.val).any Bs[index.val].overlaps =
        (Bs.drop (index.val + 1)).any Bs[index.val].overlaps)
  · rintro j ⟨hj1, hj2, hinv⟩
    unfold page_tables.ownership.overlaps_later_loop.body
    step*
    · have hr := own_listRel_getElem hB index.val (by scalar_tac) hi
      rw [← pr_post] at hr
      exact physRange_fits hr
    · have hjl : j.val < Bs.length := by scalar_tac
      have ho := own_listRel_getElem hB j.val (by scalar_tac) hjl
      rw [← pr1_post] at ho
      exact physRange_fits ho
    · have hjl : j.val < Bs.length := by scalar_tac
      have hr := own_listRel_getElem hB index.val (by scalar_tac) hi
      rw [← pr_post] at hr
      have ho := own_listRel_getElem hB j.val (by scalar_tac) hjl
      rw [← pr1_post] at ho
      rw [← hinv, any_drop_cons hjl, own_overlaps_repr hr ho, ← b_post, ‹b = true›, Bool.true_or]
    · have hjl : j.val < Bs.length := by scalar_tac
      have hr := own_listRel_getElem hB index.val (by scalar_tac) hi
      rw [← pr_post] at hr
      have ho := own_listRel_getElem hB j.val (by scalar_tac) hjl
      rw [← pr1_post] at ho
      refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
      rw [later1_post, ← hinv, any_drop_cons (l := Bs) (i := j.val) hjl, own_overlaps_repr hr ho,
        ← b_post, (Bool.not_eq_true _).mp ‹¬b = true›, Bool.false_or]
    · rw [← hinv, show j.val = Bs.length by scalar_tac, List.drop_length, List.any_nil]
  · exact ⟨by scalar_tac, by scalar_tac, by rw [later_post]⟩

/-- `any_overlap(banks)`: whether two banks overlap, `anyOverlap`, for banks
that stand for the banks `Bs`. -/
@[step] theorem any_overlap_spec (banks : Slice page_tables.PhysRange) (Bs : List PhysRange)
    (hB : ListRel PhysRangeRepr banks.val Bs) :
    page_tables.ownership.any_overlap banks ⦃ b => b = anyOverlap Bs ⦄ := by
  have hlen : Bs.length = banks.length := (listRel_length hB).symm
  unfold page_tables.ownership.any_overlap page_tables.ownership.any_overlap_loop
  apply loop.spec_decr_nat (measure := fun (i : Usize) => banks.length - i.val)
    (inv := fun (i : Usize) => i.val ≤ banks.length ∧ anyOverlap (Bs.drop i.val) = anyOverlap Bs)
  · rintro i ⟨hi, hinv⟩
    unfold page_tables.ownership.any_overlap_loop.body
    step*
    · have hil : i.val < Bs.length := by scalar_tac
      rw [← hinv, own_anyOverlap_drop hil, ← b_post, ‹b = true›, Bool.true_or]
    · have hil : i.val < Bs.length := by scalar_tac
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [index1_post, ← hinv, own_anyOverlap_drop hil, ← b_post,
        (Bool.not_eq_true _).mp ‹¬b = true›, Bool.false_or]
    · rw [← hinv, show i.val = Bs.length by scalar_tac, List.drop_length]
      rfl
  · exact ⟨by simp, by simp⟩

/-- `copy_exclusions(records, exclusions)`: the records hold the exclusions
first, for at most `X` exclusions. -/
@[step] theorem copy_exclusions_spec {X : Usize}
    (records : Aeneas.Std.Array page_tables.Exclusion X)
    (exclusions : Slice page_tables.Exclusion) (hl : exclusions.length ≤ X.val) :
    page_tables.ownership.copy_exclusions records exclusions ⦃ r =>
      r.val.take exclusions.length = exclusions.val ⦄ := by
  unfold page_tables.ownership.copy_exclusions page_tables.ownership.copy_exclusions_loop
  apply loop.spec_decr_nat
    (measure := fun (x : Aeneas.Std.Array page_tables.Exclusion X × Usize) =>
      exclusions.length - x.2.val)
    (inv := fun (x : Aeneas.Std.Array page_tables.Exclusion X × Usize) =>
      x.2.val ≤ exclusions.length ∧ x.1.val.take x.2.val = exclusions.val.take x.2.val)
  · rintro ⟨r, i⟩ ⟨hi, hinv⟩
    dsimp only at hi hinv
    unfold page_tables.ownership.copy_exclusions_loop.body
    step*
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [index1_post, a_post, Array.set_val_eq, own_take_set_succ (by scalar_tac) e, hinv, e_post,
        List.take_succ_eq_append_getElem (l := exclusions.val) (by scalar_tac)]
    · have h1 : i.val = exclusions.val.length := by scalar_tac
      show List.take exclusions.val.length r.val = exclusions.val
      rw [← h1, hinv, h1, List.take_length]
  · exact ⟨by simp, by simp⟩

theorem cut_eq_cutNat {r bank : page_tables.PhysRange} {X : Exclusion} {B : PhysRange}
    (hx : PhysRangeRepr r X.range) (hb : PhysRangeRepr bank B) :
    X.cut B = cutNat r.start.val r.len.val bank.start.val bank.len.val := by
  rw [Exclusion.cut, own_overlaps_repr hx hb, cutNat, physRange_start hx, physRange_endNat hx,
    physRange_start hb, physRange_endNat hb]
  simp only [pageDown, pageUp, PAGE_SIZE, decide_eq_true_eq]

/-- `cut(exclusion, bank)`: the pages `[start, stop)` of the bank that the
exclusion touches, `cutNat` (`Exclusion.cut`, `cut_eq_cutNat`), for an
exclusion whose end fits in 64 bits and a bank whose end fits in 64 bits and
is a multiple of 4 KiB. -/
@[step] theorem cut_spec (r bank : page_tables.PhysRange)
    (hfx : r.start.val + r.len.val < 2 ^ 64) (hfb : bank.start.val + bank.len.val < 2 ^ 64)
    (hbe : (bank.start.val + bank.len.val) % 4096 = 0) :
    page_tables.ownership.cut r bank ⦃ o =>
      o.map (fun p => (p.1.val, p.2.val)) =
        cutNat r.start.val r.len.val bank.start.val bank.len.val ⦄ := by
  unfold page_tables.ownership.cut
  simp only [page_size_eq]
  step*
  · have hov : (r.start.val < bank.start.val + bank.len.val ∧
        bank.start.val < r.start.val + r.len.val) := by
      have := ‹b = true›; rw [b_post] at this; simpa using this
    have hdown : down.val = r.start.val / 4096 * 4096 := by
      rw [down_post, i1_post, own_and_not_4095 _ i (by rw [i_post])]
    have hcn : cutNat r.start.val r.len.val bank.start.val bank.len.val =
        some (max (r.start.val / 4096 * 4096) bank.start.val,
          min ((r.start.val + r.len.val + 4096 - 1) / 4096 * 4096)
            (bank.start.val + bank.len.val)) := by
      simp only [cutNat, hov, and_self, ↓reduceIte]
    rw [hcn]
    clear down_post down_post1
    by_cases hd : down > bank.start
    · have hd' : bank.start.val < down.val := hd
      simp only [hd, ↓reduceIte]
      step*
      · have hlt : i2.val < bank.start.val + bank.len.val := by rw [← i3_post]; exact ‹i2 < i3›
        have hstop : stop.val = (i2.val + 4095) / 4096 * 4096 := by
          rw [stop_post, i5_post, own_and_not_4095 _ i (by rw [i_post]), i4_post, i_post]
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
        exact ⟨own_cut_start_lt hdown hd', own_cut_stop_lt i2_post hbe hlt hstop⟩
      · have hlt : ¬ i2.val < bank.start.val + bank.len.val := by
          rw [← i3_post]; exact ‹¬ i2 < i3›
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
        exact ⟨own_cut_start_lt hdown hd', i3_post.trans (own_cut_stop_ge i2_post hlt)⟩
    · have hd' : ¬ bank.start.val < down.val := hd
      simp only [hd, ↓reduceIte]
      step*
      · have hlt : i2.val < bank.start.val + bank.len.val := by rw [← i3_post]; exact ‹i2 < i3›
        have hstop : stop.val = (i2.val + 4095) / 4096 * 4096 := by
          rw [stop_post, i5_post, own_and_not_4095 _ i (by rw [i_post]), i4_post, i_post]
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
        exact ⟨own_cut_start_ge hdown hd', own_cut_stop_lt i2_post hbe hlt hstop⟩
      · have hlt : ¬ i2.val < bank.start.val + bank.len.val := by
          rw [← i3_post]; exact ‹¬ i2 < i3›
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
        exact ⟨own_cut_start_ge hdown hd', i3_post.trans (own_cut_stop_ge i2_post hlt)⟩
  · have hov : ¬ (r.start.val < bank.start.val + bank.len.val ∧
        bank.start.val < r.start.val + r.len.val) := by
      have := ‹¬ b = true›; rw [b_post] at this; simpa using this
    simp only [cutNat, hov, ↓reduceIte, Option.map_none]

/-- The value of a choice between two words. -/
theorem own_val_ite {c : Prop} [Decidable c] (a b : U64) :
    (if c then a else b).val = if c then a.val else b.val := by
  split <;> rfl

/-- `cuts_at(exclusions, bank, at)`: the furthest end of the cuts that start
at or below `at`, and the nearest start of the cuts above `at` or the end of
the bank, for exclusions that stand for `Xs` and a bank on pages that stands
for `B`. -/
@[step] theorem cuts_at_spec (exclusions : Slice page_tables.Exclusion)
    (bank : page_tables.PhysRange) (pos : U64) (Xs : List Exclusion) (B : PhysRange)
    (hX : ListRel ExclusionRepr exclusions.val Xs) (hb : PhysRangeRepr bank B)
    (hBp : B.endNat % 4096 = 0) :
    page_tables.ownership.cuts_at exclusions bank pos ⦃ r =>
      (r.1.val, r.2.val) = Xs.foldl (cutStep B pos.val) (pos.val, B.endNat) ⦄ := by
  have hlen : Xs.length = exclusions.length := (listRel_length hX).symm
  have hfb := physRange_fits hb
  unfold page_tables.ownership.cuts_at page_tables.ownership.cuts_at_loop
  step*
  apply loop.spec_decr_nat
    (measure := fun (x : U64 × U64 × Usize) => exclusions.length - x.2.2.val)
    (inv := fun (x : U64 × U64 × Usize) => x.2.2.val ≤ exclusions.length ∧
      (Xs.drop x.2.2.val).foldl (cutStep B pos.val) (x.1.val, x.2.1.val) =
        Xs.foldl (cutStep B pos.val) (pos.val, B.endNat))
  · rintro ⟨reach, near, i⟩ ⟨hi, hinv⟩
    dsimp only at hi hinv
    unfold page_tables.ownership.cuts_at_loop.body
    simp only [own_ite_ok]
    have hbe : (bank.start.val + bank.len.val) % 4096 = 0 := by
      rw [← physRange_endNat hb]; exact hBp
    step*
    · have hil : i.val < Xs.length := by scalar_tac
      have hr := own_listRel_getElem hX i.val (by scalar_tac) hil
      rw [← e_post] at hr
      exact physRange_fits hr.1
    · have hil : i.val < Xs.length := by scalar_tac
      have hr := own_listRel_getElem hX i.val (by scalar_tac) hil
      rw [← e_post] at hr
      have hcut : Xs[i.val].cut B = o.map (fun p => (p.1.val, p.2.val)) := by
        rw [o_post, cut_eq_cutNat hr.1 hb]
      rcases o with _ | ⟨start, stop⟩
      · simp only
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [index1_post, ← hinv, own_foldl_drop hil]
        simp only [cutStep, hcut, Option.map_none]
      · simp only
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [index1_post, ← hinv, own_foldl_drop hil]
        simp only [cutStep, hcut, Option.map_some, sweepStep]
        congr 1
        simp only [Prod.mk.injEq, own_val_ite, UScalar.le_equiv, UScalar.lt_equiv, gt_iff_lt]
        constructor <;> split_ifs <;> omega
    · rw [← hinv, show i.val = Xs.length by scalar_tac, List.drop_length, List.foldl_nil]
  · refine ⟨by simp, ?_⟩
    rw [nearest_post, ← physRange_endNat hb]
    rfl

/-- The loop of `insert_bank` from the gap at `pos`, for an array that holds
the first `pos` ranges of `P`, a gap, the other ranges of `P` and `rest`,
with `pos` at most the length of `P` and the ranges of `P` from `pos` on
starting above `bank`: the ranges of `P` that start above `bank` move up by
one, and the gap stops after the last range whose start is at or below. -/
theorem insert_bank_loop_spec {E : Usize} (sorted : Aeneas.Std.Array page_tables.PhysRange E)
    (bank : page_tables.PhysRange) (pos : Usize) (P rest : List page_tables.PhysRange)
    (X0 : page_tables.PhysRange) (h : sorted.val = P.take pos.val ++ X0 :: (P.drop pos.val ++ rest))
    (hpos : pos.val ≤ P.length)
    (hafter : ∀ y ∈ P.drop pos.val, bank.start.val < y.start.val) :
    page_tables.ownership.insert_bank_loop sorted bank pos ⦃ r =>
      r.2.1 = bank ∧ r.2.2.val ≤ P.length ∧
      (∃ X, r.1.val = P.take r.2.2.val ++ X :: (P.drop r.2.2.val ++ rest)) ∧
      (∀ y ∈ P.drop r.2.2.val, bank.start.val < y.start.val) ∧
      (∀ y, 0 < r.2.2.val → P[r.2.2.val - 1]? = some y → y.start.val ≤ bank.start.val) ⦄ := by
  unfold page_tables.ownership.insert_bank_loop
  apply loop.spec_decr_nat
    (measure := fun (x : Aeneas.Std.Array page_tables.PhysRange E × Usize) => x.2.val)
    (inv := fun (x : Aeneas.Std.Array page_tables.PhysRange E × Usize) =>
      x.2.val ≤ P.length ∧ (∃ X, x.1.val = P.take x.2.val ++ X :: (P.drop x.2.val ++ rest)) ∧
      (∀ y ∈ P.drop x.2.val, bank.start.val < y.start.val))
  · rintro ⟨arr, j⟩ ⟨hj, ⟨X, hX⟩, hafter⟩
    dsimp only at hj hX hafter
    unfold page_tables.ownership.insert_bank_loop.body
    have hal : arr.val.length = P.length + 1 + rest.length := by rw [hX]; simp; omega
    step*
    · have hj0 : 0 < j.val := by scalar_tac
      have hi : i.val = j.val - 1 := by scalar_tac
      have hget : pr1 = P[j.val - 1]'(by omega) := by
        rw [pr1_post]
        simp only [hX, hi]
        exact own_getElem_prefix (by omega) hj _
      have hgt : bank.start.val < pr1.start.val := by
        rw [pr1_post, ← pr_post]; exact ‹pr.start > bank.start›
      refine ⟨by omega, ⟨P[j.val - 1]'(by omega), ?_⟩, ?_, by omega⟩
      · rw [a_post, Array.set_val_eq, hX, hget, hi, own_shift_step hj0 hj]
      · rw [hi, List.drop_eq_getElem_cons (by omega)]
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · rw [← hget]; exact hgt
        · exact hafter y (by rwa [show j.val - 1 + 1 = j.val by omega] at hy)
    · refine ⟨hj, ⟨X, hX⟩, hafter, fun y _ hy => ?_⟩
      have hi : i.val = j.val - 1 := by scalar_tac
      have hjl : j.val - 1 < P.length := by omega
      rw [List.getElem?_eq_getElem hjl, Option.some.injEq] at hy
      subst hy
      have hp : pr = P[j.val - 1] := by
        rw [pr_post]; simp only [hX, hi]; exact own_getElem_prefix (by omega) hj _
      rw [← hp]
      have := ‹¬ pr.start > bank.start›
      scalar_tac
    · refine ⟨hj, ⟨X, hX⟩, hafter, fun y h0 _ => ?_⟩
      have := ‹¬ j > 0#usize›
      scalar_tac
  · exact ⟨hpos, ⟨X0, h⟩, hafter⟩

/-- `insert_bank(sorted, count, bank)`: the bank inserted into the first
`count` ranges, after those whose start is at or below its own and before
the others, for `count` below `E` and first `count` ranges in ascending
order of their starts. -/
@[step] theorem insert_bank_spec {E : Usize} (sorted : Aeneas.Std.Array page_tables.PhysRange E)
    (count : Usize) (bank : page_tables.PhysRange) (hc : count.val < E.val)
    (hs : (sorted.val.take count.val).Pairwise (fun a b => a.start.val ≤ b.start.val)) :
    page_tables.ownership.insert_bank sorted count bank ⦃ arr =>
      ∃ k ≤ count.val, arr.val.take (count.val + 1) =
          (sorted.val.take count.val).take k ++ bank :: (sorted.val.take count.val).drop k ∧
        (∀ y ∈ (sorted.val.take count.val).take k, y.start.val ≤ bank.start.val) ∧
        (∀ y ∈ (sorted.val.take count.val).drop k, bank.start.val < y.start.val) ⦄ := by
  have hlen : sorted.val.length = E.val := sorted.property
  have hP : (sorted.val.take count.val).length = count.val := by simp; omega
  have hsplit : sorted.val = (sorted.val.take count.val).take count.val ++
      sorted.val[count.val]'(by omega) :: ((sorted.val.take count.val).drop count.val ++
        sorted.val.drop (count.val + 1)) := by
    rw [List.take_take, Nat.min_self, List.drop_eq_nil_of_le (by omega), List.nil_append,
      ← List.drop_eq_getElem_cons (by omega), List.take_append_drop]
  unfold page_tables.ownership.insert_bank
  step with insert_bank_loop_spec sorted bank count (sorted.val.take count.val)
    (sorted.val.drop (count.val + 1)) (sorted.val[count.val]'(by omega)) hsplit (by omega)
    (by rw [List.drop_eq_nil_of_le (by omega)]; simp)
  have hal : sorted1.val.length = E.val := sorted1.property
  step*
  refine ⟨«at».val, by omega, ?_,
    own_take_le_of_sorted (key := fun y : page_tables.PhysRange => y.start.val) hs
      (by omega) sorted1_post3, sorted1_post2⟩
  have hl : ((sorted.val.take count.val).take «at».val).length = «at».val := by simp; omega
  have hset := own_set_middle ((sorted.val.take count.val).take «at».val) X bank
    ((sorted.val.take count.val).drop «at».val ++ sorted.val.drop (count.val + 1))
  rw [hl] at hset
  rw [arr_post, Array.set_val_eq, sorted1_post1, bank1_post, hset]
  conv => lhs; rw [show count.val + 1 = (sorted.val.take count.val).length + 1 by omega]
  exact own_take_insert (by omega) bank

/-- `sort_banks(sorted, banks)`: the banks in ascending order of their
starts in the first entries of `sorted`, for at most `E` banks that stand for
`Bs`. -/
@[step] theorem sort_banks_spec {E : Usize} (sorted : Aeneas.Std.Array page_tables.PhysRange E)
    (banks : Slice page_tables.PhysRange) (Bs : List PhysRange)
    (hB : ListRel PhysRangeRepr banks.val Bs) (hl : banks.length ≤ E.val) :
    page_tables.ownership.sort_banks sorted banks ⦃ arr =>
      ∃ Q, ListRel PhysRangeRepr (arr.val.take banks.length) Q ∧ Q.Perm Bs ∧
        Q.Pairwise (fun a b => a.start.toNat ≤ b.start.toNat) ⦄ := by
  have hlen : Bs.length = banks.length := (listRel_length hB).symm
  unfold page_tables.ownership.sort_banks page_tables.ownership.sort_banks_loop
  apply loop.spec_decr_nat
    (measure := fun (x : Aeneas.Std.Array page_tables.PhysRange E × Usize) =>
      banks.length - x.2.val)
    (inv := fun (x : Aeneas.Std.Array page_tables.PhysRange E × Usize) => x.2.val ≤ banks.length ∧
      ∃ Q, ListRel PhysRangeRepr (x.1.val.take x.2.val) Q ∧ Q.Perm (Bs.take x.2.val) ∧
        Q.Pairwise (fun a b => a.start.toNat ≤ b.start.toNat))
  · rintro ⟨arr, i⟩ ⟨hi, Q, hQ, hperm, hsort⟩
    dsimp only at hi hQ hperm hsort
    have hcode : (arr.val.take i.val).Pairwise (fun a b => a.start.val ≤ b.start.val) :=
      (own_listRel_pairwise (fun a b a' b' h h' => by
        rw [← physRange_start h, ← physRange_start h']) hQ).2 hsort
    unfold page_tables.ownership.sort_banks_loop.body
    step*
    · have hil : i.val < Bs.length := by scalar_tac
      have hr := own_listRel_getElem hB i.val (by scalar_tac) hil
      rw [← pr_post] at hr
      have hbefore : ∀ y ∈ Q.take k, y.start.toNat ≤ Bs[i.val].start.toNat :=
        (own_listRel_forall (fun a b h => by rw [← physRange_start h, ← physRange_start hr])
          (own_listRel_take k hQ)).1 sorted1_post1
      have hafter : ∀ y ∈ Q.drop k, Bs[i.val].start.toNat < y.start.toNat :=
        (own_listRel_forall (fun a b h => by rw [← physRange_start h, ← physRange_start hr])
          (own_listRel_drop k hQ)).1 sorted1_post2
      obtain ⟨hp, hs⟩ := own_insert_sorted hsort hbefore hafter
      refine ⟨by scalar_tac, ⟨Q.take k ++ Bs[i.val] :: Q.drop k, ?_, ?_, hs⟩, by scalar_tac⟩
      · rw [index1_post, sorted1_post]
        exact own_listRel_append (own_listRel_take k hQ) ⟨hr, own_listRel_drop k hQ⟩
      · rw [index1_post, List.take_succ_eq_append_getElem hil]
        exact hp.trans ((hperm.cons _).trans (List.perm_append_singleton _ _).symm)
    · have h1 : i.val = Bs.length := by scalar_tac
      refine ⟨Q, ?_, ?_, hsort⟩
      · rw [← hlen, ← h1]; exact hQ
      · rwa [h1, List.take_length] at hperm
  · exact ⟨by simp, [], by simp, by simp, by simp⟩

/-- The loop of `bank_extents` from the address `at1`, for a bank `⟨s, l⟩` on
pages that stands for `B`, exclusions that stand for `Xs`, a count `used` at
most `E` whose first `used` extents stand for `D`, and `at1` at or above the
start of the bank and strictly inside no free run: the extents `T`, which
are `D` and the free extents of the runs from `at1` on, or
`MetadataExhausted` when they are more than `E`. -/
theorem bank_extents_loop_spec {E : Usize} (extents : Aeneas.Std.Array page_tables.Extent E)
    (used index : Usize) (s l : U64) (exclusions : Slice page_tables.Exclusion) (at1 : U64)
    (Xs : List Exclusion) (B : PhysRange) (hX : ListRel ExclusionRepr exclusions.val Xs)
    (hb : PhysRangeRepr ⟨s, l⟩ B) (hBp : B.onPages = true) (D T : List Extent)
    (hD : ListRel ExtentRepr (extents.val.take used.val) D) (hu : used.val ≤ E.val)
    (hlo : B.start.toNat ≤ at1.val)
    (hin : NotInside (cutAll (Xs.filterMap (·.cut B)) [(B.start.toNat, B.endNat)]) at1.val)
    (hT : D ++ extentsOfRuns index.val ((cutAll (Xs.filterMap (·.cut B))
      [(B.start.toNat, B.endNat)]).filter (fun r => decide (at1.val ≤ r.1))) = T) :
    page_tables.ownership.bank_extents_loop extents used index s l exclusions at1 ⦃ r ext =>
      match r with
      | .Ok u => ListRel ExtentRepr (ext.val.take u.val) T ∧ u.val ≤ E.val
      | .Err e => e = .MetadataExhausted ∧ E.val < T.length ⦄ := by
  have hfb := physRange_fits hb
  have hBe : B.endNat % 4096 = 0 := by
    simp only [PhysRange.onPages, Bool.and_eq_true, beq_iff_eq, PAGE_SIZE] at hBp; exact hBp.2
  have hC : ∀ c ∈ Xs.filterMap (·.cut B), c.1 < c.2 := by
    intro c hc; obtain ⟨x, -, hx⟩ := List.mem_filterMap.1 hc; exact (cut_some hx).1
  have hlh := range_lt B
  have hend : B.endNat = s.val + l.val := physRange_endNat hb
  have hext : extents.val.length = E.val := extents.property
  unfold page_tables.ownership.bank_extents_loop
  apply loop.spec_decr_nat
    (measure := fun (x : Aeneas.Std.Array page_tables.Extent E × Usize × U64) =>
      B.endNat - x.2.2.val)
    (inv := fun (x : Aeneas.Std.Array page_tables.Extent E × Usize × U64) =>
      x.2.1.val ≤ E.val ∧ B.start.toNat ≤ x.2.2.val ∧
      NotInside (cutAll (Xs.filterMap (·.cut B)) [(B.start.toNat, B.endNat)]) x.2.2.val ∧
      ∃ D', ListRel ExtentRepr (x.1.val.take x.2.1.val) D' ∧
        D' ++ extentsOfRuns index.val ((cutAll (Xs.filterMap (·.cut B))
          [(B.start.toNat, B.endNat)]).filter (fun r => decide (x.2.2.val ≤ r.1))) = T)
  · rintro ⟨ext, u, p⟩ ⟨hu, hlo, hin, D', hD', hT'⟩
    dsimp only at hu hlo hin hD' hT'
    have hext' : ext.val.length = E.val := ext.property
    unfold page_tables.ownership.bank_extents_loop.body
    step*
    all_goals try
        (have hpl : p.val < B.endNat := by rw [hend, ← i1_post]; exact ‹p < i1›
         have hF : (reach.val, stop.val) =
             (Xs.filterMap (·.cut B)).foldl (sweepStep p.val) (p.val, B.endNat) := by
           rw [reach_post, foldl_cutStep]
         have e1 : ((Xs.filterMap (·.cut B)).foldl (sweepStep p.val) (p.val, B.endNat)).1 =
             reach.val := by rw [← hF]
         have e2 : ((Xs.filterMap (·.cut B)).foldl (sweepStep p.val) (p.val, B.endNat)).2 =
             stop.val := by rw [← hF]
         obtain ⟨hr1, hr2, hr3⟩ := sweep_reach p.val (Xs.filterMap (·.cut B)) (p.val, B.endNat)
         obtain ⟨hn1, hn2, hn3⟩ := sweep_nearest p.val (Xs.filterMap (·.cut B)) (p.val, B.endNat)
         rw [e1] at hr1 hr2 hr3
         rw [e2] at hn1 hn2 hn3
         dsimp only at hr1 hr3 hn1 hn3
         clear e1 e2 hF reach_post)
    · have hgt : p.val < reach.val := ‹reach > p›
      have hc : ∃ c ∈ Xs.filterMap (·.cut B), c.1 ≤ p.val ∧ c.2 = reach.val := by
        rcases hr3 with h | h
        · omega
        · exact h
      obtain ⟨hf, hni⟩ := own_runs_skip hC hlh hgt hc hin
      exact ⟨hu, by omega, hni, ⟨D', hD', by rw [← hf]; exact hT'⟩, by omega⟩
    · have hle : ¬ p.val < reach.val := ‹¬ reach > p›
      have hreach : ∀ c ∈ Xs.filterMap (·.cut B), c.1 ≤ p.val → c.2 ≤ p.val :=
        fun c hc h => Nat.le_trans (hr2 c hc h) (by omega)
      have hpq : p.val < stop.val := by
        rcases hn3 with h | ⟨c, _, h1, h2⟩ <;> omega
      obtain ⟨hf, hni⟩ := own_runs_take hC hlh hlo hpl hreach hpq hn1 hn2 hn3 hin
      clear hr3 hn3 hr2 hn2 hreach
      have hfit := B.fits
      obtain ⟨g, hg, hg1, hg2⟩ := rangeOf?_exists (s := p.val) (l := stop.val - p.val) (by omega)
        (by unfold PhysRange.endNat at hn1; omega)
      have hex : extentsOfRuns index.val ((p.val, stop.val) ::
          (cutAll (Xs.filterMap (·.cut B)) [(B.start.toNat, B.endNat)]).filter
            (fun r => decide (stop.val ≤ r.1))) =
          ⟨g, index.val, .free⟩ :: extentsOfRuns index.val
            ((cutAll (Xs.filterMap (·.cut B)) [(B.start.toNat, B.endNat)]).filter
              (fun r => decide (stop.val ≤ r.1))) := by
        simp only [extentsOfRuns, List.filterMap_cons, hg, Option.map_some]
      have hge : E.val ≤ u.val := ‹u ≥ E›
      have hl := listRel_length hD'
      rw [List.length_take, hext'] at hl
      rw [← hT', hf, hex, List.length_append, List.length_cons]
      omega
    · have hle : ¬ p.val < reach.val := ‹¬ reach > p›
      rcases hn3 with h | ⟨c, _, h1, h2⟩ <;> omega
    · have hle : ¬ p.val < reach.val := ‹¬ reach > p›
      have hreach : ∀ c ∈ Xs.filterMap (·.cut B), c.1 ≤ p.val → c.2 ≤ p.val :=
        fun c hc h => Nat.le_trans (hr2 c hc h) (by omega)
      have hpq : p.val < stop.val := by
        rcases hn3 with h | ⟨c, _, h1, h2⟩ <;> omega
      obtain ⟨hf, hni⟩ := own_runs_take hC hlh hlo hpl hreach hpq hn1 hn2 hn3 hin
      clear hr3 hn3 hr2 hn2 hreach
      have hfit := B.fits
      obtain ⟨g, hg, hg1, hg2⟩ := rangeOf?_exists (s := p.val) (l := stop.val - p.val) (by omega)
        (by unfold PhysRange.endNat at hn1; omega)
      have hex : extentsOfRuns index.val ((p.val, stop.val) ::
          (cutAll (Xs.filterMap (·.cut B)) [(B.start.toNat, B.endNat)]).filter
            (fun r => decide (stop.val ≤ r.1))) =
          ⟨g, index.val, .free⟩ :: extentsOfRuns index.val
            ((cutAll (Xs.filterMap (·.cut B)) [(B.start.toNat, B.endNat)]).filter
              (fun r => decide (stop.val ≤ r.1))) := by
        simp only [extentsOfRuns, List.filterMap_cons, hg, Option.map_some]
      have hlt : u.val < E.val := by have := ‹¬ u ≥ E›; scalar_tac
      have hrep : ExtentRepr (⟨⟨p, i2⟩, index, .Free⟩ : page_tables.Extent)
          ⟨g, index.val, .free⟩ := by
        refine ⟨⟨(word64_eq_iff.2 hg1.symm).symm, (word64_eq_iff.2 ?_).symm⟩, rfl, rfl⟩
        show i2.val = g.len.toNat
        unfold PhysRange.endNat at hg2
        omega
      refine ⟨by scalar_tac, by omega, hni, ⟨D' ++ [⟨g, index.val, .free⟩], ?_, ?_⟩, by omega⟩
      · rw [used1_post, a_post, Array.set_val_eq, own_take_set_succ (by omega) _]
        exact own_listRel_append hD' ⟨hrep, trivial⟩
      · rw [List.append_assoc, List.singleton_append, ← hex, ← hf]
        exact hT'
    · have hge : B.endNat ≤ p.val := by
        have := ‹¬ p < i1›; rw [hend]; scalar_tac
      refine ⟨?_, hu⟩
      rw [← hT', own_runs_end hC hlh hge]
      simpa [extentsOfRuns] using hD'
  · exact ⟨hu, hlo, hin, D, hD, hT⟩

/-- `bank_extents(extents, used, index, bank, exclusions)`: the free extents
of the bank of index `index` after the extents `D`, for a bank on pages that
stands for `B`, exclusions that stand for `Xs`, and a count `used` at most
`E` whose first `used` extents stand for `D`; or `MetadataExhausted` when
they are more than `E`. -/
@[step] theorem bank_extents_spec {E : Usize} (extents : Aeneas.Std.Array page_tables.Extent E)
    (used index : Usize) (bank : page_tables.PhysRange) (exclusions : Slice page_tables.Exclusion)
    (Xs : List Exclusion) (B : PhysRange) (D : List Extent)
    (hX : ListRel ExclusionRepr exclusions.val Xs) (hb : PhysRangeRepr bank B)
    (hBp : B.onPages = true) (hD : ListRel ExtentRepr (extents.val.take used.val) D)
    (hu : used.val ≤ E.val) :
    page_tables.ownership.bank_extents extents used index bank exclusions ⦃ r ext =>
      match r with
      | .Ok u => ListRel ExtentRepr (ext.val.take u.val) (D ++ bankExtents Xs index.val B) ∧
          u.val ≤ E.val
      | .Err e => e = .MetadataExhausted ∧ E.val < (D ++ bankExtents Xs index.val B).length ⦄ := by
  have hC : ∀ c ∈ Xs.filterMap (·.cut B), c.1 < c.2 := by
    intro c hc; obtain ⟨x, -, hx⟩ := List.mem_filterMap.1 hc; exact (cut_some hx).1
  obtain ⟨h1, h2⟩ := own_runs_start hC (range_lt B)
  unfold page_tables.ownership.bank_extents
  exact bank_extents_loop_spec extents used index bank.start bank.len exclusions bank.start Xs B hX
    hb hBp D _ hD hu (by rw [physRange_start hb]) (by rw [← physRange_start hb]; exact h2)
    (by rw [← physRange_start hb, h1, own_bankExtents_eq])

/-- `initial_extents(extents, banks, count, exclusions)`: the free extents of
the first `count` banks, `initialExtents`, for `count` at most `E`, first
`count` banks on pages that stand for `SB`, and exclusions that stand for
`Xs`; or `MetadataExhausted` when they are more than `E`. -/
@[step] theorem initial_extents_spec {E : Usize} (extents : Aeneas.Std.Array page_tables.Extent E)
    (banks : Aeneas.Std.Array page_tables.PhysRange E) (count : Usize)
    (exclusions : Slice page_tables.Exclusion) (SB : List PhysRange) (Xs : List Exclusion)
    (hSB : ListRel PhysRangeRepr (banks.val.take count.val) SB) (hc : count.val ≤ E.val)
    (hon : ∀ b ∈ SB, b.onPages = true) (hX : ListRel ExclusionRepr exclusions.val Xs) :
    page_tables.ownership.initial_extents extents banks count exclusions ⦃ r ext =>
      match r with
      | .Ok u => ListRel ExtentRepr (ext.val.take u.val) (initialExtents SB Xs) ∧ u.val ≤ E.val
      | .Err e => e = .MetadataExhausted ∧ E.val < (initialExtents SB Xs).length ⦄ := by
  have hc' : count.val ≤ banks.val.length := by rw [banks.property]; exact hc
  have hlen : SB.length = count.val := by
    have := listRel_length hSB; rw [List.length_take, banks.property] at this; omega
  unfold page_tables.ownership.initial_extents page_tables.ownership.initial_extents_loop
  apply loop.spec_decr_nat
    (measure := fun (x : Aeneas.Std.Array page_tables.Extent E × Usize × Usize) =>
      count.val - x.2.2.val)
    (inv := fun (x : Aeneas.Std.Array page_tables.Extent E × Usize × Usize) =>
      x.2.2.val ≤ count.val ∧ x.2.1.val ≤ E.val ∧
      ∃ D, ListRel ExtentRepr (x.1.val.take x.2.1.val) D ∧
        D ++ initialExtents.go Xs x.2.2.val (SB.drop x.2.2.val) = initialExtents SB Xs)
  · rintro ⟨ext, u, k⟩ ⟨hk, hu, D, hD, hT⟩
    dsimp only at hk hu hD hT
    unfold page_tables.ownership.initial_extents_loop.body
    step*
    case B => exact SB[k.val]'(by scalar_tac)
    case hb =>
      obtain ⟨_, hr⟩ := own_listRel_take_getElem hSB hc' k.val (by scalar_tac)
      rw [pr_post]; exact hr
    case hBp => exact hon _ (List.getElem_mem _)
    case h2 =>
      have h1 : k.val = SB.length := by scalar_tac
      rw [h1, List.drop_length, show initialExtents.go Xs SB.length [] = [] from rfl,
        List.append_nil] at hT
      exact ⟨hT ▸ hD, hu⟩
    have hkl : k.val < SB.length := by scalar_tac
    have hgo := own_go_drop (exclusions := Xs) hkl
    cases r with
    | Ok v =>
      obtain ⟨hv1, hv2⟩ := r_post
      step*
      have hval : val = v := by
        have h1 := ‹cf = core.ops.control_flow.ControlFlow.Continue val›
        rw [cf_post] at h1
        cases h1; rfl
      subst hval
      refine ⟨by scalar_tac, hv2, ⟨D ++ bankExtents Xs k.val SB[k.val], hv1, ?_⟩, by scalar_tac⟩
      rw [bank1_post, List.append_assoc, ← hgo]
      exact hT
    | Err e0 =>
      obtain ⟨he, hlt⟩ := r_post
      step*
      have hres : residual = .Err e0 := by
        have h1 := ‹cf = core.ops.control_flow.ControlFlow.Break residual›
        rw [cf_post] at h1
        cases h1; rfl
      rw [residual_post] at hres
      cases hres
      rw [r1_post, ← e_post]
      refine ⟨he, ?_⟩
      rw [← hT, hgo, ← List.append_assoc, List.length_append]
      omega
  · exact ⟨by simp, by simp, [], by simp, by simp [initialExtents]⟩

/-- `Ownership::new(arena, banks, exclusions)`: the table of `Ownership.new`,
or its error, for banks and exclusions that stand for `Bs` and `Xs`. -/
@[step] theorem ownership_new_spec (E X : Usize) (arena : U64)
    (banks : Slice page_tables.PhysRange) (exclusions : Slice page_tables.Exclusion)
    (Bs : List PhysRange) (Xs : List Exclusion) (hB : ListRel PhysRangeRepr banks.val Bs)
    (hX : ListRel ExclusionRepr exclusions.val Xs) :
    page_tables.ownership.Ownership.new E X arena banks exclusions ⦃ r =>
      Agrees OwnershipRepr ownershipErrorOf r
        (Ownership.new (E := E.val) (X := X.val) (word64 arena) Bs Xs) ⦄ := by
  have hlB : Bs.length = banks.length := (listRel_length hB).symm
  have hlX : Xs.length = exclusions.length := (listRel_length hX).symm
  unfold page_tables.ownership.Ownership.new
  step*
  case SB => exact sortByKey (·.start.toNat) Bs
  case hSB =>
    have hno : anyOverlap Bs = false := by
      rw [← b2_post]; exact (Bool.not_eq_true _).mp ‹¬b2 = true›
    rw [← own_sorted_eq hno sorted1_post1 sorted1_post2, Slice.len_val]
    exact sorted1_post
  case hon =>
    have hall : Bs.all (·.onPages) = true := by rw [← b_post]; exact ‹b = true›
    intro x hx
    exact List.all_eq_true.1 hall x ((sortByKey_perm _ Bs).mem_iff.1 hx)
  case h2 =>
    have hall : Bs.all (·.onPages) = false := by
      rw [← b_post]; exact (Bool.not_eq_true _).mp ‹¬b = true›
    rw [own_new_eq]
    simp only [hall, Bool.not_false, ↓reduceIte, agrees_err_error, ownershipErrorOf]
  all_goals
    have hall : Bs.all (·.onPages) = true := by rw [← b_post]; exact ‹b = true›
  · have h0 : word64 0#u64 = 0 := rfl
    rw [own_new_eq]
    simp only [hall, h0, Bool.not_true, Bool.false_eq_true, ↓reduceIte, agrees_err_error,
      ownershipErrorOf]
  all_goals
    have ha : ¬ word64 arena = 0 := by
      intro h; apply ‹¬arena = 0#u64›; apply u64_eq_zero_iff.2
      have := congrArg UInt64.toNat h; rwa [word64_toNat, UInt64.toNat_zero] at this
  · have hl0 : banks.length = 0 := by rw [← b1_post]; exact ‹b1 = true›
    have he : Bs.isEmpty = true := by rw [List.isEmpty_iff, ← List.length_eq_zero_iff]; omega
    rw [own_new_eq]
    simp only [hall, ha, he, Bool.not_true, Bool.false_eq_true, ↓reduceIte, agrees_err_error,
      ownershipErrorOf]
  all_goals
    have he : Bs.isEmpty = false := by
      have hl0 : ¬ banks.length = 0 := by rw [← b1_post]; exact ‹¬b1 = true›
      rw [Bool.eq_false_iff, ne_eq, List.isEmpty_iff, ← List.length_eq_zero_iff]; omega
  · have hE : E.val < Bs.length := by have := ‹banks.len > E›; scalar_tac
    rw [own_new_eq]
    simp only [hall, ha, he, hE, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      agrees_err_error, ownershipErrorOf]
  all_goals
    have hE : ¬ E.val < Bs.length := by have := ‹¬banks.len > E›; scalar_tac
  · have ho : anyOverlap Bs = true := by rw [← b2_post]; exact ‹b2 = true›
    rw [own_new_eq]
    simp only [hall, ha, he, hE, ho, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      agrees_err_error, ownershipErrorOf]
  all_goals
    have ho : anyOverlap Bs = false := by
      rw [← b2_post]; exact (Bool.not_eq_true _).mp ‹¬b2 = true›
  · have hXl : X.val < Xs.length := by have := ‹exclusions.len > X›; scalar_tac
    rw [own_new_eq]
    simp only [hall, ha, he, hE, ho, hXl, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      agrees_err_error, ownershipErrorOf]
  have hXl : ¬ X.val < Xs.length := by have := ‹¬exclusions.len > X›; scalar_tac
  have hQ := own_sorted_eq ho sorted1_post1 sorted1_post2
  subst hQ
  cases r with
  | Ok v =>
    obtain ⟨hv1, hv2⟩ := r_post
    step*
    have hval : val = v := by
      have h1 := ‹cf = core.ops.control_flow.ControlFlow.Continue val›
      rw [cf_post] at h1
      cases h1; rfl
    subst hval
    have h7 : ¬ E.val < (initialExtents (sortByKey (·.start.toNat) Bs) Xs).length := by
      have := listRel_length hv1
      rw [List.length_take, extents1.property] at this
      omega
    rw [own_new_eq]
    simp only [hall, ha, he, hE, ho, hXl, h7, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      agrees_ok_ok]
    refine ⟨by scalar_tac, hv2, by scalar_tac, rfl, ?_, hv1, ?_, rfl⟩
    · rw [Slice.len_val]; exact sorted1_post
    · rw [Slice.len_val, records1_post]; exact hX
  | Err e0 =>
    obtain ⟨he0, hlt⟩ := r_post
    step*
    have hres : residual = .Err e0 := by
      have h1 := ‹cf = core.ops.control_flow.ControlFlow.Break residual›
      rw [cf_post] at h1
      cases h1; rfl
    rw [residual_post] at hres
    cases hres
    rw [r_post, ← e_post, he0, own_new_eq]
    simp only [hall, ha, he, hE, ho, hXl, hlt, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      agrees_err_error, ownershipErrorOf]

end Krepi.Proofs.PageTables.Refinement
