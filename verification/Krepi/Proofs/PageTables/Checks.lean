module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.SpanLemmas
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.PoolLemmas
import Krepi.Proofs.PageTables.WellFormedLemmas
import Krepi.Proofs.PageTables.TreeLemmas
import Krepi.Proofs.PageTables.WalkLemmas
import Krepi.Proofs.PageTables.LeavesLemmas
import Krepi.Proofs.PageTables.RunLemmas
import Krepi.Proofs.PageTables.OwnerLemmas
import Krepi.Proofs.PageTables.NewLemmas
import Krepi.Proofs.PageTables.PreserveLemmas

/-!
# Page tables: proofs about the checks of the invariants

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about the checks of the invariants, whose
type is exactly that statement: that each computable check agrees with its
invariant, on every value or on every value that keeps the invariants that
the check reads.

The checks of the structural invariants, `Tables.checkWellFormed`,
`Ownership.checkWellFormed` and `Shared.checkWellFormed`, and the check of
the offset of the direct map, `Shared.checkDirectMapOffset`, are proved:
each conjunct of a structural check is rewritten into its proposition (the
lists of tables that the check of a table set reads by
`Krepi.Proofs.PageTables.TreeLemmas`), and the offset check walks the leaves
of the direct map (`Tables.leaves`, `Krepi.Proofs.PageTables.LeavesLemmas`)
in both directions.

The five checks of the functional invariants of the page ownership table are
proved on the values that their statements name:

- `checkFreeExtentsMaximal` and `checkGenerationsBelowCounter` compare each
  extent, or each pair of extents, as the invariant does; a holder of a page
  is the holding of an extent that holds it, and an extent of a well-formed
  table holds its first page (`Krepi.Proofs.PageTables.OwnerLemmas`,
  `PreserveLemmas`);
- `checkHolderRanges`: in a well-formed table a page has the owner of the
  one extent that holds it, so two held extents of one generation would give
  the first page of the earlier one to the later one as well;
- `checkOneOwner` and `checkFreeOrHeldUsable` compare runs of pages with
  `cutAll`: with runs and cuts on pages, the cuts leave nothing of a run
  exactly when every page of the run lies in a cut (the private
  `cutAll_single_eq_nil_iff` and `all_cutAll_iff`, from
  `Krepi.Proofs.PageTables.RunLemmas`). A page lies in the run of an extent
  on pages exactly when the extent holds it, and in the cut of an exclusion
  of a bank exactly when the exclusion touches it (`cut_some` of
  `Krepi.Proofs.PageTables.NewLemmas`); one owner is then
  `ownersOf_length_eq_one`, and the free and held pages are those of the
  extents (`freeOrHeld_iff`).

Every theorem here is proved. Mathlib is imported so that the gate counts the
heartbeats of each theorem.
-/

namespace Krepi.Proofs.PageTables.Checks

open Krepi.SpecProperties.PageTables
open Krepi.Spec.PageTables
open Krepi.Proofs.PageTables

/-- `omega` after the page size is written as its value. -/
local macro "page_omega" : tactic => `(tactic| (simp only [PAGE_SIZE] at *; omega))

private theorem conj_tables {r : Region} {N : Nat} (s : Tables r N) (base : UInt64) :
    (sortByKey id (s.level2Tables base ++ s.level3Tables base) == List.range' 1 (s.used - 1)) = true ↔
      (∀ t i, s.IsParent base t → ¬ s.PointsAt base t i 0) ∧
      (∀ c, 1 ≤ c → c < s.used → ∃ t i, s.IsParent base t ∧ s.PointsAt base t i c) ∧
      (∀ t i t' i' c, s.IsParent base t → s.IsParent base t' →
        s.PointsAt base t i c → s.PointsAt base t' i' c → t = t' ∧ i = i') := by
  rw [beq_iff_eq, sort_eq_range_iff]
  constructor
  · rintro ⟨hn, hm⟩
    have h0 : 0 ∉ s.level2Tables base ++ s.level3Tables base := fun h => by
      have := (hm 0).1 h; omega
    refine ⟨fun t i hp h => h0 ((mem_tablesOf s base).2 ⟨t, i, hp, h⟩),
      fun c h1 h2 => (mem_tablesOf s base).1 ((hm c).2 ⟨h1, h2⟩),
      (tablesOf_nodup_iff s base h0).1 hn⟩
  · rintro ⟨h8, h9, h10⟩
    have h0 : 0 ∉ s.level2Tables base ++ s.level3Tables base := fun h => by
      obtain ⟨t, i, hp, h⟩ := (mem_tablesOf s base).1 h
      exact h8 t i hp h
    refine ⟨(tablesOf_nodup_iff s base h0).2 h10, fun c => ⟨fun h => ?_, fun ⟨h1, h2⟩ =>
      (mem_tablesOf s base).2 (h9 c h1 h2)⟩⟩
    obtain ⟨t, i, hp, h⟩ := (mem_tablesOf s base).1 h
    refine ⟨Nat.pos_of_ne_zero fun hc => ?_, (pointsAt_lt h).1⟩
    subst hc; exact h8 t i hp h

public theorem checkTablesWellFormed : CheckTablesWellFormed := by
  intro r N s base bits
  have h1 : poolOk N base bits = true ↔ PoolOk N base bits := by
    simp [poolOk, PoolOk, and_assoc]
  have h4 : ((List.range N).all fun t => decide (t < s.used) || s.table t == Table.zero) = true ↔
      ∀ t, s.used ≤ t → t < N → s.table t = Table.zero := by
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
    constructor
    · intro h t ht1 ht2
      rcases h t ht2 with h | h
      · omega
      · exact h
    · intro h t ht
      by_cases h' : t < s.used
      · exact Or.inl h'
      · exact Or.inr (h t (by omega) ht)
  have h5 : ((List.range ENTRIES).all fun i =>
      s.entry 0 i == 0 || (s.pointsAt? base 0 i).isSome) = true ↔
      ∀ i, i < ENTRIES → s.entry 0 i = 0 ∨ ∃ c, s.PointsAt base 0 i c := by
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
      Option.isSome_iff_exists]
    exact forall_congr' fun i => imp_congr_right fun hi =>
      or_congr_right (exists_congr fun c => pointsAt?_eq_some s base hi)
  have h6 : ((s.level2Tables base).all fun t => (List.range ENTRIES).all fun i =>
      s.entry t i == 0 || (s.pointsAt? base t i).isSome ||
        (isReadWriteBlock (s.entry t i) && decide ((blockAddress (s.entry t i)).toNat <
          2 ^ bits.toNat))) = true ↔
      ∀ t, s.IsLevel2 base t → ∀ i, i < ENTRIES →
        s.entry t i = 0 ∨ (∃ c, s.PointsAt base t i c) ∨
          (isReadWriteBlock (s.entry t i) = true ∧
            (blockAddress (s.entry t i)).toNat < 2 ^ bits.toNat) := by
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq,
      Option.isSome_iff_exists, Bool.and_eq_true, decide_eq_true_eq, mem_level2Tables, or_assoc]
    exact forall_congr' fun t => imp_congr_right fun _ => forall_congr' fun i =>
      imp_congr_right fun hi => or_congr_right (or_congr_left
        (exists_congr fun c => pointsAt?_eq_some s base hi))
  have h7 : ((s.level3Tables base).all fun t => (List.range ENTRIES).all fun i =>
      s.entry t i == 0 || ((Kind.ofPage (s.entry t i)).isSome &&
        decide ((outputAddress (s.entry t i)).toNat < 2 ^ bits.toNat))) = true ↔
      ∀ t, s.IsLevel3 base t → ∀ i, i < ENTRIES →
        s.entry t i = 0 ∨
          ((∃ k, s.entry t i = descriptor k (outputAddress (s.entry t i))) ∧
            (outputAddress (s.entry t i)).toNat < 2 ^ bits.toNat) := by
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
      decide_eq_true_eq, mem_level3Tables, ofPage_isSome_iff]
    exact forall_congr' fun t => imp_congr_right fun _ => forall_congr' fun i =>
      imp_congr_right fun _ => or_congr_right (and_congr_left fun _ =>
        exists_congr fun k => eq_comm)
  unfold Tables.checkWellFormed Tables.WellFormed
  simp only [Bool.and_eq_true, decide_eq_true_eq, h1, h4, h5, h6, h7, conj_tables, and_assoc]

public theorem checkOwnershipWellFormed : CheckOwnershipWellFormed := by
  intro E X t
  unfold Ownership.checkWellFormed Ownership.WellFormed
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true, Krepi.Proofs.Fdt.allPairs_iff, decide_eq_true_eq, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => and_congr_right fun _ => and_congr_left fun _ =>
    forall_congr' fun x => imp_congr_right fun _ => and_congr_right fun _ => ?_
  unfold Extent.InBank
  cases t.banks[x.bank]? <;> simp

public theorem checkSharedWellFormed : CheckSharedWellFormed := by
  intro E X s cfg
  unfold Shared.checkWellFormed Shared.WellFormed
  rw [Bool.and_eq_true, Bool.and_eq_true, checkTablesWellFormed, checkTablesWellFormed, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  cases s.ownership with
  | none => simp
  | some t => simpa using checkOwnershipWellFormed E X t

/-- Runs and cuts with ends on pages: the cuts leave nothing of the run
`[a, b)` exactly when every page of it lies in a cut. -/
private theorem cutAll_single_eq_nil_iff {cuts : List (Nat × Nat)} {a b : Nat}
    (hc : ∀ c ∈ cuts, c.1 % PAGE_SIZE = 0 ∧ c.2 % PAGE_SIZE = 0)
    (ha : a % PAGE_SIZE = 0) (hb : b % PAGE_SIZE = 0) (hab : a < b) :
    cutAll cuts [(a, b)] = [] ↔
      ∀ q, q % PAGE_SIZE = 0 → a ≤ q → q < b → ∃ c ∈ cuts, c.1 ≤ q ∧ q < c.2 := by
  have hn : ∀ r ∈ [(a, b)], r.1 < r.2 := by simpa using hab
  have hr : ∀ r ∈ [(a, b)], r.1 % PAGE_SIZE = 0 ∧ r.2 % PAGE_SIZE = 0 := by simpa using ⟨ha, hb⟩
  rw [runs_eq_nil_iff (cutAll_nonempty cuts _ hn)]
  constructor
  · intro h q _ h1 h2
    by_cases hx : ∃ c ∈ cuts, c.1 ≤ q ∧ q < c.2
    · exact hx
    · exact absurd ((cutAll_mem q cuts _).2 ⟨⟨(a, b), List.mem_singleton_self _, h1, h2⟩,
        fun c hc' h' => hx ⟨c, hc', h'⟩⟩) (h q)
  · rintro h p ⟨r, hr', -, -⟩
    have hal := cutAll_aligned cuts _ hc hr r hr'
    have hnr := cutAll_nonempty cuts _ hn r hr'
    obtain ⟨⟨r', hr'', h1, h2⟩, hno⟩ := (cutAll_mem r.1 cuts _).1 ⟨r, hr', Nat.le_refl _, hnr⟩
    simp only [List.mem_singleton] at hr''
    subst hr''
    obtain ⟨c, hc', hc''⟩ := h r.1 hal.1 h1 h2
    exact hno c hc' hc''

/-- Runs on pages, each cut by cuts with ends on pages: the cuts leave nothing
of any run exactly when every page of a run lies in a cut. -/
private theorem all_cutAll_iff {A C : List (Nat × Nat)}
    (hA : ∀ a ∈ A, a.1 % PAGE_SIZE = 0 ∧ a.2 % PAGE_SIZE = 0 ∧ a.1 < a.2)
    (hC : ∀ c ∈ C, c.1 % PAGE_SIZE = 0 ∧ c.2 % PAGE_SIZE = 0 ∧ c.1 < c.2) :
    (∀ a ∈ A, cutAll C [a] = []) ↔
      ∀ q, q % PAGE_SIZE = 0 → (∃ a ∈ A, a.1 ≤ q ∧ q < a.2) → ∃ c ∈ C, c.1 ≤ q ∧ q < c.2 := by
  have hC' : ∀ c ∈ C, c.1 % PAGE_SIZE = 0 ∧ c.2 % PAGE_SIZE = 0 :=
    fun c hc => ⟨(hC c hc).1, (hC c hc).2.1⟩
  constructor
  · rintro h q hq ⟨⟨a, b⟩, ha, h1, h2⟩
    obtain ⟨h3, h4, h5⟩ := hA _ ha
    exact (cutAll_single_eq_nil_iff hC' h3 h4 h5).1 (h _ ha) q hq h1 h2
  · rintro h ⟨a, b⟩ ha
    obtain ⟨h3, h4, h5⟩ := hA _ ha
    exact (cutAll_single_eq_nil_iff hC' h3 h4 h5).2 fun q hq h1 h2 => h q hq ⟨_, ha, h1, h2⟩

/-- A page lies in a range on pages exactly when the range holds it. -/
private theorem lt_iff_holds {r : PhysRange} (hr : r.onPages = true) {q : Nat}
    (hq : q % PAGE_SIZE = 0) : (r.start.toNat ≤ q ∧ q < r.endNat) ↔ r.holdsPage q = true := by
  simp only [PhysRange.onPages, Bool.and_eq_true, beq_iff_eq] at hr
  rw [holdsPage_iff]
  constructor <;> intro h <;> page_omega

/-- The ends of the extents of a well-formed table are on pages, and each
extent is nonempty. -/
private theorem extents_runs {E X : Nat} {t : Ownership E X} (hwf : t.WellFormed) :
    ∀ c ∈ t.extents.map (fun e => (e.range.start.toNat, e.range.endNat)),
      c.1 % PAGE_SIZE = 0 ∧ c.2 % PAGE_SIZE = 0 ∧ c.1 < c.2 := by
  intro c hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
  have h := (hwf.2.2.2.2.2.1 e he).1
  simp only [PhysRange.onPages, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1, h.2, range_lt e.range⟩

/-- A page lies in the run of an extent of a well-formed table exactly when
an extent holds it. -/
private theorem extents_runs_iff {E X : Nat} {t : Ownership E X} (hwf : t.WellFormed) {q : Nat}
    (hq : q % PAGE_SIZE = 0) :
    (∃ c ∈ t.extents.map (fun e => (e.range.start.toNat, e.range.endNat)), c.1 ≤ q ∧ q < c.2) ↔
      ∃ e ∈ t.extents, e.range.holdsPage q = true := by
  constructor
  · rintro ⟨c, hc, h1, h2⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hc
    exact ⟨e, he, (lt_iff_holds (hwf.2.2.2.2.2.1 e he).1 hq).1 ⟨h1, h2⟩⟩
  · rintro ⟨e, he, h⟩
    exact ⟨_, List.mem_map.2 ⟨e, he, rfl⟩, (lt_iff_holds (hwf.2.2.2.2.2.1 e he).1 hq).2 h⟩

/-- A page that an extent of a well-formed table holds is a page of a bank. -/
private theorem bank_of_holds {E X : Nat} {t : Ownership E X} (hwf : t.WellFormed) {e : Extent}
    (he : e ∈ t.extents) {q : Nat} (hq : e.range.holdsPage q = true) :
    ∃ b ∈ t.banks, b.holdsPage q = true := by
  obtain ⟨b, hb, hc⟩ := (hwf.2.2.2.2.2.1 e he).2
  refine ⟨b, List.mem_of_getElem? hb, ?_⟩
  simp only [PhysRange.contains, Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [holdsPage_iff] at hq ⊢
  omega

public theorem checkOneOwner : CheckOneOwner := by
  intro E X t hwf
  have hl : ExtentsInOrder t.extents := hwf.2.2.2.2.2.2.1
  have hep := hwf.2.2.2.2.2.1
  have hA : (t.extents.all fun e => t.exclusions.all fun x => !x.range.overlaps e.range) = true ↔
      ∀ q, q % PAGE_SIZE = 0 → (∃ e ∈ t.extents, e.range.holdsPage q = true) →
        ¬ ∃ x ∈ t.exclusions, x.range.touchesPage q = true := by
    simp only [List.all_eq_true, Bool.not_eq_true']
    constructor
    · rintro h q - ⟨e, he, hq⟩ ⟨x, hx, hxq⟩
      have := h e he x hx
      simp only [PhysRange.overlaps, Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
      rw [holdsPage_iff] at hq
      rw [touchesPage_iff] at hxq
      page_omega
    · intro h e he x hx
      rw [← Bool.not_eq_true]
      intro ho
      simp only [PhysRange.overlaps, Bool.and_eq_true, decide_eq_true_eq] at ho
      have he' := (hep e he).1
      simp only [PhysRange.onPages, Bool.and_eq_true, beq_iff_eq] at he'
      have h1 := range_lt e.range
      have h2 := range_lt x.range
      exact h (max x.range.start.toNat e.range.start.toNat / PAGE_SIZE * PAGE_SIZE)
        (by page_omega) ⟨e, he, by rw [holdsPage_iff]; page_omega⟩
        ⟨x, hx, by rw [touchesPage_iff]; page_omega⟩
  have hB : ∀ b ∈ t.banks,
      (cutAll ((t.extents.map fun e => (e.range.start.toNat, e.range.endNat)) ++
        t.exclusions.filterMap (·.cut b)) [(b.start.toNat, b.endNat)] = [] ↔
      ∀ q, q % PAGE_SIZE = 0 → b.holdsPage q = true →
        (∃ e ∈ t.extents, e.range.holdsPage q = true) ∨
          ∃ x ∈ t.exclusions, x.range.touchesPage q = true) := by
    intro b hb
    have hbo := hwf.2.2.1 b hb
    have hbo' := hbo
    simp only [PhysRange.onPages, Bool.and_eq_true, beq_iff_eq] at hbo'
    have hcuts : ∀ c ∈ (t.extents.map fun e => (e.range.start.toNat, e.range.endNat)) ++
        t.exclusions.filterMap (·.cut b), c.1 % PAGE_SIZE = 0 ∧ c.2 % PAGE_SIZE = 0 := by
      intro c hc
      rcases List.mem_append.1 hc with hc | hc
      · exact ⟨(extents_runs hwf c hc).1, (extents_runs hwf c hc).2.1⟩
      · obtain ⟨x, -, hx⟩ := List.mem_filterMap.1 hc
        exact (cut_some hx).2.2.2.1 hbo
    rw [cutAll_single_eq_nil_iff hcuts hbo'.1 hbo'.2 (range_lt b)]
    refine forall_congr' fun q => imp_congr_right fun hq => ?_
    rw [← lt_iff_holds hbo hq]
    constructor
    · intro h hbq
      obtain ⟨c, hc, h1, h2⟩ := h hbq.1 hbq.2
      rcases List.mem_append.1 hc with hc | hc
      · exact Or.inl ((extents_runs_iff hwf hq).1 ⟨c, hc, h1, h2⟩)
      · obtain ⟨x, hx, hxc⟩ := List.mem_filterMap.1 hc
        exact Or.inr ⟨x, hx, (((cut_some hxc).2.2.2.2 q hq).1 ⟨h1, h2⟩).1⟩
    · intro h h1 h2
      rcases h ⟨h1, h2⟩ with hH | ⟨x, hx, hxq⟩
      · obtain ⟨c, hc, h3⟩ := (extents_runs_iff hwf hq).2 hH
        exact ⟨c, List.mem_append_left _ hc, h3⟩
      · cases hc : x.cut b with
        | none =>
          rw [cut_none hc ((lt_iff_holds hbo hq).1 ⟨h1, h2⟩)] at hxq
          cases hxq
        | some c =>
          exact ⟨c, List.mem_append_right _ (List.mem_filterMap.2 ⟨x, hx, hc⟩),
            ((cut_some hc).2.2.2.2 q hq).2 ⟨hxq, h1, h2⟩⟩
  unfold Ownership.checkOneOwner Ownership.OneOwner
  rw [Bool.and_eq_true, hA, List.all_eq_true]
  simp only [beq_iff_eq, Ownership.ManagedPage, ownersOf_length_eq_one _ hl]
  constructor
  · rintro ⟨h1, h2⟩ q ⟨hq, b, hb, hbq⟩
    refine ⟨h1 q hq, fun hT => ?_⟩
    rcases (hB b hb).1 (h2 b hb) q hq hbq with h | h
    · exact h
    · exact absurd h hT
  · intro h
    refine ⟨fun q hq ⟨e, he, heq⟩ => ?_, fun b hb => (hB b hb).2 fun q hq hbq => ?_⟩
    · obtain ⟨b, hb, hbq⟩ := bank_of_holds hwf he heq
      exact (h q ⟨hq, b, hb, hbq⟩).1 ⟨e, he, heq⟩
    · by_cases hT : ∃ x ∈ t.exclusions, x.range.touchesPage q = true
      · exact Or.inr hT
      · exact Or.inl ((h q ⟨hq, b, hb, hbq⟩).2 hT)

public theorem checkHolderRanges : CheckHolderRanges := by
  intro E X t hwf _
  have hl : ExtentsInOrder t.extents := hwf.2.2.2.2.2.2.1
  unfold Ownership.checkHolderRanges Ownership.HolderRanges
  rw [Krepi.Proofs.Fdt.allPairs_iff]
  constructor
  · intro hp e he o n s hh q hq
    constructor
    · rintro ⟨o', s', hq'⟩
      obtain ⟨x, hx, hxq, hxh⟩ := ownerOf_held hq'
      rcases pairwise_mem_cases hp hx he with rfl | h | h
      · exact hxq
      · rw [hxh, hh] at h; simp [Holding.generation?] at h
      · rw [hxh, hh] at h; simp [Holding.generation?] at h
    · intro hq'
      exact ⟨o, s, by rw [ownerOf_of_mem hl he hq', hh]; rfl⟩
  · intro h
    refine List.Pairwise.imp_of_mem ?_ hl
    intro a b ha hb hab
    cases hA : a.holding with
    | free => rfl
    | held o n s =>
      cases hB : b.holding with
      | free => rfl
      | held o' m s' =>
        simp only [Holding.generation?, bne_iff_ne, ne_eq]
        rintro rfl
        have hpa := (hwf.2.2.2.2.2.1 a ha).1
        have hq := holdsPage_start hpa
        have h1 := (h b hb o' n s' hB a.range.start.toNat (by
          simp only [PhysRange.onPages, Bool.and_eq_true, beq_iff_eq] at hpa; exact hpa.1)).1
          ⟨o, s, by rw [ownerOf_of_mem hl ha hq, hA]; rfl⟩
        have := range_lt a.range
        rw [holdsPage_iff] at h1
        omega

public theorem checkGenerationsBelowCounter : CheckGenerationsBelowCounter := by
  intro E X t hwf
  have hl : ExtentsInOrder t.extents := hwf.2.2.2.2.2.2.1
  unfold Ownership.checkGenerationsBelowCounter Ownership.GenerationsBelowCounter
  rw [List.all_eq_true]
  constructor
  · intro h q o n s hq
    obtain ⟨x, hx, -, hxh⟩ := ownerOf_held hq
    have hc := h x hx
    rw [hxh] at hc
    simp only [Holding.generation?, Bool.and_eq_true, decide_eq_true_eq] at hc
    refine ⟨hc.1, fun g hg => ?_⟩
    have h2 := hc.2
    rw [hg] at h2
    simpa using h2
  · intro h e he
    cases hh : e.holding with
    | free => rfl
    | held o n s =>
      have hq := ownerOf_of_mem hl he (holdsPage_start (hwf.2.2.2.2.2.1 e he).1)
      rw [hh] at hq
      obtain ⟨h1, h2⟩ := h _ o n s hq
      simp only [Holding.generation?, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨h1, ?_⟩
      cases hc : t.counter with
      | next g => simpa using h2 g hc
      | exhausted => rfl

public theorem checkFreeExtentsMaximal : CheckFreeExtentsMaximal := by
  intro E X t
  unfold Ownership.checkFreeExtentsMaximal Ownership.FreeExtentsMaximal
  simp only [List.all_eq_true]
  refine forall₂_congr fun a _ => forall₂_congr fun b _ => ?_
  cases a.holding <;> cases b.holding <;> simp [Decidable.imp_iff_not_or]

public theorem checkFreeOrHeldUsable : CheckFreeOrHeldUsable := by
  intro E X t B hwf _
  have hU : ∀ c ∈ B.availableRanges.flatMap (fun u => pageInterval u.start.toNat u.endNat),
      c.1 % PAGE_SIZE = 0 ∧ c.2 % PAGE_SIZE = 0 ∧ c.1 < c.2 := by
    intro c hc
    obtain ⟨u, -, hc⟩ := List.mem_flatMap.1 hc
    unfold pageInterval at hc
    split at hc
    · simp only [List.mem_singleton] at hc
      subst hc
      simp only [pageUp, pageDown] at *
      page_omega
    · simp at hc
  have hUq : ∀ q, q % PAGE_SIZE = 0 →
      ((∃ c ∈ B.availableRanges.flatMap (fun u => pageInterval u.start.toNat u.endNat),
        c.1 ≤ q ∧ q < c.2) ↔ usablePage B q = true) := by
    intro q hq
    simp only [usablePage, List.mem_flatMap, Bool.and_eq_true, beq_iff_eq, hq, true_and,
      List.any_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨c, ⟨u, hu, hc⟩, h1, h2⟩
      refine ⟨u, hu, ?_⟩
      unfold pageInterval at hc
      split at hc
      · simp only [List.mem_singleton] at hc
        subst hc
        simp only [pageUp, pageDown] at h1 h2
        page_omega
      · simp at hc
    · rintro ⟨u, hu, h1, h2⟩
      have hlt : pageUp u.start.toNat < pageDown u.endNat := by
        simp only [pageUp, pageDown]; page_omega
      refine ⟨(pageUp u.start.toNat, pageDown u.endNat), ⟨u, hu, ?_⟩, ?_⟩
      · simp only [pageInterval, hlt, ite_true, List.mem_singleton]
      · simp only [pageUp, pageDown]; page_omega
  unfold Ownership.checkFreeOrHeldUsable Ownership.FreeOrHeldUsable
  dsimp only
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  simp only [beq_iff_eq, freeOrHeld_iff]
  rw [all_cutAll_iff hU (extents_runs hwf), all_cutAll_iff (extents_runs hwf) hU]
  constructor
  · rintro ⟨h1, h2⟩ q hq
    rw [← hUq q hq, ← extents_runs_iff hwf hq]
    exact ⟨h2 q hq, h1 q hq⟩
  · intro h
    refine ⟨fun q hq hu => ?_, fun q hq hx => ?_⟩
    · exact (extents_runs_iff hwf hq).2 ((h q hq).2 ((hUq q hq).1 hu))
    · exact (hUq q hq).2 ((h q hq).1 ((extents_runs_iff hwf hq).1 hx))

public theorem checkDirectMapOffset : CheckDirectMapOffset := by
  intro E X sh cfg
  unfold Shared.checkDirectMapOffset Shared.DirectMapOffset
  rw [List.all_eq_true]
  have hD := direct_base_toNat
  constructor
  · intro hall v l hM
    obtain ⟨hreg, hpg, hcase⟩ := hM
    have hdec := upper_decomp hreg hpg
    have h1 := index1_lt v
    have h2 := index2_lt v
    have h3 := index3_lt v
    rcases hcase with ⟨t2, t3, d, hw, hd3, hk, hpa, -⟩ | ⟨t2, d, hw, hrw, hk, -, hpa⟩
    · obtain ⟨e2, hw2, hv2, hb2, hc2, hd⟩ := walk_ok_level3.1 hw
      rcases walk2_ok.1 hw2 with ⟨-, h⟩ | ⟨t2, hv1, hc1, h⟩
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hmem : (v.toNat, Form.page, d) ∈ sh.directMap.leaves cfg.directBase :=
          mem_leaves.2 ⟨index1 v, index2 v, t2, h1, h2, hv1, hc1, hv2, Or.inr ⟨hb2, t3, index3 v,
            hc2, h3, hd, hd3, by rw [hk]; rfl, rfl, by simp only [Region.first]; omega⟩⟩
        have hc := hall _ hmem
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
          reduceCtorEq, false_or] at hc
        obtain ⟨⟨hlt, hva⟩, hkd⟩ := hc
        rw [hk, Option.some.injEq] at hkd
        rw [← hpa] at hlt hva
        refine ⟨UInt64.toNat_inj.1 ?_, hlt, hkd⟩
        rw [direct_or hlt, hva]
    · obtain ⟨hw2, hv2, hb2⟩ := walk_ok_block.1 hw
      rcases walk2_ok.1 hw2 with ⟨-, h⟩ | ⟨t2, hv1, hc1, h⟩
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, hd⟩ := h
        subst hd
        have hmem : (v.toNat - index3 v * PAGE_SIZE, Form.block,
            sh.directMap.entry t2 (index2 v)) ∈ sh.directMap.leaves cfg.directBase :=
          mem_leaves.2 ⟨index1 v, index2 v, t2, h1, h2, hv1, hc1, hv2,
            Or.inl ⟨hb2, hrw, rfl, rfl, by simp only [Region.first]; omega⟩⟩
        have hc := hall _ hmem
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
          true_or, and_true] at hc
        obtain ⟨hlt, hva⟩ := hc
        have hm := blockAddress_mod (sh.directMap.entry t2 (index2 v))
        have hpl : l.pa.toNat < VA_LIMIT := by
          rw [hpa]; simp only [VA_LIMIT, BLOCK_SIZE, GIB_SIZE, PAGE_SIZE, ENTRIES] at hlt hm hdec h1 h2 h3 ⊢
          omega
        refine ⟨UInt64.toNat_inj.1 ?_, hpl, hk⟩
        rw [direct_or hpl, hpa]
        simp only [VA_LIMIT, BLOCK_SIZE, GIB_SIZE, PAGE_SIZE, ENTRIES] at hlt hm hdec hva h1 h2 h3 ⊢
        omega
  · rintro hoff ⟨va, form, d⟩ hmem
    obtain ⟨i, j, t2, hi, hj, hv1, hc1, hv2, hcase⟩ := mem_leaves.1 hmem
    rcases hcase with ⟨hb, hrw, rfl, rfl, rfl⟩ | ⟨hb, t3, k, hc2, hk, rfl, hd3, hp, rfl, rfl⟩
    · obtain ⟨v, hvn⟩ := exists_upper hi hj (k := 0) (by decide)
      obtain ⟨hreg, hpg, e1, e2, -⟩ := upper_of_toNat hi hj (by decide) hvn
      subst e1 e2
      have hw : sh.directMap.walk cfg.directBase v =
          .ok (.block t2 (sh.directMap.entry t2 (index2 v))) :=
        walk_ok_block.2 ⟨walk2_ok.2 (Or.inr ⟨t2, hv1, hc1, rfl⟩), hv2, hb⟩
      have hpa : (blockAddress (sh.directMap.entry t2 (index2 v))).toNat =
          (blockAddress (sh.directMap.entry t2 (index2 v))).toNat + v.toNat % BLOCK_SIZE := by
        simp only [GIB_SIZE, BLOCK_SIZE, PAGE_SIZE, hD] at hvn ⊢; omega
      obtain ⟨hv, hlt, -⟩ := hoff v ⟨blockAddress (sh.directMap.entry t2 (index2 v)), .readWrite,
        .block⟩ ⟨hreg, hpg, Or.inr ⟨t2, _, hw, hrw, rfl, rfl, hpa⟩⟩
      have hvt := congrArg UInt64.toNat hv
      rw [direct_or hlt] at hvt
      simp only [Region.first, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
        true_or, and_true]
      rw [Nat.zero_mul, Nat.add_zero] at hvn
      generalize DIRECT_BASE.toNat = D at hvn hvt ⊢
      exact ⟨hlt, hvn.symm.trans hvt⟩
    · obtain ⟨kd, hkd⟩ := Option.isSome_iff_exists.1 hp
      obtain ⟨v, hvn⟩ := exists_upper hi hj hk
      obtain ⟨hreg, hpg, e1, e2, e3⟩ := upper_of_toNat hi hj hk hvn
      subst e1 e2 e3
      have hw : sh.directMap.walk cfg.directBase v =
          .ok (.level3 t2 t3 (sh.directMap.entry t3 (index3 v))) :=
        walk_ok_level3.2 ⟨_, walk2_ok.2 (Or.inr ⟨t2, hv1, hc1, rfl⟩), hv2, hb, hc2, rfl⟩
      obtain ⟨hv, hlt, hkind⟩ := hoff v ⟨outputAddress (sh.directMap.entry t3 (index3 v)), kd, .page⟩
        ⟨hreg, hpg, Or.inl ⟨t2, t3, _, hw, hd3, hkd, rfl, rfl⟩⟩
      have hvt := congrArg UInt64.toNat hv
      rw [direct_or hlt] at hvt
      subst hkind
      simp only [Region.first, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true,
        hkd, reduceCtorEq, false_or, and_true]
      generalize DIRECT_BASE.toNat = D at hvn hvt ⊢
      exact ⟨hlt, hvn.symm.trans hvt⟩

end Krepi.Proofs.PageTables.Checks
