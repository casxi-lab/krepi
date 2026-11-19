module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.Plan
import Krepi.Proofs.PageTables.ListLemmas
import Krepi.Proofs.PageTables.OwnerLemmas
import Krepi.Proofs.PageTables.NewLemmas

/-!
# Page tables: proofs about the establishment and the well-formedness of the page ownership table

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about the establishment and the well-
formedness of the page ownership table, whose type is exactly that
statement: that `Ownership::new` establishes the invariants of the table,
and that each write entry of the table keeps it well-formed.

The six statements of `Ownership::new` are proved from what
`Krepi.Proofs.PageTables.NewLemmas` tells about its table: its banks are
sorted and apart, and its extents are free, inside their banks, in address
order, apart from each other within a bank, and hold a page exactly when a
bank holds it and no exclusion touches it. One owner and the free and held
pages follow with `Krepi.Proofs.PageTables.OwnerLemmas`; for the latter the
usable ranges of the boot memory map hold the same pages
(`Krepi.Proofs.Fdt.Plan.usableRangesExact` and
`availableRangesWellFormed`, through the private `usablePage_iff`).

The five statements of the write entries are still planned: their proof is
`sorry`, and `verification/statements.json` registers them as `planned`.
Mathlib is imported so that the gate counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.PageTables.Ownership

open Krepi.SpecProperties.PageTables
open Krepi.Spec.PageTables
open Krepi.Proofs.PageTables

public theorem newOwnershipWellFormed : NewOwnershipWellFormed := by
  intro E X arena banks exclusions t h
  obtain ⟨hp, ha, hne, -, ho, hx, hl, rfl⟩ := new_ok h
  have hperm := sortByKey_perm (·.start.toNat) banks
  have hsorted := sortByKey_banks_inOrder ho
  refine ⟨ha, fun h0 => hne (List.eq_nil_of_length_eq_zero (by
      have h0' : sortByKey (·.start.toNat) banks = [] := h0
      rw [← hperm.length_eq, h0']; rfl)),
    fun b hb => hp b (hperm.mem_iff.1 hb), hsorted, hl, fun e he => ?_,
    initialExtents_inOrder hsorted, hx, by simp⟩
  obtain ⟨j, b, hj, he⟩ := mem_initialExtents.1 he
  obtain ⟨h1, -, h3, h4, h5⟩ := mem_bankExtents he
  refine ⟨h5 (hp b (hperm.mem_iff.1 (List.mem_of_getElem? hj))), b, by rw [h1]; exact hj, ?_⟩
  simp only [PhysRange.contains, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h3, h4⟩

public theorem newOneOwner : NewOneOwner := by
  intro E X arena banks exclusions t h
  have hwf := newOwnershipWellFormed E X arena banks exclusions t h
  obtain ⟨hp, -, -, -, -, -, -, rfl⟩ := new_ok h
  rintro q ⟨hq, b, hb, hbq⟩
  rw [ownersOf_length_eq_one q hwf.2.2.2.2.2.2.1]
  dsimp only
  rw [initialExtents_holds_iff hwf.2.2.1 hq]
  constructor
  · rintro ⟨-, h⟩ ⟨x, hx, hxq⟩
    rw [h x hx] at hxq
    exact absurd hxq (by simp)
  · intro h
    refine ⟨⟨b, hb, hbq⟩, fun x hx => ?_⟩
    cases hxq : x.range.touchesPage q with
    | false => rfl
    | true => exact absurd ⟨x, hx, hxq⟩ h

public theorem newHolderRanges : NewHolderRanges := by
  intro E X arena banks exclusions t h
  obtain ⟨-, -, -, -, -, -, -, rfl⟩ := new_ok h
  intro e he o n s hs
  obtain ⟨j, b, -, he⟩ := mem_initialExtents.1 he
  rw [(mem_bankExtents he).2.1] at hs
  cases hs

public theorem newGenerationsBelowCounter : NewGenerationsBelowCounter := by
  intro E X arena banks exclusions t h
  obtain ⟨-, -, -, -, -, -, -, rfl⟩ := new_ok h
  intro q o n s hq
  obtain ⟨x, hx, -, hxh⟩ := ownerOf_held hq
  obtain ⟨j, b, -, hx⟩ := mem_initialExtents.1 hx
  rw [(mem_bankExtents hx).2.1] at hxh
  cases hxh

public theorem newFreeExtentsMaximal : NewFreeExtentsMaximal := by
  intro E X arena banks exclusions t h
  obtain ⟨-, -, -, -, -, -, -, rfl⟩ := new_ok h
  intro a ha b hb _ _ hab
  obtain ⟨j, c, hj, ha⟩ := mem_initialExtents.1 ha
  obtain ⟨j', c', hj', hb⟩ := mem_initialExtents.1 hb
  have hjj : j = j' := by rw [← (mem_bankExtents ha).1, ← (mem_bankExtents hb).1, hab]
  subst hjj
  rw [hj, Option.some.injEq] at hj'
  subst hj'
  have h1 := range_lt a.range
  have h2 := range_lt b.range
  rcases pairwise_mem_cases (bankExtents_strict exclusions j c) ha hb with rfl | h | h <;> omega

/-- The usable ranges of a well-formed boot memory map hold a page exactly
when one of its managed banks holds it and no reservation touches it. -/
private theorem usablePage_iff {B : Krepi.Spec.Fdt.MemoryPlan} (hB : B.WellFormed) {q : Nat}
    (hq : q % PAGE_SIZE = 0) :
    usablePage B q = true ↔
      (∃ s ∈ B.managed, s.start.toNat ≤ q ∧ q + PAGE_SIZE ≤ s.endNat) ∧
        ∀ x ∈ B.reservations, ¬ (x.start.toNat < q + PAGE_SIZE ∧ q < x.endNat) := by
  obtain ⟨hU1, hU2, -⟩ := Krepi.Proofs.Fdt.Plan.usableRangesExact B hB
  obtain ⟨hW, -, -⟩ := Krepi.Proofs.Fdt.Plan.availableRangesWellFormed B hB
  have hres : ∀ x ∈ B.reservations, x.size ≠ 0 := by
    intro x hx
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hboot, -, -, hfw⟩ := hB
    rcases List.mem_append.1 hx with hx | hx
    · exact (hboot x hx).1.1
    · exact (hfw x hx).1.1
  have hP : PAGE_SIZE = 4096 := rfl
  have hP' : Krepi.Spec.Fdt.MemoryPlan.PAGE_SIZE = 4096 := rfl
  unfold usablePage
  simp only [Bool.and_eq_true, beq_iff_eq, hq, true_and, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨u, hu, h1, h2⟩
    obtain ⟨hin, hx⟩ := hU1 u hu
    obtain ⟨s, hs, hsu⟩ := List.any_eq_true.1 hin
    simp only [Krepi.Spec.Fdt.Span.holds, Bool.and_eq_true, decide_eq_true_eq] at hsu
    refine ⟨⟨s, hs, by omega, by omega⟩, fun x hx' ⟨h3, h4⟩ => ?_⟩
    have := hx x hx'
    have hu0 := (hW u hu).1.1
    simp only [Krepi.Spec.Fdt.Span.touches, Krepi.Spec.Fdt.Span.overlaps, Bool.and_eq_false_iff,
      bne_eq_false_iff_eq, decide_eq_false_iff_not, hres x hx', hu0, false_or] at this
    omega
  · rintro ⟨⟨s, hs, h1, h2⟩, hx⟩
    obtain ⟨u, hu, h3, h4⟩ := hU2 s hs q h1 (by omega) fun x hx' ⟨h5, h6⟩ => hx x hx' ⟨by omega, h6⟩
    have hon := (hW u hu).2
    unfold Krepi.Spec.Fdt.Span.OnPages at hon
    rw [hP'] at hon
    rw [hP] at hq ⊢
    exact ⟨u, hu, h3, by omega⟩

public theorem newFreeOrHeldUsable : NewFreeOrHeldUsable := by
  intro E X B arena banks exclusions t hB ⟨hbanks, hexcl⟩ h
  have hwf := newOwnershipWellFormed E X arena banks exclusions t h
  obtain ⟨-, -, -, -, -, -, -, rfl⟩ := new_ok h
  have hperm := sortByKey_perm (·.start.toNat) banks
  intro q hq
  rw [freeOrHeld_iff]
  dsimp only
  rw [initialExtents_holds_iff hwf.2.2.1 hq, usablePage_iff hB hq]
  refine and_congr ⟨fun ⟨b, hb, hbq⟩ => ?_, fun ⟨s, hs, h1, h2⟩ => ?_⟩
    ⟨fun hx x hx' hxq => ?_, fun hx x hx' => ?_⟩
  · have hm : (b.start, b.len) ∈ B.managed.map (fun s => (s.start, s.size)) :=
      hbanks ▸ List.mem_map_of_mem (hperm.mem_iff.1 hb)
    obtain ⟨s, hs, he⟩ := List.mem_map.1 hm
    simp only [Prod.mk.injEq] at he
    rw [holdsPage_iff] at hbq
    refine ⟨s, hs, by rw [he.1]; exact hbq.1, ?_⟩
    unfold Krepi.Spec.Fdt.Span.endNat
    unfold PhysRange.endNat at hbq
    rw [he.1, he.2]
    exact hbq.2
  · have hm : (s.start, s.size) ∈ banks.map (fun r => (r.start, r.len)) :=
      hbanks ▸ List.mem_map_of_mem hs
    obtain ⟨b, hb, he⟩ := List.mem_map.1 hm
    simp only [Prod.mk.injEq] at he
    refine ⟨b, hperm.mem_iff.2 hb, (holdsPage_iff b q).2 ⟨by rw [he.1]; exact h1, ?_⟩⟩
    unfold PhysRange.endNat
    unfold Krepi.Spec.Fdt.Span.endNat at h2
    rw [he.1, he.2]
    exact h2
  · have hm : (x.start, x.size) ∈ exclusions.map (fun x => (x.range.start, x.range.len)) :=
      hexcl.mem_iff.2 (List.mem_map_of_mem hx')
    obtain ⟨y, hy, he⟩ := List.mem_map.1 hm
    simp only [Prod.mk.injEq] at he
    have := hx y hy
    rw [← Bool.not_eq_true, touchesPage_iff] at this
    unfold PhysRange.endNat at this
    unfold Krepi.Spec.Fdt.Span.endNat at hxq
    rw [he.1, he.2] at this
    exact this hxq
  · have hm : (x.range.start, x.range.len) ∈ B.reservations.map (fun s => (s.start, s.size)) :=
      hexcl.mem_iff.1 (List.mem_map_of_mem hx')
    obtain ⟨y, hy, he⟩ := List.mem_map.1 hm
    simp only [Prod.mk.injEq] at he
    rw [← Bool.not_eq_true, touchesPage_iff]
    have := hx y hy
    unfold PhysRange.endNat
    unfold Krepi.Spec.Fdt.Span.endNat at this
    rw [he.1, he.2] at this
    exact this

public theorem assignWellFormed : AssignWellFormed := by
  sorry

public theorem reserveWellFormed : ReserveWellFormed := by
  sorry

public theorem publishWellFormed : PublishWellFormed := by
  sorry

public theorem cancelWellFormed : CancelWellFormed := by
  sorry

public theorem releaseWellFormed : ReleaseWellFormed := by
  sorry

end Krepi.Proofs.PageTables.Ownership
