module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.SpanLemmas
import Krepi.Proofs.Fdt.PlanLemmas

/-!
# Device tree: proofs about the boot memory map

One theorem for each registered statement of `Krepi.SpecProperties.Fdt`
about the boot memory map, whose type is exactly that statement: that the
entries of the boot memory map give well-formed maps, and that their usable
ranges are well-formed and exact.

Every theorem here is proved but `FromBootMemoryWellFormed`, which is
planned: its proof is `sorry` until a proof pull request proves it. The steps of the entries and of the usable
ranges are in `Krepi.Proofs.Fdt.PlanLemmas`: the entries keep each rule of
`MemoryPlan.WellFormed` while they fold over their inputs, and the usable
ranges of a managed bank start at the bank or at the end of a reservation,
end at the bank or at the start of a reservation, and cover every address
that no reservation holds, since the fuel of `usableFrom` exceeds twice the
reservations that end past its cursor. Mathlib is imported so that the gate
counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.Fdt.Plan

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

public theorem allRamWellFormed : AllRamWellFormed :=
  fun _ _ _ _ h => allRam_wellFormed h

public theorem memoryPlanNewWellFormed : MemoryPlanNewWellFormed :=
  fun _ _ _ _ _ h => new_wellFormed h

public theorem fromBootMemoryWellFormed : FromBootMemoryWellFormed := by
  sorry

public theorem availableRangesWellFormed : AvailableRangesWellFormed := by
  intro p hp
  have hres := reservations_wf hp
  have hman := hp.2.2.2.2.2.2.1
  have hmanp := hp.2.2.2.2.2.2.2.1
  have hne : ∀ r ∈ p.availableRanges, r.Nonempty ∧ r.OnPages := by
    intro r hr
    obtain ⟨b, hb, t, n, rfl, -, h2, -, h4, -, -, h7, h8⟩ := availableRanges_mem hp hr
    obtain ⟨hs, he, hn⟩ := spanBetween_spec h2 h4
    refine ⟨hn, ?_, ?_⟩
    · rw [hs]
      rcases h7 with rfl | ⟨x, hx, rfl⟩
      · exact (hman b hb).2.1.1
      · exact (hres x hx).2.2
    · rw [he]
      rcases h8 with rfl | ⟨x, hx, rfl⟩
      · exact (hman b hb).2.1.2
      · exact (hres x hx).2.1
  have hpw : p.availableRanges.Pairwise (fun a b => a.endNat ≤ b.start.toNat) := by
    have hexcl : ∀ x ∈ p.reservations, x.start.toNat < x.endNat :=
      fun x hx => nonempty_lt (hres x hx).1
    unfold MemoryPlan.availableRanges
    rw [List.pairwise_flatMap]
    refine ⟨fun b hb => ?_, ?_⟩
    · have hbv := (hman b hb).1.2
      exact usableFrom_pairwise hbv hexcl _ _
    · refine List.Pairwise.imp_of_mem ?_ hmanp
      intro b1 b2 hb1 hb2 h12 x hx y hy
      have hv1 := (hman b1 hb1).1.2
      have hv2 := (hman b2 hb2).1.2
      obtain ⟨t, n, rfl, -, h2, h3, -⟩ := usableFrom_mem hv1 hexcl _ _ x hx
      obtain ⟨t', n', rfl, h1', h2', h3', -⟩ := usableFrom_mem hv2 hexcl _ _ y hy
      unfold Span.Valid at hv1 hv2
      obtain ⟨-, he, -⟩ := spanBetween_spec h2 (by omega)
      obtain ⟨hs, -, -⟩ := spanBetween_spec h2' (by omega)
      rw [he, hs]
      omega
  refine ⟨hne, hpw, ?_⟩
  have hnd : (p.availableRanges.map Span.endNat).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ hpw
    intro a b _ hb hab
    have := nonempty_lt (hne b hb).1
    omega
  have := length_le_of_nodup_subset hnd
    (L := p.managed.map Span.endNat ++ p.reservations.map (fun x => x.start.toNat)) (by
      intro e he
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 he
      obtain ⟨b, hb, t, n, rfl, -, h2, -, h4, -, -, -, h8⟩ := availableRanges_mem hp hr
      obtain ⟨-, he', -⟩ := spanBetween_spec h2 h4
      rw [he']
      rcases h8 with rfl | ⟨x, hx, rfl⟩
      · exact List.mem_append_left _ (List.mem_map.2 ⟨b, hb, rfl⟩)
      · exact List.mem_append_right _ (List.mem_map.2 ⟨x, hx, rfl⟩))
  simpa using this

public theorem usableRangesExact : UsableRangesExact := by
  intro p hp
  have hres := reservations_wf hp
  have hman := hp.2.2.2.2.2.2.1
  have hexcl : ∀ x ∈ p.reservations, x.start.toNat < x.endNat :=
    fun x hx => nonempty_lt (hres x hx).1
  refine ⟨fun r hr => ?_, fun b hb a h1 h2 ha => ?_, fun r hr => ?_⟩
  · obtain ⟨b, hb, t, n, rfl, h1, h2, h3, h4, h5, h6, -, -⟩ := availableRanges_mem hp hr
    obtain ⟨hs, he, -⟩ := spanBetween_spec h2 h4
    refine ⟨List.any_eq_true.2 ⟨b, hb, holds_iff.2
      ⟨by rw [hs]; exact h1, by rw [he]; exact h3⟩⟩,
      fun x hx => ?_⟩
    cases hxt : x.touches (spanBetween t n) with
    | false => rfl
    | true =>
      rw [touches_iff, hs, he] at hxt
      by_cases htx : t < x.start.toNat
      · have := h6 x hx htx
        omega
      · exact absurd ⟨by omega, hxt.2.2.2⟩ (h5 x hx)
  · have hbv := (hman b hb).1.2
    unfold Span.Valid at hbv
    obtain ⟨r, hr, hr2⟩ := usableFrom_covers hbv hexcl ha h2 (2 * p.reservations.length + 2)
      b.start.toNat h1 (by
        have := List.countP_le_length (p := fun x => decide (b.start.toNat < x.endNat))
          (l := p.reservations)
        split <;> omega)
    exact ⟨r, List.mem_flatMap.2 ⟨b, hb, hr⟩, hr2⟩
  · obtain ⟨b, hb, t, n, rfl, -, h2, -, h4, -, -, h7, h8⟩ := availableRanges_mem hp hr
    obtain ⟨hs, he, -⟩ := spanBetween_spec h2 h4
    refine ⟨?_, ?_⟩
    · rcases h7 with rfl | ⟨x, hx, rfl⟩
      · exact Or.inl ⟨b, hb, by unfold spanBetween; rw [UInt64.ofNat_toNat]⟩
      · exact Or.inr ⟨x, hx, hs.symm⟩
    · rcases h8 with rfl | ⟨x, hx, rfl⟩
      · exact Or.inl ⟨b, hb, he.symm⟩
      · exact Or.inr ⟨x, hx, he.symm⟩

end Krepi.Proofs.Fdt.Plan
