module

public import Krepi.SpecProperties.Fdt.Invariants
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.Plan

/-!
# Device tree: proofs about the boot state

One theorem for each registered statement of `Krepi.SpecProperties.Fdt`
about the boot state, whose type is exactly that statement: that the cold
entry establishes the invariants of the boot state and that each of its
transactions preserves them.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, from the lemmas below. The cold entry publishes nothing, so each
invariant holds of it trivially. An enabled transaction changes one field
and keeps the hand-over bytes: the publication of the boot memory map
publishes a map that its entry built, well-formed by the well-formedness
theorems of the entries (`Krepi.Proofs.Fdt.Plan`); the publication of the
topology publishes the topology that `Fdt::discover_cpus` gave for the tree
of the hand-over bytes; and the start of the secondary CPUs is enabled only
once both fields are published. Mathlib is imported so that the gate counts
the heartbeats of each theorem.
-/

namespace Krepi.Proofs.Fdt.Boot

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

/-- An enabled publication of the boot memory map publishes the map that its
entry built, and changes nothing else. -/
theorem publishPlan_ok {token : BootToken} {s s' : BootState} {build : PlanBuild}
    (h : BootState.publishPlan token s build = some (.ok s')) :
    s.secondaries = false ∧ ∃ p, build.run = .ok p ∧ s' = { s with plan := some p } := by
  unfold BootState.publishPlan at h
  split at h
  · exact absurd h (by simp)
  · rename_i hc
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
    refine ⟨hc.1, ?_⟩
    cases hr : build.run with
    | error e => rw [hr] at h; exact absurd h (by simp [Except.map])
    | ok p =>
      rw [hr] at h
      simp only [Except.map, Option.some.injEq, Except.ok.injEq] at h
      exact ⟨p, rfl, h.symm⟩

/-- An enabled publication of the topology publishes the topology that
`Fdt::discover_cpus` gave for the tree of the hand-over bytes, and changes
nothing else. -/
theorem publishTopology_ok {token : BootToken} {s s' : BootState} {profile : CpuProfile}
    (h : BootState.publishTopology token s profile = some (.ok s')) :
    s.secondaries = false ∧ ∃ t, (s.tree.bind fun f => f.discoverCpus profile) = .ok t ∧
      s' = { s with topology := some t } := by
  unfold BootState.publishTopology at h
  split at h
  · exact absurd h (by simp)
  · rename_i hc
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
    refine ⟨hc.1, ?_⟩
    cases hr : s.tree.bind fun f => f.discoverCpus profile with
    | error e => rw [hr] at h; exact absurd h (by simp [Except.map])
    | ok t =>
      rw [hr] at h
      simp only [Except.map, Option.some.injEq, Except.ok.injEq] at h
      exact ⟨t, rfl, h.symm⟩

/-- An enabled start of the secondary CPUs finds both fields published, and
changes nothing but its flag. -/
theorem startSecondaries_ok {token : BootToken} {s s' : BootState}
    (h : BootState.startSecondaries token s = some s') :
    s.plan.isSome = true ∧ s.topology.isSome = true ∧ s' = { s with secondaries := true } := by
  unfold BootState.startSecondaries at h
  split at h
  · exact absurd h (by simp)
  · rename_i hc
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, Option.isNone_eq_false_iff] at hc
    simp only [Option.some.injEq] at h
    exact ⟨hc.1.2, hc.2, h.symm⟩

public theorem coldEntryWellFormed : ColdEntryWellFormed := by
  sorry

public theorem coldEntryFromHandOver : ColdEntryFromHandOver := by
  sorry

public theorem coldEntryStartOrder : ColdEntryStartOrder := by
  sorry

public theorem publishPlanFromHandOver : PublishPlanFromHandOver := by
  sorry

public theorem publishPlanStartOrder : PublishPlanStartOrder := by
  sorry

public theorem publishTopologyFromHandOver : PublishTopologyFromHandOver := by
  sorry

public theorem publishTopologyStartOrder : PublishTopologyStartOrder := by
  sorry

public theorem startSecondariesFromHandOver : StartSecondariesFromHandOver := by
  sorry

public theorem startSecondariesStartOrder : StartSecondariesStartOrder := by
  sorry

public theorem publishPlanWellFormed : PublishPlanWellFormed := by
  sorry

public theorem publishTopologyWellFormed : PublishTopologyWellFormed := by
  sorry

public theorem startSecondariesWellFormed : StartSecondariesWellFormed := by
  sorry

end Krepi.Proofs.Fdt.Boot
