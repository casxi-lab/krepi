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

Every theorem here is proved. The cold entry publishes nothing, so each
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
  intro _ _ p hp
  simp [BootState.coldEntry] at hp

public theorem coldEntryFromHandOver : ColdEntryFromHandOver := by
  intro _ _ t ht
  simp [BootState.coldEntry] at ht

public theorem coldEntryStartOrder : ColdEntryStartOrder := by
  intro _ _ h
  simp [BootState.coldEntry] at h

public theorem publishPlanFromHandOver : PublishPlanFromHandOver := by
  intro _ s _ s' hs h
  obtain ⟨_, p, _, rfl⟩ := publishPlan_ok h
  exact hs

public theorem publishPlanStartOrder : PublishPlanStartOrder := by
  intro _ s _ s' _ h
  obtain ⟨hsec, p, _, rfl⟩ := publishPlan_ok h
  intro h'
  exact absurd (hsec ▸ h') (by simp)

public theorem publishTopologyFromHandOver : PublishTopologyFromHandOver := by
  intro _ s profile s' _ h
  obtain ⟨_, t, ht, rfl⟩ := publishTopology_ok h
  intro t' ht'
  simp only [Option.some.injEq] at ht'
  subst ht'
  exact ⟨profile, ht⟩

public theorem publishTopologyStartOrder : PublishTopologyStartOrder := by
  intro _ s _ s' _ h
  obtain ⟨hsec, t, _, rfl⟩ := publishTopology_ok h
  intro h'
  exact absurd (hsec ▸ h') (by simp)

public theorem startSecondariesFromHandOver : StartSecondariesFromHandOver := by
  intro _ s s' hs h
  obtain ⟨_, _, rfl⟩ := startSecondaries_ok h
  exact hs

public theorem startSecondariesStartOrder : StartSecondariesStartOrder := by
  intro _ s s' _ h
  obtain ⟨hp, ht, rfl⟩ := startSecondaries_ok h
  exact fun _ => ⟨hp, ht⟩

public theorem publishPlanWellFormed : PublishPlanWellFormed := by
  intro _ s build s' _ h
  obtain ⟨_, p, hp, rfl⟩ := publishPlan_ok h
  intro q hq
  simp only [Option.some.injEq] at hq
  subst hq
  cases build with
  | allRam ram boot firmware => exact Plan.allRamWellFormed ram boot firmware _ hp
  | new window ram boot firmware =>
    exact Plan.memoryPlanNewWellFormed window ram boot firmware _ hp
  | fromPi5 memory window more => exact Plan.fromPi5WellFormed memory window more _ hp

public theorem publishTopologyWellFormed : PublishTopologyWellFormed := by
  intro _ s _ s' hs h
  obtain ⟨_, t, _, rfl⟩ := publishTopology_ok h
  exact hs

public theorem startSecondariesWellFormed : StartSecondariesWellFormed := by
  intro _ s s' hs h
  obtain ⟨_, _, rfl⟩ := startSecondaries_ok h
  exact hs

end Krepi.Proofs.Fdt.Boot
