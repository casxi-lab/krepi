module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.ExceptLemmas

/-!
# Device tree: proofs about the CPU nodes

One theorem for each registered statement of `Krepi.SpecProperties.Fdt`
about the CPU nodes, whose type is exactly that statement: that a topology
of the discovery has a supported count and that the affinity of each of its
CPUs gives back its logical ID.

Every theorem here is proved, with two local lemmas:
`supported_of_idsComplete`, the count of a set of IDs that `idsComplete`
accepts is supported, and `or_and_mask`, flag bits outside the affinity
fields leave the affinity fields of a value unchanged. Mathlib is imported
so that the gate counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.Fdt.Cpus

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

/-- The topology of a profile and a set of IDs that `idsComplete` accepts has
a supported count. -/
theorem supported_of_idsComplete {profile : CpuProfile} {ids : List UInt64}
    (h : idsComplete profile ids = true) :
    CpuTopology.Supported ⟨profile, UInt64.ofNat ids.length⟩ := by
  unfold idsComplete at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hc, hp⟩, -⟩ := h
  unfold CpuTopology.Supported
  dsimp only
  refine ⟨?_, fun hpi => ?_⟩
  · rcases hc with (h | h) | h <;> rw [h] <;> decide
  · rcases hp with hp | hp
    · exact absurd hpi hp
    · rw [hp]
      rfl

/-- Flag bits outside the affinity fields leave the affinity fields of a value
unchanged. -/
theorem or_and_mask (a b : UInt64) (hb : b &&& AFFINITY_MASK = 0) :
    (a ||| b) &&& AFFINITY_MASK = a &&& AFFINITY_MASK := by
  have : (a ||| b) &&& AFFINITY_MASK = (a &&& AFFINITY_MASK) ||| (b &&& AFFINITY_MASK) :=
    UInt64.toBitVec_inj.1 (by simp [BitVec.and_or_distrib_right])
  rw [this, hb, UInt64.or_zero]

public theorem discoverCpusSupported : DiscoverCpusSupported := by
  intro t profile topology h
  unfold Fdt.discoverCpus at h
  obtain ⟨_, _, h⟩ := except_bind_ok.1 h
  split at h
  · obtain ⟨_, _, h⟩ := except_bind_ok.1 h
    obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨_, _, h⟩ := except_bind_ok.1 h
    obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨_, _, h⟩ := except_bind_ok.1 h
    obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨ids, _, h⟩ := except_bind_ok.1 h
    obtain ⟨hids, h⟩ := except_jp_ok h
    obtain ⟨_, _, h⟩ := except_bind_ok.1 h
    split at h
    · obtain ⟨_, _, h⟩ := except_bind_ok.1 h
      obtain ⟨-, h⟩ := except_jp_ok h
      obtain ⟨_, _, h⟩ := except_bind_ok.1 h
      obtain ⟨-, h⟩ := except_jp_ok h
      obtain ⟨-, h⟩ := except_jp_ok h
      have h := except_pure_ok.1 h
      subst h
      exact supported_of_idsComplete (by simpa using hids)
    · exact absurd h (except_throw_ne _ _)
  · exact absurd h (except_throw_ne _ _)

public theorem affinityRoundTrip : AffinityRoundTrip := by
  refine ⟨fun t i flags hs hi hf => ?_, fun p mpidr flags hf => ?_⟩
  · refine ⟨i <<< t.profile.affinityShift, by simp [CpuTopology.affinity, hi], ?_⟩
    unfold CpuProfile.logicalId
    rw [or_and_mask _ _ hf]
    have h4 : i.toNat < 4 := by
      have := UInt64.lt_iff_toNat_lt.1 hi
      rcases hs.1 with h | h | h <;> rw [h] at this <;> simp at this <;> omega
    generalize t.profile = p
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
      have : i.toNat = 0 ∨ i.toNat = 1 ∨ i.toNat = 2 ∨ i.toNat = 3 := by omega
      rcases this with h | h | h | h
      · exact Or.inl (UInt64.toNat_inj.1 h)
      · exact Or.inr (Or.inl (UInt64.toNat_inj.1 h))
      · exact Or.inr (Or.inr (Or.inl (UInt64.toNat_inj.1 h)))
      · exact Or.inr (Or.inr (Or.inr (UInt64.toNat_inj.1 h)))
    rcases this with rfl | rfl | rfl | rfl <;> cases p <;> decide
  · unfold CpuProfile.logicalId
    rw [or_and_mask _ _ hf]

end Krepi.Proofs.Fdt.Cpus
