module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.DiscoveryLemmas

/-!
# Device tree: proofs about the CPU nodes

One theorem for each registered statement of `Krepi.SpecProperties.Fdt`
about the CPU nodes, whose type is exactly that statement: that a topology
of the discovery has a supported count and that the affinity of each of its
CPUs gives back its logical ID.

Every theorem here is proved, for every CPU profile, with three local
lemmas: `supported_of_idsComplete`, the count of a set of IDs that
`idsComplete` accepts is supported; `or_and_mask`, flag bits outside the
affinity fields leave the affinity fields of a value unchanged; and
`idOf_shift`, at each of the four affinity levels the ID of a CPU below 4,
shifted to its level, lies inside the affinity fields and gives back that
ID. What a successful discovery gives is `discoverCpus_ok` of
`Krepi.Proofs.Fdt.DiscoveryLemmas`. Mathlib is imported so that the gate
counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.Fdt.Cpus

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

/-- The topology of a profile and a set of IDs that `idsComplete` accepts has
a supported count. -/
theorem supported_of_idsComplete {profile : CpuProfile} {ids : List UInt64}
    (h : idsComplete profile ids = true) :
    CpuTopology.Supported ⟨profile, UInt64.ofNat ids.length⟩ := by
  unfold idsComplete CpuProfile.allows at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h0, h4⟩, hb⟩, -⟩ := h
  have hn : (UInt64.ofNat ids.length).toNat = ids.length :=
    UInt64.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt h4 (by decide))
  unfold CpuTopology.Supported
  dsimp only
  rw [UInt64.le_iff_toNat_le, UInt64.le_iff_toNat_le, hn]
  exact ⟨by simp; omega, by simpa using h4, hb⟩

/-- Flag bits outside the affinity fields leave the affinity fields of a value
unchanged. -/
theorem or_and_mask (a b : UInt64) (hb : b &&& AFFINITY_MASK = 0) :
    (a ||| b) &&& AFFINITY_MASK = a &&& AFFINITY_MASK := by
  have : (a ||| b) &&& AFFINITY_MASK = (a &&& AFFINITY_MASK) ||| (b &&& AFFINITY_MASK) :=
    UInt64.toBitVec_inj.1 (by simp [BitVec.and_or_distrib_right])
  rw [this, hb, UInt64.or_zero]

/-- At each of the four affinity levels, the ID of a CPU below 4 shifted to
its level lies inside the affinity fields and gives back that ID. -/
theorem idOf_shift (p : CpuProfile) {i : UInt64} (hi : i.toNat < 4) :
    (i <<< p.affinityShift) &&& AFFINITY_MASK = i <<< p.affinityShift ∧
      p.idOf (i <<< p.affinityShift) = some i := by
  unfold CpuProfile.idOf
  have hs : p.affinityShift = 0 ∨ p.affinityShift = 8 ∨ p.affinityShift = 16 ∨
      p.affinityShift = 32 := by
    unfold CpuProfile.affinityShift
    cases p.affinityLevel <;> simp [AffinityLevel.shift]
  generalize p.affinityShift = sh at hs ⊢
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
    have : i.toNat = 0 ∨ i.toNat = 1 ∨ i.toNat = 2 ∨ i.toNat = 3 := by omega
    rcases this with h | h | h | h
    · exact Or.inl (UInt64.toNat_inj.1 h)
    · exact Or.inr (Or.inl (UInt64.toNat_inj.1 h))
    · exact Or.inr (Or.inr (Or.inl (UInt64.toNat_inj.1 h)))
    · exact Or.inr (Or.inr (Or.inr (UInt64.toNat_inj.1 h)))
  rcases this with rfl | rfl | rfl | rfl <;> rcases hs with rfl | rfl | rfl | rfl <;> decide

public theorem discoverCpusSupported : DiscoverCpusSupported := by
  intro t profile topology h
  obtain ⟨ids, hids, rfl⟩ := discoverCpus_ok h
  exact supported_of_idsComplete hids

public theorem affinityRoundTrip : AffinityRoundTrip := by
  refine ⟨fun t i flags hs hi hf => ?_, fun p mpidr flags hf => ?_⟩
  · refine ⟨i <<< t.profile.affinityShift, by simp [CpuTopology.affinity, hi], ?_⟩
    have h4 : i.toNat < 4 := by
      have := UInt64.lt_iff_toNat_lt.1 hi
      have := UInt64.le_iff_toNat_le.1 hs.2.1
      simp at this
      omega
    obtain ⟨hm, hid⟩ := idOf_shift t.profile h4
    unfold CpuProfile.logicalId
    rw [or_and_mask _ _ hf, hm, hid]
  · unfold CpuProfile.logicalId
    rw [or_and_mask _ _ hf]

end Krepi.Proofs.Fdt.Cpus
