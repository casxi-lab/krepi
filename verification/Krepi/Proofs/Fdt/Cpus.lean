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

Both theorems are planned: each proof is `sorry` until a proof pull
request proves it. The local lemma `or_and_mask` states that flag bits
outside the affinity fields leave the affinity fields of a value unchanged.
Mathlib is imported so that the gate counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.Fdt.Cpus

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

/-- Flag bits outside the affinity fields leave the affinity fields of a value
unchanged. -/
theorem or_and_mask (a b : UInt64) (hb : b &&& AFFINITY_MASK = 0) :
    (a ||| b) &&& AFFINITY_MASK = a &&& AFFINITY_MASK := by
  have : (a ||| b) &&& AFFINITY_MASK = (a &&& AFFINITY_MASK) ||| (b &&& AFFINITY_MASK) :=
    UInt64.toBitVec_inj.1 (by simp [BitVec.and_or_distrib_right])
  rw [this, hb, UInt64.or_zero]

public theorem discoverCpusSupported : DiscoverCpusSupported := by
  sorry

public theorem affinityRoundTrip : AffinityRoundTrip := by
  sorry

end Krepi.Proofs.Fdt.Cpus
