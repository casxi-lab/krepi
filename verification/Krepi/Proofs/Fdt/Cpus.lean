module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats

/-!
# Device tree: proofs about the CPU nodes

One theorem for each registered statement of `Krepi.SpecProperties.Fdt`
about the CPU nodes, whose type is exactly that statement: that a topology
of the discovery has a supported count and that the affinity of each of its
CPUs gives back its logical ID.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.Fdt.Cpus

open Krepi.SpecProperties.Fdt

public theorem discoverCpusSupported : DiscoverCpusSupported := by
  sorry

public theorem affinityRoundTrip : AffinityRoundTrip := by
  sorry

end Krepi.Proofs.Fdt.Cpus
