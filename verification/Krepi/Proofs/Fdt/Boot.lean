module

public import Krepi.SpecProperties.Fdt.Invariants
import Mathlib.Util.CountHeartbeats

/-!
# Device tree: proofs about the boot state

One theorem for each registered statement of `Krepi.SpecProperties.Fdt`
about the boot state, whose type is exactly that statement: that the cold
entry establishes the invariants of the boot state and that each of its
transactions preserves them.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.Fdt.Boot

open Krepi.SpecProperties.Fdt

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
