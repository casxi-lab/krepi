module

public import Krepi.SpecProperties.Fdt.Invariants
import Mathlib.Util.CountHeartbeats

/-!
# Device tree: proofs about the checks of the invariants

One theorem for each registered statement of `Krepi.SpecProperties.Fdt`
about the checks of the invariants, whose type is exactly that statement:
that each computable check agrees with its invariant on every value.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.Fdt.Checks

open Krepi.SpecProperties.Fdt

public theorem checkFdtWellFormed : CheckFdtWellFormed := by
  sorry

public theorem checkRegWellFormed : CheckRegWellFormed := by
  sorry

public theorem checkAddressMapWellFormed : CheckAddressMapWellFormed := by
  sorry

public theorem checkMemoryMapWellFormed : CheckMemoryMapWellFormed := by
  sorry

public theorem checkPi5BootMemoryConsistent : CheckPi5BootMemoryConsistent := by
  sorry

public theorem checkCpuTopologySupported : CheckCpuTopologySupported := by
  sorry

public theorem checkMemoryPlanWellFormed : CheckMemoryPlanWellFormed := by
  sorry

public theorem checkBootStateWellFormed : CheckBootStateWellFormed := by
  sorry

public theorem checkBootStateFromHandOver : CheckBootStateFromHandOver := by
  sorry

public theorem checkBootStateStartOrder : CheckBootStateStartOrder := by
  sorry

end Krepi.Proofs.Fdt.Checks
