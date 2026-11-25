module

public import Krepi.Statements.PageTables.Boot
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: refinement of the kernel mappings

One theorem for each statement of `Krepi.Statements.PageTables.Boot`,
whose type is exactly that statement.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.PageTables.Refinement.Boot

open Krepi.Statements.PageTables

/-- Proves `KernelMap`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem kernelMap : KernelMap := by
  sorry

/-- Proves `KernelMapPlanNext`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem kernelMapPlanNext : KernelMapPlanNext := by
  sorry

/-- Proves `DirectMap`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem directMap : DirectMap := by
  sorry

/-- Proves `DirectMapPlanNext`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem directMapPlanNext : DirectMapPlanNext := by
  sorry

end Krepi.Proofs.PageTables.Refinement.Boot
