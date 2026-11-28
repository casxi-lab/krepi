module

public import Krepi.Statements.PageTables.Boot
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.Refinement.KernelPlanLemmas
import Krepi.Proofs.PageTables.Refinement.DirectPlanLemmas

/-!
# Page tables: refinement of the kernel mappings

One theorem for each statement of `Krepi.Statements.PageTables.Boot`,
whose type is exactly that statement.

Every theorem here is proved, each a restatement of a lemma of the helper
modules `KernelPlanLemmas` and `DirectPlanLemmas` (below
`Krepi.Proofs.PageTables.Refinement`) or, for the two plan iterators, of
`advances_of_stands`, and `verification/statements.json` registers it as
`proved`. Mathlib is imported so that the gate counts the heartbeats of each
theorem.
-/

namespace Krepi.Proofs.PageTables.Refinement.Boot

open Krepi.Statements.PageTables Krepi.Proofs.PageTables.Refinement Krepi.Proofs.Fdt.Refinement

/-- Proves `KernelMap`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem kernelMap : KernelMap := fun hU _ s layout L base bits hL =>
  kernel_map_spec hU s layout L base bits hL

/-- Proves `KernelMapPlanNext`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem kernelMapPlanNext : KernelMapPlanNext := fun _ _ _ _ h => advances_of_stands h

/-- Proves `DirectMap`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem directMap : DirectMap := fun hU _ s memory P base bits hP hB =>
  direct_map_spec hU s memory P base bits hP hB

/-- Proves `DirectMapPlanNext`. Feature: `krepi.kernel.kernel-memory`. -/
public theorem directMapPlanNext : DirectMapPlanNext := fun _ _ _ _ h => advances_of_stands h

end Krepi.Proofs.PageTables.Refinement.Boot
