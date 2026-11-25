module

public import Krepi.Statements.Fdt.Translate
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.Refinement.SpanLemmas

/-!
# Device tree: refinement of the cells, regions, address maps and spans

One theorem for each statement of `Krepi.Statements.Fdt.Translate`,
whose type is exactly that statement.

`cellsU64`, `spanNew`, `spanEnd` and `spanContains` are proved: each
restates the triple of its function in
`Krepi.Proofs.Fdt.Refinement.SpanLemmas` (`cells_u64_spec`,
`span_new_spec`, `span_end_spec` and `span_contains_spec`), which holds
without the premise. The other theorems are planned: their proofs are
`sorry`, and `verification/statements.json` registers them as `planned`,
so that no module imports this one. Mathlib is imported so that the gate
counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.Fdt.Refinement.Translate

open Krepi.Statements.Fdt Krepi.Proofs.Fdt.Refinement

/-- Proves `CellsU64`. Feature: `krepi.platform.device-tree`. -/
public theorem cellsU64 : CellsU64 := fun _ => cells_u64_spec

/-- Proves `RegNew`. Feature: `krepi.platform.device-tree`. -/
public theorem regNew : RegNew := by
  sorry

/-- Proves `RegNext`. Feature: `krepi.platform.device-tree`. -/
public theorem regNext : RegNext := by
  sorry

/-- Proves `AddressMapNew`. Feature: `krepi.platform.device-tree`. -/
public theorem addressMapNew : AddressMapNew := by
  sorry

/-- Proves `AddressMapKind`. Feature: `krepi.platform.device-tree`. -/
public theorem addressMapKind : AddressMapKind := by
  sorry

/-- Proves `AddressMapToParent`. Feature: `krepi.platform.device-tree`. -/
public theorem addressMapToParent : AddressMapToParent := by
  sorry

/-- Proves `AddressMapToChild`. Feature: `krepi.platform.device-tree`. -/
public theorem addressMapToChild : AddressMapToChild := by
  sorry

/-- Proves `SpanNew`. Feature: `krepi.platform.device-tree`. -/
public theorem spanNew : SpanNew := fun _ => span_new_spec

/-- Proves `SpanEnd`. Feature: `krepi.platform.device-tree`. -/
public theorem spanEnd : SpanEnd := fun _ => span_end_spec

/-- Proves `SpanContains`. Feature: `krepi.platform.device-tree`. -/
public theorem spanContains : SpanContains := fun _ => span_contains_spec

end Krepi.Proofs.Fdt.Refinement.Translate
