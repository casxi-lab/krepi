module

public import Krepi.Statements.Fdt.Translate
import Mathlib.Util.CountHeartbeats

/-!
# Device tree: refinement of the cells, regions, address maps and spans

One theorem for each statement of `Krepi.Statements.Fdt.Translate`,
whose type is exactly that statement.

Every theorem here is planned: its proof is `sorry` until a proof pull
request proves it, and `verification/statements.json` registers it as
`planned`. Mathlib is imported so that the gate counts the heartbeats of
each theorem.
-/

namespace Krepi.Proofs.Fdt.Refinement.Translate

open Krepi.Statements.Fdt

/-- Proves `CellsU64`. Feature: `krepi.platform.device-tree`. -/
public theorem cellsU64 : CellsU64 := by
  sorry

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
public theorem spanNew : SpanNew := by
  sorry

/-- Proves `SpanEnd`. Feature: `krepi.platform.device-tree`. -/
public theorem spanEnd : SpanEnd := by
  sorry

/-- Proves `SpanContains`. Feature: `krepi.platform.device-tree`. -/
public theorem spanContains : SpanContains := by
  sorry

end Krepi.Proofs.Fdt.Refinement.Translate
