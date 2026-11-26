module

public import Krepi.Statements.Fdt.Translate
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.Refinement.SpanLemmas
import Krepi.Proofs.Fdt.Refinement.TranslateLemmas

/-!
# Device tree: refinement of the cells, regions, address maps and spans

One theorem for each statement of `Krepi.Statements.Fdt.Translate`,
whose type is exactly that statement.

All ten are proved, and `verification/statements.json` registers them as
`proved`. Each restates the triple of its function, which holds without the
premise: `cellsU64`, `spanNew`, `spanEnd` and `spanContains` those of
`Krepi.Proofs.Fdt.Refinement.SpanLemmas` (`cells_u64_spec`,
`span_new_spec`, `span_end_spec` and `span_contains_spec`), and `regNew`,
`addressMapNew`, `addressMapKind`, `addressMapToParent` and
`addressMapToChild` those of `Krepi.Proofs.Fdt.Refinement.TranslateLemmas`
(`reg_new_spec`, `address_map_new_spec`, `address_map_kind_spec`,
`address_map_to_parent_spec` and `address_map_to_child_spec`). `regNext`
follows from the representation of a `Reg` alone (`advances_of_stands`).
Mathlib is imported so that the gate counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.Fdt.Refinement.Translate

open Krepi.Statements.Fdt Krepi.Proofs.Fdt.Refinement

/-- Proves `CellsU64`. Feature: `krepi.platform.device-tree`. -/
public theorem cellsU64 : CellsU64 := fun _ => cells_u64_spec

/-- Proves `RegNew`. Feature: `krepi.platform.device-tree`. -/
public theorem regNew : RegNew := fun _ => reg_new_spec

/-- Proves `RegNext`. Feature: `krepi.platform.device-tree`. -/
public theorem regNext : RegNext := fun _ _ _ h => advances_of_stands h

/-- Proves `AddressMapNew`. Feature: `krepi.platform.device-tree`. -/
public theorem addressMapNew : AddressMapNew := fun _ => address_map_new_spec

/-- Proves `AddressMapKind`. Feature: `krepi.platform.device-tree`. -/
public theorem addressMapKind : AddressMapKind := fun _ => address_map_kind_spec

/-- Proves `AddressMapToParent`. Feature: `krepi.platform.device-tree`. -/
public theorem addressMapToParent : AddressMapToParent := fun _ => address_map_to_parent_spec

/-- Proves `AddressMapToChild`. Feature: `krepi.platform.device-tree`. -/
public theorem addressMapToChild : AddressMapToChild := fun _ => address_map_to_child_spec

/-- Proves `SpanNew`. Feature: `krepi.platform.device-tree`. -/
public theorem spanNew : SpanNew := fun _ => span_new_spec

/-- Proves `SpanEnd`. Feature: `krepi.platform.device-tree`. -/
public theorem spanEnd : SpanEnd := fun _ => span_end_spec

/-- Proves `SpanContains`. Feature: `krepi.platform.device-tree`. -/
public theorem spanContains : SpanContains := fun _ => span_contains_spec

end Krepi.Proofs.Fdt.Refinement.Translate
