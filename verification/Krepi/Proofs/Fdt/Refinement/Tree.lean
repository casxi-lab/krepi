module

public import Krepi.Statements.Fdt.Tree
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.Refinement.ParseHeaderLemmas
import Krepi.Proofs.Fdt.Refinement.NodeWalkLemmas

/-!
# Device tree: refinement of the parse and the node access

One theorem for each statement of `Krepi.Statements.Fdt.Tree`,
whose type is exactly that statement.

Seven are proved, and `verification/statements.json` registers them as
`proved`: `fdtTotalSize` and `fdtReservations` restate the triples of
`Krepi.Proofs.Fdt.Refinement.ParseHeaderLemmas` (`fdt_total_size_spec` and
`fdt_reservations_spec`); `fdtNodes`, `nodeName` and `nodeParent` restate
those of `Krepi.Proofs.Fdt.Refinement.NodeWalkLemmas` (`fdt_nodes_spec`,
`node_name_spec` and `node_parent_spec`); and `reservationsNext` and
`nodesNext` follow from the representation of an iterator alone
(`advances_of_stands`). The other eleven are planned: `fdtParse`,
`fdtFindNode`, `nodeProperty`, `nodeStringProperty`, `nodeEnabled`,
`nodeAddressCells`, `nodeSizeCells`, `nodeReg`, `nodeRanges`, `nodeDmaRanges`
and `nodeTranslateReg`. Each proof is `sorry` until a proof pull request
proves it, and `verification/statements.json` registers it as `planned`.
`fdtFindNode` among them does not hold as stated: for a path of `Usize.max`
bytes, which a `Str` of the translation may have and a `&str` of Rust may
not, the code leaves `usize`. `fdt_find_node_spec_of_lt` of
`Krepi.Proofs.Fdt.Refinement.NodeWalkLemmas` proves it for a path of fewer
bytes.
Mathlib is imported so that the gate counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.Fdt.Refinement.Tree

open Krepi.Statements.Fdt Krepi.Proofs.Fdt.Refinement

/-- Proves `FdtParse`. Feature: `krepi.platform.device-tree`. -/
public theorem fdtParse : FdtParse := by
  sorry

/-- Proves `FdtTotalSize`. Feature: `krepi.platform.device-tree`. -/
public theorem fdtTotalSize : FdtTotalSize := fun hU t T hR => fdt_total_size_spec hU t T hR

/-- Proves `FdtNodes`. Feature: `krepi.platform.device-tree`. -/
public theorem fdtNodes : FdtNodes := fdt_nodes_spec

/-- Proves `NodesNext`. Feature: `krepi.platform.device-tree`. -/
public theorem nodesNext : NodesNext := fun _ _ _ h => advances_of_stands h

/-- Proves `FdtFindNode`. Feature: `krepi.platform.device-tree`. -/
public theorem fdtFindNode : FdtFindNode := by
  sorry

/-- Proves `FdtReservations`. Feature: `krepi.platform.device-tree`. -/
public theorem fdtReservations : FdtReservations := fun _ t T hR => fdt_reservations_spec t T hR

/-- Proves `ReservationsNext`. Feature: `krepi.platform.device-tree`. -/
public theorem reservationsNext : ReservationsNext := fun _ _ _ h => advances_of_stands h

/-- Proves `NodeName`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeName : NodeName := node_name_spec

/-- Proves `NodeParent`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeParent : NodeParent := node_parent_spec

/-- Proves `NodeProperty`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeProperty : NodeProperty := by
  sorry

/-- Proves `NodeStringProperty`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeStringProperty : NodeStringProperty := by
  sorry

/-- Proves `NodeEnabled`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeEnabled : NodeEnabled := by
  sorry

/-- Proves `NodeAddressCells`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeAddressCells : NodeAddressCells := by
  sorry

/-- Proves `NodeSizeCells`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeSizeCells : NodeSizeCells := by
  sorry

/-- Proves `NodeReg`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeReg : NodeReg := by
  sorry

/-- Proves `NodeRanges`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeRanges : NodeRanges := by
  sorry

/-- Proves `NodeDmaRanges`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeDmaRanges : NodeDmaRanges := by
  sorry

/-- Proves `NodeTranslateReg`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeTranslateReg : NodeTranslateReg := by
  sorry

end Krepi.Proofs.Fdt.Refinement.Tree
