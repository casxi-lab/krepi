module

public import Krepi.Statements.Fdt.Tree
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.Refinement.ParseHeaderLemmas
import Krepi.Proofs.Fdt.Refinement.NodeWalkLemmas
import Krepi.Proofs.Fdt.Refinement.ParseWalkLemmas
import Krepi.Proofs.Fdt.Refinement.NodePropertyLemmas

/-!
# Device tree: refinement of the parse and the node access

One theorem for each statement of `Krepi.Statements.Fdt.Tree`,
whose type is exactly that statement.

All eighteen are proved, and `verification/statements.json` registers them
as `proved`: `fdtParse` restates the triple `fdt_parse_spec` of
`Krepi.Proofs.Fdt.Refinement.ParseWalkLemmas`; `fdtTotalSize` and
`fdtReservations` restate the triples of
`Krepi.Proofs.Fdt.Refinement.ParseHeaderLemmas` (`fdt_total_size_spec` and
`fdt_reservations_spec`); `fdtNodes`, `fdtFindNode`, `nodeName` and
`nodeParent` restate those of `Krepi.Proofs.Fdt.Refinement.NodeWalkLemmas`
(`fdt_nodes_spec`, `fdt_find_node_spec`, `node_name_spec` and
`node_parent_spec`); `nodeProperty`, `nodeStringProperty`, `nodeEnabled`,
`nodeAddressCells`, `nodeSizeCells`, `nodeReg`, `nodeRanges`,
`nodeDmaRanges` and `nodeTranslateReg` restate those of
`Krepi.Proofs.Fdt.Refinement.NodePropertyLemmas` (`node_property_spec`,
`node_string_property_spec`, `node_enabled_spec`, `node_address_cells_spec`,
`node_size_cells_spec`, `node_reg_spec`, `node_ranges_spec`,
`node_dma_ranges_spec` and `node_translate_reg_spec`); and `reservationsNext`
and `nodesNext` follow from the representation of an iterator alone
(`advances_of_stands`).
Mathlib is imported so that the gate counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.Fdt.Refinement.Tree

open Krepi.Statements.Fdt Krepi.Proofs.Fdt.Refinement

/-- Proves `FdtParse`. Feature: `krepi.platform.device-tree`. -/
public theorem fdtParse : FdtParse := fdt_parse_spec

/-- Proves `FdtTotalSize`. Feature: `krepi.platform.device-tree`. -/
public theorem fdtTotalSize : FdtTotalSize := fun hU t T hR => fdt_total_size_spec hU t T hR

/-- Proves `FdtNodes`. Feature: `krepi.platform.device-tree`. -/
public theorem fdtNodes : FdtNodes := fdt_nodes_spec

/-- Proves `NodesNext`. Feature: `krepi.platform.device-tree`. -/
public theorem nodesNext : NodesNext := fun _ _ _ h => advances_of_stands h

/-- Proves `FdtFindNode`. Feature: `krepi.platform.device-tree`. -/
public theorem fdtFindNode : FdtFindNode := fdt_find_node_spec

/-- Proves `FdtReservations`. Feature: `krepi.platform.device-tree`. -/
public theorem fdtReservations : FdtReservations := fun _ t T hR => fdt_reservations_spec t T hR

/-- Proves `ReservationsNext`. Feature: `krepi.platform.device-tree`. -/
public theorem reservationsNext : ReservationsNext := fun _ _ _ h => advances_of_stands h

/-- Proves `NodeName`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeName : NodeName := node_name_spec

/-- Proves `NodeParent`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeParent : NodeParent := node_parent_spec

/-- Proves `NodeProperty`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeProperty : NodeProperty := node_property_spec

/-- Proves `NodeStringProperty`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeStringProperty : NodeStringProperty := node_string_property_spec

/-- Proves `NodeEnabled`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeEnabled : NodeEnabled := node_enabled_spec

/-- Proves `NodeAddressCells`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeAddressCells : NodeAddressCells := node_address_cells_spec

/-- Proves `NodeSizeCells`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeSizeCells : NodeSizeCells := node_size_cells_spec

/-- Proves `NodeReg`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeReg : NodeReg := node_reg_spec

/-- Proves `NodeRanges`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeRanges : NodeRanges := node_ranges_spec

/-- Proves `NodeDmaRanges`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeDmaRanges : NodeDmaRanges := node_dma_ranges_spec

/-- Proves `NodeTranslateReg`. Feature: `krepi.platform.device-tree`. -/
public theorem nodeTranslateReg : NodeTranslateReg := node_translate_reg_spec

end Krepi.Proofs.Fdt.Refinement.Tree
