module

public import Krepi.Statements.Fdt.Representation

/-!
# Device tree: refinement of the parse and the node access

One statement for each function of lines 109 and 110 of the entry table of
the contract (`docs/domains/boot-platform/fdt/contract.md`), and for the
`next` of the iterators of the nodes and of the reservation entries: for
every input of its machine widths, under the premises that its arguments
need, the function returns, and its result agrees with that of its function
of `Krepi.Spec.Fdt` through the representation of
`Krepi.Statements.Fdt.Representation`, the same error with the same
priority included. None of these functions writes anything. The theorems
below `Krepi.Proofs.Fdt.Refinement` prove them.
-/

@[expose] public section

open Aeneas
open Aeneas.Std (Slice Str U8 U32 U64)
open KrepiGen.Fdt
open Krepi.Spec.Fdt

namespace Krepi.Statements.Fdt

/-! ## The tree -/

/-- `Fdt::parse(input)`: for every slice of bytes, the tree that stands for
that of `Fdt.parse` of its bytes, or its error. Feature:
`krepi.platform.device-tree`. -/
def FdtParse : Prop :=
  ∀ input : Slice U8,
    fdt.parser.Fdt.parse input ⦃ r => Agrees FdtRepr errorOf r (Fdt.parse (bytesOf input)) ⦄

/-- `Fdt::total_size()`: the `totalsize` of the tree. Feature:
`krepi.platform.device-tree`. -/
def FdtTotalSize : Prop :=
  ∀ (t : fdt.Fdt) (T : Fdt), FdtRepr t T →
    fdt.parser.Fdt.total_size t ⦃ n => word64 n = T.totalSize ⦄

/-- `Fdt::nodes()`: an iterator that stands for the nodes of the tree in the
order of the structure block, `Fdt.nodes`. Feature:
`krepi.platform.device-tree`. -/
def FdtNodes : Prop :=
  ∀ (t : fdt.Fdt) (T : Fdt), FdtRepr t T →
    fdt.nodes.Fdt.nodes t ⦃ it => Stands fdt.nodes.Nodes.next NodeRepr it T.nodes ⦄

/-- `Nodes::next()`: one call gives the next node of the list that the
iterator stands for and leaves it standing for the rest; at the end it
gives none and stays at the end. Feature: `krepi.platform.device-tree`. -/
def NodesNext : Prop :=
  ∀ (it : fdt.Nodes) (l : List Node), Stands fdt.nodes.Nodes.next NodeRepr it l →
    Advances fdt.nodes.Nodes.next NodeRepr it l

/-- `Fdt::find_node(path)`: the node of `Fdt.findNode` of the path, none when
no node has it, or its error, for a path whose `as_bytes` gives the bytes
of the string of the specification. Feature:
`krepi.platform.device-tree`. -/
def FdtFindNode : Prop :=
  ∀ (t : fdt.Fdt) (T : Fdt) (path : Str) (p : String), FdtRepr t T → StrRepr path p →
    fdt.nodes.Fdt.find_node t path ⦃ r => Agrees (OptionRel NodeRepr) errorOf r (T.findNode p) ⦄

/-- `Fdt::reservations()`: an iterator that stands for the entries of the
reservation map before its terminator, `Fdt.reservations`. Feature:
`krepi.platform.device-tree`. -/
def FdtReservations : Prop :=
  ∀ (t : fdt.Fdt) (T : Fdt), FdtRepr t T →
    fdt.parser.Fdt.reservations t ⦃ it =>
      Stands fdt.nodes.Reservations.next SpanRepr it T.reservations ⦄

/-- `Reservations::next()`: one call gives the next entry of the list that
the iterator stands for and leaves it standing for the rest; at the end it
gives none and stays at the end. Feature: `krepi.platform.device-tree`. -/
def ReservationsNext : Prop :=
  ∀ (it : fdt.Reservations) (l : List Span), Stands fdt.nodes.Reservations.next SpanRepr it l →
    Advances fdt.nodes.Reservations.next SpanRepr it l

/-! ## The nodes -/

/-- `Node::name()`: the bytes of the name of the node, `Node.name`, without
its NUL. Feature: `krepi.platform.device-tree`. -/
def NodeName : Prop :=
  ∀ (n : fdt.Node) (N : Node), NodeRepr n N →
    fdt.nodes.Node.name n ⦃ b => bytesOf b = N.name.toUTF8 ⦄

/-- `Node::parent()`: the parent of the node, none for the root,
`Node.parent`. Feature: `krepi.platform.device-tree`. -/
def NodeParent : Prop :=
  ∀ (n : fdt.Node) (N : Node), NodeRepr n N →
    fdt.nodes.Node.parent n ⦃ o => OptionRel NodeRepr o N.parent ⦄

/-- `Node::property(name)`: the bytes of the value of the property of that
name, none without it, `Node.property`, for a name whose `as_bytes` gives
the bytes of the string of the specification. Feature:
`krepi.platform.device-tree`. -/
def NodeProperty : Prop :=
  ∀ (n : fdt.Node) (N : Node) (key : Str) (s : String), NodeRepr n N → StrRepr key s →
    fdt.nodes.Node.property n key ⦃ o => o.map bytesOf = N.property s ⦄

/-- `Node::string_property(name)`: the bytes of the string of the property,
none without it, or the error of `Node.stringProperty`, for a name whose
`as_bytes` gives the bytes of the string of the specification. Feature:
`krepi.platform.device-tree`. -/
def NodeStringProperty : Prop :=
  ∀ (n : fdt.Node) (N : Node) (key : Str) (s : String), NodeRepr n N → StrRepr key s →
    fdt.nodes.Node.string_property n key ⦃ r =>
      Agrees (fun o v => o.map bytesOf = v.map String.toUTF8) errorOf r (N.stringProperty s) ⦄

/-- `Node::enabled()`: whether the node is enabled, or the error of
`Node.enabled`. Feature: `krepi.platform.device-tree`. -/
def NodeEnabled : Prop :=
  ∀ (n : fdt.Node) (N : Node), NodeRepr n N →
    fdt.nodes.Node.enabled n ⦃ r => Agrees (· = ·) errorOf r N.enabled ⦄

/-- `Node::address_cells()`: the node's own `#address-cells`, or the error
of `Node.addressCells`. Feature: `krepi.platform.device-tree`. -/
def NodeAddressCells : Prop :=
  ∀ (n : fdt.Node) (N : Node), NodeRepr n N →
    fdt.nodes.Node.address_cells n ⦃ r =>
      Agrees (fun c C => word32 c = C) errorOf r N.addressCells ⦄

/-- `Node::size_cells()`: the node's own `#size-cells`, or the error of
`Node.sizeCells`. Feature: `krepi.platform.device-tree`. -/
def NodeSizeCells : Prop :=
  ∀ (n : fdt.Node) (N : Node), NodeRepr n N →
    fdt.nodes.Node.size_cells n ⦃ r => Agrees (fun c C => word32 c = C) errorOf r N.sizeCells ⦄

/-- `Node::reg()`: a `Reg` that stands for the entries of `Node.reg`, or its
error. Feature: `krepi.platform.device-tree`. -/
def NodeReg : Prop :=
  ∀ (n : fdt.Node) (N : Node), NodeRepr n N →
    fdt.nodes.Node.reg n ⦃ r => Agrees (fun g R => RegRepr g R.entries) errorOf r N.reg ⦄

/-- `Node::ranges()`: an address map that stands for that of `Node.ranges`,
or its error. Feature: `krepi.platform.device-tree`. -/
def NodeRanges : Prop :=
  ∀ (n : fdt.Node) (N : Node), NodeRepr n N →
    fdt.nodes.Node.ranges n ⦃ r => Agrees AddressMapRepr errorOf r N.ranges ⦄

/-- `Node::dma_ranges()`: an address map that stands for that of
`Node.dmaRanges`, or its error. Feature: `krepi.platform.device-tree`. -/
def NodeDmaRanges : Prop :=
  ∀ (n : fdt.Node) (N : Node), NodeRepr n N →
    fdt.nodes.Node.dma_ranges n ⦃ r => Agrees AddressMapRepr errorOf r N.dmaRanges ⦄

/-- `Node::translate_reg(span)`: the span of `Node.translateReg` of the span,
or its error. Feature: `krepi.platform.device-tree`. -/
def NodeTranslateReg : Prop :=
  ∀ (n : fdt.Node) (N : Node) (span : fdt.Span), NodeRepr n N →
    fdt.nodes.Node.translate_reg n span ⦃ r =>
      Agrees SpanRepr errorOf r (N.translateReg (spanOf span)) ⦄

end Krepi.Statements.Fdt
