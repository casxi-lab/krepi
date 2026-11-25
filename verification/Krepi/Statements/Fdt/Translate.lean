module

public import Krepi.Statements.Fdt.Representation

/-!
# Device tree: refinement of the cells, regions, address maps and spans

One statement for each function of lines 115 and 118 of the entry table of
the contract (`docs/domains/boot-platform/fdt/contract.md`), and for the
`next` of a `Reg`: for every input of its machine widths, under the premises
that its arguments need, the function returns, and its result agrees with
that of its function of `Krepi.Spec.Fdt` through the representation of
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

/-! ## Cells and regions -/

/-- `cells_u64(bytes, cells)`: the number of `cellsU64`, or its error.
Feature: `krepi.platform.device-tree`. -/
def CellsU64 : Prop :=
  ∀ (bytes : Slice U8) (cells : U32),
    fdt.cells_u64 bytes cells ⦃ r =>
      Agrees (fun n N => word64 n = N) errorOf r (cellsU64 (bytesOf bytes) (word32 cells)) ⦄

/-- `Reg::new(bytes, address_cells, size_cells)`: a `Reg` that stands for the
entries of `Reg.new` of the bytes and the cells, or its error.
Feature: `krepi.platform.device-tree`. -/
def RegNew : Prop :=
  ∀ (bytes : Slice U8) (addressCells sizeCells : U32),
    fdt.translation.Reg.new bytes addressCells sizeCells ⦃ r =>
      Agrees (fun g R => RegRepr g R.entries) errorOf r
        (Reg.new (bytesOf bytes) (word32 addressCells) (word32 sizeCells)) ⦄

/-- `Reg::next()`: one call gives the next entry of the list that the `Reg`
stands for and leaves it standing for the rest; at the end it gives none and
stays at the end.
Feature: `krepi.platform.device-tree`. -/
def RegNext : Prop :=
  ∀ (g : fdt.Reg) (l : List Span), RegRepr g l → Advances fdt.translation.Reg.next SpanRepr g l

/-! ## Address maps -/

/-- `AddressMap::new(bytes, child_cells, parent_cells, size_cells)`: an
address map that stands for that of `AddressMap.new` of the value, none when
it is absent, and the cells, or its error.
Feature: `krepi.platform.device-tree`. -/
def AddressMapNew : Prop :=
  ∀ (bytes : Option (Slice U8)) (childCells parentCells sizeCells : U32),
    fdt.translation.AddressMap.new bytes childCells parentCells sizeCells ⦃ r =>
      Agrees AddressMapRepr errorOf r
        (AddressMap.new (bytes.map bytesOf) (word32 childCells) (word32 parentCells)
          (word32 sizeCells)) ⦄

/-- `AddressMap::kind()`: the kind of `AddressMap.kind`.
Feature: `krepi.platform.device-tree`. -/
def AddressMapKind : Prop :=
  ∀ (m : fdt.AddressMap) (M : AddressMap), AddressMapRepr m M →
    fdt.translation.AddressMap.kind m ⦃ k => kindOf k = M.kind ⦄

/-- `AddressMap::to_parent(span)`: the span of `AddressMap.toParent` of the
span, or its error.
Feature: `krepi.platform.device-tree`. -/
def AddressMapToParent : Prop :=
  ∀ (m : fdt.AddressMap) (M : AddressMap) (span : fdt.Span), AddressMapRepr m M →
    fdt.translation.AddressMap.to_parent m span ⦃ r =>
      Agrees SpanRepr errorOf r (M.toParent (spanOf span)) ⦄

/-- `AddressMap::to_child(span)`: the span of `AddressMap.toChild` of the
span, or its error.
Feature: `krepi.platform.device-tree`. -/
def AddressMapToChild : Prop :=
  ∀ (m : fdt.AddressMap) (M : AddressMap) (span : fdt.Span), AddressMapRepr m M →
    fdt.translation.AddressMap.to_child m span ⦃ r =>
      Agrees SpanRepr errorOf r (M.toChild (spanOf span)) ⦄

/-! ## Spans -/

/-- `Span::new(start, size)`: the span of `Span.new`, or its error.
Feature: `krepi.platform.device-tree`. -/
def SpanNew : Prop :=
  ∀ start size : U64,
    fdt.span.Span.new start size ⦃ r =>
      Agrees SpanRepr errorOf r (Span.new (word64 start) (word64 size)) ⦄

/-- `Span::end()`: the end of `Span.endAddr`, or its error.
Feature: `krepi.platform.device-tree`. -/
def SpanEnd : Prop :=
  ∀ s : fdt.Span,
    fdt.span.Span.end s ⦃ r => Agrees (fun n N => word64 n = N) errorOf r (spanOf s).endAddr ⦄

/-- `Span::contains(other)`: whether the span holds the other, or the error,
of `Span.contains`.
Feature: `krepi.platform.device-tree`. -/
def SpanContains : Prop :=
  ∀ s other : fdt.Span,
    fdt.span.Span.contains s other ⦃ r =>
      Agrees (· = ·) errorOf r ((spanOf s).contains (spanOf other)) ⦄

end Krepi.Statements.Fdt
