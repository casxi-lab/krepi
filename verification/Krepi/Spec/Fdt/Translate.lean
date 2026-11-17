module

public import Krepi.Spec.Fdt.Nodes

/-!
# Device tree: cells and address translation

The entries of `Address translation`: the numbers of cells, the regions of a
`reg`, the maps of `ranges` and `dma-ranges` with the translation through
them, and the node entries that read these properties in the cells of the
right node. Step 7 of the error order of the entries on a tree gives the
order of the checks of `cells_u64`, `Reg::new`, `AddressMap::new` and a
translation.

A `Reg` and an `AddressMap` are checked completely at construction, so their
values hold only spans that passed every check: the entries of a `Reg` are
its spans, and the windows of an `AddressMap` are its pairs of child and
parent spans of one size. A number is read in 0, 1 or 2 cells and never
truncated; an address of one cell lies in the first 4 GiB, and one of two
cells within 64 bits.
-/

@[expose] public section

namespace Krepi.Spec.Fdt

/-! ## Cells -/

/-- `cells_u64(bytes, cells)`: the number of `cells` big-endian cells. More
than 2 cells, `UnsupportedCells`; then bytes that are not exactly that many
cells, `BadProperty`. -/
def cellsU64 (bytes : ByteArray) (cells : UInt32) : Except Error UInt64 :=
  if 2 < cells.toNat then .error .unsupportedCells
  else if bytes.size ≠ cells.toNat * 4 then .error .badProperty
  else .ok (UInt64.ofNat (beNat bytes 0 bytes.size))

/-- The `count` pieces of `stride` bytes from the start of `bytes`. -/
def chunks (bytes : ByteArray) (stride : Nat) : (count : Nat) → (from_ : Nat) → List ByteArray
  | 0, _ => []
  | count + 1, from_ => bytes.extract from_ (from_ + stride) :: chunks bytes stride count (from_ + stride)

/-- The width of an address of `cells` cells: the span ends within 64 bits,
`Overflow`, and with one cell it starts and ends within the first 4 GiB,
`Overflow`. -/
def checkWidth (s : Span) (cells : UInt32) : Except Error Unit :=
  if ¬ s.Valid then .error .overflow
  else if cells == 1 && (2 ^ 32 ≤ s.start.toNat || 2 ^ 32 < s.endNat) then .error .overflow
  else .ok ()

/-! ## Regions -/

/-- `Reg`: the regions of a `reg` value, its spans in the order of the value,
each checked when the value was. -/
structure Reg where
  entries : List Span
  deriving DecidableEq, Repr

/-- One entry of a `reg`: its address in `addressCells` cells and its size in
`sizeCells`, a span whose end leaves 64 bits or, with one address cell, the
first 4 GiB, `Overflow`. -/
def regEntry (addressCells sizeCells : UInt32) (entry : ByteArray) : Except Error Span := do
  let split := addressCells.toNat * 4
  let start ← cellsU64 (entry.extract 0 split) addressCells
  let size ← cellsU64 (entry.extract split entry.size) sizeCells
  let span ← Span.new start size
  checkWidth span addressCells
  pure span

/-- `Reg::new(bytes, address_cells, size_cells)`: address cells other than 1 or
2 or size cells above 2, `UnsupportedCells`; an empty value or one that is not
a whole number of entries, `BadProperty`; then each entry in order. -/
def Reg.new (bytes : ByteArray) (addressCells sizeCells : UInt32) : Except Error Reg := do
  if !(addressCells == 1 || addressCells == 2) || 2 < sizeCells.toNat then
    throw .unsupportedCells
  let stride := (addressCells.toNat + sizeCells.toNat) * 4
  if bytes.size == 0 || bytes.size % stride != 0 then throw .badProperty
  let entries ← (chunks bytes stride (bytes.size / stride) 0).mapM
    (regEntry addressCells sizeCells)
  pure ⟨entries⟩

/-! ## Address maps -/

/-- The three kinds of an address map. -/
inductive MappingKind where
  | absent
  | identity
  | windows
  deriving DecidableEq, Repr

/-- A window of a map: a span of the child's addresses and the span of the
parent's addresses of the same size that it maps to. -/
structure Window where
  child : Span
  parent : Span
  deriving DecidableEq, Repr

/-- `AddressMap`: the map of a `ranges` or `dma-ranges` value with the cells of
its two sides. `windows` is none for an absent property, which maps nothing,
the empty list for an empty one, the identity, and the windows of the value
otherwise. -/
structure AddressMap where
  windows : Option (List Window)
  childCells : UInt32
  parentCells : UInt32
  sizeCells : UInt32
  deriving DecidableEq, Repr

/-- One window of a map: its child address, its parent address and its size,
in their cells. A size of 0, `EmptyRegion`; then a child or parent span whose
end leaves 64 bits or the width of its side, `Overflow`. -/
def window (childCells parentCells sizeCells : UInt32) (entry : ByteArray) :
    Except Error Window := do
  let childEnd := childCells.toNat * 4
  let parentEnd := childEnd + parentCells.toNat * 4
  let child ← cellsU64 (entry.extract 0 childEnd) childCells
  let parent ← cellsU64 (entry.extract childEnd parentEnd) parentCells
  let size ← cellsU64 (entry.extract parentEnd entry.size) sizeCells
  if size = 0 then throw .emptyRegion
  let childSpan ← Span.new child size
  let parentSpan ← Span.new parent size
  checkWidth childSpan childCells
  checkWidth parentSpan parentCells
  pure ⟨childSpan, parentSpan⟩

/-- `AddressMap::new(bytes, child_cells, parent_cells, size_cells)`: child or
parent address cells other than 1 or 2, or size cells above 2,
`UnsupportedCells`; an absent value is the kind `Absent` and an empty one the
kind `Identity`; any other value without size cells or that is not a whole
number of windows, `BadProperty`; then each window in order. -/
def AddressMap.new (bytes : Option ByteArray) (childCells parentCells sizeCells : UInt32) :
    Except Error AddressMap := do
  if !(childCells == 1 || childCells == 2) || !(parentCells == 1 || parentCells == 2) ||
      2 < sizeCells.toNat then
    throw .unsupportedCells
  let windows ← match bytes with
    | none => pure none
    | some value =>
      if value.size = 0 then pure (some [])
      else do
        let stride := (childCells.toNat + parentCells.toNat + sizeCells.toNat) * 4
        if sizeCells == 0 || value.size % stride != 0 then throw .badProperty
        let ws ← (chunks value stride (value.size / stride) 0).mapM
          (window childCells parentCells sizeCells)
        pure (some ws)
  pure { windows, childCells, parentCells, sizeCells }

/-- `AddressMap::kind`. -/
def AddressMap.kind (m : AddressMap) : MappingKind :=
  match m.windows with
  | none => .absent
  | some [] => .identity
  | some (_ :: _) => .windows

/-- The translation of `request` through the windows `ws`, from the side
`source` of each window to its side `target`, after the windows before them
gave `found`: a second window that holds the request, `AmbiguousMapping`; a
window that holds part of it, `Unmapped`; the translated span, `Overflow`;
no window that holds it, `Unmapped`. -/
def throughWindows (request : Span) (source target : Window → Span) :
    List Window → Option Span → Except Error Span
  | [], none => .error .unmapped
  | [], some s => .ok s
  | w :: ws, found =>
    if (source w).holds request then do
      if found.isSome then throw .ambiguousMapping
      let start ← checkedAdd (target w).start.toNat
        (request.start.toNat - (source w).start.toNat)
      let s ← Span.new (UInt64.ofNat start) request.size
      throughWindows request source target ws (some s)
    else if (source w).overlaps request then .error .unmapped
    else throughWindows request source target ws found

/-- The translation of a request from the side whose cells are `sourceCells`
to the side whose cells are `targetCells`: the request of size 0,
`EmptyRegion`; its width, `Overflow`; an absent map, `Unmapped`; an identity
map, the width of the target side, `Overflow`; the windows in order. -/
def AddressMap.translate (m : AddressMap) (request : Span) (reverse : Bool) :
    Except Error Span := do
  if request.size = 0 then throw .emptyRegion
  let (sourceCells, targetCells) :=
    if reverse then (m.parentCells, m.childCells) else (m.childCells, m.parentCells)
  checkWidth request sourceCells
  match m.windows with
  | none => throw .unmapped
  | some [] =>
    checkWidth request targetCells
    pure request
  | some ws =>
    if reverse then throughWindows request (·.parent) (·.child) ws none
    else throughWindows request (·.child) (·.parent) ws none

/-- `AddressMap::to_parent(span)`: a span of the child's addresses as one of
the parent's. -/
def AddressMap.toParent (m : AddressMap) (span : Span) : Except Error Span :=
  m.translate span false

/-- `AddressMap::to_child(span)`: a span of the parent's addresses as one of
the child's. -/
def AddressMap.toChild (m : AddressMap) (span : Span) : Except Error Span :=
  m.translate span true

/-! ## The node entries -/

/-- `Node::reg`: the `reg` of the node in the cells of its parent. The root,
which has no parent, `BadTree`; no `reg`, `MissingProperty`; the address
cells and then the size cells of the parent, `BadProperty`; then `Reg::new`.
-/
def Node.reg (n : Node) : Except Error Reg := do
  let some parent := n.parent | throw .badTree
  let some value := n.property "reg" | throw .missingProperty
  let addressCells ← parent.addressCells
  let sizeCells ← parent.sizeCells
  Reg.new value addressCells sizeCells

/-- The map of the property `name` of the node, with the node's own address
cells on the child side, its parent's on the parent side and the node's own
size cells. The root, `BadTree`; the node's address cells, its parent's
address cells and the node's size cells, `BadProperty`; then
`AddressMap::new`. -/
def Node.addressMap (n : Node) (name : String) : Except Error AddressMap := do
  let some parent := n.parent | throw .badTree
  let value := n.property name
  let childCells ← n.addressCells
  let parentCells ← parent.addressCells
  let sizeCells ← n.sizeCells
  AddressMap.new value childCells parentCells sizeCells

/-- `Node::ranges`: the translation of CPU addresses below the node. -/
def Node.ranges (n : Node) : Except Error AddressMap := n.addressMap "ranges"

/-- `Node::dma_ranges`: the separate map of the addresses that devices below
the node use; absent when the node has no `dma-ranges`. -/
def Node.dmaRanges (n : Node) : Except Error AddressMap := n.addressMap "dma-ranges"

/-- The translation of `span` through the `ranges` of `bus` and of each bus
above it, the nearest first, up to the root, which translates nothing, taking
at most `fuel` steps. Out of fuel, `LimitExceeded`, which a tree that the
parse accepted never reaches: no node lies deeper than `MAX_DEPTH - 1`. -/
def climbRanges : (fuel : Nat) → (bus : Node) → (span : Span) → Except Error Span
  | 0, _, _ => .error .limitExceeded
  | fuel + 1, bus, span =>
    match bus.parent with
    | none => .ok span
    | some up => do
      let map ← bus.ranges
      let translated ← map.toParent span
      climbRanges fuel up translated

/-- `Node::translate_reg(span)`: a span of the node's parent bus as a CPU
address, through the `ranges` of each bus above the node. The root, which has
no parent bus, `BadTree`; then each bus from the nearest; a result whose end
leaves 64 bits, `Overflow`. -/
def Node.translateReg (n : Node) (span : Span) : Except Error Span := do
  let some bus := n.parent | throw .badTree
  let translated ← climbRanges MAX_DEPTH.toNat bus span
  let _ ← translated.endAddr
  pure translated

end Krepi.Spec.Fdt
