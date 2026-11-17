module

public import Krepi.Spec.Fdt.Bytes

/-!
# Device tree: the parse

`Fdt::parse` as an executable function from the bytes given to a tree or one
error. It checks the header and the blocks, then the reservation map entry by
entry, then every token of the structure block in its order, and builds the
tree only from bytes that passed those checks. The three parts are the first
three steps of the error order of the parse and the entries on a tree in the
contract's `Rejection and error priority`, and each part checks its rules in
the order that the step lists them, so the first broken rule decides the
error.

The tree is the abstract value of what the parse accepted: `totalsize`, the
entries of the reservation map before its terminator, and the nodes in the
order of the structure block, each with its name, the index of its parent and
its properties with their names and values. A property value is exactly its
declared length; the padding after it is checked to lie within the block but
is not part of the value. The contract's tree borrows the bytes and copies
none; the specification states only the values that the entries read from it.

The loops are structural recursion on a bound taken from the contract: the
reservation map reads at most `MAX_RESERVATIONS + 1` entries and the
structure block at most `MAX_TOKENS` tokens.
-/

@[expose] public section

namespace Krepi.Spec.Fdt

/-! ## The tree -/

/-- One node of a tree: its name, the index of its parent among the nodes of
the tree, none for the root, and its properties in the order of the structure
block. -/
structure NodeRecord where
  name : String
  parent : Option Nat
  properties : List (String × ByteArray)
  deriving DecidableEq, Inhabited

/-- `Fdt`, the tree that `Fdt::parse` returns. `totalSize` is the header's
`totalsize`, which `Fdt::total_size` gives; `reservations` holds the entries
of the reservation map in their order, which `Fdt::reservations` gives;
`records` holds the nodes in the order of the structure block, the root first.
-/
structure Fdt where
  totalSize : UInt64
  reservations : List Span
  records : Array NodeRecord
  deriving DecidableEq, Inhabited

/-! ## The header and the blocks -/

/-- The size of the header in bytes. -/
def HEADER_SIZE : Nat := 40

/-- The magic of a device tree. -/
def FDT_MAGIC : UInt32 := 0xd00d_feed

/-- The offsets and sizes of the blocks, read from the header. -/
structure Layout where
  total : Nat
  structStart : Nat
  structSize : Nat
  stringsStart : Nat
  stringsSize : Nat
  reserveStart : Nat
  deriving DecidableEq, Repr

/-- The end of the structure block. -/
def Layout.structEnd (l : Layout) : Nat := l.structStart + l.structSize

/-- The end of the strings block. -/
def Layout.stringsEnd (l : Layout) : Nat := l.stringsStart + l.stringsSize

/-- The block of `size` bytes at `start` of the tree `blob`: `BadLayout` when
it starts inside the header, `Overflow` when its end leaves 64 bits and
`Truncated` when it ends past the tree. -/
def block (blob : ByteArray) (start size : Nat) : Except Error ByteArray := do
  if start < HEADER_SIZE then throw .badLayout
  let e ← checkedAdd start size
  if blob.size < e then throw .truncated
  pure (blob.extract start e)

/-- What the first step of the parse yields: the tree's bytes, the first
`totalsize` of the input, its layout and its two blocks. -/
structure Header where
  blob : ByteArray
  layout : Layout
  structure_ : ByteArray
  strings : ByteArray

/-- Step 1 of the error order: the header and the blocks. Fewer than 40 bytes,
`Truncated`; the magic, `BadMagic`; `totalsize` below 40, `BadLayout`; above
`MAX_BLOB_SIZE`, `LimitExceeded`; fewer bytes than `totalsize`, `Truncated`;
the versions, `UnsupportedVersion`; the alignment of the structure block and
of the reservation map, `BadAlignment`; the structure block and then the
strings block within the tree (`block`); a structure block shorter than 12
bytes or a reservation map inside the header, then intersecting structure and
strings blocks, `BadLayout`. -/
def header (input : ByteArray) : Except Error Header := do
  if input.size < HEADER_SIZE then throw .truncated
  let magic ← u32At input 0
  if magic ≠ FDT_MAGIC then throw .badMagic
  let total := (← u32At input 4).toNat
  if total < HEADER_SIZE then throw .badLayout
  if MAX_BLOB_SIZE.toNat < total then throw .limitExceeded
  if input.size < total then throw .truncated
  let blob := input.extract 0 total
  let version := (← u32At blob 20).toNat
  let compatible := (← u32At blob 24).toNat
  if version < 17 || !(compatible == 16 || compatible == 17) || version < compatible then
    throw .unsupportedVersion
  let structStart := (← u32At blob 8).toNat
  let stringsStart := (← u32At blob 12).toNat
  let reserveStart := (← u32At blob 16).toNat
  let stringsSize := (← u32At blob 32).toNat
  let structSize := (← u32At blob 36).toNat
  if structStart % 4 != 0 || structSize % 4 != 0 || reserveStart % 8 != 0 then
    throw .badAlignment
  let structure_ ← block blob structStart structSize
  let strings ← block blob stringsStart stringsSize
  if structSize < 12 || reserveStart < HEADER_SIZE then throw .badLayout
  let layout : Layout :=
    { total, structStart, structSize, stringsStart, stringsSize, reserveStart }
  if intersects structStart layout.structEnd stringsStart layout.stringsEnd then
    throw .badLayout
  pure { blob, layout, structure_, strings }

/-! ## The reservation map -/

/-- The entries of the reservation map from `cursor` on, after the entries
`earlier`, reading at most `fuel` more entries. For each entry: past the
tree, `Overflow` or `Truncated`; on the structure or strings block,
`BadLayout`; two zeros end the map; otherwise more than `MAX_RESERVATIONS`
entries, `LimitExceeded`; its end, `Overflow`; its size, `EmptyRegion`;
overlap with an earlier entry, `Overlap`. Out of fuel, `LimitExceeded`, which
the bound `MAX_RESERVATIONS + 1` of `reservationMap` never reaches. -/
def reservationsFrom (h : Header) :
    (fuel cursor : Nat) → (earlier : List Span) → Except Error (List Span)
  | 0, _, _ => .error .limitExceeded
  | fuel + 1, cursor, earlier => do
    let e ← checkedAdd cursor 16
    if h.layout.total < e then throw .truncated
    if intersects cursor e h.layout.structStart h.layout.structEnd ||
        intersects cursor e h.layout.stringsStart h.layout.stringsEnd then
      throw .badLayout
    let start ← u64At h.blob cursor
    let size ← u64At h.blob (cursor + 8)
    if start == 0 && size == 0 then return earlier
    if MAX_RESERVATIONS.toNat < earlier.length + 1 then throw .limitExceeded
    let span ← Span.new start size
    if size = 0 then throw .emptyRegion
    if earlier.any (·.overlaps span) then throw .overlap
    reservationsFrom h fuel e (earlier ++ [span])

/-- Step 2 of the error order: the reservation map, entry by entry. -/
def reservationMap (h : Header) : Except Error (List Span) :=
  reservationsFrom h (MAX_RESERVATIONS.toNat + 1) h.layout.reserveStart []

/-! ## Tokens -/

/-- A token of the structure block, decoded. -/
inductive Token where
  | beginNode (name : String)
  | endNode
  | property (name : String) (value : ByteArray)
  | nop
  | endStructure

/-- The encoding of the token at `cursor` of the structure block `str`, whose
property names lie in the strings block `strs`, and the offset of the next
token. Its tag past the end of the block, `Truncated`; a tag other than 1, 2,
3, 4 and 9, `BadToken`. A begin node: its name without a NUL in the block or
not UTF-8, `BadString`; the padding after the name past the end of the block,
`Truncated`, then a nonzero byte in it, `BadPadding`; then a character of the
name outside its set, `BadString`. A property: its length and name offset
past the end of the block, `Truncated`; the end of its value beyond 64 bits,
`Overflow`, then past the end of the block, `Truncated`; its name, empty,
longer than `MAX_PROPERTY_NAME` bytes, not a NUL-terminated UTF-8 string
within the strings block or with a character outside its set, `BadString`;
then the padding after the value past the end of the block, `Truncated`. -/
def decodeToken (str strs : ByteArray) (cursor : Nat) : Except Error (Token × Nat) := do
  let tag ← u32At str cursor
  let next := cursor + 4
  match tag.toNat with
  | 1 =>
    let (name, nameEnd) ← cString str next
    let after ← paddedEnd str nameEnd true
    if !name.toList.all isNodeNameChar then throw .badString
    pure (.beginNode name, after)
  | 2 => pure (.endNode, next)
  | 3 =>
    let length ← u32At str next
    let nameOffset ← u32At str (next + 4)
    let valueStart := next + 8
    let valueEnd ← checkedAdd valueStart length.toNat
    if str.size < valueEnd then throw .truncated
    let (name, _) ← cString strs nameOffset.toNat
    if name.isEmpty || MAX_PROPERTY_NAME.toNat < name.utf8ByteSize ||
        !name.toList.all isPropertyNameChar then
      throw .badString
    let after ← paddedEnd str valueEnd false
    pure (.property name (str.extract valueStart valueEnd), after)
  | 4 => pure (.nop, next)
  | 9 => pure (.endStructure, next)
  | _ => throw .badToken

/-! ## The place of a token in the tree -/

/-- An open node: the index of its record, the names of its properties so far
and whether a child has begun in it. -/
structure Frame where
  index : Nat
  names : List String
  children : Bool

/-- The state of the walk over the tokens: the open nodes, innermost first,
whether the root has begun, and the nodes so far. -/
structure Walk where
  open_ : List Frame
  seenRoot : Bool
  records : Array NodeRecord

/-- The walk before the first token. -/
def Walk.start : Walk := { open_ := [], seenRoot := false, records := #[] }

/-- The place of a token other than the end token in the tree, in the order of
the contract: `BadTree`, the depth `LimitExceeded`, the properties of its node
`LimitExceeded`, then `DuplicateProperty`. A begin node outside every node is
the root, which must be the first and have an empty name; inside a node it is
a child, which must have a name, and no node lies deeper than
`MAX_DEPTH - 1`. A property belongs to the innermost open node and precedes
its children. An end node closes the innermost open node. -/
def Walk.place (w : Walk) : Token → Except Error Walk
  | .beginNode name => do
    match w.open_ with
    | [] => if w.seenRoot || name ≠ "" then throw .badTree
    | _ :: _ => if name = "" then throw .badTree
    if MAX_DEPTH.toNat ≤ w.open_.length then throw .limitExceeded
    let parent := w.open_.head?.map (·.index)
    let outer := match w.open_ with
      | [] => []
      | f :: rest => { f with children := true } :: rest
    pure { open_ := ⟨w.records.size, [], false⟩ :: outer, seenRoot := true,
           records := w.records.push ⟨name, parent, []⟩ }
  | .property name value => do
    match w.open_ with
    | [] => throw .badTree
    | f :: rest =>
      if f.children then throw .badTree
      if MAX_PROPERTIES.toNat < f.names.length + 1 then throw .limitExceeded
      if f.names.contains name then throw .duplicateProperty
      pure { w with
        open_ := { f with names := f.names ++ [name] } :: rest
        records := w.records.modify f.index
          fun r => { r with properties := r.properties ++ [(name, value)] } }
  | .endNode =>
    match w.open_ with
    | [] => .error .badTree
    | _ :: rest => .ok { w with open_ := rest }
  | .nop => .ok w
  | .endStructure => .ok w

/-- The tokens from `cursor` on, reading at most `fuel` more. Each token is
decoded, then placed in the tree. The end token ends the walk: without a root,
with open nodes or before the end of the block, `BadTree`. Out of fuel, the
structure block holds more than `MAX_TOKENS` tokens without its end token,
`LimitExceeded`. -/
def walkTokens (str strs : ByteArray) :
    (fuel cursor : Nat) → Walk → Except Error (Array NodeRecord)
  | 0, _, _ => .error .limitExceeded
  | fuel + 1, cursor, w => do
    let (token, next) ← decodeToken str strs cursor
    match token with
    | .endStructure =>
      if !w.seenRoot || !w.open_.isEmpty || next ≠ str.size then throw .badTree
      pure w.records
    | token =>
      let w ← w.place token
      walkTokens str strs fuel next w

/-- Step 3 of the error order: the tokens, in the order of the structure
block, at most `MAX_TOKENS` of them, the end token included. -/
def structureNodes (h : Header) : Except Error (Array NodeRecord) :=
  walkTokens h.structure_ h.strings MAX_TOKENS.toNat 0 Walk.start

/-! ## The parse -/

/-- `Fdt::parse(input)`: the tree of the device tree in `input`, or the error
of the first broken rule of steps 1 to 3 of the error order. -/
def Fdt.parse (input : ByteArray) : Except Error Fdt := do
  let h ← header input
  let reservations ← reservationMap h
  let records ← structureNodes h
  pure { totalSize := UInt64.ofNat h.layout.total, reservations, records }

end Krepi.Spec.Fdt
