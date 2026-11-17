module

public import Krepi.SpecProperties.Fdt.Properties

/-!
# Device tree: a builder of test trees

A builder of small device trees, from which the specification tests of the
`fdt` component state their inputs. It has the operations of the builder of
the tests of the prototype tree: begin and end a node; add a property with
its value, its cells, a string, a list of strings or no value; add a
no-operation token or a raw word; write over the last bytes of the structure
block, such as the padding after a property value; add an entry of the
reservation map; and finish the tree with its header, padded with zero bytes
to a larger `totalsize` where one is asked. On a finished tree, a word or
bytes can be written at an offset, such as a field of the header, and a byte
can be inverted. `minimal` is the tree of the helper of that name of those
tests, with one RAM range.

The builder writes the format through the encoder of
`Krepi.SpecProperties.Fdt`, `BuiltTree` with its `Item`s, from which the
limits of the parse are stated, so the specification tests and the
properties share one encoding of a tree: a header of version 17, compatible
with 16; the reservation map at offset 40 with its terminator; the structure
block right after it, each token padded with zero bytes to a multiple of 4
and the end token last; and the strings block right after that. As in the
prototype's builder, each property adds its name to the end of the strings
block, so a name that two properties share is written twice. The builder
checks nothing: a tree that it writes may break any rule of the format, and
the parse decides.
-/

@[expose] public section

namespace Krepi.SpecTests.Fdt

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

/-! ## Bytes -/

/-- The big-endian cells of `values`, 4 bytes each, the low 32 bits of each
value. -/
def cellBytes (values : List Nat) : List UInt8 := values.flatMap be32

/-- The bytes of a NUL-terminated string. -/
def stringBytes (s : String) : List UInt8 := s.toByteArray.toList ++ [0]

/-- Bytes as a `ByteArray`. -/
def bytesOf (bytes : List UInt8) : ByteArray := ⟨bytes.toArray⟩

/-- `list` with `bytes` written over it from the index `offset`, for an
`offset` and a length within the list. -/
def writeAt (list : List UInt8) (offset : Nat) (bytes : List UInt8) : List UInt8 :=
  list.take offset ++ bytes ++ list.drop (offset + bytes.length)

/-! ## The builder -/

/-- A tree being built: its reservation entries, property names and items, as
the encoder takes them, and the bytes written over parts of its structure
block, each at its offset from the start of that block, in the order in
which they were written. -/
structure Builder where
  tree : BuiltTree := ⟨[], [], []⟩
  overwrites : List (Nat × List UInt8) := []

namespace Builder

/-- The builder of a tree without reservation entries, names or items. -/
def empty : Builder := {}

/-- The builder with `item` added at the end of the structure block. -/
def item (b : Builder) (item : Item) : Builder :=
  { b with tree := { b.tree with items := b.tree.items ++ [item] } }

/-- A begin-node token with the name `name`, padded with zero bytes. -/
def beginNode (b : Builder) (name : String) : Builder := b.item (.beginNode name)

/-- An end-node token. -/
def endNode (b : Builder) : Builder := b.item .endNode

/-- A no-operation token. -/
def nop (b : Builder) : Builder := b.item .nop

/-- A property token with the name `name`, which is added at the end of the
strings block, and the value `value`, padded with zero bytes. -/
def property (b : Builder) (name : String) (value : List UInt8) : Builder :=
  { b with tree := { b.tree with
      names := b.tree.names ++ [name]
      items := b.tree.items ++ [.property b.tree.names.length value] } }

/-- A property whose value is the big-endian cells of `values`. -/
def cells (b : Builder) (name : String) (values : List Nat) : Builder :=
  b.property name (cellBytes values)

/-- A property whose value is the NUL-terminated string `s`. -/
def string (b : Builder) (name : String) (s : String) : Builder :=
  b.property name (stringBytes s)

/-- A property whose value is the NUL-terminated strings `ss`, in order. -/
def strings (b : Builder) (name : String) (ss : List String) : Builder :=
  b.property name (ss.flatMap stringBytes)

/-- A property without a value, such as `no-map` or an empty `ranges`. -/
def flag (b : Builder) (name : String) : Builder := b.property name []

/-- An entry of the reservation map, its address and its size, before the
terminator. -/
def reserve (b : Builder) (start size : Nat) : Builder :=
  { b with tree := { b.tree with reservations := b.tree.reservations ++ [(start, size)] } }

/-- The number of bytes of the structure block so far, its end token not
counted. -/
def structureSize (b : Builder) : Nat :=
  (b.tree.items.flatMap (Item.bytes (nameOffsets 0 b.tree.names))).length

/-- `bytes` written over the last bytes of the structure block so far, as the
prototype's tests write into its structure: after a property value, over the
padding that follows it. -/
def overwrite (b : Builder) (bytes : List UInt8) : Builder :=
  { b with overwrites := b.overwrites ++ [(b.structureSize - bytes.length, bytes)] }

/-- A raw big-endian word in the structure block: a no-operation token with
`value` written over it. -/
def word (b : Builder) (value : Nat) : Builder := b.nop.overwrite (be32 value)

/-- The begin node of the root, with 2 address cells and 2 size cells. -/
def root (b : Builder) : Builder :=
  b.beginNode "" |>.cells "#address-cells" [2] |>.cells "#size-cells" [2]

/-- The memory node of the prototype's tests, `memory@100000000` with the
`device_type` `memory` and the one RAM range `[0x1_0000_0000, 0x1_0020_0000)`
in 2 address cells and 2 size cells. -/
def memory (b : Builder) : Builder :=
  b.beginNode "memory@100000000" |>.string "device_type" "memory"
    |>.cells "reg" [1, 0, 0, 0x20_0000] |>.endNode

/-- The finished tree: the bytes of the tree with its end token, followed by
zero bytes up to a `totalsize` of `size` when the tree is shorter, with the
overwrites written into the structure block at the offset that its header
gives. -/
def finishTo (b : Builder) (size : Nat) : ByteArray :=
  let blob := b.tree.bytes size
  let start := beNat blob 8 4
  bytesOf (b.overwrites.foldl (fun list w => writeAt list (start + w.1) w.2) blob.data.toList)

/-- The finished tree, without zero bytes after its strings block. -/
def finish (b : Builder) : ByteArray := b.finishTo 0

end Builder

/-! ## Finished trees -/

/-- `minimal` of the prototype's tests, 223 bytes: the root with 2 address
cells and 2 size cells and the memory node of `Builder.memory`, and no
reservation entry. -/
def minimal : ByteArray := (Builder.empty.root.memory.endNode).finish

/-- `bytes` with `new` written from the offset `offset`, for an `offset` and a
length within `bytes`. -/
def setBytes (bytes : ByteArray) (offset : Nat) (new : List UInt8) : ByteArray :=
  bytesOf (writeAt bytes.data.toList offset new)

/-- `bytes` with the big-endian word `value` at `offset`: the prototype's
`set_word`, such as on a field of the header. -/
def setWord (bytes : ByteArray) (offset value : Nat) : ByteArray :=
  setBytes bytes offset (be32 value)

/-- `bytes` with the byte at `offset` inverted, `xor 0xff`: the change of one
byte of the prototype's tests. -/
def flipByte (bytes : ByteArray) (offset : Nat) : ByteArray :=
  setBytes bytes offset [bytes.data.toList.getD offset 0 ^^^ 0xff]

end Krepi.SpecTests.Fdt
