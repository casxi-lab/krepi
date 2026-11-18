module

public import Krepi.Spec.PageTables.Basic

/-!
# Page tables: kinds and descriptors

`page_tables::Kind`, `page_tables::descriptor` and `page_tables::direct_address`
of the contract's entry table, with the formats of `Descriptors and
attributes`:

- a descriptor is invalid when its bits 1 and 0 are `0b00`, and the
  component writes an invalid entry as 0;
- a table descriptor, at level 1 or 2, holds `0b11` in bits 1 and 0 and the
  address of the next table in bits 12 to 47, and no attribute;
- a page descriptor, at level 3, holds `0b11`, and a block descriptor, at
  level 2, `0b01`; both hold the output address, bits 12 to 47 for a page and
  21 to 47 for a block, and the bits of a kind;
- the nine kinds, each with the AP[2:1], PXN, UXN, AttrIndx, SH, nG and AF of
  its row, at the positions that the contract gives; every other bit of a
  leaf is 0.

The block descriptor of `ReadWrite` is its page descriptor with bit 1 clear,
and no other kind has a block form. The decoding functions read a descriptor
back into its kind, and the permission bits of a kind into whether it is
writable or executable, so that the rules of RO, NX and W^X can be stated on
the bits.
-/

@[expose] public section

namespace Krepi.Spec.PageTables

/-! ## Kinds -/

/-- `page_tables::Kind`: the nine attribute sets of a leaf, in the order of
the kind table. `KernelPrivateReadWrite` is a kind of the component, which no
mapping of release 0.1 uses. -/
inductive Kind where
  | readExecute
  | readOnly
  | readWrite
  | kernelPrivateReadWrite
  | device
  | userReadExecute
  | userReadOnly
  | userReadWrite
  | userDevice
  deriving DecidableEq, Repr, Inhabited

/-- The name of a kind as the contract writes it. -/
def Kind.name : Kind → String
  | .readExecute => "ReadExecute"
  | .readOnly => "ReadOnly"
  | .readWrite => "ReadWrite"
  | .kernelPrivateReadWrite => "KernelPrivateReadWrite"
  | .device => "Device"
  | .userReadExecute => "UserReadExecute"
  | .userReadOnly => "UserReadOnly"
  | .userReadWrite => "UserReadWrite"
  | .userDevice => "UserDevice"

/-- The nine kinds, in the order of the kind table. -/
def Kind.all : List Kind :=
  [.readExecute, .readOnly, .readWrite, .kernelPrivateReadWrite, .device,
    .userReadExecute, .userReadOnly, .userReadWrite, .userDevice]

/-- The columns of the kind table that a leaf holds: AP[2:1] as a number of
two bits, AP[2] the higher; PXN, UXN, nG and AF of one bit; AttrIndx of three
bits; SH of two bits. -/
structure Attributes where
  ap : Nat
  pxn : Nat
  uxn : Nat
  attrIndx : Nat
  sh : Nat
  ng : Nat
  af : Nat
  deriving DecidableEq, Repr

/-- The row of a kind in the kind table of `Descriptors and attributes`. -/
def Kind.attributes : Kind → Attributes
  | .readExecute =>            ⟨0b10, 0, 1, 1, 0b11, 0, 1⟩
  | .readOnly =>               ⟨0b10, 1, 1, 1, 0b11, 0, 1⟩
  | .readWrite =>              ⟨0b00, 1, 1, 1, 0b11, 0, 1⟩
  | .kernelPrivateReadWrite => ⟨0b00, 1, 1, 1, 0b11, 1, 1⟩
  | .device =>                 ⟨0b00, 1, 1, 0, 0b00, 0, 1⟩
  | .userReadExecute =>        ⟨0b11, 1, 0, 1, 0b11, 1, 1⟩
  | .userReadOnly =>           ⟨0b11, 1, 1, 1, 0b11, 1, 1⟩
  | .userReadWrite =>          ⟨0b01, 1, 1, 1, 0b11, 1, 1⟩
  | .userDevice =>             ⟨0b01, 1, 1, 0, 0b00, 1, 1⟩

/-- The bits of a leaf that its attributes set: AP[2:1] at bits 7 and 6,
AttrIndx at bits 2 to 4, SH at bits 8 and 9, AF at bit 10, nG at bit 11, PXN at
bit 53 and UXN at bit 54. -/
def Attributes.bits (a : Attributes) : UInt64 :=
  UInt64.ofNat (a.attrIndx * 2 ^ 2 + a.ap * 2 ^ 6 + a.sh * 2 ^ 8 + a.af * 2 ^ 10 +
    a.ng * 2 ^ 11 + a.pxn * 2 ^ 53 + a.uxn * 2 ^ 54)

/-- RO: AP[2] is set, so neither EL1 nor EL0 writes the page. -/
def Attributes.readOnly (a : Attributes) : Bool := a.ap / 2 % 2 == 1

/-- Whether EL1 or EL0 can write the page: AP[2] is clear. -/
def Attributes.writable (a : Attributes) : Bool := !a.readOnly

/-- Whether EL0 has data access: AP[1] is set. -/
def Attributes.el0Access (a : Attributes) : Bool := a.ap % 2 == 1

/-- Whether EL1 executes the page: PXN is clear. -/
def Attributes.executableEl1 (a : Attributes) : Bool := a.pxn % 2 == 0

/-- Whether EL0 executes the page: UXN is clear. -/
def Attributes.executableEl0 (a : Attributes) : Bool := a.uxn % 2 == 0

/-- Whether EL1 or EL0 executes the page. -/
def Attributes.executable (a : Attributes) : Bool := a.executableEl1 || a.executableEl0

/-- Device: AttrIndx 0, Device-nGnRnE memory. -/
def Attributes.isDevice (a : Attributes) : Bool := a.attrIndx == 0

/-- Global: nG clear, so the translation holds for every ASID. -/
def Attributes.isGlobal (a : Attributes) : Bool := a.ng % 2 == 0

/-! ## Descriptors -/

/-- Bits 12 to 47, the output address of a page and the address of the next
table of a table descriptor. -/
def ADDRESS_MASK : UInt64 := 0x0000_ffff_ffff_f000

/-- Bits 21 to 47, the output address of a block. -/
def BLOCK_ADDRESS_MASK : UInt64 := 0x0000_ffff_ffe0_0000

/-- Bits 1 and 0 of a table or a page descriptor. -/
def TABLE_OR_PAGE : UInt64 := 0b11

/-- Bits 1 and 0 of a block descriptor. -/
def BLOCK : UInt64 := 0b01

/-- The invalid descriptor that the component writes. -/
def INVALID : UInt64 := 0

/-- Bits 1 and 0 of a descriptor. -/
def typeBits (d : UInt64) : UInt64 := d &&& 0b11

/-- Whether a descriptor is valid: its bits 1 and 0 are not `0b00`. -/
def isValid (d : UInt64) : Bool := typeBits d != 0

/-- The output address of a page descriptor, or the address that a table
descriptor holds: bits 12 to 47. -/
def outputAddress (d : UInt64) : UInt64 := d &&& ADDRESS_MASK

/-- The output address of a block descriptor: bits 21 to 47. -/
def blockAddress (d : UInt64) : UInt64 := d &&& BLOCK_ADDRESS_MASK

/-- `page_tables::descriptor(kind, address)`: the page descriptor of a kind and
an output address. The address takes bits 12 to 47; its other bits do not
reach the descriptor, since every other bit of a leaf is 0 or a bit of the
kind. -/
def descriptor (k : Kind) (a : UInt64) : UInt64 :=
  (a &&& ADDRESS_MASK) ||| k.attributes.bits ||| TABLE_OR_PAGE

/-- The block descriptor of `ReadWrite` at an output address: its page
descriptor at the address rounded to bits 21 to 47, with bit 1 clear. -/
def blockDescriptor (a : UInt64) : UInt64 :=
  descriptor .readWrite (a &&& BLOCK_ADDRESS_MASK) &&& ~~~(0b10 : UInt64)

/-- The table descriptor of the table at an address: the address in bits 12
to 47 and `0b11` in bits 1 and 0, with no attribute. -/
def tableDescriptor (a : UInt64) : UInt64 := (a &&& ADDRESS_MASK) ||| TABLE_OR_PAGE

/-- Whether a descriptor is a table descriptor with no attribute: `0b11` in
bits 1 and 0 and nothing outside them and bits 12 to 47. -/
def isPlainTableDescriptor (d : UInt64) : Bool := d &&& ~~~ADDRESS_MASK == TABLE_OR_PAGE

/-- The kind of a page descriptor: the kind whose page descriptor at the
output address of `d` is `d`, if there is one. The rows of the kind table
differ, so at most one kind fits. -/
def Kind.ofPage (d : UInt64) : Option Kind :=
  Kind.all.find? fun k => descriptor k (outputAddress d) == d

/-- Whether a descriptor is the block descriptor of `ReadWrite` at its output
address. -/
def isReadWriteBlock (d : UInt64) : Bool := blockDescriptor (blockAddress d) == d

/-! ## The direct address -/

/-- `page_tables::direct_address(range)`: `DIRECT_BASE | start` for a physical
range whose end is at most $2^{39}$, and nothing otherwise, so that a range
that would wrap or leave the window of the direct map has no direct address.
-/
def directAddress (r : PhysRange) : Option UInt64 :=
  if r.endNat ≤ VA_LIMIT then some (DIRECT_BASE ||| r.start) else none

end Krepi.Spec.PageTables
