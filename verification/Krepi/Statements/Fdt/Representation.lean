module

public import KrepiGen.Fdt.Funs
public import Krepi.Statements.Basic
public import Krepi.Spec.Fdt.Boot

/-!
# Device tree: the representation of the values of the code

How a value of the code of the `fdt` component, as Aeneas translates it into
`KrepiGen.Fdt`, stands for a value of its specification, `Krepi.Spec.Fdt`.
The refinement statements of the component relate each function to its
specification through these relations, and take them, with the premises of
the proof path (`docs/domains/boot-platform/fdt/proof.md`), as the
hypotheses on their arguments.

- The errors, the spans, the reserved regions, the profiles and the CPU
  topology carry no invariant: each is a function of its fields.
- A memory map, a boot memory and a boot memory map hold arrays with a count
  of the entries in use: each stands for the value whose lists are the first
  `count` entries, with each count within its array.
- A tree is a view of bytes that the parse checked: it stands for the tree
  that `Fdt.parse` gives for its bytes, its blocks where the header of those
  bytes places them. A node is a begin-node token of its structure block:
  it stands for the node of the same index in the order of the block, with
  the offsets of its name, its properties and its parent.
- A `Reg` and an address map hold the value that the code checked: each
  stands for the value that its constructor of the specification gives for
  the same bytes and cells.
- An iterator stands for the list that its calls of `next` give
  (`Krepi.Statements.Stands`).
- A `&str` argument is read through `core::str::{str}::as_bytes`, which the
  translation keeps as a declaration without a body (`StrRepr`).
-/

@[expose] public section

open Aeneas
open Aeneas.Std (Slice Str U8 U32 U64)
open KrepiGen.Fdt
open Krepi.Spec.Fdt

namespace Krepi.Statements.Fdt

/-! ## Errors -/

/-- An error of the code as the error of the specification of the same name.
-/
def errorOf : fdt.Error → Error
  | .Truncated => .truncated
  | .BadMagic => .badMagic
  | .UnsupportedVersion => .unsupportedVersion
  | .BadLayout => .badLayout
  | .BadAlignment => .badAlignment
  | .BadToken => .badToken
  | .BadTree => .badTree
  | .BadString => .badString
  | .BadPadding => .badPadding
  | .DuplicateProperty => .duplicateProperty
  | .LimitExceeded => .limitExceeded
  | .UnsupportedCells => .unsupportedCells
  | .BadProperty => .badProperty
  | .MissingProperty => .missingProperty
  | .Overflow => .overflow
  | .EmptyRegion => .emptyRegion
  | .Overlap => .overlap
  | .Unmapped => .unmapped
  | .AmbiguousMapping => .ambiguousMapping
  | .BadPath => .badPath
  | .NoMemory => .noMemory

/-- An error of the boot memory map of the code as the error of the
specification of the same name. -/
def planErrorOf : fdt.PlanError → PlanError
  | .InvalidRange => .invalidRange
  | .Overflow => .overflow
  | .Alignment => .alignment
  | .Capacity => .capacity
  | .Overlap => .overlap
  | .OutsideRam => .outsideRam
  | .ArenaTooLarge => .arenaTooLarge

/-! ## Values without an invariant -/

/-- A span of the code as a span of the specification. -/
def spanOf (s : fdt.Span) : Span := ⟨word64 s.start, word64 s.size⟩

/-- A span of the code stands for its span of the specification. -/
def SpanRepr (s : fdt.Span) (t : Span) : Prop := spanOf s = t

/-- The spans of a slice of the code, in their order. -/
def spansOf (s : Slice fdt.Span) : List Span := s.val.map spanOf

/-- A reserved region of the code as one of the specification. -/
def regionOf (r : fdt.ReservedRegion) : ReservedRegion :=
  ⟨spanOf r.span, r.no_map, r.reusable⟩

/-- The reserved regions of a slice of the code, in their order. -/
def regionsOf (s : Slice fdt.ReservedRegion) : List ReservedRegion := s.val.map regionOf

/-- A PSCI conduit of the code as that of the specification. -/
def conduitOf : fdt.PsciConduit → PsciConduit
  | .Hvc => .hvc
  | .Smc => .smc

/-- An affinity level of the code as that of the specification. -/
def levelOf : fdt.AffinityLevel → AffinityLevel
  | .Aff0 => .aff0
  | .Aff1 => .aff1
  | .Aff2 => .aff2
  | .Aff3 => .aff3

/-- The timer interrupts of the code as those of the specification: the five
numbers in their order and the count. -/
def timersOf (t : fdt.TimerInterrupts) : TimerInterrupts :=
  ⟨Vector.ofFn fun i : Fin 5 => word32 t.numbers.val[i.val]!, byte t.count⟩

/-- A CPU profile of the code as that of the specification. -/
def profileOf (p : fdt.CpuProfile) : CpuProfile :=
  ⟨conduitOf p.conduit, levelOf p.affinity_level, byte p.cpu_counts, p.cpu0_enable_method,
    p.timer_interrupts.map timersOf⟩

/-- A CPU topology of the code as that of the specification. -/
def topologyOf (t : fdt.CpuTopology) : CpuTopology := ⟨profileOf t.profile, word64 t.count⟩

/-- A hand-over profile of the code as that of the specification. -/
def handOverOf (h : fdt.HandOverProfile) : HandOverProfile :=
  ⟨word64 h.max_blob_size, byte h.alignment_log2, bytesOf h.compatible⟩

/-- A mapping kind of the code as that of the specification. -/
def kindOf : fdt.MappingKind → MappingKind
  | .Absent => .absent
  | .Identity => .identity
  | .Windows => .windows

/-! ## Values with a count -/

/-- A memory map of the code stands for the memory map of the specification
whose RAM ranges and reserved regions are the first `ram_count` and
`reserved_count` entries of its arrays, each count within its array. -/
def MemoryMapRepr (m : fdt.MemoryMap) (M : MemoryMap) : Prop :=
  m.ram_count.val ≤ MAX_MEMORY_REGIONS.toNat ∧
    m.reserved_count.val ≤ MAX_RESERVED_REGIONS.toNat ∧
    M = ⟨(m.ram.val.take m.ram_count.val).map spanOf,
      (m.reserved.val.take m.reserved_count.val).map regionOf, word64 m.dynamic⟩

/-- A boot memory of the code stands for the boot memory of the
specification whose memory map its memory map stands for and whose spans,
sum, limit and alignment are its own. -/
def BootMemoryRepr (m : fdt.BootMemory) (M : BootMemory) : Prop :=
  MemoryMapRepr m.memory M.memory ∧ M.dtb = spanOf m.dtb ∧ M.image = spanOf m.image ∧
    M.ramBytes = word64 m.ram_bytes ∧ M.maxBlobSize = word64 m.max_blob_size ∧
    M.alignmentLog2 = byte m.alignment_log2

/-- A boot memory map of the code stands for the boot memory map of the
specification whose banks and managed banks are the first `ram_count` and
`managed_count` entries of their arrays, and whose boot storage and firmware
reservations are the first `boot_count` and the next up to `reserved_count`
entries of the array of reservations, each count within its array. -/
def MemoryPlanRepr (p : fdt.MemoryPlan) (P : MemoryPlan) : Prop :=
  p.ram_count.val ≤ MemoryPlan.MAX_BANKS ∧ p.managed_count.val ≤ MemoryPlan.MAX_BANKS ∧
    p.boot_count.val ≤ p.reserved_count.val ∧
    p.reserved_count.val ≤ MemoryPlan.MAX_BOOT_SPANS + MemoryPlan.MAX_FIRMWARE ∧
    P = ⟨(p.ram.val.take p.ram_count.val).map spanOf,
      (p.managed.val.take p.managed_count.val).map spanOf,
      (p.reserved.val.take p.boot_count.val).map spanOf,
      ((p.reserved.val.take p.reserved_count.val).drop p.boot_count.val).map spanOf⟩

/-! ## Trees and nodes -/

/-- The offsets of the begin-node tokens of a structure block `str`, whose
property names lie in the strings block `strs`, from the token at `cursor`
on: the tokens as `decodeToken` reads them, at most `fuel` of them, up to the
end token or the first token that it refuses. For the blocks of a tree that
the parse accepted, from the offset 0 with the fuel `MAX_TOKENS`, these are
the offsets at which the nodes of `Fdt.records` begin, in their order. -/
def beginOffsets (str strs : ByteArray) : (fuel cursor : Nat) → List Nat
  | 0, _ => []
  | fuel + 1, cursor =>
    match decodeToken str strs cursor with
    | .ok (.beginNode _, next) => cursor :: beginOffsets str strs fuel next
    | .ok (.endStructure, _) => []
    | .ok (_, next) => beginOffsets str strs fuel next
    | .error _ => []

/-- A tree of the code stands for the tree `T` of the specification: its
bytes are a tree that `Fdt.parse` takes to `T`, and its views are the
first `totalsize` bytes, the structure block and the strings block that the
header of those bytes places, and the entries of the reservation map before
its terminator. This is the premise of the proof path that a tree is one
that `Fdt::parse` returned from its bytes. -/
def FdtRepr (t : fdt.Fdt) (T : Fdt) : Prop :=
  Fdt.parse (bytesOf t.blob) = .ok T ∧
    ∃ h, header (bytesOf t.blob) = .ok h ∧ h.blob = bytesOf t.blob ∧
      bytesOf t.structure = h.structure_ ∧ bytesOf t.strings = h.strings ∧
      bytesOf t.reservations =
        h.blob.extract h.layout.reserveStart (h.layout.reserveStart + 16 * T.reservations.length)

/-- The offsets of the begin-node tokens of the structure block of a tree of
the code. -/
def offsetsOf (t : fdt.Fdt) : List Nat :=
  beginOffsets (bytesOf t.structure) (bytesOf t.strings) MAX_TOKENS.toNat 0

/-- A node of the code stands for the node `N` of the specification: its
tree stands for the tree of `N`, and it is the begin-node token of the index
of `N` in the order of the structure block, with its name after the tag,
its NUL at the end of the name, its properties at the next multiple of 4
after the NUL, and its parent the begin-node token of the parent of `N`, none
for the root. This is the premise of the proof path that a node is one of its
tree. -/
def NodeRepr (n : fdt.Node) (N : Node) : Prop :=
  FdtRepr n.tree N.fdt ∧
    (offsetsOf n.tree)[N.index.val]? = some n.at.offset.val ∧
    n.at.name_start.val = n.at.offset.val + 4 ∧
    n.at.name_end.val = n.at.name_start.val + N.name.utf8ByteSize ∧
    n.at.properties.val = align4 (n.at.name_end.val + 1) ∧
    n.at.parent.map (·.val) = N.record.parent.bind ((offsetsOf n.tree)[·]?)

/-- The premise on a `&str` argument: `core::str::{str}::as_bytes` returns the
bytes of the UTF-8 encoding of the string `s` of the specification. The
translation keeps the function as a declaration without a body, so a
statement about a function that reads a `&str` through it holds for every
interpretation of the declaration that meets this premise, as the function
of Rust does: it returns the bytes of the string, which are UTF-8. -/
def StrRepr (p : Str) (s : String) : Prop :=
  core.str.Str.as_bytes p ⦃ b => bytesOf b = s.toUTF8 ⦄

/-! ## Checked values -/

/-- An address map of the code stands for the address map that
`AddressMap.new` gives for its value, none when the property is absent, and
its cells. -/
def AddressMapRepr (m : fdt.AddressMap) (M : AddressMap) : Prop :=
  AddressMap.new (if m.present then some (bytesOf m.bytes) else none) (word32 m.child_cells)
    (word32 m.parent_cells) (word32 m.size_cells) = .ok M

/-- A `Reg` of the code stands for the list of entries that its calls of
`next` give. -/
def RegRepr (r : fdt.Reg) (l : List Span) : Prop :=
  Stands fdt.translation.Reg.next SpanRepr r l

end Krepi.Statements.Fdt
