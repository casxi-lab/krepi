module

public import Krepi.Spec.Fdt.Discovery

/-!
# Device tree: the Pi 5 boot memory

`Fdt::discover_pi5_boot_memory` of the contract's `Memory discovery`, which
checks the hand-over tree of a Raspberry Pi 5 against the spans that the board
gives for the tree and for the image, and the two queries of its result,
`Pi5BootMemory::is_available` and `find_available`, with steps 5 and 8 of the
error order of the parse and the entries on a tree.

A `Pi5BootMemory` knows the memory map of the tree, the span of the tree, the
span of the image with its BSS and stacks, and the sum of the RAM ranges. Its
queries exclude only the tree, the image and the reserved regions: boot
storage beyond them, such as a boot bundle that the board gives as a span of
its own, is excluded by the boot memory map alone. A query describes memory;
it grants no ownership.

The selection is a bounded search: the RAM ranges in tree order, and in each
range at most `Q + 3` candidates, where `Q` is the number of reserved regions,
each compared with the image, the tree and the regions. Each candidate after
the first lies past the end of every span that the one before it touched, so
it touches none of them again, and the bound is never reached.
-/

@[expose] public section

namespace Krepi.Spec.Fdt

/-! ## The value -/

/-- `Pi5BootMemory`, the result of `Fdt::discover_pi5_boot_memory`: the memory
map of the tree, the span of the tree (`Pi5BootMemory::dtb`), the span of the
image (`Pi5BootMemory::image`) and the sum of the RAM ranges
(`Pi5BootMemory::ram_bytes`). -/
structure Pi5BootMemory where
  memory : MemoryMap
  dtb : Span
  image : Span
  ramBytes : UInt64
  deriving DecidableEq, Repr, Inhabited

/-- `Pi5BootMemory::ram`: the RAM ranges of the memory map. -/
def Pi5BootMemory.ram (m : Pi5BootMemory) : List Span := m.memory.ram

/-- `Pi5BootMemory::reserved`: the reserved regions of the memory map. -/
def Pi5BootMemory.reserved (m : Pi5BootMemory) : List ReservedRegion := m.memory.reserved

/-- `Pi5BootMemory::dynamic`: the number of dynamic reservations of the memory
map. -/
def Pi5BootMemory.dynamic (m : Pi5BootMemory) : UInt64 := m.memory.dynamic

/-! ## The root `compatible` -/

/-- The pieces of a byte string between its NUL bytes. -/
def splitAtNul : List UInt8 → List (List UInt8)
  | [] => [[]]
  | b :: rest =>
    match splitAtNul rest with
    | [] => [[b]]
    | w :: ws => if b == 0 then [] :: w :: ws else (b :: w) :: ws

/-- The entries of a `compatible` value after its final NUL was removed, in
order: an entry that is not UTF-8, `BadString`, then an empty one,
`BadProperty`. -/
def compatibleEntries : List (List UInt8) → Except Error (List String)
  | [] => .ok []
  | e :: rest =>
    match String.fromUTF8? (ByteArray.mk e.toArray) with
    | none => .error .badString
    | some s => if s.isEmpty then .error .badProperty else do
      let more ← compatibleEntries rest
      pure (s :: more)

/-- The root `compatible` of a Pi 5 hand-over tree: a value that does not end
with a NUL, `BadProperty`; then each entry in order (`compatibleEntries`);
then a list without `raspberrypi,5-model-b` or without `brcm,bcm2712`,
`BadProperty`. -/
def checkPi5Compatible (value : ByteArray) : Except Error Unit := do
  let bytes := value.toList
  if bytes.getLast? != some 0 then throw .badProperty
  let entries ← compatibleEntries (splitAtNul bytes.dropLast)
  if !(entries.contains "raspberrypi,5-model-b" && entries.contains "brcm,bcm2712") then
    throw .badProperty

/-! ## The discovery -/

/-- `Fdt::discover_pi5_boot_memory(dtb_address, image)`: the Pi 5 boot memory
of the tree, or the error of the first broken rule of step 5 of the error
order. `totalsize` above `PI5_MAX_BLOB_SIZE`, `LimitExceeded`; the address of
the tree not a multiple of 8, `BadAlignment`; the root, and a tree without one,
which the parse never builds, `BadTree`; the address cells of the root, a value
that is not 4 bytes `BadProperty`, then a number other than 2
`UnsupportedCells`, and then its size cells in the same way; the root
`compatible`: absent, `MissingProperty`, then `checkPi5Compatible`; the span of
the tree, `Overflow`; the image, `EmptyRegion` then `Overflow`; the image
sharing an address with the tree, `Overlap`; `Fdt::discover_memory`, with its
errors; the tree, then the image, outside every single RAM range, `Unmapped`;
the sum of the RAM ranges, `Overflow`. -/
def Fdt.discoverPi5BootMemory (t : Fdt) (dtbAddress : UInt64) (image : Span) :
    Except Error Pi5BootMemory := do
  if PI5_MAX_BLOB_SIZE < t.totalSize then throw .limitExceeded
  if dtbAddress % 8 != 0 then throw .badAlignment
  let some root ← t.findNode "/" | throw .badTree
  if (← root.addressCells) != 2 then throw .unsupportedCells
  if (← root.sizeCells) != 2 then throw .unsupportedCells
  let some compatible := root.property "compatible" | throw .missingProperty
  checkPi5Compatible compatible
  let dtb ← Span.new dtbAddress t.totalSize
  if image.size = 0 then throw .emptyRegion
  let _ ← image.endAddr
  if image.touches dtb then throw .overlap
  let memory ← t.discoverMemory
  if !inOneRange memory.ram dtb then throw .unmapped
  if !inOneRange memory.ram image then throw .unmapped
  let ramBytes ← memory.ram.foldlM (fun sum s => checkedAdd sum s.size.toNat) 0
  pure { memory, dtb, image, ramBytes := UInt64.ofNat ramBytes }

/-! ## Availability -/

/-- The spans that a query of the Pi 5 boot memory excludes: the image, the
tree and every reserved region, `reusable` ones included. -/
def Pi5BootMemory.exclusions (m : Pi5BootMemory) : List Span :=
  m.image :: m.dtb :: m.reserved.map (·.span)

/-- `Pi5BootMemory::is_available(span)`: a span of size 0, `EmptyRegion`; then
one whose end leaves 64 bits, `Overflow`; otherwise whether it lies inside one
RAM range and touches neither the tree, nor the image, nor any reserved
region. -/
def Pi5BootMemory.isAvailable (m : Pi5BootMemory) (s : Span) : Except Error Bool :=
  if s.size = 0 then .error .emptyRegion
  else if ¬ s.Valid then .error .overflow
  else .ok (inOneRange m.ram s && !m.exclusions.any (·.touches s))

/-! ## Selection -/

/-- Whether `alignment` is a power of two: one of `2 ^ 0`, ..., `2 ^ 63`. -/
def isPowerOfTwo (alignment : UInt64) : Bool :=
  (List.range 64).any fun k => alignment.toNat == 2 ^ k

/-- The least multiple of `alignment` that is at least `address`, or
`Overflow` when it leaves 64 bits. -/
def alignUp (address alignment : Nat) : Except Error Nat :=
  let aligned := (address + alignment - 1) / alignment * alignment
  if aligned < 2 ^ 64 then .ok aligned else .error .overflow

/-- The candidates of one RAM range from the aligned address `start`, with the
end `bound`, the lesser of the end of the range and the limit, trying at most
`fuel` more. A candidate whose end leaves 64 bits or lies past `bound` ends
the search in this range with none. A candidate that touches no exclusion is
the span. Otherwise the next candidate starts at the end of the furthest
exclusion that it touches, aligned up (`alignUp`, which fails with
`Overflow`): every start before that end touches that exclusion too. Out of
fuel, `LimitExceeded`, which `findAvailable` never reaches: each candidate
after the first lies past every exclusion that an earlier one touched. -/
def Pi5BootMemory.searchRange (m : Pi5BootMemory) (size alignment bound : Nat) :
    (fuel start : Nat) → Except Error (Option Span)
  | 0, _ => .error .limitExceeded
  | fuel + 1, start =>
    if 2 ^ 64 ≤ start + size || bound < start + size then .ok none
    else
      let candidate : Span := ⟨UInt64.ofNat start, UInt64.ofNat size⟩
      let touched := m.exclusions.filter (·.touches candidate)
      if touched.isEmpty then .ok (some candidate)
      else do
        let next ← alignUp (touched.foldl (fun e s => max e s.endNat) 0) alignment
        m.searchRange size alignment bound fuel next

/-- The search through the RAM ranges `ranges`, in order: in each, the first
candidate is the greater of the start of the range and `minimum`, aligned up
(`alignUp`, which fails with `Overflow`), and the search tries at most
`Q + 3` candidates; the first range that has a span gives it. -/
def Pi5BootMemory.searchRanges (m : Pi5BootMemory) (size alignment minimum limit : Nat) :
    List Span → Except Error (Option Span)
  | [] => .ok none
  | r :: rest => do
    let start ← alignUp (max r.start.toNat minimum) alignment
    match ← m.searchRange size alignment (min r.endNat limit) (m.reserved.length + 3) start with
    | some s => pure (some s)
    | none => m.searchRanges size alignment minimum limit rest

/-- `Pi5BootMemory::find_available(size, alignment, minimum, limit)`: a size
of 0 or an empty bound, `minimum` at or above `limit`, `EmptyRegion`; an
alignment that is not a power of two, `BadAlignment`; then the search, whose
alignments fail with `Overflow`. The span has `size` bytes, starts at a
multiple of `alignment`, lies within `[minimum, limit)` and inside one RAM
range, and touches neither the image, nor the tree, nor any reserved region;
it is the one with the lowest start in the first RAM range, in tree order,
that has one, and none when no range has one. -/
def Pi5BootMemory.findAvailable (m : Pi5BootMemory) (size alignment minimum limit : UInt64) :
    Except Error (Option Span) := do
  if size = 0 || limit ≤ minimum then throw .emptyRegion
  if !isPowerOfTwo alignment then throw .badAlignment
  m.searchRanges size.toNat alignment.toNat minimum.toNat limit.toNat m.ram

end Krepi.Spec.Fdt
