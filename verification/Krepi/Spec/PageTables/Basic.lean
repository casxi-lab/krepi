module

/-!
# Page tables: sizes, regions, errors and physical ranges

The values that every part of the specification of the `page-tables`
component shares, as its contract (`docs/domains/memory/page-tables/contract.md`)
states them:

- the sizes of a page, a block, the slot of a root entry and a table, and the
  indices of a virtual address at the three levels of a walk (`Terms`);
- the two regions of the 39-bit virtual address space, with `DIRECT_BASE`,
  and the physical widths 32 to 48 (`Terms`, `Kernel direct map`);
- the seven errors of table sets (`Errors of table sets`) and the twelve errors
  of the page ownership table (`Page ownership`), each in the order of its
  table;
- the value type `PhysRange` with `PhysRange::new`, `end`, `contains` and
  `overlaps` (`Terms`).

Machine widths are explicit where a value crosses an entry: addresses,
lengths, descriptors and `base` are `UInt64`, and the physical width `bits` is
`UInt8`, as the prototype takes it, which the contract follows for the
arguments of the entries (`Table pool`). Inside a definition arithmetic is on
`Nat`, which does not wrap, and every rule that compares with a power of two
compares the exact value.
-/

@[expose] public section

namespace Krepi.Spec.PageTables

/-! ## Sizes and indices -/

/-- A page, 4 KiB. -/
def PAGE_SIZE : Nat := 0x1000

/-- A block, the span of a level 2 entry, 2 MiB. -/
def BLOCK_SIZE : Nat := 0x20_0000

/-- The span of a root entry, 1 GiB. -/
def GIB_SIZE : Nat := 0x4000_0000

/-- The descriptors of a table, 512 of 64 bits. -/
def ENTRIES : Nat := 512

/-- The index of a virtual address at level 1, the root: its bits 30 to 38. -/
def index1 (v : UInt64) : Nat := v.toNat / GIB_SIZE % ENTRIES

/-- The index of a virtual address at level 2: its bits 21 to 29. -/
def index2 (v : UInt64) : Nat := v.toNat / BLOCK_SIZE % ENTRIES

/-- The index of a virtual address at level 3: its bits 12 to 20. -/
def index3 (v : UInt64) : Nat := v.toNat / PAGE_SIZE % ENTRIES

/-- $\mathrm{blk}(v)$: a virtual address rounded down to 2 MiB. -/
def blk (v : UInt64) : UInt64 := UInt64.ofNat (v.toNat / BLOCK_SIZE * BLOCK_SIZE)

/-- $\mathrm{gib}(v)$: a virtual address rounded down to 1 GiB. -/
def gib (v : UInt64) : UInt64 := UInt64.ofNat (v.toNat / GIB_SIZE * GIB_SIZE)

/-! ## Regions and widths -/

/-- The end of the lower region and the size of the direct map's window,
$2^{39}$. -/
def VA_LIMIT : Nat := 2 ^ 39

/-- `DIRECT_BASE`: the start of the upper region, $2^{64} - 2^{39}$, the
complement of $2^{39} - 1$. -/
def DIRECT_BASE : UInt64 := 0xffff_ff80_0000_0000

/-- A region of the EL1&0 regime: the lower region, the addresses below
$2^{39}$, which `TTBR0_EL1` translates, and the upper region, the addresses at
or above `DIRECT_BASE`, which `TTBR1_EL1` translates. -/
inductive Region where
  | lower
  | upper
  deriving DecidableEq, Repr, Inhabited

/-- The name of a region as the contract writes it. -/
def Region.name : Region → String
  | .lower => "lower"
  | .upper => "upper"

/-- Whether a virtual address lies in a region. No address lies in both, and
the addresses from $2^{39}$ up to `DIRECT_BASE` lie in neither. -/
def Region.holds : Region → UInt64 → Bool
  | .lower, v => v.toNat < VA_LIMIT
  | .upper, v => DIRECT_BASE.toNat ≤ v.toNat

/-- The smallest physical width, 32. -/
def MIN_BITS : Nat := 32

/-- The largest physical width, 48. -/
def MAX_BITS : Nat := 48

/-- Whether `bits` is a physical width, 32 to 48. -/
def widthOk (bits : UInt8) : Bool := MIN_BITS ≤ bits.toNat && bits.toNat ≤ MAX_BITS

/-! ## Errors -/

/-- The seven errors of table sets, in the order of the table of
`Errors of table sets`. -/
inductive TableError where
  | alignment
  | addressWidth
  | tableBacking
  | outOfTables
  | alreadyMapped
  | notMapped
  | invalidDescriptor
  deriving DecidableEq, Repr, Inhabited

/-- The name of a variant of `TableError` as the contract writes it. -/
def TableError.name : TableError → String
  | .alignment => "Alignment"
  | .addressWidth => "AddressWidth"
  | .tableBacking => "TableBacking"
  | .outOfTables => "OutOfTables"
  | .alreadyMapped => "AlreadyMapped"
  | .notMapped => "NotMapped"
  | .invalidDescriptor => "InvalidDescriptor"

/-- The twelve errors of the page ownership table and of physical ranges, in
the order of the error table of `Page ownership`. -/
inductive OwnershipError where
  | invalidRange
  | addressOverflow
  | invalidAlignment
  | invalidSize
  | invalidArena
  | metadataExhausted
  | outOfMemory
  | generationExhausted
  | zeroFailed
  | wrongArena
  | wrongOwner
  | invalidAllocation
  deriving DecidableEq, Repr, Inhabited

/-- The name of a variant of `OwnershipError` as the contract writes it. -/
def OwnershipError.name : OwnershipError → String
  | .invalidRange => "InvalidRange"
  | .addressOverflow => "AddressOverflow"
  | .invalidAlignment => "InvalidAlignment"
  | .invalidSize => "InvalidSize"
  | .invalidArena => "InvalidArena"
  | .metadataExhausted => "MetadataExhausted"
  | .outOfMemory => "OutOfMemory"
  | .generationExhausted => "GenerationExhausted"
  | .zeroFailed => "ZeroFailed"
  | .wrongArena => "WrongArena"
  | .wrongOwner => "WrongOwner"
  | .invalidAllocation => "InvalidAllocation"

/-! ## Physical ranges -/

/-- `page_tables::PhysRange`: the physical addresses `[start, start + len)`.
The term of the contract is the type's invariant: the range is nonempty and
its end fits in 64 bits, so its last byte is at most $2^{64} - 2$ and no range
ends past $2^{64} - 1$. `PhysRange::new` is the only way to build one from
two numbers. -/
structure PhysRange where
  start : UInt64
  len : UInt64
  nonempty : len ≠ 0
  fits : start.toNat + len.toNat < 2 ^ 64
  deriving DecidableEq

/-- The exclusive end `start + len` of a range, exact. -/
def PhysRange.endNat (r : PhysRange) : Nat := r.start.toNat + r.len.toNat

/-- `PhysRange::new(start, len)`: the range, or the error of its first broken
rule: a length of 0, `InvalidRange`; an end that does not fit in 64 bits,
`AddressOverflow`. A range of length 0 has the end `start`, which fits, so the
order of the two rules is not observable. -/
def PhysRange.new (start len : UInt64) : Except OwnershipError PhysRange :=
  if h : len = 0 then .error .invalidRange
  else if h' : start.toNat + len.toNat < 2 ^ 64 then .ok ⟨start, len, h, h'⟩
  else .error .addressOverflow

/-- `PhysRange::end`: the exclusive end `start + len`, which fits in 64 bits.
-/
def PhysRange.endAddr (r : PhysRange) : UInt64 := UInt64.ofNat r.endNat

/-- `PhysRange::contains(other)`: every address of `other` lies in the range.
-/
def PhysRange.contains (r other : PhysRange) : Bool :=
  r.start.toNat ≤ other.start.toNat && other.endNat ≤ r.endNat

/-- `PhysRange::overlaps(other)`: the two ranges share an address. Both are
nonempty, so they do when each starts before the other ends. -/
def PhysRange.overlaps (r other : PhysRange) : Bool :=
  r.start.toNat < other.endNat && other.start.toNat < r.endNat

end Krepi.Spec.PageTables
