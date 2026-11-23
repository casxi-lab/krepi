module

/-!
# Device tree: limits, errors and spans

The values that every part of the specification of the `fdt` component
shares, as its contract (`docs/domains/boot-platform/fdt/contract.md`) states
them:

- the eight limits of the entry table, with the values of `Format and bounds`;
- the two error types of `Rejection and error priority`, `Error` with 21
  variants and `PlanError` with 7;
- the value type `Span` with `Span::new`, `end` and `contains`, and the
  checked addition that stands for the contract's "leaves 64 bits".

Machine widths are explicit where a value crosses an entry: addresses and
sizes are `UInt64`, cells and header words `UInt32`, bytes `UInt8`. Inside a
definition, arithmetic is on `Nat`, and every sum that the contract checks
against 64 bits is compared with `2 ^ 64` explicitly (`checkedAdd`), so that
no result wraps.
-/

@[expose] public section

namespace Krepi.Spec.Fdt

/-! ## Limits -/

/-- `MAX_BLOB_SIZE`: the largest `totalsize` that the parse accepts, 2 MiB. -/
def MAX_BLOB_SIZE : UInt64 := 0x20_0000

/-- `MAX_DEPTH`: the most nodes on a path from the root, the root included, so
no node lies deeper than 31. -/
def MAX_DEPTH : UInt64 := 32

/-- `MAX_TOKENS`: the most tokens of the structure block that the parse reads,
the end token included. -/
def MAX_TOKENS : UInt64 := 65536

/-- `MAX_PROPERTIES`: the most properties of one node. -/
def MAX_PROPERTIES : UInt64 := 512

/-- `MAX_PROPERTY_NAME`: the most bytes of a property name, its NUL not
counted. -/
def MAX_PROPERTY_NAME : UInt64 := 64

/-- `MAX_RESERVATIONS`: the most entries of the reservation map before its
terminator. -/
def MAX_RESERVATIONS : UInt64 := 128

/-- `MAX_MEMORY_REGIONS`: the most RAM ranges of a memory discovery. -/
def MAX_MEMORY_REGIONS : UInt64 := 32

/-- `MAX_RESERVED_REGIONS`: the most reserved regions of a memory discovery,
the entries of the reservation map and the spans of `/reserved-memory`
together. -/
def MAX_RESERVED_REGIONS : UInt64 := 128

/-! ## Errors -/

/-- `Error`: the 21 errors of the parse, the node access, the translation, the
memory discovery, the CPU nodes and the boot memory, in the order of the
error table of the contract. -/
inductive Error where
  | truncated
  | badMagic
  | unsupportedVersion
  | badLayout
  | badAlignment
  | badToken
  | badTree
  | badString
  | badPadding
  | duplicateProperty
  | limitExceeded
  | unsupportedCells
  | badProperty
  | missingProperty
  | overflow
  | emptyRegion
  | overlap
  | unmapped
  | ambiguousMapping
  | badPath
  | noMemory
  deriving DecidableEq, Repr, Inhabited

/-- The name of a variant of `Error` as the contract writes it. -/
def Error.name : Error → String
  | .truncated => "Truncated"
  | .badMagic => "BadMagic"
  | .unsupportedVersion => "UnsupportedVersion"
  | .badLayout => "BadLayout"
  | .badAlignment => "BadAlignment"
  | .badToken => "BadToken"
  | .badTree => "BadTree"
  | .badString => "BadString"
  | .badPadding => "BadPadding"
  | .duplicateProperty => "DuplicateProperty"
  | .limitExceeded => "LimitExceeded"
  | .unsupportedCells => "UnsupportedCells"
  | .badProperty => "BadProperty"
  | .missingProperty => "MissingProperty"
  | .overflow => "Overflow"
  | .emptyRegion => "EmptyRegion"
  | .overlap => "Overlap"
  | .unmapped => "Unmapped"
  | .ambiguousMapping => "AmbiguousMapping"
  | .badPath => "BadPath"
  | .noMemory => "NoMemory"

/-- `PlanError`: the 7 errors of the boot memory map, in the order of the error
table of the contract. -/
inductive PlanError where
  | invalidRange
  | overflow
  | alignment
  | capacity
  | overlap
  | outsideRam
  | arenaTooLarge
  deriving DecidableEq, Repr, Inhabited

/-- The name of a variant of `PlanError` as the contract writes it. -/
def PlanError.name : PlanError → String
  | .invalidRange => "InvalidRange"
  | .overflow => "Overflow"
  | .alignment => "Alignment"
  | .capacity => "Capacity"
  | .overlap => "Overlap"
  | .outsideRam => "OutsideRam"
  | .arenaTooLarge => "ArenaTooLarge"

/-! ## Checked arithmetic -/

/-- The sum `a + b` when it fits in 64 bits, and `Overflow` when it does not:
the contract's rule that an offset, span or sum "leaves 64 bits" is this
comparison with `2 ^ 64`. -/
def checkedAdd (a b : Nat) : Except Error Nat :=
  if a + b < 2 ^ 64 then .ok (a + b) else .error .overflow

/-! ## Spans -/

/-- `Span`: the addresses `[start, start + size)`. The type has no invariant,
since the entries take spans whose end leaves 64 bits as input and reject them
with `Overflow`; `Span.Valid` is the condition of the contract's term. -/
structure Span where
  start : UInt64
  size : UInt64
  deriving DecidableEq, Repr, Inhabited

/-- The end `start + size` of a span, exact, without a bound. -/
def Span.endNat (s : Span) : Nat := s.start.toNat + s.size.toNat

/-- The contract's span: `start + size` fits in 64 bits. -/
def Span.Valid (s : Span) : Prop := s.endNat < 2 ^ 64

instance (s : Span) : Decidable s.Valid := inferInstanceAs (Decidable (_ < _))

/-- `Span::new(start, size)`: the span, or `Overflow` when its end leaves
64 bits. An empty span is a span; the entries that refuse one say so. -/
def Span.new (start size : UInt64) : Except Error Span :=
  if start.toNat + size.toNat < 2 ^ 64 then .ok ⟨start, size⟩ else .error .overflow

/-- `Span::end`: the end `start + size`, or `Overflow` when it leaves 64 bits.
-/
def Span.endAddr (s : Span) : Except Error UInt64 :=
  if s.Valid then .ok (s.start + s.size) else .error .overflow

/-- Whether `inner` lies inside `outer`, as address sets of the exact ends. -/
def Span.holds (outer inner : Span) : Bool :=
  outer.start.toNat ≤ inner.start.toNat && inner.endNat ≤ outer.endNat

/-- `Span::contains(other)`: `Overflow` when `other` and then the span itself
end beyond 64 bits; otherwise whether `other` lies inside the span. -/
def Span.contains (s other : Span) : Except Error Bool :=
  if ¬ other.Valid then .error .overflow
  else if ¬ s.Valid then .error .overflow
  else .ok (s.holds other)

/-- Whether each of two spans starts before the other ends, compared at their
exact ends: for two nonempty spans, whether they share an address. -/
def Span.overlaps (a b : Span) : Bool :=
  a.start.toNat < b.endNat && b.start.toNat < a.endNat

end Krepi.Spec.Fdt
