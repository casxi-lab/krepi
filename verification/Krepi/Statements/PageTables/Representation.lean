module

public import KrepiGen.PageTables.Funs
public import Krepi.Statements.Basic
public import Krepi.Spec.PageTables.Tokens

/-!
# Page tables: the representation of the values of the code

How a value of the code of the `page-tables` component, as Aeneas
translates it into `KrepiGen.PageTables`, stands for a value of its
specification, `Krepi.Spec.PageTables`. The refinement statements of the
component relate each function to its specification through these
relations, and take them, with the premises of the proof path
(`docs/domains/memory/page-tables/proof.md`), as the hypotheses on their
arguments.

- The errors, the kinds, the steps, the owners and the counter are
  enumerations: each stands for the value of the same name.
- A set of tables stands for the set of the specification of its region,
  `lower` for `UPPER` false and `upper` for `UPPER` true, with its pool and
  its record of the tables in use. A write plan stands for its steps:
  `Zero(0)` to `Zero(zero_tables - 1)`, then the first `len` of its steps.
- A physical range stands for the range of the specification with its start
  and length, which exists only for a range that keeps the invariant of the
  type: a length that is not 0 and an end that fits in 64 bits. The values
  that hold ranges, a layout, an extent, an exclusion, a receipt, a
  reservation, a packet, a choice and a placement, stand for the values of
  the specification whose ranges their ranges stand for.
- A page ownership table holds arrays with a count of the entries in use:
  it stands for the table whose lists are the first `count` entries, with
  each count within its array.
- The boot memory map that `direct_map` reads is a value of the code of the
  `fdt` component, as this target's translation holds it: it stands for the
  boot memory map of `Krepi.Spec.Fdt`, as the representation of the `fdt`
  target states it over that target's own translation.
- A plan iterator stands for the list of steps that its calls of `next`
  give (`Krepi.Statements.Stands`).
-/

@[expose] public section

open Aeneas
open Aeneas.Std (Slice U8 U64 Usize)
open KrepiGen.PageTables
open Krepi.Spec.PageTables

namespace Krepi.Statements.PageTables

/-! ## Enumerations -/

/-- An error of a table set of the code as the error of the specification of
the same name. -/
def tableErrorOf : page_tables.TableError → TableError
  | .Alignment => .alignment
  | .AddressWidth => .addressWidth
  | .TableBacking => .tableBacking
  | .OutOfTables => .outOfTables
  | .AlreadyMapped => .alreadyMapped
  | .NotMapped => .notMapped
  | .InvalidDescriptor => .invalidDescriptor

/-- An error of the page ownership table of the code as the error of the
specification of the same name. -/
def ownershipErrorOf : page_tables.OwnershipError → OwnershipError
  | .InvalidRange => .invalidRange
  | .AddressOverflow => .addressOverflow
  | .InvalidAlignment => .invalidAlignment
  | .InvalidSize => .invalidSize
  | .InvalidArena => .invalidArena
  | .MetadataExhausted => .metadataExhausted
  | .OutOfMemory => .outOfMemory
  | .GenerationExhausted => .generationExhausted
  | .ZeroFailed => .zeroFailed
  | .WrongArena => .wrongArena
  | .WrongOwner => .wrongOwner
  | .InvalidAllocation => .invalidAllocation

/-- A kind of the code as the kind of the specification of the same name. -/
def kindOf : page_tables.Kind → Kind
  | .ReadExecute => .readExecute
  | .ReadOnly => .readOnly
  | .ReadWrite => .readWrite
  | .KernelPrivateReadWrite => .kernelPrivateReadWrite
  | .Device => .device
  | .UserReadExecute => .userReadExecute
  | .UserReadOnly => .userReadOnly
  | .UserReadWrite => .userReadWrite
  | .UserDevice => .userDevice

/-- A kind of a layout of the code as the kind of the specification of the
same name. -/
def layoutKindOf : page_tables.LayoutKind → Kind
  | .ReadExecute => .readExecute
  | .ReadOnly => .readOnly
  | .ReadWrite => .readWrite
  | .Device => .device

/-- The region of a set of the code: the upper region when `UPPER` is true. -/
def regionOf (upper : Bool) : Region := cond upper .upper .lower

/-- A step of the code as the step of the specification. -/
def stepOf : page_tables.Step → Step
  | .Zero t => .zero t.val
  | .Store t i d => .store t.val i.val (word64 d)
  | .Fence => .fence
  | .Sync => .sync
  | .Invalidate v => .invalidate (word64 v)

/-- A step of the code stands for its step of the specification. -/
def StepRepr (s : page_tables.Step) (t : Step) : Prop := stepOf s = t

/-- A state of a holder of the code as that of the specification. -/
def holdStateOf : page_tables.HoldState → HoldState
  | .Reserved => .reserved
  | .Published => .published

/-- An owner of an exclusion of the code as that of the specification. -/
def excluderOf : page_tables.Excluder → Excluder
  | .Firmware => .firmware
  | .Image => .image
  | .BootStorage => .bootStorage

/-- A holding of the code as that of the specification. -/
def holdingOf : page_tables.Holding → Holding
  | .Free => .free
  | .Held o n s => .held (word64 o) (word64 n) (holdStateOf s)

/-- An owner of a page of the code as that of the specification. -/
def ownerOf : page_tables.Owner → Owner
  | .Free => .free
  | .Excluded x => .excluded (excluderOf x)
  | .Held o n s => .held (word64 o) (word64 n) (holdStateOf s)

/-- The generation counter of the code as that of the specification. -/
def counterOf : page_tables.Counter → Counter
  | .Next g => .next (word64 g)
  | .Exhausted => .exhausted

/-- A direction of a placement of the code as that of the specification. -/
def directionOf : page_tables.Direction → Direction
  | .Low => .low
  | .High => .high

/-! ## Table sets and plans -/

/-- The pool of a set of the code: its `N` tables of 512 descriptors each. -/
def poolOf {N : Usize} (pool : Aeneas.Std.Array (Aeneas.Std.Array U64 512#usize) N) : Pool N.val :=
  Vector.ofFn fun t => Vector.ofFn fun i =>
    word64 ((pool.val[t.val]?.bind fun table => table.val[i.val]?).getD 0#u64)

/-- A set of tables of the code as the set of the specification of its
region and capacity, with its pool and its record of the tables in use. -/
def tablesOf {N : Usize} {upper : Bool} (s : page_tables.Tables N upper) :
    Tables (regionOf upper) N.val :=
  ⟨poolOf s.pool, s.used.val⟩

/-- The steps of a write plan of the code: `Zero(0)` to
`Zero(zero_tables - 1)`, then the first `len` of its steps. -/
def planOf (p : page_tables.WritePlan) : Plan :=
  (List.range p.zero_tables.val).map Step.zero ++ (p.steps.val.take p.len.val).map stepOf

/-- A write plan of the code stands for the plan of the specification of its
steps, with `len` within its array of steps. -/
def WritePlanRepr (p : page_tables.WritePlan) (P : Plan) : Prop :=
  p.len.val ≤ p.steps.val.length ∧ planOf p = P

/-! ## Ranges and the values that hold them -/

/-- A physical range of the code stands for the range of the specification
with its start and length. -/
def PhysRangeRepr (r : page_tables.PhysRange) (R : PhysRange) : Prop :=
  R.start = word64 r.start ∧ R.len = word64 r.len

/-- A range of a layout of the code stands for that of the specification
with its range and kind. -/
def LayoutRangeRepr (r : page_tables.LayoutRange) (R : LayoutRange) : Prop :=
  PhysRangeRepr r.range R.range ∧ R.kind = layoutKindOf r.kind

/-- A layout of the code stands for the layout of the specification whose
ranges are the first `count` of its ranges, with `count` within its array,
and whose guard pages are its guard addresses. -/
def LayoutRepr (l : page_tables.Layout) (L : Layout) : Prop :=
  l.count.val ≤ MAX_LAYOUT_RANGES ∧ ListRel LayoutRangeRepr (l.ranges.val.take l.count.val) L.ranges ∧
    L.guards = l.guards.val.map word64

/-- An extent of the code stands for that of the specification. -/
def ExtentRepr (e : page_tables.Extent) (E : Extent) : Prop :=
  PhysRangeRepr e.range E.range ∧ E.bank = e.bank.val ∧ E.holding = holdingOf e.holding

/-- An exclusion of the code stands for that of the specification. -/
def ExclusionRepr (x : page_tables.Exclusion) (X : Exclusion) : Prop :=
  PhysRangeRepr x.range X.range ∧ X.owner = excluderOf x.owner

/-- A receipt of the code stands for that of the specification. -/
def AllocationRepr (a : page_tables.Allocation) (A : Allocation) : Prop :=
  A.arena = word64 a.arena ∧ A.owner = word64 a.owner ∧ A.generation = word64 a.generation ∧
    PhysRangeRepr a.range A.range

/-- A reservation of the code stands for that of the specification. -/
def ReservationRepr (r : page_tables.Reservation) (R : Reservation) : Prop :=
  AllocationRepr r.allocation R.allocation ∧ R.attempted = r.attempted ∧
    R.failures = word64 r.failures

/-- A packet of the code stands for that of the specification. -/
def InitializedRepr (x : page_tables.Initialized) (X : Initialized) : Prop :=
  AllocationRepr x.allocation X.allocation ∧ X.failures = word64 x.failures

/-- A choice of the code stands for that of the specification. -/
def ChoiceRepr (c : page_tables.Choice) (C : Choice) : Prop :=
  C.owner = word64 c.owner ∧ PhysRangeRepr c.range C.range

/-- A placement of the code stands for that of the specification. -/
def PlacementRepr (p : page_tables.Placement) (P : Placement) : Prop :=
  P.direction = directionOf p.direction ∧ OptionRel PhysRangeRepr p.window P.window

/-- The statistics of the code stand for those of the specification. -/
def StatsRepr (s : page_tables.Stats) (S : Stats) : Prop :=
  S.managed = s.managed.val ∧ S.free = s.free.val ∧ S.allocated = s.allocated.val ∧
    S.allocations = s.allocations.val ∧ S.freeExtents = s.free_extents.val ∧
    S.largestFree = s.largest_free.val ∧ S.extents = s.extents.val ∧ S.capacity = s.capacity.val

/-- A page ownership table of the code stands for the table of the
specification of its capacities whose banks, extents and exclusion records
are the first `bank_count`, `extent_count` and `exclusion_count` entries of
its arrays, each count within its array, with its arena and its counter. -/
def OwnershipRepr {E X : Usize} (t : page_tables.Ownership E X) (T : Ownership E.val X.val) :
    Prop :=
  t.bank_count.val ≤ E.val ∧ t.extent_count.val ≤ E.val ∧ t.exclusion_count.val ≤ X.val ∧
    T.arena = word64 t.arena ∧
    ListRel PhysRangeRepr (t.banks.val.take t.bank_count.val) T.banks ∧
    ListRel ExtentRepr (t.extents.val.take t.extent_count.val) T.extents ∧
    ListRel ExclusionRepr (t.exclusions.val.take t.exclusion_count.val) T.exclusions ∧
    T.counter = counterOf t.counter

/-! ## The boot memory map -/

/-- A span of the `fdt` component as this target's translation holds it, as
a span of the specification of that component. -/
def spanOf (s : fdt.Span) : Krepi.Spec.Fdt.Span := ⟨word64 s.start, word64 s.size⟩

/-- A boot memory map of the `fdt` component, as this target's translation
holds it, stands for the boot memory map of the specification of that
component whose banks and managed banks are the first `ram_count` and
`managed_count` entries of their arrays, and whose boot storage and firmware
reservations are the first `boot_count` and the next up to `reserved_count`
entries of the array of reservations, each count within its array: the
representation that the `fdt` target states over its own translation. -/
def MemoryPlanRepr (p : fdt.MemoryPlan) (P : Krepi.Spec.Fdt.MemoryPlan) : Prop :=
  p.ram_count.val ≤ Krepi.Spec.Fdt.MemoryPlan.MAX_BANKS ∧
    p.managed_count.val ≤ Krepi.Spec.Fdt.MemoryPlan.MAX_BANKS ∧
    p.boot_count.val ≤ p.reserved_count.val ∧
    p.reserved_count.val ≤
      Krepi.Spec.Fdt.MemoryPlan.MAX_BOOT_SPANS + Krepi.Spec.Fdt.MemoryPlan.MAX_FIRMWARE ∧
    P = ⟨(p.ram.val.take p.ram_count.val).map spanOf,
      (p.managed.val.take p.managed_count.val).map spanOf,
      (p.reserved.val.take p.boot_count.val).map spanOf,
      ((p.reserved.val.take p.reserved_count.val).drop p.boot_count.val).map spanOf⟩

end Krepi.Statements.PageTables
