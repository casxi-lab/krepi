module

public import Krepi.Spec.PageTables.Basic

/-!
# Page tables: the page ownership table

`page_tables::Ownership` of the contract's entry table, rows 113 to 117:
`Ownership::new`, `choose`, `assign`, `reserve`, `Reservation::initialized`,
`publish`, `cancel`, `release`, `owner`, `validate` and `stats`, with the
rules of `Page ownership`, `After ownership`, `Check and execute`,
`Work bounds` and `Determinism`.

The table is modelled at the level of its extents, as the contract records
it. Its state is the arena, the managed banks in address order, the extents
in address order, each a range of pages of one bank that is free or held by
one holder, the exclusion records, each an exclusion with its owner as the
boot wiring gives it, and the generation counter, which is the generation of
the next allocation or reservation, or exhausted. The owner function $O$ of
the contract is `Ownership.ownerOf`: a page in an extent has the owner of the
extent, and a page of a managed bank in no extent the first owner, in the
order firmware, image, boot storage, of the exclusion records that touch it.

The capacities are parameters of the type: `Ownership E X` records at most
`E` extents, free and held together, and `X` exclusion records. The core's
constants are `EXTENTS`, 160, and `EXCLUSION_RECORDS`, 132; the vectors of the
prototype build tables of other extent capacities, so every entry is stated
for every `E` and `X`.

Every entry checks in the order of its rules and returns the error of the
first broken rule and nothing else, so a refused request writes nothing and
the table keeps no count of failures (`Behaviour changes` of the contract's
legacy test vectors). An entry that succeeds returns the table after its
write phase. `choose`, `owner`, `validate` and `stats` write nothing.

Machine widths are explicit where a value crosses an entry: addresses,
lengths, the arena, owner identities and generations are `UInt64`; the pages
and the alignment of a request, which count pages, are `UInt64`, as the
request of $2^{64} - 1$ pages of `own-07` and `own-28` is an input; the count
of failures of a reservation is `UInt64`. The capacities, the bank of an
extent and the fields of `Stats` are `Nat`: on a table that the entries built
the counts are at most the capacity and the bytes are those of disjoint
ranges below $2^{64}$. Arithmetic inside a definition is on `Nat`, and the
rules that compare with $2^{64}$ compare the exact value.
-/

@[expose] public section

namespace Krepi.Spec.PageTables

/-! ## Capacities -/

/-- The extents of the page ownership table of the core, free and held
together: 160 (`Page ownership`, Capacity). -/
def EXTENTS : Nat := 160

/-- The exclusion records of the page ownership table of the core: 132, the
4 spans of boot storage and the 128 firmware reservations that the boot memory
map admits at most (`Page ownership`, Capacity). -/
def EXCLUSION_RECORDS : Nat := 132

/-! ## Owners and values -/

/-- The state of a holder: reserved, its pages not yet zeroed or not yet
published, or published. -/
inductive HoldState where
  | reserved
  | published
  deriving DecidableEq, Repr, Inhabited

/-- The owner of an exclusion and of the pages that it excludes: firmware,
the kernel image, or another span of boot storage. -/
inductive Excluder where
  | firmware
  | image
  | bootStorage
  deriving DecidableEq, Repr, Inhabited

/-- The owner of a managed page, a row of the owner table of
`Page ownership`: free, the owner of an exclusion, or a holder
$\mathrm{held}(o, n, s)$ of owner identity `o`, generation `n` and state
`s`. -/
inductive Owner where
  | free
  | excluded (x : Excluder)
  | held (o n : UInt64) (s : HoldState)
  deriving DecidableEq, Repr, Inhabited

/-- What an extent records: its pages free, or held by one holder. -/
inductive Holding where
  | free
  | held (o n : UInt64) (s : HoldState)
  deriving DecidableEq, Repr, Inhabited

/-- The owner of the pages of an extent of a holding. -/
def Holding.owner : Holding → Owner
  | .free => .free
  | .held o n s => .held o n s

/-- An extent: a range of whole pages of the bank of index `bank`, in the
address order of the banks, with one holding. -/
structure Extent where
  range : PhysRange
  bank : Nat
  holding : Holding
  deriving DecidableEq

/-- An exclusion record: an exclusion as the boot wiring gives it, a physical
range that need not lie on page boundaries, with its owner. -/
structure Exclusion where
  range : PhysRange
  owner : Excluder
  deriving DecidableEq

/-- The generation counter: the generation of the next allocation or
reservation, or exhausted once the generation $2^{64} - 1$ has been given. -/
inductive Counter where
  | next (g : UInt64)
  | exhausted
  deriving DecidableEq, Repr, Inhabited

/-- The counter after it gave the generation `g`: `g + 1`, or exhausted after
$2^{64} - 1$, so that no generation is given twice. -/
def Counter.after (g : UInt64) : Counter :=
  if g.toNat + 1 < 2 ^ 64 then .next (g + 1) else .exhausted

/-- `page_tables::Ownership` of extent capacity `E` and exclusion capacity
`X`: the arena, a nonzero 64-bit value; the managed banks in address order;
the extents in address order; the exclusion records; and the generation
counter. -/
structure Ownership (E X : Nat) where
  arena : UInt64
  banks : List PhysRange
  extents : List Extent
  exclusions : List Exclusion
  counter : Counter
  deriving DecidableEq

/-- `page_tables::Allocation`, a receipt: the arena, the owner identity, the
generation and the range of an allocation. Bookkeeping, not authority. -/
structure Allocation where
  arena : UInt64
  owner : UInt64
  generation : UInt64
  range : PhysRange
  deriving DecidableEq

/-- `page_tables::Reservation`: held pages whose bytes are not yet zeroed,
with whether a zeroing was attempted and the count of failed zeroings. -/
structure Reservation where
  allocation : Allocation
  attempted : Bool
  failures : UInt64
  deriving DecidableEq

/-- `page_tables::Initialized`: held pages whose zeroing has completed and
that are not yet published, with the count of the failed zeroings before. -/
structure Initialized where
  allocation : Allocation
  failures : UInt64
  deriving DecidableEq

/-- The direction of a placement: from the lowest free extent, or from the
highest. -/
inductive Direction where
  | low
  | high
  deriving DecidableEq, Repr, Inhabited

/-- A placement, the caller's choice: low or high, with an optional window, a
physical range. -/
structure Placement where
  direction : Direction
  window : Option PhysRange
  deriving DecidableEq

/-- The result of `choose`: the owner identity of the request and the range
that its allocation takes. -/
structure Choice where
  owner : UInt64
  range : PhysRange
  deriving DecidableEq

/-! ## Arithmetic -/

/-- An address rounded down to a page. -/
def pageDown (a : Nat) : Nat := a / PAGE_SIZE * PAGE_SIZE

/-- An address rounded up to a page. -/
def pageUp (a : Nat) : Nat := (a + PAGE_SIZE - 1) / PAGE_SIZE * PAGE_SIZE

/-- An address rounded up to a multiple of `align`, which is not 0. -/
def alignUp (a align : Nat) : Nat := (a + align - 1) / align * align

/-- An address rounded down to a multiple of `align`, which is not 0. -/
def alignDown (a align : Nat) : Nat := a / align * align

/-- Whether a number is a power of two; 0 is not. -/
def isPowerOfTwo (n : Nat) : Bool := n != 0 && n &&& (n - 1) == 0

/-- The range `[start, start + len)` when it is one: `len` not 0 and the end
below $2^{64}$. -/
def rangeOf? (start len : Nat) : Option PhysRange :=
  if h : 0 < len ∧ start + len < 2 ^ 64 then
    some ⟨UInt64.ofNatLT start (by unfold UInt64.size; omega),
      UInt64.ofNatLT len (by unfold UInt64.size; omega),
      fun h0 => by
        have := congrArg UInt64.toNat h0
        simp only [UInt64.toNat_ofNatLT, UInt64.toNat_zero] at this
        omega,
      by simp only [UInt64.toNat_ofNatLT]; omega⟩
  else none

/-- Whether a range starts and ends on page boundaries. -/
def PhysRange.onPages (r : PhysRange) : Bool :=
  r.start.toNat % PAGE_SIZE == 0 && r.endNat % PAGE_SIZE == 0

/-- Whether a range holds the page at the address `q`, a multiple of 4 KiB. -/
def PhysRange.holdsPage (r : PhysRange) (q : Nat) : Bool :=
  r.start.toNat ≤ q && q + PAGE_SIZE ≤ r.endNat

/-- Whether a range touches the page at the address `q`: shares an address
with it. -/
def PhysRange.touchesPage (r : PhysRange) (q : Nat) : Bool :=
  r.start.toNat < q + PAGE_SIZE && q < r.endNat

/-! ## Initialization -/

/-- The pages of a bank that an exclusion touches, `[start, stop)`: its start
rounded down and its end rounded up to a page, within the bank; none when the
exclusion does not overlap the bank. -/
def Exclusion.cut (x : Exclusion) (bank : PhysRange) : Option (Nat × Nat) :=
  if x.range.overlaps bank then
    some (max (pageDown x.range.start.toNat) bank.start.toNat,
      min (pageUp x.range.endNat) bank.endNat)
  else none

/-- The runs `[a, b)` of a list in address order less the pages
`[start, stop)`: a run that the cut meets keeps its parts before and after
it. -/
def cutRuns (start stop : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | (a, b) :: rest =>
    if stop ≤ a || b ≤ start then (a, b) :: cutRuns start stop rest
    else (if a < start then [(a, start)] else []) ++
      (if stop < b then [(stop, b)] else []) ++ cutRuns start stop rest

/-- The free extents of the bank of index `i`: the maximal runs of its pages
that no exclusion touches, in address order. Each exclusion cuts the pages
that it touches out of the runs; an exclusion outside the bank cuts nothing,
and overlapping exclusions cut their union. -/
def bankExtents (exclusions : List Exclusion) (i : Nat) (bank : PhysRange) : List Extent :=
  let runs := exclusions.foldl (fun runs x =>
    match x.cut bank with
    | some (start, stop) => cutRuns start stop runs
    | none => runs) [(bank.start.toNat, bank.endNat)]
  runs.filterMap fun (a, b) => (rangeOf? a (b - a)).map (⟨·, i, .free⟩)

/-- The extents of a table at initialization: those of each bank, the banks
in address order. -/
def initialExtents (banks : List PhysRange) (exclusions : List Exclusion) : List Extent :=
  let rec go : Nat → List PhysRange → List Extent
    | _, [] => []
    | i, bank :: rest => bankExtents exclusions i bank ++ go (i + 1) rest
  go 0 banks

/-- Whether two of a list of ranges overlap. -/
def anyOverlap : List PhysRange → Bool
  | [] => false
  | r :: rest => rest.any r.overlaps || anyOverlap rest

/-- `Ownership::new(arena, banks, exclusions)`: the table of the managed banks
and the exclusions of the boot memory map with their owners. The checks, in
the order of `Page ownership`, Initialization: a bank that does not start or
end on a page boundary, `InvalidAlignment`; the arena 0, `InvalidArena`; no
bank, `InvalidRange`, and more banks than `E`, `MetadataExhausted`; two banks
that overlap, `InvalidRange`; more exclusions than `X`, then more extents than
`E` for the banks split by the exclusions, `MetadataExhausted`. The table
keeps the banks in address order, one free extent for each maximal run of
the pages of a bank that no exclusion touches, every exclusion in a record of
its own, and the counter at 1. -/
def Ownership.new (arena : UInt64) (banks : List PhysRange) (exclusions : List Exclusion) :
    Except OwnershipError (Ownership E X) := do
  if !banks.all (·.onPages) then throw .invalidAlignment
  if arena = 0 then throw .invalidArena
  if banks.isEmpty then throw .invalidRange
  if E < banks.length then throw .metadataExhausted
  if anyOverlap banks then throw .invalidRange
  if X < exclusions.length then throw .metadataExhausted
  let sorted := sortByKey (·.start.toNat) banks
  let extents := initialExtents sorted exclusions
  if E < extents.length then throw .metadataExhausted
  pure ⟨arena, sorted, extents, exclusions, .next 1⟩

/-! ## The owner function -/

/-- The first owner, in the order firmware, image, boot storage, of the
exclusion records that touch the page at `q`; none when none touches it. -/
def firstExcluder (exclusions : List Exclusion) (q : Nat) : Option Excluder :=
  let touching := exclusions.filter (·.range.touchesPage q)
  if touching.any (·.owner == .firmware) then some .firmware
  else if touching.any (·.owner == .image) then some .image
  else if touching.any (·.owner == .bootStorage) then some .bootStorage
  else none

/-- $O(q)$, the owner of the page at the address `q`, a multiple of 4 KiB:
the owner of the extent that holds it; for a page of a managed bank in no
extent, the first owner in the order firmware, image, boot storage among the
exclusion records that touch it; none for a page of no managed bank, and for
a page of a managed bank that neither an extent nor an exclusion record
holds, which a table that the entries built has not. -/
def Ownership.ownerOf (t : Ownership E X) (q : Nat) : Option Owner :=
  match t.extents.find? (·.range.holdsPage q) with
  | some e => some e.holding.owner
  | none =>
    if t.banks.any (·.holdsPage q) then (firstExcluder t.exclusions q).map .excluded
    else none

/-- `Ownership::owner(address)`: the owner of the page that holds the
address, $O$ of that page. -/
def Ownership.owner (t : Ownership E X) (address : UInt64) : Option Owner :=
  t.ownerOf (pageDown address.toNat)

/-! ## Placement -/

/-- The part of a free extent inside the window of a placement, `[lo, hi)`;
empty when `hi ≤ lo`. -/
def Placement.part (p : Placement) (r : PhysRange) : Nat × Nat :=
  match p.window with
  | none => (r.start.toNat, r.endNat)
  | some w => (max r.start.toNat w.start.toNat, min r.endNat w.endNat)

/-- What a part `[lo, hi)` of a free extent gives a request of `bytes` at the
alignment `align` in bytes. -/
inductive Fit where
  /-- The part holds no aligned range of the request. -/
  | none
  /-- The rounding of the start, or the end of the range, does not fit in
  64 bits. -/
  | overflow
  /-- The range that the part gives. -/
  | range (r : PhysRange)
  deriving DecidableEq

/-- The range of a request in the part `[lo, hi)` of a free extent: for a low
placement the lowest aligned start, `lo` rounded up, `overflow` when it or the
end of its range is $2^{64}$ or more, and the range when it ends inside the
part; for a high placement the highest aligned start whose range ends inside
the part, `hi - bytes` rounded down, when it is not below `lo`. `bytes` is not
0, as `choose` checks first. -/
def fit (d : Direction) (lo hi bytes align : Nat) : Fit :=
  if hi ≤ lo then .none
  else match d with
    | .low =>
      let s := alignUp lo align
      if 2 ^ 64 ≤ s + bytes then .overflow
      else match rangeOf? s bytes with
        | some r => if s + bytes ≤ hi then .range r else .none
        | none => .none
    | .high =>
      if hi < bytes then .none
      else
        let s := alignDown (hi - bytes) align
        match rangeOf? s bytes with
        | some r => if lo ≤ s then .range r else .none
        | none => .none

/-- The extents that taking the range `r` from the free extent `e` adds: one
for a part of `e` before `r` and one for a part after it. -/
def Extent.extra (e : Extent) (r : PhysRange) : Nat :=
  (if e.range.start.toNat < r.start.toNat then 1 else 0) +
    (if r.endNat < e.range.endNat then 1 else 0)

/-- The scan of `choose` over the extents in the order of its placement, with
`room` extents free in the capacity: a held extent is passed; in a free extent
the part inside the window gives its range (`fit`), `AddressOverflow` at once
when the rounding does not fit in 64 bits, and the first extent that gives a
range gives the result unless the range needs more extents than `room`, in
which case the scan goes on and remembers it (`limited`). At the end,
`MetadataExhausted` when an extent was passed over for capacity, and
`OutOfMemory` otherwise. -/
def scan (room bytes align : Nat) (p : Placement) :
    List Extent → (limited : Bool) → Except OwnershipError PhysRange
  | [], limited => .error (if limited then .metadataExhausted else .outOfMemory)
  | e :: rest, limited =>
    match e.holding with
    | .held .. => scan room bytes align p rest limited
    | .free =>
      let (lo, hi) := p.part e.range
      match fit p.direction lo hi bytes align with
      | .none => scan room bytes align p rest limited
      | .overflow => .error .addressOverflow
      | .range r =>
        if room < e.extra r then scan room bytes align p rest true else .ok r

/-- `Ownership::choose(owner, pages, alignment, placement)`: the range that an
allocation takes, without a write. The checks, in the order of
`Page ownership`, Placement: the request or its alignment in bytes, 4 KiB a
page, $2^{64}$ or more, `AddressOverflow`; 0 pages, `InvalidSize`; an
alignment that is not a power of two, among them 0, `InvalidAlignment`; the
counter exhausted, `GenerationExhausted`; then the scan of the free extents
in address order, from the lowest for a low placement and from the highest
for a high one (`scan`). The first fit in that order gives the range, so the
range follows from the table and the caller's placement and window. -/
def Ownership.choose (t : Ownership E X) (owner pages alignment : UInt64) (p : Placement) :
    Except OwnershipError Choice := do
  let bytes := pages.toNat * PAGE_SIZE
  let align := alignment.toNat * PAGE_SIZE
  if 2 ^ 64 ≤ bytes || 2 ^ 64 ≤ align then throw .addressOverflow
  if pages = 0 then throw .invalidSize
  if !isPowerOfTwo alignment.toNat then throw .invalidAlignment
  if t.counter = .exhausted then throw .generationExhausted
  let order := match p.direction with
    | .low => t.extents
    | .high => t.extents.reverse
  let range ← scan (E - t.extents.length) bytes align p order false
  pure ⟨owner, range⟩

/-! ## Taking and returning pages -/

/-- The extents before the first that satisfies `p`, in reverse order, that
extent and the extents after it. -/
def splitFirst (p : Extent → Bool) : List Extent → List Extent →
    Option (List Extent × Extent × List Extent)
  | [], _ => none
  | e :: rest, before => if p e then some (before, e, rest) else splitFirst p rest (e :: before)

/-- The extents that replace the free extent `e` when its range `r` is taken
with the holding `h`: the part before `r` and the part after it, which stay
free, around `r`. -/
def Extent.take (e : Extent) (r : PhysRange) (h : Holding) : List Extent :=
  let before := (rangeOf? e.range.start.toNat (r.start.toNat - e.range.start.toNat)).map
    (⟨·, e.bank, .free⟩)
  let after := (rangeOf? r.endNat (e.range.endNat - r.endNat)).map (⟨·, e.bank, .free⟩)
  before.toList ++ ⟨r, e.bank, h⟩ :: after.toList

/-- The write that `assign` and `reserve` make for the choice `c`: its range
held by its owner identity with the generation of the counter and the state
`s`, and the counter advanced. The checks of the requirement of `assign`, a
choice of `choose` under the same token, in the order of the checks of
`choose` that they repeat: the counter exhausted, `GenerationExhausted`; the
range not inside one free extent, `OutOfMemory`; more extents than the
capacity has free, as `scan` counts them, `MetadataExhausted`. A choice of
`choose` on the same table passes them. -/
def Ownership.take (t : Ownership E X) (c : Choice) (s : HoldState) :
    Except OwnershipError (Ownership E X × Allocation) := do
  let g ← match t.counter with
    | .next g => pure g
    | .exhausted => throw .generationExhausted
  let some (before, e, after) := splitFirst (fun e => e.holding == .free && e.range.contains c.range)
      t.extents [] | throw .outOfMemory
  if E - t.extents.length < e.extra c.range then throw .metadataExhausted
  let extents := before.reverseAux (e.take c.range (.held c.owner g s) ++ after)
  pure ({ t with extents, counter := Counter.after g }, ⟨t.arena, c.owner, g, c.range⟩)

/-- `Ownership::assign(c, zeroed)`: once the caller has zeroed the range of the
choice `c` through the direct map, `zeroed` tells whether the zeroing
completed. When it failed, `ZeroFailed`, and the pages stay free and no
generation is consumed; otherwise the pages are held by the owner identity of
`c` with the generation of the counter, published, and the receipt is
returned. -/
def Ownership.assign (t : Ownership E X) (c : Choice) (zeroed : Bool) :
    Except OwnershipError (Ownership E X × Allocation) :=
  if zeroed then t.take c .published else .error .zeroFailed

/-- `Ownership::reserve(owner, pages, alignment, placement)`: the checks of
`choose`; then the pages of the range that `choose` gives are held at once,
reserved, without zeroing, with the generation of the counter, and the
reservation is returned, not attempted and with no failure. -/
def Ownership.reserve (t : Ownership E X) (owner pages alignment : UInt64) (p : Placement) :
    Except OwnershipError (Ownership E X × Reservation) := do
  let c ← t.choose owner pages alignment p
  let (t', a) ← t.take c .reserved
  pure (t', ⟨a, false, 0⟩)

/-- What `Reservation::initialized` gives: the packet of a completed zeroing,
or the reservation, returned after a failed one. -/
inductive Initialization where
  | packet (x : Initialized)
  | retained (r : Reservation)
  deriving DecidableEq

/-- `Reservation::initialized(zeroed)`: it consumes the reservation, whose
range the caller has zeroed, and changes no table. When the zeroing
completed, the `Initialized` packet of its allocation with its count of
failures; otherwise the same reservation, marked as attempted, with its count
of failures increased by one, which stays at $2^{64} - 1$ once there. -/
def Reservation.initialized (r : Reservation) (zeroed : Bool) : Initialization :=
  if zeroed then .packet ⟨r.allocation, r.failures⟩
  else .retained { r with
    attempted := true
    failures := if r.failures.toNat + 1 < 2 ^ 64 then r.failures + 1 else r.failures }

/-- The checks of a value that names the allocation `a` held in the state
`s`, by the owner identity `o`, in the order of `Page ownership`, Receipts:
another arena, `WrongArena`; another owner identity, `WrongOwner`; no extent
that is exactly its range held by `o` with its generation in the state `s`,
`InvalidAllocation`. The extents before that extent, in reverse order, the
extent and the extents after it. -/
def Ownership.findHeld (t : Ownership E X) (o : UInt64) (a : Allocation) (s : HoldState) :
    Except OwnershipError (List Extent × Extent × List Extent) := do
  if a.arena != t.arena then throw .wrongArena
  if a.owner != o then throw .wrongOwner
  match splitFirst (fun e => e.range == a.range && e.holding == .held o a.generation s)
      t.extents [] with
  | some found => pure found
  | none => throw .invalidAllocation

/-- Two extents in address order as one free extent, when both are free, of
one bank, and the first ends where the second starts. -/
def Extent.join (a b : Extent) : Option Extent :=
  if a.holding == .free && b.holding == .free && a.bank == b.bank &&
      a.range.endNat == b.range.start.toNat then
    (rangeOf? a.range.start.toNat (b.range.endNat - a.range.start.toNat)).map (⟨·, a.bank, .free⟩)
  else none

/-- The extents with the extent `e` freed between `before`, in reverse order,
and `after`: the freed extent merges with the free extent next to it on each
side in the same bank, so a release never needs an extent. -/
def mergeFreed (before : List Extent) (e : Extent) (after : List Extent) : List Extent :=
  let freed : Extent := { e with holding := .free }
  let (before, freed) := match before with
    | l :: ls => match l.join freed with
      | some m => (ls, m)
      | none => (before, freed)
    | [] => ([], freed)
  let (freed, after) := match after with
    | r :: rs => match freed.join r with
      | some m => (m, rs)
      | none => (freed, after)
    | [] => (freed, [])
  before.reverseAux (freed :: after)

/-- `Ownership::release(owner, receipt)`: the checks of a receipt, published
(`findHeld`); then its pages are free, merged with the free extents next to
them in the same bank, and the counter is unchanged. -/
def Ownership.release (t : Ownership E X) (o : UInt64) (x : Allocation) :
    Except OwnershipError (Ownership E X) := do
  let (before, e, after) ← t.findHeld o x .published
  pure { t with extents := mergeFreed before e after }

/-- `Ownership::validate(owner, value)`: the checks of `release` without a
write, for a receipt, which names its allocation published, and for an
initialized packet, which names it reserved: `s` is the state that the value
names. -/
def Ownership.validate (t : Ownership E X) (o : UInt64) (a : Allocation) (s : HoldState) :
    Except OwnershipError Unit :=
  (t.findHeld o a s).map fun _ => ()

/-- `Ownership::publish(owner, packet)`: the checks of the packet, reserved
(`findHeld`); a refused packet is returned with the error. Then its pages are
held published with the same generation, the counter is unchanged, and the
receipt is returned. -/
def Ownership.publish (t : Ownership E X) (o : UInt64) (x : Initialized) :
    Except (OwnershipError × Initialized) (Ownership E X × Allocation) :=
  match t.findHeld o x.allocation .reserved with
  | .error e => .error (e, x)
  | .ok (before, e, after) =>
    let published : Extent := { e with holding := .held o x.allocation.generation .published }
    .ok ({ t with extents := before.reverseAux (published :: after) }, x.allocation)

/-- `Ownership::cancel(owner, reservation)`: first a reservation whose zeroing
was attempted, `ZeroFailed`; then the checks of the reservation, reserved
(`findHeld`); a refused reservation is returned with the error. Then its
pages are free, merged as by `release`, and the counter is unchanged. -/
def Ownership.cancel (t : Ownership E X) (o : UInt64) (r : Reservation) :
    Except (OwnershipError × Reservation) (Ownership E X) :=
  if r.attempted then .error (.zeroFailed, r)
  else match t.findHeld o r.allocation .reserved with
    | .error e => .error (e, r)
    | .ok (before, e, after) => .ok { t with extents := mergeFreed before e after }

/-! ## Statistics -/

/-- `page_tables::Stats`: the managed bytes, of the free and held pages; the
free and the allocated bytes, reserved pages counted as allocated; the number
of allocations, reservations included; the number of free extents and the
bytes of the largest; the extents in use and the capacity. -/
structure Stats where
  managed : Nat
  free : Nat
  allocated : Nat
  allocations : Nat
  freeExtents : Nat
  largestFree : Nat
  extents : Nat
  capacity : Nat
  deriving DecidableEq, Repr

/-- `Ownership::stats()`, which writes nothing. The excluded pages take no
extent, so they are not managed bytes. -/
def Ownership.stats (t : Ownership E X) : Stats :=
  t.extents.foldl (fun s e =>
    let n := e.range.len.toNat
    match e.holding with
    | .free =>
      ⟨s.managed + n, s.free + n, s.allocated, s.allocations, s.freeExtents + 1,
        max s.largestFree n, s.extents, s.capacity⟩
    | .held .. =>
      ⟨s.managed + n, s.free, s.allocated + n, s.allocations + 1, s.freeExtents,
        s.largestFree, s.extents, s.capacity⟩)
    ⟨0, 0, 0, 0, 0, 0, t.extents.length, E⟩

end Krepi.Spec.PageTables
