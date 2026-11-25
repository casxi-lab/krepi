module

public import Krepi.Spec.PageTables.Ownership

/-!
# Page tables: witnesses of the page ownership table

Theorems that witness that the specification of the page ownership table of
the `page-tables` component is not vacuous: for every frozen function of rows
113 to 117 of the entry table of its contract
(`docs/domains/memory/page-tables/contract.md`), one input on which it
succeeds, with the value that it gives, and for every error that the contract
gives that function, one input on which it fails with that error. The table
sets, rows 107 to 112, have their witnesses in
`Krepi.Spec.PageTables.Witnesses.TableSets`. Every expected value is a literal
worked out from the contract, never computed by the specification.

Each witness is proved here by `decide +kernel`, with a local instance that
decides the equality of `Except` values, as in the witnesses of the table
sets. Where an error has several rules, its witness is a conjunction with one
input for each rule that the contract names.

The tables are written here as literals of their state: the arena, the
managed banks, the extents, the exclusion records and the counter. A table is
an input as its type admits it, as the tests of the prototype set its
generation counter directly (`own-01`). The tables of extent capacity 8 have
the capacity of the prototype's tests (`PageAllocator::<8>`) and the
exclusion capacity of the core; a witness of a capacity takes a table of a
smaller one, since every entry is stated for every capacity.

For each step of the error orders of the contract, one more witness gives an
input that breaks a rule of that step and a later rule of the same entry, and
states the error of the step (`priorityNewStep1` to `priorityNewStep4`,
`priorityChooseStep1` to `priorityChooseStep5` for `choose` and `reserve`,
`priorityReceiptStep1` to `priorityReceiptStep3` for `publish`, `cancel`,
`release` and `validate`).

Error branches that no input of an entry reaches have no witness; for each,
a proposition below states that the entry never takes it, with its reason,
and a planned theorem proves it. The two variants of the specification that
reject every input or accept every input are refuted for the functions of
these rows by `notAlwaysRejecting` and `notAlwaysSucceeding`.
-/

@[expose] public section

namespace Krepi.Spec.PageTables.Witnesses.PageOwnership

/-- Equality of two `Except` values, decided by their constructors and
payloads; Lean core has no such instance. -/
local instance instDecidableEqExcept {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (Except.ok.inj e)
  | .error a, .error b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (Except.error.inj e)
  | .ok _, .error _ => isFalse nofun
  | .error _, .ok _ => isFalse nofun

/-! ## Inputs -/

/-- The physical range `[start, start + len)`, for a length that is not 0 and an
end below $2^{64}$, which `decide` checks where the witness writes it. -/
def phys (start len : Nat) (h : 0 < len ∧ start + len < 2 ^ 64 := by decide) : PhysRange :=
  ⟨UInt64.ofNatLT start (by unfold UInt64.size; omega),
    UInt64.ofNatLT len (by unfold UInt64.size; omega),
    fun h0 => by
      have := congrArg UInt64.toNat h0
      simp only [UInt64.toNat_ofNatLT, UInt64.toNat_zero] at this
      omega,
    by simp only [UInt64.toNat_ofNatLT]; omega⟩

/-- A table of extent capacity 8 and the exclusion capacity of the core. -/
abbrev Table8 := Ownership 8 EXCLUSION_RECORDS

/-- The first bank, `[0, 0x4000)`. -/
def BANK0 : PhysRange := phys 0 0x4000

/-- The second bank, `[0x10_0000, 0x10_8000)`, after a hole. -/
def BANK1 : PhysRange := phys 0x10_0000 0x8000

/-- A firmware reservation of 16 bytes at `0x1800`, which touches the page
`0x1000`. -/
def FIRMWARE : Exclusion := ⟨phys 0x1800 0x10, .firmware⟩

/-- An image span of 16 bytes at `0x10_0000`. -/
def IMAGE : Exclusion := ⟨phys 0x10_0000 0x10, .image⟩

/-- The free extents of the two banks less the page `0x1000`. -/
def FREE : List Extent :=
  [⟨phys 0 0x1000, 0, .free⟩, ⟨phys 0x2000 0x2000, 0, .free⟩, ⟨phys 0x10_0000 0x8000, 1, .free⟩]

/-- The table that `Ownership::new` gives on the two banks with `FIRMWARE`:
the arena 1, the banks in address order, three free extents and the counter
at 1. -/
def initial : Table8 := ⟨1, [BANK0, BANK1], FREE, [FIRMWARE], .next 1⟩

/-- `initial` with the counter `c`. -/
def initialAt (c : Counter) : Table8 := ⟨1, [BANK0, BANK1], FREE, [FIRMWARE], c⟩

/-- `initial` in a table of extent capacity 3, which its 3 extents fill. -/
def full : Ownership 3 EXCLUSION_RECORDS := ⟨1, [BANK0, BANK1], FREE, [FIRMWARE], .next 1⟩

/-- The receipt of the allocation of the page `0x10_1000` by the owner identity
7 with the generation 1. -/
def RECEIPT : Allocation := ⟨1, 7, 1, phys 0x10_1000 0x1000⟩

/-- `initial` after the allocation `RECEIPT`, published: the second bank in
three extents, and the counter at 2. -/
def held : Table8 :=
  ⟨1, [BANK0, BANK1],
    [⟨phys 0 0x1000, 0, .free⟩, ⟨phys 0x2000 0x2000, 0, .free⟩, ⟨phys 0x10_0000 0x1000, 1, .free⟩,
      ⟨phys 0x10_1000 0x1000, 1, .held 7 1 .published⟩, ⟨phys 0x10_2000 0x6000, 1, .free⟩],
    [FIRMWARE], .next 2⟩

/-- The allocation of the reservation of the page `0` by the owner identity 9
with the generation 1. -/
def RESERVED : Allocation := ⟨1, 9, 1, phys 0 0x1000⟩

/-- The reservation `RESERVED`, not attempted, without a failure. -/
def RESERVATION : Reservation := ⟨RESERVED, false, 0⟩

/-- The packet of `RESERVED` after a completed zeroing. -/
def PACKET : Initialized := ⟨RESERVED, 0⟩

/-- `initial` after the reservation `RESERVATION`: the page `0` reserved, and
the counter at 2. -/
def reserved : Table8 :=
  ⟨1, [BANK0, BANK1],
    [⟨phys 0 0x1000, 0, .held 9 1 .reserved⟩, ⟨phys 0x2000 0x2000, 0, .free⟩,
      ⟨phys 0x10_0000 0x8000, 1, .free⟩],
    [FIRMWARE], .next 2⟩

/-- A table of one free extent `[2^64 - 0x3000, 2^64 - 0x1000)`, near the end of
64 bits, with the counter `c`. -/
def top (c : Counter) : Table8 :=
  ⟨1, [phys 0xffff_ffff_ffff_d000 0x2000], [⟨phys 0xffff_ffff_ffff_d000 0x2000, 0, .free⟩], [], c⟩

/-- A table of extent capacity 2 with two free extents, `[0, 0x2000)` and that of
`top`. -/
def capTop : Ownership 2 EXCLUSION_RECORDS :=
  ⟨1, [phys 0 0x2000, phys 0xffff_ffff_ffff_d000 0x2000],
    [⟨phys 0 0x2000, 0, .free⟩, ⟨phys 0xffff_ffff_ffff_d000 0x2000, 1, .free⟩], [], .next 1⟩

/-- The result of `Ownership::new` for a table of extent capacity `E` and
exclusion capacity `X`. -/
abbrev NewResult (E X : Nat) := Except OwnershipError (Ownership E X)

/-- The result of `Ownership::new` for a table of `Table8`. -/
abbrev Result8 := NewResult 8 EXCLUSION_RECORDS

/-- A low placement without a window. -/
def LOW : Placement := ⟨.low, none⟩

/-- A high placement without a window. -/
def HIGH : Placement := ⟨.high, none⟩

/-! ## `Ownership::new` -/

/-- `Ownership::new`: the banks in address order, a free extent for each run of
pages that the firmware reservation leaves, its page `0x1000` in no extent,
the reservation in a record, and the counter at 1. -/
theorem newOk :
    (Ownership.new 1 [BANK1, BANK0] [FIRMWARE] : Result8) = .ok initial := by
  decide +kernel

/-- `Ownership::new`: a bank that starts, and one that ends, off a page. -/
theorem newInvalidAlignment :
    (Ownership.new 1 [phys 0x800 0x1000] [] : Result8) = .error .invalidAlignment ∧
      (Ownership.new 1 [phys 0 0x1800] [] : Result8) = .error .invalidAlignment := by
  decide +kernel

/-- `Ownership::new`: the arena 0. -/
theorem newInvalidArena :
    (Ownership.new 0 [BANK0] [] : Result8) = .error .invalidArena := by
  decide +kernel

/-- `Ownership::new`: no bank, and two banks that share `[0x3000, 0x4000)`. -/
theorem newInvalidRange :
    (Ownership.new 1 [] [] : Result8) = .error .invalidRange ∧
      (Ownership.new 1 [BANK0, phys 0x3000 0x2000] [] : Result8) =
        .error .invalidRange := by
  decide +kernel

/-- `Ownership::new`: two banks for the capacity of 1 extent; two exclusions for
the capacity of 1 record; and three free runs for the capacity of 2 extents.
-/
theorem newMetadataExhausted :
    (Ownership.new 1 [BANK0, BANK1] [] : NewResult 1 EXCLUSION_RECORDS) =
        .error .metadataExhausted ∧
      (Ownership.new 1 [BANK0] [FIRMWARE, IMAGE] : NewResult 8 1) =
        .error .metadataExhausted ∧
      (Ownership.new 1 [BANK0, BANK1] [FIRMWARE] : NewResult 2 EXCLUSION_RECORDS) =
        .error .metadataExhausted := by
  decide +kernel

/-! ## `Ownership::choose` and `assign` -/

/-- `choose`: 2 pages low, the second extent, which the first cannot hold; and
1 page high in the window `[0x10_0000, 0x10_2000)`, its highest page. -/
theorem chooseOk :
    initial.choose 7 2 1 LOW = .ok ⟨7, phys 0x2000 0x2000⟩ ∧
      initial.choose 7 1 1 ⟨.high, some (phys 0x10_0000 0x2000)⟩ = .ok ⟨7, phys 0x10_1000 0x1000⟩ := by
  decide +kernel

/-- `choose`: a request of $2^{52}$ pages and an alignment of $2^{52}$ pages,
$2^{64}$ bytes each; the start `2^64 - 0x3000` rounded up to 4 pages, $2^{64}$;
and 3 pages from that start, which end at $2^{64}$. -/
theorem chooseAddressOverflow :
    initial.choose 7 0x10_0000_0000_0000 1 LOW = .error .addressOverflow ∧
      initial.choose 7 1 0x10_0000_0000_0000 LOW = .error .addressOverflow ∧
      (top (.next 1)).choose 7 1 4 LOW = .error .addressOverflow ∧
      (top (.next 1)).choose 7 3 1 LOW = .error .addressOverflow := by
  decide +kernel

/-- `choose`: 0 pages. -/
theorem chooseInvalidSize : initial.choose 7 0 1 LOW = .error .invalidSize := by decide +kernel

/-- `choose`: the alignments 3 and 0. -/
theorem chooseInvalidAlignment :
    initial.choose 7 1 3 LOW = .error .invalidAlignment ∧
      initial.choose 7 1 0 LOW = .error .invalidAlignment := by
  decide +kernel

/-- `choose`: the counter exhausted. -/
theorem chooseGenerationExhausted :
    (initialAt .exhausted).choose 7 1 1 LOW = .error .generationExhausted := by
  decide +kernel

/-- `choose`: 3 pages high in a table whose 3 extents fill its capacity: the
second bank holds them but would split, and neither extent of the first bank
holds them. -/
theorem chooseMetadataExhausted : full.choose 7 3 1 HIGH = .error .metadataExhausted := by
  decide +kernel

/-- `choose`: 9 pages, more than any extent; a window in the hole between the
banks; and a window on the excluded page `0x1000`. -/
theorem chooseOutOfMemory :
    initial.choose 7 9 1 LOW = .error .outOfMemory ∧
      initial.choose 7 1 1 ⟨.low, some (phys 0x8000 0x1000)⟩ = .error .outOfMemory ∧
      initial.choose 7 1 1 ⟨.low, some (phys 0x1000 0x1000)⟩ = .error .outOfMemory := by
  decide +kernel

/-- `assign`: the choice of `chooseOk` in the window, zeroed: its page held,
published, by 7 with the generation 1, the extent split around it, the
counter at 2, and the receipt. -/
theorem assignOk : initial.assign ⟨7, phys 0x10_1000 0x1000⟩ true = .ok (held, RECEIPT) := by
  decide +kernel

/-- `assign`: a zeroing that failed. -/
theorem assignZeroFailed : initial.assign ⟨7, phys 0x10_1000 0x1000⟩ false = .error .zeroFailed := by
  decide +kernel

/-- `assign` of choices that `choose` does not give on the table, outside the
requirement of the entry: on an exhausted counter, `GenerationExhausted`; of
a range outside every free extent, `OutOfMemory`; of a range whose extent
would split beyond the capacity, `MetadataExhausted`. Each is the error that
`choose` gives at the rule that the choice breaks. -/
theorem assignRechecks :
    (initialAt .exhausted).assign ⟨7, phys 0x2000 0x1000⟩ true = .error .generationExhausted ∧
      initial.assign ⟨7, phys 0x8000 0x1000⟩ true = .error .outOfMemory ∧
      full.assign ⟨7, phys 0x2000 0x1000⟩ true = .error .metadataExhausted := by
  decide +kernel

/-! ## `Ownership::reserve`, `Reservation::initialized` and `publish` -/

/-- `reserve`: 1 page low, the page `0`, held at once, reserved, by 9 with the
generation 1, and the reservation, not attempted and without a failure. -/
theorem reserveOk : initial.reserve 9 1 1 LOW = .ok (reserved, RESERVATION) := by decide +kernel

/-- `reserve`: the requests of `chooseAddressOverflow`. -/
theorem reserveAddressOverflow :
    initial.reserve 9 0x10_0000_0000_0000 1 LOW = .error .addressOverflow ∧
      initial.reserve 9 1 0x10_0000_0000_0000 LOW = .error .addressOverflow ∧
      (top (.next 1)).reserve 9 1 4 LOW = .error .addressOverflow ∧
      (top (.next 1)).reserve 9 3 1 LOW = .error .addressOverflow := by
  decide +kernel

/-- `reserve`: 0 pages. -/
theorem reserveInvalidSize : initial.reserve 9 0 1 LOW = .error .invalidSize := by decide +kernel

/-- `reserve`: the alignments 3 and 0. -/
theorem reserveInvalidAlignment :
    initial.reserve 9 1 3 LOW = .error .invalidAlignment ∧
      initial.reserve 9 1 0 LOW = .error .invalidAlignment := by
  decide +kernel

/-- `reserve`: the counter exhausted. -/
theorem reserveGenerationExhausted :
    (initialAt .exhausted).reserve 9 1 1 LOW = .error .generationExhausted := by
  decide +kernel

/-- `reserve`: the request of `chooseMetadataExhausted`. -/
theorem reserveMetadataExhausted : full.reserve 9 3 1 HIGH = .error .metadataExhausted := by
  decide +kernel

/-- `reserve`: the requests of `chooseOutOfMemory`. -/
theorem reserveOutOfMemory :
    initial.reserve 9 9 1 LOW = .error .outOfMemory ∧
      initial.reserve 9 1 1 ⟨.low, some (phys 0x8000 0x1000)⟩ = .error .outOfMemory ∧
      initial.reserve 9 1 1 ⟨.low, some (phys 0x1000 0x1000)⟩ = .error .outOfMemory := by
  decide +kernel

/-- `Reservation::initialized`: after a completed zeroing the packet; after a
failed one the same reservation, attempted, with 1 failure; and a count of
failures at $2^{64} - 1$ stays there. -/
theorem initializedOk :
    RESERVATION.initialized true = .packet PACKET ∧
      RESERVATION.initialized false = .retained ⟨RESERVED, true, 1⟩ ∧
      (⟨RESERVED, true, 0xffff_ffff_ffff_ffff⟩ : Reservation).initialized false =
        .retained ⟨RESERVED, true, 0xffff_ffff_ffff_ffff⟩ := by
  decide +kernel

/-- `publish`: the packet of the reserved page `0`: the page held published
with the same generation, the counter unchanged, and the receipt. -/
theorem publishOk :
    reserved.publish 9 PACKET =
      .ok (⟨1, [BANK0, BANK1],
        [⟨phys 0 0x1000, 0, .held 9 1 .published⟩, ⟨phys 0x2000 0x2000, 0, .free⟩,
          ⟨phys 0x10_0000 0x8000, 1, .free⟩], [FIRMWARE], .next 2⟩, RESERVED) := by
  decide +kernel

/-- `publish`: a packet of the arena 2, which it returns with the error. -/
theorem publishWrongArena :
    reserved.publish 9 ⟨⟨2, 9, 1, phys 0 0x1000⟩, 0⟩ =
      .error (.wrongArena, ⟨⟨2, 9, 1, phys 0 0x1000⟩, 0⟩) := by
  decide +kernel

/-- `publish`: the owner identity 8. -/
theorem publishWrongOwner : reserved.publish 8 PACKET = .error (.wrongOwner, PACKET) := by
  decide +kernel

/-- `publish`: a packet of the generation 2; one of a range that is published,
not reserved; and one of a range that no extent is exactly. -/
theorem publishInvalidAllocation :
    reserved.publish 9 ⟨⟨1, 9, 2, phys 0 0x1000⟩, 0⟩ =
        .error (.invalidAllocation, ⟨⟨1, 9, 2, phys 0 0x1000⟩, 0⟩) ∧
      held.publish 7 ⟨RECEIPT, 0⟩ = .error (.invalidAllocation, ⟨RECEIPT, 0⟩) ∧
      reserved.publish 9 ⟨⟨1, 9, 1, phys 0 0x2000⟩, 0⟩ =
        .error (.invalidAllocation, ⟨⟨1, 9, 1, phys 0 0x2000⟩, 0⟩) := by
  decide +kernel

/-! ## `Ownership::cancel` and `release` -/

/-- `cancel`: the reservation of the page `0`, not attempted: the page free
again, the counter unchanged. -/
theorem cancelOk : reserved.cancel 9 RESERVATION = .ok (initialAt (.next 2)) := by decide +kernel

/-- `cancel`: an attempted reservation, which it returns with the error. -/
theorem cancelZeroFailed :
    reserved.cancel 9 ⟨RESERVED, true, 1⟩ = .error (.zeroFailed, ⟨RESERVED, true, 1⟩) := by
  decide +kernel

/-- `cancel`: a reservation of the arena 2. -/
theorem cancelWrongArena :
    reserved.cancel 9 ⟨⟨2, 9, 1, phys 0 0x1000⟩, false, 0⟩ =
      .error (.wrongArena, ⟨⟨2, 9, 1, phys 0 0x1000⟩, false, 0⟩) := by
  decide +kernel

/-- `cancel`: the owner identity 8. -/
theorem cancelWrongOwner : reserved.cancel 8 RESERVATION = .error (.wrongOwner, RESERVATION) := by
  decide +kernel

/-- `cancel`: a reservation of the generation 2, and one on a table where its
page is free. -/
theorem cancelInvalidAllocation :
    reserved.cancel 9 ⟨⟨1, 9, 2, phys 0 0x1000⟩, false, 0⟩ =
        .error (.invalidAllocation, ⟨⟨1, 9, 2, phys 0 0x1000⟩, false, 0⟩) ∧
      initial.cancel 9 RESERVATION = .error (.invalidAllocation, RESERVATION) := by
  decide +kernel

/-- `release`: the receipt of the page `0x10_1000`: the page free and merged
with the free extents on both sides into the one extent of the second bank,
the counter unchanged. -/
theorem releaseOk : held.release 7 RECEIPT = .ok (initialAt (.next 2)) := by decide +kernel

/-- `release`: a receipt of the arena 2. -/
theorem releaseWrongArena :
    held.release 7 ⟨2, 7, 1, phys 0x10_1000 0x1000⟩ = .error .wrongArena := by
  decide +kernel

/-- `release`: the owner identity 8. -/
theorem releaseWrongOwner : held.release 8 RECEIPT = .error .wrongOwner := by decide +kernel

/-- `release`: a receipt of the generation 2; the receipt again once its page is
released; and the allocation of a reservation, not published. -/
theorem releaseInvalidAllocation :
    held.release 7 ⟨1, 7, 2, phys 0x10_1000 0x1000⟩ = .error .invalidAllocation ∧
      (initialAt (.next 2)).release 7 RECEIPT = .error .invalidAllocation ∧
      reserved.release 9 RESERVED = .error .invalidAllocation := by
  decide +kernel

/-! ## `Ownership::owner`, `validate` and `stats` -/

/-- `owner`: the holder of the allocated page, by an address inside it; the
firmware of the excluded page `0x1000`; free; and none in the hole between the
banks and past the second bank. -/
theorem ownerOk :
    held.owner 0x10_1800 = some (.held 7 1 .published) ∧
      held.owner 0x1234 = some (.excluded .firmware) ∧
      held.owner 0x3fff = some .free ∧
      held.owner 0x8000 = none ∧
      held.owner 0x10_8000 = none := by
  decide +kernel

/-- `validate`: the receipt of `held`, and the allocation of the reservation of
`reserved` in the state of a packet. -/
theorem validateOk :
    held.validate 7 RECEIPT .published = .ok () ∧
      reserved.validate 9 RESERVED .reserved = .ok () := by
  decide +kernel

/-- `validate`: a receipt of the arena 2. -/
theorem validateWrongArena :
    held.validate 7 ⟨2, 7, 1, phys 0x10_1000 0x1000⟩ .published = .error .wrongArena := by
  decide +kernel

/-- `validate`: the owner identity 8. -/
theorem validateWrongOwner : held.validate 8 RECEIPT .published = .error .wrongOwner := by
  decide +kernel

/-- `validate`: a receipt of the generation 2, and the receipt in the state of a
packet. -/
theorem validateInvalidAllocation :
    held.validate 7 ⟨1, 7, 2, phys 0x10_1000 0x1000⟩ .published = .error .invalidAllocation ∧
      held.validate 7 RECEIPT .reserved = .error .invalidAllocation := by
  decide +kernel

/-- `stats` of `held`: `0xb000` managed bytes, the excluded page not among them;
`0xa000` free and `0x1000` allocated; 1 allocation; 4 free extents, the
largest of `0x6000` bytes; 5 extents of the capacity 8. -/
theorem statsOk : held.stats = ⟨0xb000, 0xa000, 0x1000, 1, 4, 0x6000, 5, 8⟩ := by decide +kernel

/-! ## Error priority

For each step of the error orders of `Page ownership`, one input that breaks a
rule of that step and a later rule of the same entry, and gives the error of
the step: the error of the later rule is the one that the input gives once
the earlier rule is repaired. -/

/-- Step 1 of the order of `Ownership::new`: a bank off a page,
`InvalidAlignment`, before the arena 0, `InvalidArena`. -/
theorem priorityNewStep1 :
    (Ownership.new 0 [phys 0x800 0x1000] [] : Result8) = .error .invalidAlignment := by
  decide +kernel

/-- Step 2: the arena 0, `InvalidArena`, before the missing bank,
`InvalidRange`. -/
theorem priorityNewStep2 :
    (Ownership.new 0 [] [] : Result8) = .error .invalidArena := by
  decide +kernel

/-- Step 3: two banks for the capacity of 1 extent, `MetadataExhausted`, before
their overlap, `InvalidRange`. -/
theorem priorityNewStep3 :
    (Ownership.new 1 [BANK0, phys 0x3000 0x2000] [] : NewResult 1 EXCLUSION_RECORDS) =
      .error .metadataExhausted := by
  decide +kernel

/-- Step 4: two banks that overlap, `InvalidRange`, before two exclusions for
the capacity of 1 record, and before the three free runs of the banks
`[0, 0x3000)` and, once the overlap is repaired, `[0x3000, 0x5000)` for the
capacity of 2 extents, each `MetadataExhausted`. -/
theorem priorityNewStep4 :
    (Ownership.new 1 [BANK0, phys 0x3000 0x2000] [FIRMWARE, IMAGE] : NewResult 8 1) =
        .error .invalidRange ∧
      (Ownership.new 1 [phys 0 0x3000, phys 0x2000 0x3000] [FIRMWARE] :
          NewResult 2 EXCLUSION_RECORDS) = .error .invalidRange := by
  decide +kernel

/-- Step 1 of the order of `choose` and `reserve`: an alignment of $2^{64}$
bytes, `AddressOverflow`, before 0 pages, `InvalidSize`. -/
theorem priorityChooseStep1 :
    initial.choose 7 0 0x10_0000_0000_0000 LOW = .error .addressOverflow ∧
      initial.reserve 7 0 0x10_0000_0000_0000 LOW = .error .addressOverflow := by
  decide +kernel

/-- Step 2: 0 pages, `InvalidSize`, before the alignment 3, `InvalidAlignment`.
-/
theorem priorityChooseStep2 :
    initial.choose 7 0 3 LOW = .error .invalidSize ∧
      initial.reserve 7 0 3 LOW = .error .invalidSize := by
  decide +kernel

/-- Step 3: the alignment 0, `InvalidAlignment`, before the exhausted counter,
`GenerationExhausted`. -/
theorem priorityChooseStep3 :
    (initialAt .exhausted).choose 7 1 0 LOW = .error .invalidAlignment ∧
      (initialAt .exhausted).reserve 7 1 0 LOW = .error .invalidAlignment := by
  decide +kernel

/-- Step 4: the exhausted counter, `GenerationExhausted`, before the rounding of
the start of `top` beyond 64 bits, `AddressOverflow`. -/
theorem priorityChooseStep4 :
    (top .exhausted).choose 7 1 4 LOW = .error .generationExhausted ∧
      (top .exhausted).reserve 7 1 4 LOW = .error .generationExhausted := by
  decide +kernel

/-- Step 5: the rounding of a start beyond 64 bits, `AddressOverflow`, before an
extent passed over for capacity, `MetadataExhausted`: in `capTop`, whose 2
extents fill its capacity, the first holds the page but would split, and the
second rounds its start to $2^{64}$. -/
theorem priorityChooseStep5 :
    capTop.choose 7 1 4 LOW = .error .addressOverflow ∧
      capTop.reserve 7 1 4 LOW = .error .addressOverflow := by
  decide +kernel

/-- Step 1 of the order of `cancel`: an attempted reservation, `ZeroFailed`,
before its arena 2, `WrongArena`. -/
theorem priorityReceiptStep1 :
    reserved.cancel 9 ⟨⟨2, 9, 1, phys 0 0x1000⟩, true, 1⟩ =
      .error (.zeroFailed, ⟨⟨2, 9, 1, phys 0 0x1000⟩, true, 1⟩) := by
  decide +kernel

/-- Step 2 of the order of the receipts, for `release`, `validate`, `publish`
and `cancel`: the arena 2, `WrongArena`, before the owner identity 8,
`WrongOwner`. -/
theorem priorityReceiptStep2 :
    held.release 8 ⟨2, 7, 1, phys 0x10_1000 0x1000⟩ = .error .wrongArena ∧
      held.validate 8 ⟨2, 7, 1, phys 0x10_1000 0x1000⟩ .published = .error .wrongArena ∧
      reserved.publish 8 ⟨⟨2, 9, 1, phys 0 0x1000⟩, 0⟩ =
        .error (.wrongArena, ⟨⟨2, 9, 1, phys 0 0x1000⟩, 0⟩) ∧
      reserved.cancel 8 ⟨⟨2, 9, 1, phys 0 0x1000⟩, false, 0⟩ =
        .error (.wrongArena, ⟨⟨2, 9, 1, phys 0 0x1000⟩, false, 0⟩) := by
  decide +kernel

/-- Step 3: the owner identity 8, `WrongOwner`, before the generation 2,
`InvalidAllocation`. -/
theorem priorityReceiptStep3 :
    held.release 8 ⟨1, 7, 2, phys 0x10_1000 0x1000⟩ = .error .wrongOwner ∧
      held.validate 8 ⟨1, 7, 2, phys 0x10_1000 0x1000⟩ .published = .error .wrongOwner ∧
      reserved.publish 8 ⟨⟨1, 9, 2, phys 0 0x1000⟩, 0⟩ =
        .error (.wrongOwner, ⟨⟨1, 9, 2, phys 0 0x1000⟩, 0⟩) ∧
      reserved.cancel 8 ⟨⟨1, 9, 2, phys 0 0x1000⟩, false, 0⟩ =
        .error (.wrongOwner, ⟨⟨1, 9, 2, phys 0 0x1000⟩, false, 0⟩) := by
  decide +kernel

/-! ## Unreachable error branches

Branches of the entries that fail with an error, but that no input of the
entry reaches under its machine widths or under its requirement on the tables
that the entries build. Each proposition states that the entry never takes
the branch, with its reason; a planned theorem below
`Krepi.Proofs.PageTables.Witnesses.PageOwnership` proves it. The error of
each branch is witnessed above where another branch of the same entry gives
it. -/

/-- A page ownership table that the entries of the specification build: one
that `Ownership::new` gives, and each table that a write entry gives on such
a table, `assign` on a choice that `choose` gives on that table. -/
inductive Built {E X : Nat} : Ownership E X → Prop
  | new {a banks exclusions t} : Ownership.new a banks exclusions = .ok t → Built t
  | assign {t o m al p c z t' x} :
      Built t → t.choose o m al p = .ok c → t.assign c z = .ok (t', x) → Built t'
  | reserve {t o m al p t' r} : Built t → t.reserve o m al p = .ok (t', r) → Built t'
  | publish {t o x t' a} : Built t → t.publish o x = .ok (t', a) → Built t'
  | cancel {t o r t'} : Built t → t.cancel o r = .ok t' → Built t'
  | release {t o x t'} : Built t → t.release o x = .ok t' → Built t'

/-- `assign` of a choice that `choose` gives on the same table, the
requirement of the entry, never fails with `GenerationExhausted`,
`OutOfMemory` or `MetadataExhausted`, and `reserve` never fails after its
`choose`: on a table that the entries build, the free extents are disjoint,
so the one extent that holds the chosen range is the one where `choose`
found it, with the room that `choose` counted, and the counter that `choose`
found not exhausted is unchanged. The only error of `assign` is `ZeroFailed`
(`assignZeroFailed`), and the errors of `reserve` are those of `choose`.
Feature: `krepi.kernel.kernel-memory`. -/
def TakeAcceptsChoice : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (o m al : UInt64) (p : Placement) (c : Choice) (s : HoldState),
    Built t → t.choose o m al p = .ok c → ∃ y, t.take c s = .ok y

/-- A high placement never fails with `AddressOverflow` at the
rounding of a start or the end of a range: its start is the end of the part
of a free extent less the request, rounded down, so the range ends inside an
extent below $2^{64}$. Its `AddressOverflow` is that of the size of the
request or of its alignment; that of the rounding is the low placement's
(`chooseAddressOverflow`).
Feature: `krepi.kernel.kernel-memory`. -/
def HighPlacementNoOverflow : Prop :=
  ∀ (E X : Nat) (t : Ownership E X) (o m al : UInt64) (w : Option PhysRange),
    t.choose o m al ⟨.high, w⟩ = .error .addressOverflow →
      2 ^ 64 ≤ m.toNat * PAGE_SIZE ∨ 2 ^ 64 ≤ al.toNat * PAGE_SIZE

/-! ## The two variants -/

/-- **The variant that rejects every input is refuted.** Each frozen function of
rows 113 to 117 that can fail succeeds on an input, by the success witnesses
above. -/
theorem notAlwaysRejecting :
    (∃ E X a b x, ∃ t : Ownership E X, Ownership.new a b x = .ok t) ∧
    (∃ E X, ∃ t : Ownership E X, ∃ o m al p c, t.choose o m al p = .ok c) ∧
    (∃ E X, ∃ t : Ownership E X, ∃ c z y, t.assign c z = .ok y) ∧
    (∃ E X, ∃ t : Ownership E X, ∃ o m al p y, t.reserve o m al p = .ok y) ∧
    (∃ E X, ∃ t : Ownership E X, ∃ o x y, t.publish o x = .ok y) ∧
    (∃ E X, ∃ t : Ownership E X, ∃ o r y, t.cancel o r = .ok y) ∧
    (∃ E X, ∃ t : Ownership E X, ∃ o x y, t.release o x = .ok y) ∧
    (∃ E X, ∃ t : Ownership E X, ∃ o a s, t.validate o a s = .ok ()) :=
  ⟨⟨_, _, _, _, _, _, newOk⟩, ⟨_, _, _, _, _, _, _, _, chooseOk.1⟩, ⟨_, _, _, _, _, _, assignOk⟩,
    ⟨_, _, _, _, _, _, _, _, reserveOk⟩, ⟨_, _, _, _, _, _, publishOk⟩,
    ⟨_, _, _, _, _, _, cancelOk⟩, ⟨_, _, _, _, _, _, releaseOk⟩,
    ⟨_, _, _, _, _, _, validateOk.1⟩⟩

/-- **The variant that accepts every input is refuted.** Each frozen function
of rows 113 to 117 that can fail fails on an input, by the rejection
witnesses above. -/
theorem notAlwaysSucceeding :
    (∃ E X a b x e, (Ownership.new a b x : Except OwnershipError (Ownership E X)) = .error e) ∧
    (∃ E X, ∃ t : Ownership E X, ∃ o m al p e, t.choose o m al p = .error e) ∧
    (∃ E X, ∃ t : Ownership E X, ∃ c z e, t.assign c z = .error e) ∧
    (∃ E X, ∃ t : Ownership E X, ∃ o m al p e, t.reserve o m al p = .error e) ∧
    (∃ E X, ∃ t : Ownership E X, ∃ o x e, t.publish o x = .error e) ∧
    (∃ E X, ∃ t : Ownership E X, ∃ o r e, t.cancel o r = .error e) ∧
    (∃ E X, ∃ t : Ownership E X, ∃ o x e, t.release o x = .error e) ∧
    (∃ E X, ∃ t : Ownership E X, ∃ o a s e, t.validate o a s = .error e) :=
  ⟨⟨_, _, _, _, _, _, newInvalidArena⟩, ⟨_, _, _, _, _, _, _, _, chooseInvalidSize⟩,
    ⟨_, _, _, _, _, _, assignZeroFailed⟩, ⟨_, _, _, _, _, _, _, _, reserveInvalidSize⟩,
    ⟨_, _, _, _, _, _, publishWrongOwner⟩, ⟨_, _, _, _, _, _, cancelZeroFailed⟩,
    ⟨_, _, _, _, _, _, releaseWrongOwner⟩, ⟨_, _, _, _, _, _, _, validateWrongOwner⟩⟩

end Krepi.Spec.PageTables.Witnesses.PageOwnership
