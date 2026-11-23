module

public import Krepi.Spec.Fdt.BootMemory

/-!
# Device tree: the boot memory map

`MemoryPlan::all_ram`, `new` and `from_boot_memory` of the contract's
`Boot memory map`, with the eight steps of its error order in
`Rejection and error priority`, and the queries of the value that they build:
`MemoryPlan::managed_banks`, `ram`, `reservations`, `boot_ranges`,
`firmware_ranges`, `described_bytes`, `managed_bytes`, `contains_ram`,
`is_available`, `permits_backing` and `available_ranges`.

A `MemoryPlan` holds the RAM banks sorted by their start, the managed banks,
the complete 4 KiB pages that it manages, and the boot storage and the
firmware reservations, each rounded outward to whole pages and kept in input
order. It describes memory: it allocates nothing and maps nothing.

Every entry checks its rules in the order of the error order and builds its
result while it checks, so that the first broken rule decides the error and a
failure returns that error and nothing else. The loops are structural
recursion on lists that the capacities of step 2 bound before any of them is
read, and the usable ranges are found by a cursor that moves forward within
each managed bank, with fuel from the number of reservations.
-/

@[expose] public section

namespace Krepi.Spec.Fdt

/-! ## Limits of the boot memory map -/

/-- The page of the boot memory map, 4 KiB. -/
def MemoryPlan.PAGE_SIZE : Nat := 4096

/-- The most RAM banks, 32. -/
def MemoryPlan.MAX_BANKS : Nat := 32

/-- The most spans of boot storage, 4. -/
def MemoryPlan.MAX_BOOT_SPANS : Nat := 4

/-- The most firmware reservations, 128. -/
def MemoryPlan.MAX_FIRMWARE : Nat := 128

/-- The most bytes of a managed window of `MemoryPlan::new`, 128 MiB. -/
def MemoryPlan.MAX_WINDOW_BYTES : Nat := 0x800_0000

/-- The most bytes of the RAM banks together, 16 GiB. -/
def MemoryPlan.MAX_RAM_BYTES : Nat := 0x4_0000_0000

/-! ## The value -/

/-- `MemoryPlan`, the boot memory map: the RAM banks, sorted by their start
(`MemoryPlan::ram`); the managed banks, in address order
(`MemoryPlan::managed_banks`); the pages of the boot storage, in input order
(`MemoryPlan::boot_ranges`); and the pages of the firmware reservations, in
input order (`MemoryPlan::firmware_ranges`). -/
structure MemoryPlan where
  ram : List Span
  managed : List Span
  boot : List Span
  firmware : List Span
  deriving DecidableEq, Repr, Inhabited

/-! ## Pages and banks -/

/-- A span that the boot memory map takes: of size 0, `InvalidRange`; whose
end leaves 64 bits, `Overflow`. -/
def checkPlanSpan (s : Span) : Except PlanError Unit :=
  if s.size = 0 then .error .invalidRange
  else if ¬ s.Valid then .error .overflow
  else .ok ()

/-- The span of the addresses from `start` up to `stop`. -/
def spanBetween (start stop : Nat) : Span :=
  ⟨UInt64.ofNat start, UInt64.ofNat (stop - start)⟩

/-- The pages of a span, rounded outward to whole pages: the span itself
(`checkPlanSpan`); then its end rounded up, `Overflow` when it leaves 64 bits.
-/
def pagesOf (s : Span) : Except PlanError Span := do
  checkPlanSpan s
  let start := s.start.toNat / MemoryPlan.PAGE_SIZE * MemoryPlan.PAGE_SIZE
  let stop := (s.endNat + MemoryPlan.PAGE_SIZE - 1) / MemoryPlan.PAGE_SIZE * MemoryPlan.PAGE_SIZE
  if 2 ^ 64 ≤ stop then throw .overflow
  pure (spanBetween start stop)

/-- One RAM bank after the banks `banks`, in input order: the span
(`checkPlanSpan`), then sharing an address with an earlier bank, `Overlap`. -/
def addBank (banks : List Span) (s : Span) : Except PlanError (List Span) := do
  checkPlanSpan s
  if banks.any (·.touches s) then throw .overlap
  pure (banks ++ [s])

/-- A span put among spans sorted by their start, before the first that does
not start below it. -/
def insertByStart (s : Span) : List Span → List Span
  | [] => [s]
  | b :: rest => if s.start.toNat ≤ b.start.toNat then s :: b :: rest else b :: insertByStart s rest

/-- Spans sorted by their start. Disjoint nonempty spans have distinct starts,
so the order of the banks is unique. -/
def sortByStart : List Span → List Span
  | [] => []
  | s :: rest => insertByStart s (sortByStart rest)

/-- One RAM bank in address order, after the sum `acc.1` of the banks before
it and their managed banks `acc.2`: the sum, `Overflow` when it leaves 64
bits, which disjoint banks never reach, then above 16 GiB, `ArenaTooLarge`;
then the start of the bank rounded up to a page, `Overflow` when it leaves 64
bits. The complete pages of the bank, from that start to its end rounded
down, are its managed bank; a bank without one contributes none. -/
def admitBank (acc : Nat × List Span) (b : Span) : Except PlanError (Nat × List Span) := do
  let sum := acc.1 + b.size.toNat
  if 2 ^ 64 ≤ sum then throw .overflow
  if MemoryPlan.MAX_RAM_BYTES < sum then throw .arenaTooLarge
  let start := (b.start.toNat + MemoryPlan.PAGE_SIZE - 1) / MemoryPlan.PAGE_SIZE * MemoryPlan.PAGE_SIZE
  if 2 ^ 64 ≤ start then throw .overflow
  let stop := b.endNat / MemoryPlan.PAGE_SIZE * MemoryPlan.PAGE_SIZE
  pure (sum, if start < stop then acc.2 ++ [spanBetween start stop] else acc.2)

/-- One span of boot storage after the pages `boot` of the spans before it,
in input order: its pages (`pagesOf`); not inside one bank of `banks`,
`OutsideRam`; sharing a page with earlier boot storage, `Overlap`. -/
def addBoot (banks : List Span) (boot : List Span) (s : Span) : Except PlanError (List Span) := do
  let pages ← pagesOf s
  if !inOneRange banks pages then throw .outsideRam
  if boot.any (·.touches pages) then throw .overlap
  pure (boot ++ [pages])

/-- One firmware reservation after the pages `firmware` of those before it,
in input order: its pages (`pagesOf`); sharing a page with the boot storage
`boot`, `Overlap`. Its flags do not matter: every page of every reservation
is excluded. -/
def addFirmware (boot : List Span) (firmware : List Span) (r : ReservedRegion) :
    Except PlanError (List Span) := do
  let pages ← pagesOf r.span
  if boot.any (·.touches pages) then throw .overlap
  pure (firmware ++ [pages])

/-! ## The entries -/

/-- `MemoryPlan::all_ram(ram, boot, firmware)`: the boot memory map that
manages every complete page of every bank, or the error of the first broken
rule of steps 2 to 7 of the error order of the boot memory map. No bank or
more than 32, no boot storage or more than 4 spans, more than 128 firmware
reservations, `Capacity`; each bank in input order (`addBank`); the banks in
address order (`admitBank`); no complete page in any bank, `Alignment`; each
span of boot storage in input order (`addBoot`); each firmware reservation
in input order (`addFirmware`). -/
def MemoryPlan.allRam (ram boot : List Span) (firmware : List ReservedRegion) :
    Except PlanError MemoryPlan := do
  if ram.isEmpty || MemoryPlan.MAX_BANKS < ram.length || boot.isEmpty ||
      MemoryPlan.MAX_BOOT_SPANS < boot.length || MemoryPlan.MAX_FIRMWARE < firmware.length then
    throw .capacity
  let banks := sortByStart (← ram.foldlM addBank [])
  let (_, managed) ← banks.foldlM admitBank (0, [])
  if managed.isEmpty then throw .alignment
  let bootPages ← boot.foldlM (addBoot banks) []
  let firmwarePages ← firmware.foldlM (addFirmware bootPages) []
  pure { ram := banks, managed, boot := bootPages, firmware := firmwarePages }

/-- `MemoryPlan::contains_ram(range)`: one bank holds the range. A range of
size 0, or whose end leaves 64 bits, lies in no bank. -/
def MemoryPlan.containsRam (p : MemoryPlan) (s : Span) : Bool :=
  s.size != 0 && decide s.Valid && inOneRange p.ram s

/-- `MemoryPlan::new(window, ram, boot, firmware)`: the boot memory map of
`all_ram` that manages only `window`, or the error of the first broken rule
of the eight steps. The window (`checkPlanSpan`); its ends not on pages,
`Alignment`; above 128 MiB, `ArenaTooLarge`; then `MemoryPlan::all_ram`, with
its errors; then the window outside every single bank, `OutsideRam`. -/
def MemoryPlan.new (window : Span) (ram boot : List Span) (firmware : List ReservedRegion) :
    Except PlanError MemoryPlan := do
  checkPlanSpan window
  if window.start.toNat % MemoryPlan.PAGE_SIZE != 0 || window.endNat % MemoryPlan.PAGE_SIZE != 0 then
    throw .alignment
  if MemoryPlan.MAX_WINDOW_BYTES < window.size.toNat then throw .arenaTooLarge
  let plan ← MemoryPlan.allRam ram boot firmware
  if !plan.containsRam window then throw .outsideRam
  pure { plan with managed := [window] }

/-- `MemoryPlan::from_boot_memory(memory, window, more)`: `MemoryPlan::new`
with the RAM ranges of the boot memory, the boot storage of its image, its tree
and the further spans `more` of the board, such as the boot bundle, and its
reserved regions as firmware reservations. More than two further spans make
more than 4 spans of boot storage, `Capacity`. -/
def MemoryPlan.fromBootMemory (memory : BootMemory) (window : Span) (more : List Span) :
    Except PlanError MemoryPlan :=
  MemoryPlan.new window memory.ram (memory.image :: memory.dtb :: more) memory.reserved

/-! ## The queries -/

/-- `MemoryPlan::managed_banks`: the managed banks, in address order. -/
def MemoryPlan.managedBanks (p : MemoryPlan) : List Span := p.managed

/-- `MemoryPlan::boot_ranges`: the pages of the boot storage, in input order.
-/
def MemoryPlan.bootRanges (p : MemoryPlan) : List Span := p.boot

/-- `MemoryPlan::firmware_ranges`: the pages of the firmware reservations, in
input order. -/
def MemoryPlan.firmwareRanges (p : MemoryPlan) : List Span := p.firmware

/-- `MemoryPlan::reservations`: the pages of the boot storage and then those
of the firmware reservations. -/
def MemoryPlan.reservations (p : MemoryPlan) : List Span := p.boot ++ p.firmware

/-- The sum of the sizes of spans, at their width. A boot memory map of the
entries holds at most 16 GiB in its banks, so no sum of its spans wraps. -/
def sumSizes (spans : List Span) : UInt64 :=
  UInt64.ofNat (spans.foldl (fun sum s => sum + s.size.toNat) 0)

/-- `MemoryPlan::described_bytes`: the sum of the banks. -/
def MemoryPlan.describedBytes (p : MemoryPlan) : UInt64 := sumSizes p.ram

/-- `MemoryPlan::managed_bytes`: the sum of the managed banks. -/
def MemoryPlan.managedBytes (p : MemoryPlan) : UInt64 := sumSizes p.managed

/-- `MemoryPlan::is_available(range)`: one bank holds the range
(`MemoryPlan.containsRam`) and no reservation touches it. -/
def MemoryPlan.isAvailable (p : MemoryPlan) (s : Span) : Bool :=
  p.containsRam s && !p.reservations.any (·.touches s)

/-- `MemoryPlan::permits_backing(range)`: a managed bank holds the range and
it is available (`MemoryPlan.isAvailable`). -/
def MemoryPlan.permitsBacking (p : MemoryPlan) (s : Span) : Bool :=
  inOneRange p.managed s && p.isAvailable s

/-- The usable ranges of one managed bank that ends at `stop`, from the
cursor `cursor`, with at most `fuel` more steps. At or past the end, none. A
cursor inside a reservation moves to the furthest end of the reservations
that hold it, or to the end of the bank. Otherwise the range from the cursor
to the nearest start of a reservation above it, or to the end of the bank, is
usable, and the cursor moves to its end. Each step either moves the cursor
past a reservation, which never holds it again, or ends a range at the end of
the bank or at the start of a reservation, which the next step moves past, so
`2 * R + 2` steps suffice for `R` reservations; out of fuel, none more, which
`MemoryPlan.availableRanges` never reaches. -/
def usableFrom (exclusions : List Span) (stop : Nat) : (fuel cursor : Nat) → List Span
  | 0, _ => []
  | fuel + 1, cursor =>
    if stop ≤ cursor then []
    else
      let holding := exclusions.filter fun r => r.start.toNat ≤ cursor && cursor < r.endNat
      if holding.isEmpty then
        let next := exclusions.foldl
          (fun e r => if cursor < r.start.toNat then min e r.start.toNat else e) stop
        spanBetween cursor next :: usableFrom exclusions stop fuel next
      else
        usableFrom exclusions stop fuel (min stop (holding.foldl (fun e r => max e r.endNat) cursor))

/-- `MemoryPlan::available_ranges`: the usable ranges, the managed banks
without the union of the reservations, in address order. Each is a maximal
range of whole pages inside one managed bank, so none bridges two banks or a
hole. -/
def MemoryPlan.availableRanges (p : MemoryPlan) : List Span :=
  p.managed.flatMap fun b =>
    usableFrom p.reservations b.endNat (2 * p.reservations.length + 2) b.start.toNat

end Krepi.Spec.Fdt
