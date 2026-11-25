module

public import Krepi.Spec.PageTables.Tokens

/-!
# Page tables: specification tests

The specification tests of the `page-tables` component: for each requirement
of `docs/domains/memory/page-tables/requirements.md`, PGT-R01 to PGT-R12, one
input that the specification must accept, with the result that it must give,
and one that it must reject, with the error that it must give. Each test is a
proposition on concrete states and inputs, and a theorem below
`Krepi.Proofs.PageTables.Stp` proves it. Each instantiates the criterion of
its requirement, the sentence of the requirement that begins "The criterion:",
and its docstring quotes the words of that sentence that it instantiates.

The expected results are literals written from the requirements and the
contract: the descriptors from the rows of the kind table of `Descriptors and
attributes`, the plans from the rules of `Write plans and publication`, the
counts of the direct maps of the Pi 5 models from the table of `Table pool`,
and the outputs of the rows of the frozen vectors. None is computed by the
specification. Where the criterion is that the frozen vectors hold, the test
takes the input of a vector of the requirement's evidence, named in its
docstring, and states the outputs of its row together with the state that
the row reads. Where a test states the state before a refused call, that
state is the one that the refusal leaves: a refused entry gives an error and
no state and no plan.

Three requirements have no rejection of their own, since what they rule out
is an outcome and not an input. PGT-R01's descriptors are a total function of
a kind and an address; its rejecting test takes the rule that every bit of a
leaf outside its row and its output address is 0, on an address whose every
bit is set. PGT-R05 forbids a direct address for an excluded page; its
rejecting test is a direct map that succeeds, with the counts of the usable
pages, on which `lookup_page` refuses every excluded page with `NotMapped`.
PGT-R07's plans have no failure; its rejecting test takes the rule that a
plan for the kernel tables writes only invalid entries: the fill of a valid
entry of the lower kernel set is refused. Each of the three would fail for a
specification that accepted the outcome.

The sets of the tests hold at most 10 tables, the kernel sets the 32 and 80
tables of their pools, and the tables of page ownership a few extents, except
where the criterion names a size: the 4,096 blocks of 8 GiB in 9 tables of
PGT-R03; the RAM of the five Pi 5 models, up to 16 GiB, 8,188 blocks and 581
pages, of the accepting test of PGT-R05; and the direct map of exactly 80
tables and the table of exactly 160 extents and 132 exclusions of PGT-R11,
whose inputs `PhysRange::new` builds.
-/

@[expose] public section

namespace Krepi.SpecTests.PageTables

open Krepi.Spec Krepi.Spec.PageTables

/-! ## Helpers -/

/-- The base of the pools of the tests, `0x1_0000_0000`, as in the vectors of
`src/arch/aarch64/paging/tests.rs`. -/
def BASE : UInt64 := 0x1_0000_0000

/-- The base of the pools of the direct maps of the tests, `0x8_0000`, as in
the vectors of `src/platform/mapping.rs`. -/
def DM_BASE : UInt64 := 0x8_0000

/-- The physical width of the tests, 40, that of the Cortex-A76. -/
def BITS : UInt8 := 40

/-- A set of region `r` and `N` tables that `Tables::new` makes from storage
that is zero in all its tables. -/
def newSet (r : Region) (N : Nat) : Tables r N := Tables.new (Pool.zero N)

/-- `map_page(v, p, k)` on the set at `base`, `BASE` unless given, and `BITS`,
with its plan executed on the pool, as its caller does before anything else
runs on the set. -/
def withPage (s : Tables r N) (v p : UInt64) (k : Kind) (base : UInt64 := BASE) :
    Except TableError (Tables r N) :=
  (s.mapPage v p k base BITS).map fun (t, plan) => t.apply plan

/-- `map_block(v, p)` on the set at `BASE` and `BITS`, with its plan
executed. -/
def withBlock (s : Tables r N) (v p : UInt64) : Except TableError (Tables r N) :=
  (s.mapBlock v p BASE BITS).map fun (t, plan) => t.apply plan

/-- The physical range `[start, start + len)` of a test, for a length that is
not 0 and an end below $2^{64}$, which `decide` checks where the test writes
the range. -/
def range (start len : Nat) (h : 0 < len ∧ start + len < 2 ^ 64 := by decide) : PhysRange :=
  ⟨UInt64.ofNatLT start (by unfold UInt64.size; omega),
    UInt64.ofNatLT len (by unfold UInt64.size; omega),
    fun h0 => by
      have := congrArg UInt64.toNat h0
      simp only [UInt64.toNat_ofNatLT, UInt64.toNat_zero] at this
      omega,
    by simp only [UInt64.toNat_ofNatLT]; omega⟩

/-- A table of page ownership of extent capacity 8, the capacity of the
prototype's tests (`PageAllocator::<8>`), and the exclusion capacity of the
core. -/
abbrev Table8 := Ownership 8 EXCLUSION_RECORDS

/-- The result of `publish` or `cancel` without the value that a refusal hands
back. -/
def dropReturned : Except (OwnershipError × β) α → Except OwnershipError α
  | .ok a => .ok a
  | .error (e, _) => .error e

/-- The nine kinds, in the order of the kind table. -/
def kinds : List Kind :=
  [.readExecute, .readOnly, .readWrite, .kernelPrivateReadWrite, .device,
    .userReadExecute, .userReadOnly, .userReadWrite, .userDevice]

/-! ## PGT-R01: descriptor kinds -/

/-- **PGT-R01, accepted.** Criterion: "the descriptor of every kind equals the
bits of its row, written from the Arm Architecture Reference Manual, and the
frozen vectors that read descriptor bits hold". The descriptors of the nine
kinds at the output address `0x10_0800_0000` of `pt-01` are the bits of their
rows, AP[2:1] at bits 7 and 6, AttrIndx at 2 to 4, SH at 8 and 9, AF at 10,
nG at 11, PXN at 53 and UXN at 54, with `0b11` in bits 1 and 0; the block
descriptor of `ReadWrite` at `0x1_0000_0000` is that of a page with bit 1
clear. The leaves that the sets write are those descriptors: `pt-01` maps
`0x2_0000_0000` to `0x10_0800_0000` as `ReadOnly` in a lower set of 6 tables,
and `lookup_page` gives its descriptor; `pt-15` maps the block of
`0xffff_ff81_0000_0000` to `0x1_0000_0000` in an upper set of 3 tables, and
`lookup_block` gives its descriptor.
Feature: `krepi.kernel.kernel-memory`. -/
def DescriptorsFollowKindRows : Prop :=
  kinds.map (descriptor · 0x10_0800_0000) =
    [0x40_0010_0800_0787, 0x60_0010_0800_0787, 0x60_0010_0800_0707, 0x60_0010_0800_0f07,
      0x60_0010_0800_0403, 0x20_0010_0800_0fc7, 0x60_0010_0800_0fc7, 0x60_0010_0800_0f47,
      0x60_0010_0800_0c43] ∧
  blockDescriptor 0x1_0000_0000 = 0x60_0001_0000_0705 ∧
  ((withPage (newSet .lower 6) 0x2_0000_0000 0x10_0800_0000 .readOnly).bind
      (·.lookupPage 0x2_0000_0000 BASE BITS)) = .ok 0x60_0010_0800_0787 ∧
  ((withBlock (newSet .upper 3) 0xffff_ff81_0000_0000 0x1_0000_0000).bind
      (·.lookupBlock 0xffff_ff81_0000_0000 BASE BITS)) = .ok 0x60_0001_0000_0705

/-- **PGT-R01, rejected.** Criterion: "the descriptor of every kind equals the
bits of its row", with the requirement's "every other bit 0". The rule has no
rejection of its own, since every kind and every address have a descriptor;
this test rejects the other bits of the address. At the output address
`0xffff_ffff_ffff_ffff`, whose bits 0 to 11 lie where AttrIndx, AP, SH, AF and
nG lie and whose bits 48 to 63 where PXN and UXN lie, the descriptor of each
kind holds the bits of its row and bits 12 to 47 of the address, and no other
bit, and the block descriptor bits 21 to 47: a descriptor that let a bit of the
address through would be writable and executable, or of another kind, or
hold a bit that the kind table does not name.
Feature: `krepi.kernel.kernel-memory`. -/
def DescriptorKeepsOnlyItsBits : Prop :=
  kinds.map (descriptor · 0xffff_ffff_ffff_ffff) =
    [0x40_ffff_ffff_f787, 0x60_ffff_ffff_f787, 0x60_ffff_ffff_f707, 0x60_ffff_ffff_ff07,
      0x60_ffff_ffff_f403, 0x20_ffff_ffff_ffc7, 0x60_ffff_ffff_ffc7, 0x60_ffff_ffff_ff47,
      0x60_ffff_ffff_fc43] ∧
  blockDescriptor 0xffff_ffff_ffff_ffff = 0x60_ffff_ffe0_0705

/-! ## PGT-R02: mapping and looking up a page -/

/-- **PGT-R02, accepted.** Criterion: "the frozen vectors hold", here `pt-03`
and `pt-14`: in a lower set of 3 tables, `0x4000_0000` to itself as
`ReadWrite` uses 3 tables, the root, a level 2 and a level 3 table, and
`lookup_page` gives its descriptor; in an upper set of 3 tables,
`0xffff_ff80_0000_0000`, the first address of the upper region, to
`0x1_0000_0000` as `ReadWrite` does the same.
Feature: `krepi.kernel.kernel-memory`. -/
def MapPageThenLookup : Prop :=
  (withPage (newSet .lower 3) 0x4000_0000 0x4000_0000 .readWrite).map
      (fun s => (s.usedTables, s.lookupPage 0x4000_0000 BASE BITS)) =
    .ok (3, .ok 0x60_0000_4000_0707) ∧
  (withPage (newSet .upper 3) 0xffff_ff80_0000_0000 0x1_0000_0000 .readWrite).map
      (fun s => (s.usedTables, s.lookupPage 0xffff_ff80_0000_0000 BASE BITS)) =
    .ok (3, .ok 0x60_0001_0000_0707)

/-- **PGT-R02, rejected.** Criterion: "the frozen vectors hold, with the
tables and the count of tables in use unchanged after every refusal", here
`pt-03`: on the set of `MapPageThenLookup`, the same address to `0x4000_1000`
as `Device`, an address that a page already maps, is refused with
`AlreadyMapped`, where a remapping would replace the leaf; the refusal gives
no set and no plan, so the set stays the one before the call, whose
descriptor of `0x4000_0000` and count of 3 tables the test states.
Feature: `krepi.kernel.kernel-memory`. -/
def MapPageRefusesMappedPage : Prop :=
  (withPage (newSet .lower 3) 0x4000_0000 0x4000_0000 .readWrite).map
      (fun s => (s.mapPage 0x4000_0000 0x4000_1000 .device BASE BITS,
        s.lookupPage 0x4000_0000 BASE BITS, s.usedTables)) =
    .ok (.error .alreadyMapped, .ok 0x60_0000_4000_0707, 3)

/-! ## PGT-R03: blocks -/

/-- The upper set of 9 tables of `pt-17` after the first `count` blocks, each
`0xffff_ff80_0000_0000` plus `pa` to `pa` for `pa` the multiples of 2 MiB from
0, in this order; the error of the first block refused. -/
def blocksFromZero (count : Nat) : Except TableError (Tables .upper 9) :=
  (List.range count).foldlM
    (fun s i => withBlock s (DIRECT_BASE ||| UInt64.ofNat (i * BLOCK_SIZE)) (UInt64.ofNat (i * BLOCK_SIZE)))
    (newSet .upper 9)

/-- The physical addresses of the blocks that `pt-17` looks up: the first, the
last below 1 GiB, the first of the second 1 GiB, the first above 4 GiB and the
last below 8 GiB. -/
def pt17Lookups : List UInt64 := [0x0, 0x3fe0_0000, 0x4000_0000, 0x1_0000_0000, 0x1_ffe0_0000]

/-- **PGT-R03, accepted.** Criterion: "4,096 blocks in a pool of 9 tables",
`pt-17`: the 4,096 blocks of `blocksFromZero` map the 8 GiB from 0, across the
boundaries of 1 GiB and of 4 GiB, with 9 tables in use, the root and 8 level 2
tables; `lookup_block` at the blocks of `pt17Lookups` gives the block
descriptor of each at its own physical address. The input is the criterion's
own: 4,096 writes of a block.
Feature: `krepi.kernel.kernel-memory`. -/
def EightGibOfBlocksInNineTables : Prop :=
  (blocksFromZero 4096).bind (fun s =>
      (pt17Lookups.mapM fun pa => s.lookupBlock (DIRECT_BASE ||| pa) BASE BITS).map
        (fun ds => (s.usedTables, ds))) =
    .ok (9, [0x60_0000_0000_0705, 0x60_0000_3fe0_0705, 0x60_0000_4000_0705, 0x60_0001_0000_0705,
      0x60_0001_ffe0_0705])

/-- **PGT-R03, rejected.** Criterion: "the refusal of one more with
`OutOfTables`", `pt-17`: on the set of the 4,096 blocks, the block of
`0x2_0000_0000`, in the ninth 1 GiB slot, would need a tenth table and is
refused with `OutOfTables`. The input is the criterion's own.
Feature: `krepi.kernel.kernel-memory`. -/
def BlockBeyondNineTablesRefused : Prop :=
  (blocksFromZero 4096).map (fun s =>
      s.mapBlock (DIRECT_BASE ||| 0x2_0000_0000) 0x2_0000_0000 BASE BITS) =
    .ok (.error .outOfTables)

/-! ## PGT-R04: unmapping and reset -/

/-- **PGT-R04, accepted.** Criterion: "the frozen vectors hold, and the plan of
`unmap_page` equals the order of the contract", `pt-09`: in a lower set of 4
tables with `0x0` to `0x1000` as `ReadWrite` and `0x20_0000` to `0x2000` as
`UserReadWrite`, `unmap_page` of `0x0` returns the page `0x1000` with the plan
`Store(t, i, 0)` of its leaf, entry 0 of table 2, and then `Invalidate(0x0)`;
after it 4 tables stay in use, `0x0` is `NotMapped` and `0x20_0000` keeps its
descriptor. `reset` then gives the plan of a `Zero` of each of the 4 tables in
use, in index order, and leaves 1 table in use and every entry 0; after it
`0x4000_0000` to `0x8000` as `UserReadExecute` uses 3 tables and `lookup_page`
gives its descriptor.
Feature: `krepi.kernel.kernel-memory`. -/
def UnmapAndResetFollowContract : Prop :=
  (do
    let s ← withPage (newSet .lower 4) 0x0 0x1000 .readWrite
    let s ← withPage s 0x20_0000 0x2000 .userReadWrite
    let (plan, page) ← s.unmapPage 0x0 BASE BITS
    let s := s.apply plan
    let (r, resetPlan) := s.reset
    let r := r.apply resetPlan
    let again ← withPage r 0x4000_0000 0x8000 .userReadExecute
    pure (plan, page, s.usedTables, s.lookupPage 0x0 BASE BITS, s.lookupPage 0x20_0000 BASE BITS,
      resetPlan, r.usedTables, r.pool.toList.all (·.toList.all (· == 0)), again.usedTables,
      again.lookupPage 0x4000_0000 BASE BITS)) =
    .ok ([.store 2 0 0x0, .invalidate 0x0], 0x1000, 4, .error .notMapped, .ok 0x60_0000_0000_2f47,
      [.zero 0, .zero 1, .zero 2, .zero 3], 1, true, 3, .ok 0x20_0000_0000_8fc7)

/-- **PGT-R04, rejected.** Criterion: "the frozen vectors hold", here `pt-05`
and the requirement's refusal of "an address without a page leaf with
`NotMapped`": in a lower set of 4 tables with `0x0` to `0x1000` as
`ReadWrite` and `0x1000` to `0x2000` as `ReadOnly`, once the plan of
`unmap_page` of `0x0` has run, a second `unmap_page` of `0x0` is refused with
`NotMapped`.
Feature: `krepi.kernel.kernel-memory`. -/
def UnmapRefusesUnmappedPage : Prop :=
  (do
    let s ← withPage (newSet .lower 4) 0x0 0x1000 .readWrite
    let s ← withPage s 0x1000 0x2000 .readOnly
    let (plan, _) ← s.unmapPage 0x0 BASE BITS
    pure ((s.apply plan).unmapPage 0x0 BASE BITS)) =
    .ok (.error .notMapped)

/-! ## PGT-R05: kernel direct map -/

/-- A Pi 5 model in a test: its RAM banks, as the fdt contract gives them, and
the tables, blocks and pages of its direct map in the table of `Table pool`. -/
structure Pi5Model where
  ram : List Fdt.Span
  tables : Nat
  blocks : Nat
  pages : Nat

/-- The five Pi 5 models, 1, 2, 4, 8 and 16 GB, with the rows of the table of
`Table pool`: the RAM below 1 GiB less 4 MiB, then the inferred or, for 8 GB,
measured banks above it. -/
def pi5Models : List Pi5Model :=
  [⟨[⟨0, 0x3fc0_0000⟩], 4, 508, 581⟩,
   ⟨[⟨0, 0x3fc0_0000⟩, ⟨0x4000_0000, 0x4000_0000⟩], 5, 1020, 581⟩,
   ⟨[⟨0, 0x3fc0_0000⟩, ⟨0x4000_0000, 0xc000_0000⟩], 7, 2044, 581⟩,
   ⟨[⟨0, 0x3fc0_0000⟩, ⟨0x4000_0000, 0xc000_0000⟩, ⟨0x1_0000_0000, 0x1_0000_0000⟩], 11, 4092, 581⟩,
   ⟨[⟨0, 0x3fc0_0000⟩, ⟨0x4000_0000, 0xc000_0000⟩, ⟨0x1_0000_0000, 0x3_0000_0000⟩], 19, 8188, 581⟩]

/-- The boot memory map of a Pi 5 model, `MemoryPlan::all_ram` of its banks
with the exclusions that `Table pool` gives, measured on the 8 GB model: the
image `[0x8_0000, 0x1a_7000)` and the device tree `[0x20_0000, 0x21_3ad4)` as
boot storage, and the firmware's `atf@0` reservation `[0, 0x8_0000)`, with
`no-map`. -/
def pi5Memory (ram : List Fdt.Span) : Except Fdt.PlanError Fdt.MemoryPlan :=
  Fdt.MemoryPlan.allRam ram [⟨0x8_0000, 0x12_7000⟩, ⟨0x20_0000, 0x1_3ad4⟩] [⟨⟨0, 0x8_0000⟩, true, false⟩]

/-- **PGT-R05, accepted.** Criterion: "the four other Pi 5 models give the
counts of tables, blocks and pages of the contract", here with the 8 GB model
as well: for each model, `direct_map` of its boot memory map into a new set of
the 80 tables of the direct map's pool succeeds, with the tables in use, the
blocks and the pages of its row. The inputs are the RAM of the models
themselves, up to 16 GiB.
Feature: `krepi.kernel.kernel-memory`. -/
def DirectMapCountsOfPi5Models : Prop :=
  ∀ m ∈ pi5Models,
    (pi5Memory m.ram).toOption.map (fun memory =>
        ((newSet .upper DIRECT_MAP_TABLES).directMap memory DM_BASE BITS).map
          (fun (s, plan) => (s.usedTables, plan.counts.blocks, plan.counts.pages))) =
      some (.ok (m.tables, m.blocks, m.pages))

/-- A boot memory map with an excluded page of each kind: the managed window
`[0x4000_0000, 0x40a0_0000)` of the bank of the same span; a second bank
`[0x4100_0000, 0x4120_0000)` outside the window, beyond a hole; the image
`[0x4000_0000, 0x4000_1000)`, the device tree `[0x4000_2800, 0x4000_2900)` and
the boot bundle `[0x4000_8000, 0x4000_9000)` as boot storage; and the
firmware reservations `[0x4000_4000, 0x4000_5000)`, `no-map`, and
`[0x4000_5fff, 0x4000_6001)`, `reusable`, which touches two pages. -/
def excludedMemory : Except Fdt.PlanError Fdt.MemoryPlan :=
  Fdt.MemoryPlan.new ⟨0x4000_0000, 0xa0_0000⟩ [⟨0x4000_0000, 0xa0_0000⟩, ⟨0x4100_0000, 0x20_0000⟩]
    [⟨0x4000_0000, 0x1000⟩, ⟨0x4000_2800, 0x100⟩, ⟨0x4000_8000, 0x1000⟩]
    [⟨⟨0x4000_4000, 0x1000⟩, true, false⟩, ⟨⟨0x4000_5fff, 0x2⟩, false, true⟩]

/-- The physical pages of `excludedMemory` that the direct map must not map:
the image, the device tree, the two firmware reservations, the boot bundle,
the first page of the hole between the banks and the first page of the bank
outside the window. -/
def excludedPages : List UInt64 :=
  [0x4000_0000, 0x4000_2000, 0x4000_4000, 0x4000_5000, 0x4000_6000, 0x4000_8000, 0x40a0_0000,
    0x4100_0000]

/-- **PGT-R05, rejected.** Criterion: "every page below 8 GiB is mapped to
itself or absent exactly as an independent page model says", with the
requirement's "No page of a firmware reservation, `no-map` or not, of the
image, of the device tree, of the boot bundle or of another boot storage, no
hole between banks and no RAM outside the managed banks has a direct
address", on the boot memory map `excludedMemory`. `direct_map` into an upper
set of 4 tables succeeds with the usable pages alone: 4 blocks and 506 pages,
`0x9f_a000` bytes, the 10 MiB of the window less the 6 pages of boot storage
and firmware. Once its plan has run, `lookup_page` refuses each page of
`excludedPages` with `NotMapped`, where a direct map that mapped it would
give a descriptor. And of the requirement's "A map that needs more tables
than the pool has, or a range beyond $2^{39}$, fails before any write", the
range: on the boot memory map of one bank `[0x7f_ffe0_0000, +4 MiB)` across
$2^{39}$, `direct_map` fails with `AddressWidth` and gives no plan.
Feature: `krepi.kernel.kernel-memory`. -/
def DirectMapOmitsExcludedPages : Prop :=
  excludedMemory.toOption.map (fun memory =>
      ((newSet .upper 4).directMap memory DM_BASE BITS).map fun (s, plan) =>
        (plan.counts, excludedPages.map fun pa => (s.apply plan).lookupPage (DIRECT_BASE ||| pa) DM_BASE BITS)) =
    some (.ok (⟨0x9f_a000, 4, 506⟩, List.replicate 8 (.error .notMapped))) ∧
  (Fdt.MemoryPlan.allRam [⟨0x7f_ffe0_0000, 0x40_0000⟩] [⟨0x7f_ffe0_0000, 0x1000⟩] []).toOption.map
      (fun memory => ((newSet .upper 4).directMap memory DM_BASE BITS).map (·.2)) =
    some (.error .addressWidth)

/-! ## PGT-R06: kernel mappings of the image -/

/-- The layout of an image on QEMU virt in a test: its text
`[0x4020_0000, 0x4020_2000)` `ReadExecute`, its read-only data
`[0x4020_2000, 0x4020_3000)` `ReadOnly`, its data `[0x4020_3000, 0x4020_4000)`
and a stack `[0x4020_5000, 0x4020_6000)` `ReadWrite`, with the guard page
`0x4020_4000` below the stack; the device tree `[0x4000_0000, 0x4000_1000)`
`ReadOnly`; and the registers of the interrupt controller
`[0x0800_0000, 0x0800_1000)` and of the console `[0x0900_0000, 0x0900_1000)`
`Device`. -/
def qemuLayout : Layout :=
  ⟨[⟨range 0x4020_0000 0x2000, .readExecute, by decide⟩, ⟨range 0x4020_2000 0x1000, .readOnly, by decide⟩,
    ⟨range 0x4020_3000 0x1000, .readWrite, by decide⟩, ⟨range 0x4020_5000 0x1000, .readWrite, by decide⟩,
    ⟨range 0x4000_0000 0x1000, .readOnly, by decide⟩, ⟨range 0x0800_0000 0x1000, .device, by decide⟩,
    ⟨range 0x0900_0000 0x1000, .device, by decide⟩], [0x4020_4000], by decide⟩

/-- The pages of `qemuLayout` that the test looks up: the two of the text, the
read-only data, the data, the stack, the device tree, the interrupt
controller, the console, and the guard. -/
def qemuLayoutPages : List UInt64 :=
  [0x4020_0000, 0x4020_1000, 0x4020_2000, 0x4020_3000, 0x4020_5000, 0x4000_0000, 0x0800_0000,
    0x0900_0000, 0x4020_4000]

/-- **PGT-R06, accepted.** Criterion: "on QEMU virt with the MMU on, a write
to a `ReadOnly` page, an execution from an execute-never page and an access
to the guard each take the fault of the contract, and a `Device` page of the
console is written", on the host as the descriptors that give those faults
and that write. `kernel_map` of `qemuLayout` into a new lower set of the 32
tables of the lower kernel set's pool succeeds with 7 tables in use, as an
image within one 2 MiB block needs (`Table pool`); once its plan has run,
`lookup_page` gives each page of the layout at its physical address with the
descriptor of its kind: the text `ReadExecute`, the read-only data and the
device tree `ReadOnly`, with AP[2] set, so that a write faults; the data and
the stack `ReadWrite`, with PXN and UXN set, so that an execution faults; the
interrupt controller and the console `Device`, AP[2:1] `0b00`, written; and
the guard `NotMapped`, so that an access faults.
Feature: `krepi.kernel.kernel-memory`. -/
def KernelMapGivesKindsAndGuard : Prop :=
  ((newSet .lower KERNEL_TABLES).kernelMap qemuLayout BASE BITS).map
      (fun (s, plan) => (s.usedTables, qemuLayoutPages.map fun v => (s.apply plan).lookupPage v BASE BITS)) =
    .ok (7, [.ok 0x40_0000_4020_0787, .ok 0x40_0000_4020_1787, .ok 0x60_0000_4020_2787,
      .ok 0x60_0000_4020_3707, .ok 0x60_0000_4020_5707, .ok 0x60_0000_4000_0787,
      .ok 0x60_0000_0800_0403, .ok 0x60_0000_0900_0403, .error .notMapped])

/-- A layout whose text `[0x4020_0000, 0x4020_2000)`, `ReadExecute`, and data
`[0x4020_1000, 0x4020_3000)`, `ReadWrite`, both start and end on a page
boundary and share the page `0x4020_1000`. -/
def sharedPageLayout : Layout :=
  ⟨[⟨range 0x4020_0000 0x2000, .readExecute, by decide⟩, ⟨range 0x4020_1000 0x2000, .readWrite, by decide⟩], [],
    by decide⟩

/-- **PGT-R06, rejected.** Criterion: "on the host, a layout whose text and
data share a page is refused": `kernel_map` of `sharedPageLayout` into a new
lower set of 32 tables is refused with `AlreadyMapped`, so no plan maps the
page `0x4020_1000` writable and executable.
Feature: `krepi.kernel.kernel-memory`. -/
def KernelMapRefusesSharedPage : Prop :=
  ((newSet .lower KERNEL_TABLES).kernelMap sharedPageLayout BASE BITS).map Prod.snd = .error .alreadyMapped

/-! ## PGT-R07: write plans and publication -/

/-- The layout of the plan of `kernel_map` in `PlansFollowContractOrder`:
`[0x4000_0000, 0x4000_2000)` `ReadExecute` and `[0x4020_0000, 0x4020_1000)`
`ReadWrite`, two pages in one 2 MiB slot and one in the next, under one level
2 table. -/
def planLayout : Layout :=
  ⟨[⟨range 0x4000_0000 0x2000, .readExecute, by decide⟩, ⟨range 0x4020_0000 0x1000, .readWrite, by decide⟩], [],
    by decide⟩

/-- The boot memory map of the plan of `direct_map` in
`PlansFollowContractOrder`: the bank `[0x4000_0000, 0x4040_0000)` with the boot
storage `[0x4000_0000, 0x401f_e000)`, which leaves the usable range
`[0x401f_e000, 0x4040_0000)`, two pages and a block. -/
def planMemory : Except Fdt.PlanError Fdt.MemoryPlan :=
  Fdt.MemoryPlan.allRam [⟨0x4000_0000, 0x40_0000⟩] [⟨0x4000_0000, 0x1f_e000⟩] []

/-- **PGT-R07, accepted.** Criterion: "the plans of `map_page`, `map_block`,
`unmap_page`, `clone_kernel_from`, `kernel_map` and `direct_map` equal the
order of the contract, written from it". On new sets at `BASE`, or `DM_BASE`
for the direct map, the plans are, as `Write plans and publication` writes
them:

- `map_page` of `0x4020_3000` in a lower set of 3 tables, a page that needs a
  new level 2 table 1 and a new level 3 table 2: `Zero(2)`, the `Store` of the
  page into entry 3, `Zero(1)`, the `Store` of the table descriptor of table 2
  into entry 1, `Fence`, the `Store` of the table descriptor of table 1 into
  entry 1 of the root, `Sync`;
- `map_block` of `pt-15` in an upper set of 3 tables: `Zero(1)`, the `Store`
  of the block, `Fence`, the `Store` into entry 4 of the root, `Sync`;
- `unmap_page` of `0x0` in the set of `pt-09`: `Store(2, 0, 0)`, then
  `Invalidate(0x0)`;
- the copy of a lower set of 3 tables with `0x4000` to `0x4000_0000` as
  `ReadExecute` into a new set at `0x1_0000_3000`: `Zero(0)`, the target's one
  table in use, the `Store` of each valid entry of the source into the
  target's table of its index, the table descriptors pointing into the
  target's pool, by table and then entry index, `Sync`;
- `kernel_map` of `planLayout` and `direct_map` of `planMemory`: each new
  level 3 table zeroed and filled, then the new level 2 table zeroed and
  filled with its entries in index order, one `Fence`, the one `Store` that
  makes the tables reachable from the root, `Sync`.
Feature: `krepi.kernel.kernel-memory`. -/
def PlansFollowContractOrder : Prop :=
  ((newSet .lower 3).mapPage 0x4020_3000 0x4020_3000 .readWrite BASE BITS).map Prod.snd =
    .ok [.zero 2, .store 2 3 0x60_0000_4020_3707, .zero 1, .store 1 1 0x1_0000_2003, .fence,
      .store 0 1 0x1_0000_1003, .sync] ∧
  ((newSet .upper 3).mapBlock 0xffff_ff81_0000_0000 0x1_0000_0000 BASE BITS).map Prod.snd =
    .ok [.zero 1, .store 1 0 0x60_0001_0000_0705, .fence, .store 0 4 0x1_0000_1003, .sync] ∧
  ((do
      let s ← withPage (newSet .lower 4) 0x0 0x1000 .readWrite
      let s ← withPage s 0x20_0000 0x2000 .userReadWrite
      s.unmapPage 0x0 BASE BITS).map Prod.fst) =
    .ok [.store 2 0 0x0, .invalidate 0x0] ∧
  ((withPage (newSet .lower 3) 0x4000 0x4000_0000 .readExecute).bind fun source =>
      ((newSet .lower 3).cloneKernelFrom source BASE 0x1_0000_3000 BITS).map Prod.snd) =
    .ok [.zero 0, .store 0 0 0x1_0000_4003, .store 1 0 0x1_0000_5003, .store 2 4 0x40_0000_4000_0787,
      .sync] ∧
  ((newSet .lower 8).kernelMap planLayout BASE BITS).map Prod.snd =
    .ok [.zero 2, .store 2 0 0x40_0000_4000_0787, .store 2 1 0x40_0000_4000_1787, .zero 3,
      .store 3 0 0x60_0000_4020_0707, .zero 1, .store 1 0 0x1_0000_2003, .store 1 1 0x1_0000_3003,
      .fence, .store 0 1 0x1_0000_1003, .sync] ∧
  planMemory.toOption.map (fun memory => ((newSet .upper 4).directMap memory DM_BASE BITS).map Prod.snd) =
    some (.ok [.zero 2, .store 2 510 0x60_0000_401f_e707, .store 2 511 0x60_0000_401f_f707, .zero 1,
      .store 1 0 0x8_2003, .store 1 1 0x60_0000_4020_0705, .fence, .store 0 1 0x8_1003, .sync])

/-- The layout of the kernel tables in `KernelFillRefusesValidEntry`: the
text page `[0x4020_0000, 0x4020_1000)` `ReadExecute` and the data page
`[0x4020_1000, 0x4020_2000)` `ReadWrite`. -/
def fillLayout : Layout :=
  ⟨[⟨range 0x4020_0000 0x1000, .readExecute, by decide⟩, ⟨range 0x4020_1000 0x1000, .readWrite, by decide⟩], [],
    by decide⟩

/-- The shared state once the boot CPU has built the lower kernel set from
`fillLayout` with `kernel_map`, on the zero pools of the boot, and has turned
the MMU on; none when a transaction is not enabled or fails. -/
def bootedShared : Option (Shared EXTENTS EXCLUSION_RECORDS) := do
  let s : Shared EXTENTS EXCLUSION_RECORDS :=
    Shared.boot BootCpu.boot (Pool.zero KERNEL_TABLES) (Pool.zero DIRECT_MAP_TABLES)
  let (s, _) ← (s.buildKernelMap BootCpu.boot fillLayout BASE BITS).bind Except.toOption
  s.enable BootCpu.boot

/-- **PGT-R07, rejected.** Criterion: "the plans ... equal the order of the
contract", with the requirement's "a plan for the kernel tables writes only
invalid entries". The plans have no failure of their own; this test rejects
a plan that would write a valid entry of the kernel tables. On
`bootedShared`, the fill under the token of the kernel tables of the data
page `0x4020_1000`, which `kernel_map` mapped, with the frame `0x4030_0000` as
`Device`, is refused with `AlreadyMapped` and gives no plan.
Feature: `krepi.kernel.kernel-memory`. -/
def KernelFillRefusesValidEntry : Prop :=
  (bootedShared.bind fun s =>
      s.fillKernel KernelTablesToken.executing 0x4020_1000 0x4030_0000 .device BASE BITS).map
      (·.map Prod.snd) =
    some (.error .alreadyMapped)

/-! ## PGT-R08: one owner for every page -/

/-- A board shape in a test: the RAM banks, the boot storage, the image first,
and the firmware reservations that the board gives the boot memory map; the
managed banks and the exclusions that the boot wiring gives
`Ownership::new`, the pages of each span of boot storage and of each
reservation with its owner; the usable ranges, each with the index of its
bank; and owners of pages. -/
structure BoardShape where
  ram : List Fdt.Span
  boot : List Fdt.Span
  firmware : List Fdt.ReservedRegion
  banks : List PhysRange
  exclusions : List Exclusion
  usable : List (PhysRange × Nat)
  owners : List (UInt64 × Option Owner)

/-- The exclusions of every Pi 5 model, those of `pi5Memory` by their pages:
the image, the device tree rounded out to `[0x20_0000, 0x21_4000)` and
`atf@0`. -/
def pi5Exclusions : List Exclusion :=
  [⟨range 0x8_0000 0x12_7000, .image⟩, ⟨range 0x20_0000 0x1_4000, .bootStorage⟩,
    ⟨range 0 0x8_0000, .firmware⟩]

/-- The free runs of the first bank of every Pi 5 model, around the image and
the device tree. -/
def pi5FirstBank : List (PhysRange × Nat) :=
  [(range 0x1a_7000 0x5_9000, 0), (range 0x21_4000 0x3f9e_c000, 0)]

/-- The owners of pages of the first bank of every Pi 5 model: `atf@0`, the
image, the first free page, the device tree, the free page after it. -/
def pi5Owners : List (UInt64 × Option Owner) :=
  [(0x0, some (.excluded .firmware)), (0x8_0000, some (.excluded .image)), (0x1a_7000, some .free),
    (0x20_0000, some (.excluded .bootStorage)), (0x21_4000, some .free), (0x3fc0_0000, none)]

/-- A Pi 5 model as a board shape, from its banks above the first, as
`PhysRange` and as spans. -/
def pi5Shape (more : List (Nat × Nat)) (usable : List (PhysRange × Nat)) (banks : List PhysRange) :
    BoardShape :=
  ⟨⟨0, 0x3fc0_0000⟩ :: more.map (fun (a, l) => ⟨UInt64.ofNat a, UInt64.ofNat l⟩),
    [⟨0x8_0000, 0x12_7000⟩, ⟨0x20_0000, 0x1_3ad4⟩], [⟨⟨0, 0x8_0000⟩, true, false⟩],
    range 0 0x3fc0_0000 :: banks, pi5Exclusions, pi5FirstBank ++ usable, pi5Owners⟩

/-- The board shapes: QEMU virt, its bank of 128 MiB at 1 GiB with the image
`[0x4020_0000, 0x4030_0000)` and the device tree `[0x4000_0000, 0x4000_1234)`;
and the five Pi 5 models with the exclusions of `pi5Memory`, whose banks
above the first are free. -/
def boardShapes : List BoardShape :=
  [⟨[⟨0x4000_0000, 0x800_0000⟩], [⟨0x4020_0000, 0x10_0000⟩, ⟨0x4000_0000, 0x1234⟩], [],
     [range 0x4000_0000 0x800_0000],
     [⟨range 0x4020_0000 0x10_0000, .image⟩, ⟨range 0x4000_0000 0x2000, .bootStorage⟩],
     [(range 0x4000_2000 0x1f_e000, 0), (range 0x4030_0000 0x7d0_0000, 0)],
     [(0x4000_0000, some (.excluded .bootStorage)), (0x4000_2000, some .free),
       (0x4020_0000, some (.excluded .image)), (0x4030_0000, some .free), (0x4800_0000, none)]⟩,
   pi5Shape [] [] [],
   pi5Shape [(0x4000_0000, 0x4000_0000)] [(range 0x4000_0000 0x4000_0000, 1)] [range 0x4000_0000 0x4000_0000],
   pi5Shape [(0x4000_0000, 0xc000_0000)] [(range 0x4000_0000 0xc000_0000, 1)] [range 0x4000_0000 0xc000_0000],
   pi5Shape [(0x4000_0000, 0xc000_0000), (0x1_0000_0000, 0x1_0000_0000)]
     [(range 0x4000_0000 0xc000_0000, 1), (range 0x1_0000_0000 0x1_0000_0000, 2)]
     [range 0x4000_0000 0xc000_0000, range 0x1_0000_0000 0x1_0000_0000],
   pi5Shape [(0x4000_0000, 0xc000_0000), (0x1_0000_0000, 0x3_0000_0000)]
     [(range 0x4000_0000 0xc000_0000, 1), (range 0x1_0000_0000 0x3_0000_0000, 2)]
     [range 0x4000_0000 0xc000_0000, range 0x1_0000_0000 0x3_0000_0000]]

/-- The start and the length of a physical range. -/
def pairOf (r : PhysRange) : Nat × Nat := (r.start.toNat, r.len.toNat)

/-- **PGT-R08, accepted.** Criterion: "for the boot memory map of every board
shape, every managed page has exactly one owner, the free pages are exactly
the pages of the direct map". For each board shape, `MemoryPlan::all_ram`
gives the managed banks of the shape and its usable ranges, the pages that
`direct_map` maps; and `Ownership::new` of the arena 1, those banks and the
exclusions of the shape gives the table of the banks, one free extent for
each usable range and no other extent, every exclusion in its record and the
counter at 1. So a page of an extent has the owner free, a page of an
exclusion the owner of its record, and no page both: `owner` gives for the
pages of the shape their owners, `none` for a page of no managed bank.
Feature: `krepi.kernel.kernel-memory`. -/
def OwnershipOfBoardShapes : Prop :=
  ∀ b ∈ boardShapes,
    (Fdt.MemoryPlan.allRam b.ram b.boot b.firmware).toOption.map
        (fun memory => (memory.managed.map fun s => (s.start.toNat, s.size.toNat),
          memory.availableRanges.map fun s => (s.start.toNat, s.size.toNat))) =
      some (b.banks.map pairOf, b.usable.map (pairOf ·.1)) ∧
    (Ownership.new 1 b.banks b.exclusions : Except OwnershipError (Ownership EXTENTS EXCLUSION_RECORDS)).map
        (fun t => (t, b.owners.map fun (q, _) => t.owner q)) =
      .ok (⟨1, b.banks, b.usable.map fun (r, i) => ⟨r, i, .free⟩, b.exclusions, .next 1⟩,
        b.owners.map (·.2))

/-- **PGT-R08, rejected.** Criterion: "every managed page has exactly one
owner", with the requirement's refusal of "overlapping ... banks", `own-17`:
`Ownership::new` of the banks `[0x0, 0x2000)` and `[0x1000, 0x2000)`, which
share the page `0x1000`, in a table of 8 extents, is refused with
`InvalidRange`, where a table of both banks would hold that page in two
extents.
Feature: `krepi.kernel.kernel-memory`. -/
def OwnershipRefusesOverlappingBanks : Prop :=
  (Ownership.new 1 [range 0x0 0x2000, range 0x1000 0x1000] [] : Except OwnershipError Table8) =
    .error .invalidRange

/-! ## PGT-R09: allocation and release -/

/-- The placement of `own-20`: high, in the window `[0x1_0000_1001, 0x1_0000_d001)`,
whose ends are not on pages. -/
def own20Placement : Placement := ⟨.high, some (range 0x1_0000_1001 0xc000)⟩

/-- **PGT-R09, accepted.** Criterion: "the frozen vectors hold", here `own-20`
with the release that ends it: on a table of 8 extents of the arena 1 with
the bank `[0x1_0000_0000, 0x1_0001_0000)`, `choose` of 2 pages at an alignment
of 4 pages for owner 1 with the high placement in the window gives
`[0x1_0000_8000, 0x1_0000_a000)`, the highest aligned range inside the window;
`assign` of it with a failed zeroing is refused with `ZeroFailed`, which
leaves the pages free and consumes no generation, so `choose` for owner 2
gives the same range and `assign` with a completed zeroing holds it for
owner 2 with generation 1 and gives that receipt, the bank split into three
extents; the release of the receipt by owner 2 leaves one free extent of the
whole bank and the counter at 2.
Feature: `krepi.kernel.kernel-memory`. -/
def AllocationTakesWindowAndGeneration : Prop :=
  (do
    let t ← (Ownership.new 1 [range 0x1_0000_0000 0x1_0000] [] : Except OwnershipError Table8)
    let c1 ← t.choose 1 2 4 own20Placement
    let c2 ← t.choose 2 2 4 own20Placement
    let (t2, a) ← t.assign c2 true
    let t3 ← t2.release 2 a
    pure (c1.range, (t.assign c1 false).map Prod.snd, c2.range, a, t2.extents, t3.extents, t3.counter)) =
    .ok (range 0x1_0000_8000 0x2000, .error .zeroFailed, range 0x1_0000_8000 0x2000,
      ⟨1, 2, 1, range 0x1_0000_8000 0x2000⟩,
      [⟨range 0x1_0000_0000 0x8000, 0, .free⟩, ⟨range 0x1_0000_8000 0x2000, 0, .held 2 1 .published⟩,
        ⟨range 0x1_0000_a000 0x6000, 0, .free⟩],
      [⟨range 0x1_0000_0000 0x1_0000, 0, .free⟩], .next 2)

/-- **PGT-R09, rejected.** Criterion: "the frozen vectors hold", here `own-10`
and the requirement's refusal of a release "with a stale receipt": on a table
of 2 extents of the arena 1 with the bank `[0x0, 0x1000)`, owner 3 allocates
the page and releases it; the next allocation of owner 3 takes the same page
with generation 2; the release of the first receipt, of generation 1, is then
refused with `InvalidAllocation`, where a release that read the range and
the owner alone would free the page of the second.
Feature: `krepi.kernel.kernel-memory`. -/
def ReleaseRefusesStaleReceipt : Prop :=
  (do
    let t ← (Ownership.new 1 [range 0x0 0x1000] [] : Except OwnershipError (Ownership 2 EXCLUSION_RECORDS))
    let (t, a) ← t.assign (← t.choose 3 1 1 ⟨.low, none⟩) true
    let t ← t.release 3 a
    let (t, b) ← t.assign (← t.choose 3 1 1 ⟨.low, none⟩) true
    pure (b, t.release 3 a)) =
    .ok (⟨1, 3, 2, range 0x0 0x1000⟩, .error .invalidAllocation)

/-! ## PGT-R10: staged reservation -/

/-- The receipt of the reservation of `own-23`: the arena 7, owner `0xb`,
generation 1 and the pages `[0x0, 0x2000)`. -/
def own23Allocation : Allocation := ⟨7, 0xb, 1, range 0x0 0x2000⟩

/-- **PGT-R10, accepted.** Criterion: "the frozen vectors hold", here
`own-23`: on a table of 8 extents of the arena 7 with the bank
`[0x0, 0x4000)`, owner `0xb` reserves 2 pages and gets the reservation of
`[0x0, 0x2000)` with generation 1, not attempted and without failures, held at
once without a zeroing: the statistics count `0x2000` allocated bytes and 1
allocation. Owner `0x16` then allocates 1 page outside it, `[0x2000, 0x3000)`
with generation 2. After the zeroing, `Reservation::initialized` gives the
packet with no failure, which validates, and its publication by owner `0xb`
gives the receipt of the reservation; after the release of both receipts
the free bytes are `0x4000`.
Feature: `krepi.kernel.kernel-memory`. -/
def ReservationPublishesAfterZeroing : Prop :=
  (do
    let t ← (Ownership.new 7 [range 0x0 0x4000] [] : Except OwnershipError Table8)
    let (t, r) ← t.reserve 0xb 2 1 ⟨.low, none⟩
    let held := (t.stats.allocated, t.stats.allocations)
    let (t, o) ← t.assign (← t.choose 0x16 1 1 ⟨.low, none⟩) true
    let x : Initialized := ⟨own23Allocation, 0⟩
    t.validate 0xb x.allocation .reserved
    let (t, a) ← dropReturned (t.publish 0xb x)
    let t ← t.release 0xb a
    let t ← t.release 0x16 o
    pure (r, held, o, r.initialized true, a, t.stats.free)) =
    .ok (⟨own23Allocation, false, 0⟩, (0x2000, 1), ⟨7, 0x16, 2, range 0x2000 0x1000⟩,
      .packet ⟨own23Allocation, 0⟩, own23Allocation, 0x4000)

/-- The reservation of `own-24` after one failed zeroing: the arena 3, owner 4,
generation 1, the pages `[0x0, 0x2000)`, attempted, with 1 failure. -/
def own24Retained : Reservation := ⟨⟨3, 4, 1, range 0x0 0x2000⟩, true, 1⟩

/-- **PGT-R10, rejected.** Criterion: "the frozen vectors hold", here `own-24`
and the requirement's "a reservation may be cancelled only before any
attempt": on a table of 4 extents of the arena 3 with the bank `[0x0, 0x2000)`,
owner 4 reserves 2 pages; a failed zeroing gives back the reservation,
attempted and with 1 failure; its cancel by owner 4 is refused with
`ZeroFailed` and returns it, where a cancel would free pages whose bytes a
zeroing may have changed.
Feature: `krepi.kernel.kernel-memory`. -/
def CancelRefusesAttemptedReservation : Prop :=
  (do
    let t ← (Ownership.new 3 [range 0x0 0x2000] [] : Except OwnershipError (Ownership 4 EXCLUSION_RECORDS))
    let (t, r) ← t.reserve 4 2 1 ⟨.low, none⟩
    pure (r.initialized false, t.cancel 4 own24Retained)) =
    .ok (.retained own24Retained, .error (.zeroFailed, own24Retained))

/-! ## PGT-R11: capacities -/

/-- A boot memory map of one bank of `count` blocks from 1 GiB whose usable
ranges are the first page of each block: the boot storage takes the rest of
the first block, `[0x4000_1000, 0x4020_0000)`, and one firmware reservation
the rest of each further block. Its direct map needs the root, one level 2
table and a level 3 table for each block, `count + 2` tables. -/
def firstPageOfEachBlock (count : Nat) : Except Fdt.PlanError Fdt.MemoryPlan :=
  Fdt.MemoryPlan.allRam [⟨0x4000_0000, UInt64.ofNat (count * BLOCK_SIZE)⟩] [⟨0x4000_1000, 0x1f_f000⟩]
    ((List.range (count - 1)).map fun i =>
      ⟨⟨UInt64.ofNat (0x4000_0000 + (i + 1) * BLOCK_SIZE + PAGE_SIZE), 0x1f_f000⟩, true, false⟩)

/-- The 28 banks of a table at its capacity of extents, each 1 MiB from
`i * 0x10_0000`, made by `PhysRange::new`. -/
def capacityBanks : Except OwnershipError (List PhysRange) :=
  (List.range 28).mapM fun i => PhysRange.new (UInt64.ofNat (i * 0x10_0000)) 0x10_0000

/-- The 132 firmware exclusions of one page each of a table at its
capacities, made by `PhysRange::new`: the pages 2, 4, 6, 8 and 10 of each of
the banks 0 to 23, and 2, 4 and 6 of each of the banks 24 to 27, which split
the banks into 160 free runs, 6 in each of the first 24 banks and 4 in each
of the last 4. -/
def capacityExclusions : Except OwnershipError (List Exclusion) :=
  ((List.range 28).flatMap fun i =>
      ((if i < 24 then [2, 4, 6, 8, 10] else [2, 4, 6]).map fun j => i * 0x10_0000 + j * PAGE_SIZE)).mapM
    fun a => (PhysRange.new (UInt64.ofNat a) 0x1000).map (⟨·, .firmware⟩)

/-- The table of the arena 1 of the core's capacities on `capacityBanks` and
`capacityExclusions`, followed by the exclusions `more`. -/
def capacityTable (more : List Exclusion) : Except OwnershipError (Ownership EXTENTS EXCLUSION_RECORDS) := do
  Ownership.new 1 (← capacityBanks) ((← capacityExclusions) ++ more)

/-- **PGT-R11, accepted.** Criterion: "a direct map that needs exactly 80
tables succeeds ...; a page ownership table at exactly 160 extents works ...;
an initialization with 132 exclusions succeeds":

- `direct_map` of `firstPageOfEachBlock 78`, whose plan needs exactly 80
  tables, into a new set of the 80 tables of the direct map's pool succeeds
  with 80 tables in use and 78 pages, `0x4_e000` bytes;
- `Ownership::new` with the 132 exclusions of `capacityExclusions` succeeds
  with exactly 160 extents, whose statistics count `0x1b7_c000` managed and
  free bytes, the largest free extent `0xf_9000`, and 160 extents in use of
  the capacity of 160;
- at those 160 extents an allocation of 1 page with the low placement works:
  `choose` passes over the first extent, whose split would need a 161st, and
  gives `[0x3000, 0x4000)`, an extent of exactly one page, which `assign`
  holds with generation 1, still with 160 extents.
Feature: `krepi.kernel.kernel-memory`. -/
def CapacitiesAtTheirLimits : Prop :=
  (firstPageOfEachBlock 78).toOption.map (fun memory =>
      ((newSet .upper DIRECT_MAP_TABLES).directMap memory DM_BASE BITS).map
        fun (s, plan) => (s.usedTables, plan.counts)) =
    some (.ok (80, ⟨0x4_e000, 0, 78⟩)) ∧
  (do
    let t ← capacityTable []
    let (t', a) ← t.assign (← t.choose 1 1 1 ⟨.low, none⟩) true
    pure (t.stats, a, t'.stats.extents)) =
    .ok (⟨0x1b7_c000, 0x1b7_c000, 0, 0, 160, 0xf_9000, 160, 160⟩, ⟨1, 1, 1, range 0x3000 0x1000⟩, 160)

/-- **PGT-R11, rejected.** Criterion: "... and one that needs 81 is refused;
... and one more extent is refused; ... and one with 133 is refused":

- `direct_map` of `firstPageOfEachBlock 79`, whose plan needs 81 tables, into
  a new set of 80 tables is refused with `OutOfTables`;
- at the 160 extents of `CapacitiesAtTheirLimits`, a reservation of 3 pages,
  for which every free extent that holds it would need one more extent, is
  refused with `MetadataExhausted`;
- `Ownership::new` with a 133rd exclusion, `[0x1c0_8000, 0x1c0_9000)`, which
  lies outside every bank and adds no extent, is refused with
  `MetadataExhausted`, for the 132 exclusion records of the core.
Feature: `krepi.kernel.kernel-memory`. -/
def CapacitiesRefuseOneMore : Prop :=
  (firstPageOfEachBlock 79).toOption.map (fun memory =>
      ((newSet .upper DIRECT_MAP_TABLES).directMap memory DM_BASE BITS).map Prod.snd) =
    some (.error .outOfTables) ∧
  ((capacityTable []).bind fun t => (t.reserve 1 3 1 ⟨.low, none⟩).map Prod.snd) = .error .metadataExhausted ∧
  ((capacityTable [⟨range 0x1c0_8000 0x1000, .firmware⟩]).map (·.stats)) = .error .metadataExhausted

/-! ## PGT-R12: copying the kernel tables -/

/-- The base of the pool of the target of `pt-07`, `0x1_0000_a000`. -/
def PT07_TARGET : UInt64 := 0x1_0000_a000

/-- **PGT-R12, accepted.** Criterion: "the frozen vectors hold, and the plan of
the copy equals the order of the contract", `pt-07`: a lower source set of 10
tables at `BASE` with `0x4000` to `0x4000_0000` as `ReadExecute`,
`0x900_0000` to itself as `Device` and `0x4000_0000` to `0x2_0000_0000` as
`ReadWrite`, 6 tables in use; a lower target set of 10 tables at
`0x1_0000_a000` with `0x8000_0000` to `0x0` as `ReadWrite`, 3 tables in use.
The copy succeeds with the plan of a `Zero` of each of the target's 3 tables
in use, then a `Store` of each valid entry of the source into the target's
table of its index, by table and entry index, each table descriptor pointing
at the target's table of the source's index, and `Sync`. Once the plan has
run, the target uses 6 tables and maps the three pages with the source's
descriptors, and `0x8000_0000` is `NotMapped`; after `0x8000` to `0x6000` as
`UserReadWrite` in the target, `0x8000` is `NotMapped` in the source, and
after `unmap_page` of `0x4000` in the source the target still maps it.
Feature: `krepi.kernel.kernel-memory`. -/
def CopyIsPrivateAndOrdered : Prop :=
  (do
    let source ← withPage (newSet .lower 10) 0x4000 0x4000_0000 .readExecute
    let source ← withPage source 0x900_0000 0x900_0000 .device
    let source ← withPage source 0x4000_0000 0x2_0000_0000 .readWrite
    let target ← withPage (newSet .lower 10) 0x8000_0000 0x0 .readWrite PT07_TARGET
    let (copy, plan) ← target.cloneKernelFrom source BASE PT07_TARGET BITS
    let copy := copy.apply plan
    let later ← withPage copy 0x8000 0x6000 .userReadWrite PT07_TARGET
    let (unmap, _) ← source.unmapPage 0x4000 BASE BITS
    pure (plan, copy.usedTables,
      [0x4000, 0x900_0000, 0x4000_0000, 0x8000_0000].map (copy.lookupPage · PT07_TARGET BITS),
      source.lookupPage 0x8000 BASE BITS, (source.apply unmap).lookupPage 0x4000 BASE BITS,
      later.lookupPage 0x4000 PT07_TARGET BITS)) =
    .ok ([.zero 0, .zero 1, .zero 2, .store 0 0 0x1_0000_b003, .store 0 1 0x1_0000_e003,
        .store 1 0 0x1_0000_c003, .store 1 72 0x1_0000_d003, .store 2 4 0x40_0000_4000_0787,
        .store 3 0 0x60_0000_0900_0403, .store 4 0 0x1_0000_f003, .store 5 0 0x60_0002_0000_0707, .sync],
      6, [.ok 0x40_0000_4000_0787, .ok 0x60_0000_0900_0403, .ok 0x60_0002_0000_0707, .error .notMapped],
      .error .notMapped, .error .notMapped, .ok 0x40_0000_4000_0787)

/-- **PGT-R12, rejected.** Criterion: "the frozen vectors hold", here `pt-12`
and the requirement's refusal of "a source ... with a leaf of a kind other
than `ReadExecute`, `ReadOnly`, `ReadWrite` and `Device`": a lower source
set of 3 tables with `0x2000_1000` to `0x4100_0000` as
`KernelPrivateReadWrite`, a stack private to its address space, and a lower
target set of 3 tables at `0x1_0000_4000` with `0x4000_0000` to itself as
`ReadWrite`: the copy is refused with `InvalidDescriptor`, before any write,
where a copy would give the target the private leaf.
Feature: `krepi.kernel.kernel-memory`. -/
def CopyRefusesPrivateLeaf : Prop :=
  (do
    let source ← withPage (newSet .lower 3) 0x2000_1000 0x4100_0000 .kernelPrivateReadWrite
    let target ← withPage (newSet .lower 3) 0x4000_0000 0x4000_0000 .readWrite 0x1_0000_4000
    pure ((target.cloneKernelFrom source BASE 0x1_0000_4000 BITS).map Prod.snd)) =
    .ok (.error .invalidDescriptor)

end Krepi.SpecTests.PageTables
