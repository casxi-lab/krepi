module

public import Krepi.Spec.PageTables.Boot

/-!
# Page tables: witnesses of the table sets

Theorems that witness that the specification of the table sets of the
`page-tables` component is not vacuous: for every frozen function of rows 106
to 111 of the entry table of its contract
(`docs/domains/memory/page-tables/contract.md`), one input on which it
succeeds, with the value that it gives, and for every error that the contract
gives that function, one input on which it fails with that error. The page
ownership table, rows 112 to 116, has its witnesses in
`Krepi.Spec.PageTables.Witnesses.PageOwnership`. The value type `Kind` is
read through `descriptor` and has no witness of its own. Every expected value
is a literal worked out from the contract, never computed by the
specification.

Each witness is proved here by `decide +kernel`: the kernel evaluates both
sides. Lean core decides no equality of `Except`, so the module states each
witness as an equation `f x = .ok v` or `f x = .error e` and decides it with
a local instance that compares the constructors and their payloads; the
instance appears in no statement. Where an error has several rules, its
witness is a conjunction with one input for each rule that the contract names.

The inputs are written here, since the module imports the specification
alone: the pools by their descriptors, entry by entry, as the tests of the
prototype write storage directly; the layouts by their ranges; and the boot
memory maps as the values that `MemoryPlan::all_ram` of the fdt specification
gives (`plansBuilt`). A table set is an input as its type admits it, any pool
with any record of the tables in use. The boot memory map of `direct_map` is
an input as the fdt entries build it, since the fdt contract builds it only so.

For each step of the error orders of the contract, one more witness gives an
input that breaks a rule of that step and a later rule of the same entry, and
states the error of the step (`priorityStep1` to `priorityStep6` for the
entries on one address, `priorityMapStep1` to `priorityMapStep8` for
`kernel_map` and `direct_map`, `priorityCloneStep1` to `priorityCloneStep7`
for `clone_kernel_from`); each is a conjunction over the entries that have
both rules.

Error branches that no input of an entry reaches have no witness; for each,
a proposition below states that the entry never takes it, with its reason,
and a planned theorem proves it. The two variants of the specification that
reject every input or accept every input are refuted for the functions of
these rows by `notAlwaysRejecting` and `notAlwaysSucceeding`.
-/

@[expose] public section

namespace Krepi.Spec.PageTables.Witnesses.TableSets

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

/-- The base of the pools, `0x1_0000_0000`, as in the vectors of
`src/arch/aarch64/paging/tests.rs`. -/
def BASE : UInt64 := 0x1_0000_0000

/-- The physical width, 40. -/
def BITS : UInt8 := 40

/-- A base whose pool of 4 tables ends above $2^{40}$: `0xff_ffff_e000`. -/
def HIGH_BASE : UInt64 := 0xff_ffff_e000

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

/-- A range of a layout, of a kind that a layout names. -/
def lr (start len : Nat) (k : Kind) (h : 0 < len ∧ start + len < 2 ^ 64 := by decide)
    (hk : layoutKinds.contains k = true := by decide) : LayoutRange :=
  ⟨phys start len h, k, hk⟩

/-- A layout of at most 16 ranges, with its guard addresses. -/
def lay (ranges : List LayoutRange) (guards : List UInt64 := [])
    (h : ranges.length ≤ MAX_LAYOUT_RANGES := by decide) : Layout :=
  ⟨ranges, guards, h⟩

/-- A table, zero but for the entries `es`, each an index and a descriptor; a
later entry of one index replaces an earlier one. -/
def table (es : List (Nat × UInt64)) : Table := es.foldl (fun t e => t.setIfInBounds e.1 e.2) Table.zero

/-- The root of the lower sets below: entry 1, of the 1 GiB slot of
`0x4000_0000`, points at table 1. -/
def ROOT : Table := table [(1, 0x1_0000_1003)]

/-- The level 2 table of the lower sets below: entry 0 points at table 2. -/
def LEVEL2 : Table := table [(0, 0x1_0000_2003)]

/-- The level 3 table of the lower sets below: entry 0 is the page descriptor
of `ReadWrite` at `0x4000_0000`. -/
def LEVEL3 : Table := table [(0, 0x60_0000_4000_0707)]

/-- The set of region `r` and `N` tables that `Tables::new` makes from storage
that is zero, the root alone in use. -/
def emptySet (r : Region) (N : Nat) : Tables r N := ⟨Pool.zero N, 1⟩

/-- The lower set of 4 tables at `BASE` that maps the page `0x4000_0000` to
itself as `ReadWrite`: root entry 1 points at table 1, its entry 0 at table 2,
whose entry 0 is the page descriptor; 3 tables in use. -/
def pageSet : Tables .lower 4 := ⟨⟨#[ROOT, LEVEL2, LEVEL3, Table.zero], rfl⟩, 3⟩

/-- `pageSet` in a pool of 3 tables, all in use. -/
def pageSet3 : Tables .lower 3 := ⟨⟨#[ROOT, LEVEL2, LEVEL3], rfl⟩, 3⟩

/-- `pageSet` with the block `0x4020_0000` to `0x20_0000` in entry 1 of
table 1. -/
def heldSet : Tables .lower 4 :=
  ⟨⟨#[ROOT, table [(0, 0x1_0000_2003), (1, 0x60_0000_0020_0705)], LEVEL3, Table.zero], rfl⟩, 3⟩

/-- A set of region `r` and 2 tables, both in use, whose root entry `i` points
at table 2, outside the pool. -/
def badRoot (r : Region) (i : Nat) : Tables r 2 := ⟨⟨#[table [(i, 0x1_0000_2003)], Table.zero], rfl⟩, 2⟩

/-- A lower set of 4 tables, 2 in use, whose root entry 1 points at table 1 and
whose level 2 entry of `0x4000_0000` points at table 3, outside the tables in
use. -/
def badLevel2 : Tables .lower 4 :=
  ⟨⟨#[ROOT, table [(0, 0x1_0000_3003)], Table.zero, Table.zero], rfl⟩, 2⟩

/-- The source `pageSet` with the page descriptor `d` in place of its page, the
further root entries `more` and the record `used`. -/
def sourceWith (d : UInt64) (used : Nat := 3) (more : List (Nat × UInt64) := []) :
    Tables .lower 4 :=
  ⟨⟨#[table ((1, 0x1_0000_1003) :: more), LEVEL2, table [(0, d)], Table.zero], rfl⟩, used⟩

/-- The descriptor of `KernelPrivateReadWrite` at `0x4000_0000`, a kind that
the copy refuses. -/
def PRIVATE_LEAF : UInt64 := 0x60_0000_4000_0f07

/-- The base of the target pools of the copies, `0x1_0000_4000`, after the 4
tables of the source pools at `BASE`. -/
def TARGET_BASE : UInt64 := 0x1_0000_4000

/-- The upper tables that map the page `DIRECT_BASE | 0x40_0000` to
`0x40_0000` as `ReadWrite`: root entry 0 points at table 1, its entry 2 at
table 2, whose entry 0 is the page descriptor. -/
def UPPER : List Table :=
  [table [(0, 0x1_0000_1003)], table [(2, 0x1_0000_2003)], table [(0, 0x60_0000_0040_0707)]]

/-- An upper set of 4 tables, 3 in use, of the tables `UPPER`. -/
def upperPage : Tables .upper 4 := ⟨⟨(UPPER ++ [Table.zero]).toArray, rfl⟩, 3⟩

/-- An upper set of 3 tables, all in use, of the tables `UPPER`. -/
def upperPage3 : Tables .upper 3 := ⟨⟨UPPER.toArray, rfl⟩, 3⟩

/-- The record of the tables in use and the plan of a write entry on a set: the
write phase changes no table of the pool, which keeps the input's until the
plan is executed. -/
def outcome (x : Except TableError (Tables r N × Plan)) : Except TableError (Nat × Plan) :=
  x.map fun y => (y.1.used, y.2)

/-- A success of `outcome` is one of the entry. -/
theorem ok_of_outcome {x : Except TableError (Tables r N × Plan)} {v : Nat × Plan}
    (h : outcome x = .ok v) : ∃ y, x = .ok y := by
  cases x with
  | error e => cases h
  | ok y => exact ⟨y, rfl⟩

/-- The boot memory map of one bank `[0x1f_d000, 0x40_2000)` with the boot
storage `[0x1f_d000, +0x10)`: one usable range `[0x1f_e000, 0x40_2000)`. -/
def dmPlan : Fdt.MemoryPlan :=
  ⟨[⟨0x1f_d000, 0x20_5000⟩], [⟨0x1f_d000, 0x20_5000⟩], [⟨0x1f_d000, 0x1000⟩], []⟩

/-- The boot memory map of one bank `[0x7f_ffe0_0000, +4 MiB)` across
$2^{39}$, with the boot storage on its first page. -/
def edgePlan : Fdt.MemoryPlan :=
  ⟨[⟨0x7f_ffe0_0000, 0x40_0000⟩], [⟨0x7f_ffe0_0000, 0x40_0000⟩], [⟨0x7f_ffe0_0000, 0x1000⟩], []⟩

/-- The boot memory map of one bank `[0x1_0000_0000, +4 MiB)` above 4 GiB,
with the boot storage on its first page. -/
def highPlan : Fdt.MemoryPlan :=
  ⟨[⟨0x1_0000_0000, 0x40_0000⟩], [⟨0x1_0000_0000, 0x40_0000⟩], [⟨0x1_0000_0000, 0x1000⟩], []⟩

/-- The boot memory map of the banks `[0x40_0000, +0x2000)` and
`[0x7f_ffe0_0000, +4 MiB)`, the second given first, with the boot storage on
the page `0x40_1000`: the usable ranges `[0x40_0000, +0x1000)` and the second
bank. -/
def twoPlan : Fdt.MemoryPlan :=
  ⟨[⟨0x40_0000, 0x2000⟩, ⟨0x7f_ffe0_0000, 0x40_0000⟩],
    [⟨0x40_0000, 0x2000⟩, ⟨0x7f_ffe0_0000, 0x40_0000⟩], [⟨0x40_1000, 0x1000⟩], []⟩

/-- Every boot memory map of the witnesses is the one that `MemoryPlan::all_ram`
gives for its banks and boot storage, so each is in the domain of
`direct_map`. -/
theorem plansBuilt :
    Fdt.MemoryPlan.allRam [⟨0x1f_d000, 0x20_5000⟩] [⟨0x1f_d000, 0x10⟩] [] = .ok dmPlan ∧
    Fdt.MemoryPlan.allRam [⟨0x7f_ffe0_0000, 0x40_0000⟩] [⟨0x7f_ffe0_0000, 0x10⟩] [] =
      .ok edgePlan ∧
    Fdt.MemoryPlan.allRam [⟨0x1_0000_0000, 0x40_0000⟩] [⟨0x1_0000_0000, 0x10⟩] [] =
      .ok highPlan ∧
    Fdt.MemoryPlan.allRam [⟨0x7f_ffe0_0000, 0x40_0000⟩, ⟨0x40_0000, 0x2000⟩] [⟨0x40_1000, 0x10⟩] [] =
      .ok twoPlan := by
  decide +kernel

/-! ## `page_tables::descriptor` and `direct_address` -/

/-- The nine kinds, in the order of the kind table. -/
def kinds : List Kind :=
  [.readExecute, .readOnly, .readWrite, .kernelPrivateReadWrite, .device,
    .userReadExecute, .userReadOnly, .userReadWrite, .userDevice]

/-- `descriptor`: the page descriptor of each kind at `0x4000_0000`, the bits of
its row with the address in bits 12 to 47 and `0b11` in bits 1 and 0. -/
theorem descriptorOk :
    kinds.map (descriptor · 0x4000_0000) =
      [0x40_0000_4000_0787, 0x60_0000_4000_0787, 0x60_0000_4000_0707, 0x60_0000_4000_0f07,
        0x60_0000_4000_0403, 0x20_0000_4000_0fc7, 0x60_0000_4000_0fc7, 0x60_0000_4000_0f47,
        0x60_0000_4000_0c43] := by
  decide +kernel

/-- `direct_address`: `DIRECT_BASE | start` for a range that ends at most at
$2^{39}$, the last page of the window included; nothing for one that ends
above it. -/
theorem directAddressOk :
    directAddress (phys 0x1000 0x1000) = some 0xffff_ff80_0000_1000 ∧
      directAddress (phys 0x7f_ffff_f000 0x1000) = some 0xffff_ffff_ffff_f000 ∧
      directAddress (phys 0x7f_ffff_f000 0x2000) = none := by
  decide +kernel

/-! ## `PhysRange::new`, `end`, `contains` and `overlaps` -/

/-- `PhysRange::new`: the range `[0x1000, 0x3000)`, and the range whose end is
$2^{64} - 1$. -/
theorem physRangeNewOk :
    PhysRange.new 0x1000 0x2000 = .ok (phys 0x1000 0x2000) ∧
      PhysRange.new 0xffff_ffff_ffff_fffe 1 = .ok (phys 0xffff_ffff_ffff_fffe 1) := by
  decide +kernel

/-- `PhysRange::new`: a length of 0. -/
theorem physRangeNewInvalidRange : PhysRange.new 0x1000 0 = .error .invalidRange := by
  decide +kernel

/-- `PhysRange::new`: a range whose end is $2^{64}$. -/
theorem physRangeNewAddressOverflow :
    PhysRange.new 0xffff_ffff_ffff_f000 0x1000 = .error .addressOverflow := by
  decide +kernel

/-- `PhysRange::end`: the exclusive end, and $2^{64} - 1$ for the last range. -/
theorem endOk :
    (phys 0x1000 0x2000).endAddr = 0x3000 ∧
      (phys 0xffff_ffff_ffff_fffe 1).endAddr = 0xffff_ffff_ffff_ffff := by
  decide +kernel

/-- `PhysRange::contains`: a range inside, and one that starts inside and ends
past the end. -/
theorem containsOk :
    (phys 0x1000 0x3000).contains (phys 0x2000 0x2000) = true ∧
      (phys 0x1000 0x3000).contains (phys 0x3000 0x2000) = false := by
  decide +kernel

/-- `PhysRange::overlaps`: two ranges that share the page `0x2000`, and two
adjacent ranges, which share no address. -/
theorem overlapsOk :
    (phys 0x1000 0x2000).overlaps (phys 0x2000 0x1000) = true ∧
      (phys 0x1000 0x2000).overlaps (phys 0x3000 0x1000) = false := by
  decide +kernel

/-! ## `Tables::lookup_page`, `lookup_block` and `used` -/

/-- `lookup_page`: the page descriptor of `0x4000_0000`. -/
theorem lookupPageOk : heldSet.lookupPage 0x4000_0000 BASE BITS = .ok 0x60_0000_4000_0707 := by
  decide +kernel

/-- `lookup_page`: `0x4000_0001`, and the base `0x1_0000_0001`, not multiples
of 4 KiB. -/
theorem lookupPageAlignment :
    heldSet.lookupPage 0x4000_0001 BASE BITS = .error .alignment ∧
      heldSet.lookupPage 0x4000_0000 0x1_0000_0001 BITS = .error .alignment := by
  decide +kernel

/-- `lookup_page`: `0x80_0000_0000`, outside the lower region, and the widths 31
and 49. -/
theorem lookupPageAddressWidth :
    heldSet.lookupPage 0x80_0000_0000 BASE BITS = .error .addressWidth ∧
      heldSet.lookupPage 0x4000_0000 BASE 31 = .error .addressWidth ∧
      heldSet.lookupPage 0x4000_0000 BASE 49 = .error .addressWidth := by
  decide +kernel

/-- `lookup_page`: a pool of 4 tables at `HIGH_BASE`, which ends above
$2^{40}$; a pool of no table; and a level 2 entry that points outside the
tables in use. -/
theorem lookupPageTableBacking :
    heldSet.lookupPage 0x4000_0000 HIGH_BASE BITS = .error .tableBacking ∧
      (emptySet .lower 0).lookupPage 0x4000_0000 BASE BITS = .error .tableBacking ∧
      badLevel2.lookupPage 0x4000_0000 BASE BITS = .error .tableBacking := by
  decide +kernel

/-- `lookup_page`: an invalid level 3 entry, a page of a block, and an invalid
root entry. -/
theorem lookupPageNotMapped :
    heldSet.lookupPage 0x4000_1000 BASE BITS = .error .notMapped ∧
      heldSet.lookupPage 0x4020_1000 BASE BITS = .error .notMapped ∧
      heldSet.lookupPage 0x8000_0000 BASE BITS = .error .notMapped := by
  decide +kernel

/-- `lookup_block`: the block descriptor of `0x4020_0000`. -/
theorem lookupBlockOk :
    heldSet.lookupBlock 0x4020_0000 BASE BITS = .ok 0x60_0000_0020_0705 := by
  decide +kernel

/-- `lookup_block`: `0x4000_1000`, not a multiple of 2 MiB, and a base off a
page. -/
theorem lookupBlockAlignment :
    heldSet.lookupBlock 0x4000_1000 BASE BITS = .error .alignment ∧
      heldSet.lookupBlock 0x4020_0000 0x1_0000_0001 BITS = .error .alignment := by
  decide +kernel

/-- `lookup_block`: `0x80_0000_0000`, outside the lower region, and the width
31. -/
theorem lookupBlockAddressWidth :
    heldSet.lookupBlock 0x80_0000_0000 BASE BITS = .error .addressWidth ∧
      heldSet.lookupBlock 0x4020_0000 BASE 31 = .error .addressWidth := by
  decide +kernel

/-- `lookup_block`: the pool at `HIGH_BASE`, and a root entry that points
outside the pool. -/
theorem lookupBlockTableBacking :
    heldSet.lookupBlock 0x4020_0000 HIGH_BASE BITS = .error .tableBacking ∧
      (badRoot .lower 1).lookupBlock 0x4020_0000 BASE BITS = .error .tableBacking := by
  decide +kernel

/-- `lookup_block`: a level 2 entry that points at a level 3 table, one that is
invalid, and an invalid root entry. -/
theorem lookupBlockNotMapped :
    heldSet.lookupBlock 0x4000_0000 BASE BITS = .error .notMapped ∧
      heldSet.lookupBlock 0x4040_0000 BASE BITS = .error .notMapped ∧
      heldSet.lookupBlock 0x8000_0000 BASE BITS = .error .notMapped := by
  decide +kernel

/-- `Tables::used`: 3 tables in use, and 1 in a new set. -/
theorem usedOk : heldSet.usedTables = 3 ∧ (emptySet .upper 4).usedTables = 1 := by decide +kernel

/-! ## `Tables::new`, `reset` and `clone_kernel_from` -/

/-- `Tables::new`: for every storage, the set of that storage with the root
alone in use. -/
theorem newOk (storage : Pool N) : (Tables.new storage : Tables r N) = ⟨storage, 1⟩ := rfl

/-- `reset`: the record of 1 table, and a `Zero` of each of the 3 tables in
use; the pool is the input's. -/
theorem resetOk :
    heldSet.reset.1.pool = heldSet.pool ∧
      (heldSet.reset.1.used, heldSet.reset.2) = (1, [.zero 0, .zero 1, .zero 2]) :=
  ⟨rfl, by decide +kernel⟩

/-- `clone_kernel_from`: the page of `pageSet` into a new set at
`TARGET_BASE`: the record of the source, a `Zero` of the target's table in
use, a `Store` of each valid entry of the source into the target's table of
its index, the table descriptors pointing into the target's pool, and `Sync`.
-/
theorem cloneKernelFromOk :
    outcome ((emptySet .lower 4).cloneKernelFrom pageSet BASE TARGET_BASE BITS) =
      .ok (3,
        [.zero 0, .store 0 1 0x1_0000_5003, .store 1 0 0x1_0000_6003,
          .store 2 0 0x60_0000_4000_0707, .sync]) := by
  decide +kernel

/-- `clone_kernel_from`: the source base `0x1_0000_0001` and the target base
`0x1_0000_4001`. -/
theorem cloneKernelFromAlignment :
    (emptySet .lower 4).cloneKernelFrom pageSet 0x1_0000_0001 TARGET_BASE BITS =
        .error .alignment ∧
      (emptySet .lower 4).cloneKernelFrom pageSet BASE 0x1_0000_4001 BITS =
        .error .alignment := by
  decide +kernel

/-- `clone_kernel_from`: the widths 31 and 49. -/
theorem cloneKernelFromAddressWidth :
    (emptySet .lower 4).cloneKernelFrom pageSet BASE TARGET_BASE 31 = .error .addressWidth ∧
      (emptySet .lower 4).cloneKernelFrom pageSet BASE TARGET_BASE 49 =
        .error .addressWidth := by
  decide +kernel

/-- `clone_kernel_from`, each rule of `TableBacking`: the source pool and the
target pool at `HIGH_BASE`; pools that overlap; a record of no table and one of
5 tables; a table descriptor that points at table 2 with a record of 2 tables;
two root entries on table 1, which the walk reaches twice; and a record of 4
tables, one of which the walk does not reach. -/
theorem cloneKernelFromTableBacking :
    (emptySet .lower 4).cloneKernelFrom pageSet HIGH_BASE TARGET_BASE BITS =
        .error .tableBacking ∧
      (emptySet .lower 4).cloneKernelFrom pageSet BASE HIGH_BASE BITS = .error .tableBacking ∧
      (emptySet .lower 4).cloneKernelFrom pageSet BASE 0x1_0000_2000 BITS =
        .error .tableBacking ∧
      (emptySet .lower 4).cloneKernelFrom (sourceWith 0x60_0000_4000_0707 0) BASE TARGET_BASE BITS =
        .error .tableBacking ∧
      (emptySet .lower 4).cloneKernelFrom (sourceWith 0x60_0000_4000_0707 5) BASE TARGET_BASE BITS =
        .error .tableBacking ∧
      (emptySet .lower 4).cloneKernelFrom (sourceWith 0x60_0000_4000_0707 2) BASE TARGET_BASE BITS =
        .error .tableBacking ∧
      (emptySet .lower 4).cloneKernelFrom (sourceWith 0x60_0000_4000_0707 3 [(2, 0x1_0000_1003)])
        BASE TARGET_BASE BITS = .error .tableBacking ∧
      (emptySet .lower 4).cloneKernelFrom (sourceWith 0x60_0000_4000_0707 4) BASE TARGET_BASE BITS =
        .error .tableBacking := by
  decide +kernel

/-- `clone_kernel_from`, each rule of `InvalidDescriptor`: a root entry with bit
6 set; a block in place of a table descriptor at level 2; a leaf of
`KernelPrivateReadWrite`; and a leaf at the output address $2^{40}$. -/
theorem cloneKernelFromInvalidDescriptor :
    (emptySet .lower 4).cloneKernelFrom (sourceWith 0x60_0000_4000_0707 3 [(1, 0x1_0000_1043)])
        BASE TARGET_BASE BITS = .error .invalidDescriptor ∧
      (emptySet .lower 4).cloneKernelFrom heldSet BASE TARGET_BASE BITS = .error .invalidDescriptor ∧
      (emptySet .lower 4).cloneKernelFrom (sourceWith PRIVATE_LEAF) BASE TARGET_BASE BITS =
        .error .invalidDescriptor ∧
      (emptySet .lower 4).cloneKernelFrom (sourceWith 0x60_0100_0000_0707) BASE TARGET_BASE BITS =
        .error .invalidDescriptor := by
  decide +kernel

/-! ## `Tables::map_page`, `map_block` and `unmap_page` -/

/-- `map_page`: `0x4000_0000` to itself as `ReadWrite` in a new set: a new level
2 table 1 and level 3 table 2, the plan of the contract, and 3 tables in use.
-/
theorem mapPageOk :
    outcome ((emptySet .lower 4).mapPage 0x4000_0000 0x4000_0000 .readWrite BASE BITS) =
      .ok (3,
        [.zero 2, .store 2 0 0x60_0000_4000_0707, .zero 1, .store 1 0 0x1_0000_2003, .fence,
          .store 0 1 0x1_0000_1003, .sync]) := by
  decide +kernel

/-- `map_page`: the virtual address `0x4000_0001`, the base `0x1_0000_0001` and
the physical address `0x1`, each off a page. -/
theorem mapPageAlignment :
    heldSet.mapPage 0x4000_0001 0x1000 .readWrite BASE BITS = .error .alignment ∧
      heldSet.mapPage 0x4000_1000 0x1000 .readWrite 0x1_0000_0001 BITS = .error .alignment ∧
      heldSet.mapPage 0x4000_1000 0x1 .readWrite BASE BITS = .error .alignment := by
  decide +kernel

/-- `map_page`: the virtual address `0x80_0000_0000`, outside the lower region;
the widths 31 and 49; and the physical address $2^{40}$. -/
theorem mapPageAddressWidth :
    heldSet.mapPage 0x80_0000_0000 0x1000 .readWrite BASE BITS = .error .addressWidth ∧
      heldSet.mapPage 0x4000_1000 0x1000 .readWrite BASE 31 = .error .addressWidth ∧
      heldSet.mapPage 0x4000_1000 0x1000 .readWrite BASE 49 = .error .addressWidth ∧
      heldSet.mapPage 0x4000_1000 0x100_0000_0000 .readWrite BASE BITS = .error .addressWidth := by
  decide +kernel

/-- `map_page`: the pool at `HIGH_BASE`; a root entry that points outside the
pool; and a level 2 entry that points outside the tables in use. -/
theorem mapPageTableBacking :
    heldSet.mapPage 0x4000_1000 0x1000 .readWrite HIGH_BASE BITS = .error .tableBacking ∧
      (badRoot .lower 1).mapPage 0x4000_0000 0x1000 .readWrite BASE BITS = .error .tableBacking ∧
      badLevel2.mapPage 0x4000_0000 0x1000 .readWrite BASE BITS = .error .tableBacking := by
  decide +kernel

/-- `map_page`: a mapped page, and a page of a block. -/
theorem mapPageAlreadyMapped :
    heldSet.mapPage 0x4000_0000 0x4000_1000 .device BASE BITS = .error .alreadyMapped ∧
      heldSet.mapPage 0x4020_1000 0x1000 .readWrite BASE BITS = .error .alreadyMapped := by
  decide +kernel

/-- `map_page`: a page of a new 1 GiB slot needs 2 new tables, and the pool of
4 tables has 1 free. -/
theorem mapPageOutOfTables :
    pageSet.mapPage 0x8000_0000 0x0 .readWrite BASE BITS = .error .outOfTables := by
  decide +kernel

/-- `map_block`: the block `0x4020_0000` to `0x20_0000` as `ReadWrite`, with a
new level 2 table in a new set, and in the level 2 table of `pageSet`. -/
theorem mapBlockOk :
    outcome ((emptySet .lower 4).mapBlock 0x4020_0000 0x20_0000 BASE BITS) =
        .ok (2, [.zero 1, .store 1 1 0x60_0000_0020_0705, .fence, .store 0 1 0x1_0000_1003, .sync]) ∧
      outcome (pageSet.mapBlock 0x4020_0000 0x20_0000 BASE BITS) =
        .ok (3, [.store 1 1 0x60_0000_0020_0705, .sync]) := by
  decide +kernel

/-- `map_block`: the virtual address `0x4000_1000` and the physical address
`0x1000`, not multiples of 2 MiB, and the base `0x1_0000_0001`. -/
theorem mapBlockAlignment :
    heldSet.mapBlock 0x4000_1000 0x0 BASE BITS = .error .alignment ∧
      heldSet.mapBlock 0x4040_0000 0x1000 BASE BITS = .error .alignment ∧
      heldSet.mapBlock 0x4040_0000 0x0 0x1_0000_0001 BITS = .error .alignment := by
  decide +kernel

/-- `map_block`: the virtual address `0x80_0000_0000`, the width 31, and the
physical address $2^{40}$. -/
theorem mapBlockAddressWidth :
    heldSet.mapBlock 0x80_0000_0000 0x0 BASE BITS = .error .addressWidth ∧
      heldSet.mapBlock 0x4040_0000 0x0 BASE 31 = .error .addressWidth ∧
      heldSet.mapBlock 0x4040_0000 0x100_0000_0000 BASE BITS = .error .addressWidth := by
  decide +kernel

/-- `map_block`: the pool at `HIGH_BASE`, and a root entry that points outside
the pool. -/
theorem mapBlockTableBacking :
    heldSet.mapBlock 0x4040_0000 0x0 HIGH_BASE BITS = .error .tableBacking ∧
      (badRoot .lower 1).mapBlock 0x4040_0000 0x0 BASE BITS = .error .tableBacking := by
  decide +kernel

/-- `map_block`: a slot that holds a block, and one that holds a level 3 table,
so that it is not free of tables. -/
theorem mapBlockAlreadyMapped :
    heldSet.mapBlock 0x4020_0000 0x60_0000 BASE BITS = .error .alreadyMapped ∧
      heldSet.mapBlock 0x4000_0000 0x60_0000 BASE BITS = .error .alreadyMapped := by
  decide +kernel

/-- `map_block`: a block of a new 1 GiB slot needs a new table, and the pool of
3 tables has none free. -/
theorem mapBlockOutOfTables : pageSet3.mapBlock 0x8000_0000 0x0 BASE BITS = .error .outOfTables := by
  decide +kernel

/-- `unmap_page`: the plan stores the invalid descriptor into the leaf and
invalidates the address, and the entry gives the physical page. -/
theorem unmapPageOk :
    heldSet.unmapPage 0x4000_0000 BASE BITS =
      .ok ([.store 2 0 0, .invalidate 0x4000_0000], 0x4000_0000) := by
  decide +kernel

/-- `unmap_page`: `0x4000_0001`, and the base `0x1_0000_0001`. -/
theorem unmapPageAlignment :
    heldSet.unmapPage 0x4000_0001 BASE BITS = .error .alignment ∧
      heldSet.unmapPage 0x4000_0000 0x1_0000_0001 BITS = .error .alignment := by
  decide +kernel

/-- `unmap_page`: `0x80_0000_0000`, and the width 49. -/
theorem unmapPageAddressWidth :
    heldSet.unmapPage 0x80_0000_0000 BASE BITS = .error .addressWidth ∧
      heldSet.unmapPage 0x4000_0000 BASE 49 = .error .addressWidth := by
  decide +kernel

/-- `unmap_page`: the pool at `HIGH_BASE`, and a level 2 entry that points
outside the tables in use. -/
theorem unmapPageTableBacking :
    heldSet.unmapPage 0x4000_0000 HIGH_BASE BITS = .error .tableBacking ∧
      badLevel2.unmapPage 0x4000_0000 BASE BITS = .error .tableBacking := by
  decide +kernel

/-- `unmap_page`: an invalid level 3 entry, and a page of a block. -/
theorem unmapPageNotMapped :
    heldSet.unmapPage 0x4000_1000 BASE BITS = .error .notMapped ∧
      heldSet.unmapPage 0x4020_0000 BASE BITS = .error .notMapped := by
  decide +kernel

/-! ## `page_tables::kernel_map` -/

/-- `kernel_map`: a layout of the data `[0x4000_2000, +0x1000)`, `ReadWrite`,
given first, and the text `[0x4000_0000, +0x1000)`, `ReadExecute`, with the
guard `0x4000_1000`: the pages in address order in a new level 3 table 2 under
a new level 2 table 1, the guard left invalid, and 3 tables in use. -/
theorem kernelMapOk :
    outcome ((emptySet .lower 4).kernelMap
        (lay [lr 0x4000_2000 0x1000 .readWrite, lr 0x4000_0000 0x1000 .readExecute] [0x4000_1000])
        BASE BITS) =
      .ok (3,
        [.zero 2, .store 2 0 0x40_0000_4000_0787, .store 2 2 0x60_0000_4000_2707, .zero 1,
          .store 1 0 0x1_0000_2003, .fence, .store 0 1 0x1_0000_1003, .sync]) := by
  decide +kernel

/-- `kernel_map`: the base `0x1_0000_0001`, and a range that ends 2 KiB into a
page. -/
theorem kernelMapAlignment :
    (emptySet .lower 4).kernelMap (lay [lr 0x4000_0000 0x1000 .readOnly]) 0x1_0000_0001 BITS =
        .error .alignment ∧
      (emptySet .lower 4).kernelMap (lay [lr 0x4000_0000 0x800 .readOnly]) BASE BITS =
        .error .alignment := by
  decide +kernel

/-- `kernel_map`: the width 31; a range that ends above $2^{39}$; and, at the
width 32 with the pool at `0x1000_0000`, a range that ends above $2^{32}$. -/
theorem kernelMapAddressWidth :
    (emptySet .lower 4).kernelMap (lay [lr 0x4000_0000 0x1000 .readOnly]) BASE 31 =
        .error .addressWidth ∧
      (emptySet .lower 4).kernelMap (lay [lr 0x7f_ffff_f000 0x2000 .readOnly]) BASE BITS =
        .error .addressWidth ∧
      (emptySet .lower 4).kernelMap (lay [lr 0xffff_f000 0x2000 .readOnly]) 0x1000_0000 32 =
        .error .addressWidth := by
  decide +kernel

/-- `kernel_map`: the pool at `HIGH_BASE`, and a root entry that points outside
the pool. -/
theorem kernelMapTableBacking :
    (emptySet .lower 4).kernelMap (lay [lr 0x4000_0000 0x1000 .readOnly]) HIGH_BASE BITS =
        .error .tableBacking ∧
      (badRoot .lower 1).kernelMap (lay [lr 0x4000_0000 0x1000 .readOnly]) BASE BITS =
        .error .tableBacking := by
  decide +kernel

/-- `kernel_map`: two ranges that share the page `0x4000_1000`; a range that
holds a guard address; a page that the set maps; and a page of a block. -/
theorem kernelMapAlreadyMapped :
    (emptySet .lower 4).kernelMap
        (lay [lr 0x4000_0000 0x2000 .readExecute, lr 0x4000_1000 0x2000 .readWrite]) BASE BITS =
        .error .alreadyMapped ∧
      (emptySet .lower 4).kernelMap (lay [lr 0x4000_0000 0x2000 .readWrite] [0x4000_1800]) BASE BITS =
        .error .alreadyMapped ∧
      heldSet.kernelMap (lay [lr 0x4000_0000 0x1000 .readOnly]) BASE BITS = .error .alreadyMapped ∧
      heldSet.kernelMap (lay [lr 0x4020_0000 0x1000 .readOnly]) BASE BITS = .error .alreadyMapped := by
  decide +kernel

/-- `kernel_map`: a page of a new 1 GiB slot needs 2 new tables, and the pool of
4 tables has 1 free. -/
theorem kernelMapOutOfTables :
    pageSet.kernelMap (lay [lr 0x8000_0000 0x1000 .readOnly]) BASE BITS = .error .outOfTables := by
  decide +kernel

/-! ## `page_tables::direct_map` -/

/-- `direct_map`: the usable range `[0x1f_e000, 0x40_2000)` of `dmPlan` at
`DIRECT_BASE | pa`: the pages `0x1f_e000` and `0x1f_f000`, the block
`0x20_0000` and the pages `0x40_0000` and `0x40_1000`, in a new level 2 table 1
and the new level 3 tables 2 and 3 of the two 2 MiB slots with pages, built
before the table descriptors that reach them; 4 tables in use. -/
theorem directMapOk :
    outcome ((emptySet .upper 4).directMap dmPlan BASE BITS) =
      .ok (4,
        [.zero 2, .store 2 510 0x60_0000_001f_e707, .store 2 511 0x60_0000_001f_f707, .zero 3,
          .store 3 0 0x60_0000_0040_0707, .store 3 1 0x60_0000_0040_1707, .zero 1,
          .store 1 0 0x1_0000_2003, .store 1 1 0x60_0000_0020_0705, .store 1 2 0x1_0000_3003,
          .fence, .store 0 0 0x1_0000_1003, .sync]) := by
  decide +kernel

/-- `direct_map`: the base `0x1_0000_0001`. A usable range off a page has no
witness: `DirectMapRangesOnPages`. -/
theorem directMapAlignment :
    (emptySet .upper 4).directMap dmPlan 0x1_0000_0001 BITS = .error .alignment := by
  decide +kernel

/-- `direct_map`: the width 31; a usable range that ends above $2^{39}$; and, at
the width 32 with the pool at `0x8_0000`, one that ends above $2^{32}$. -/
theorem directMapAddressWidth :
    (emptySet .upper 4).directMap dmPlan BASE 31 = .error .addressWidth ∧
      (emptySet .upper 4).directMap edgePlan BASE BITS = .error .addressWidth ∧
      (emptySet .upper 4).directMap highPlan 0x8_0000 32 = .error .addressWidth := by
  decide +kernel

/-- `direct_map`: the pool at `HIGH_BASE`, and a root entry that points outside
the pool. -/
theorem directMapTableBacking :
    (emptySet .upper 4).directMap dmPlan HIGH_BASE BITS = .error .tableBacking ∧
      (badRoot .upper 0).directMap dmPlan BASE BITS = .error .tableBacking := by
  decide +kernel

/-- `direct_map`: a set that maps the direct address of the usable page
`0x40_0000`. A leaf that an earlier usable range shares has no witness:
`DirectMapRangesApart`. -/
theorem directMapAlreadyMapped :
    upperPage.directMap dmPlan BASE BITS = .error .alreadyMapped := by
  decide +kernel

/-- `direct_map`: the map of `dmPlan` needs 3 new tables, and the pool of 3
tables has 2 free. -/
theorem directMapOutOfTables :
    (emptySet .upper 3).directMap dmPlan BASE BITS = .error .outOfTables := by
  decide +kernel

/-! ## Error priority

For each step of the error orders of `Errors of table sets` and of
`Copying the kernel tables`, one input that breaks a rule of that step and a
later rule of the same entry, and gives the error of the step: the error of
the later rule is the one that the input gives once the earlier rule is
repaired. Two rules of one error are not told apart, so each pair has two
errors. -/

/-- Step 1 of the order of an entry on one address, the alignment of the
virtual address or of `base`, `Alignment`, before the region of the address
or the width, `AddressWidth`. -/
theorem priorityStep1 :
    heldSet.mapPage 0x80_0000_0001 0x1000 .readWrite BASE BITS = .error .alignment ∧
      heldSet.mapBlock 0x4040_0000 0x0 0x1_0000_0001 31 = .error .alignment ∧
      heldSet.unmapPage 0x4000_0001 BASE 49 = .error .alignment ∧
      heldSet.lookupPage 0x80_0000_0001 BASE BITS = .error .alignment ∧
      heldSet.lookupBlock 0x80_0000_1000 BASE BITS = .error .alignment := by
  decide +kernel

/-- Step 2: the region of the address or the width, `AddressWidth`, before the
pool, `TableBacking`; here `0x80_0000_0000` with the pool at `HIGH_BASE`. -/
theorem priorityStep2 :
    heldSet.mapPage 0x80_0000_0000 0x1000 .readWrite HIGH_BASE BITS = .error .addressWidth ∧
      heldSet.mapBlock 0x80_0000_0000 0x0 HIGH_BASE BITS = .error .addressWidth ∧
      heldSet.unmapPage 0x80_0000_0000 HIGH_BASE BITS = .error .addressWidth ∧
      heldSet.lookupPage 0x80_0000_0000 HIGH_BASE BITS = .error .addressWidth ∧
      heldSet.lookupBlock 0x80_0000_0000 HIGH_BASE BITS = .error .addressWidth := by
  decide +kernel

/-- Step 3: the pool at `HIGH_BASE`, `TableBacking`, before the physical
address off a page or of a block, `Alignment`, and before an address without
a page or a block, `NotMapped`. -/
theorem priorityStep3 :
    heldSet.mapPage 0x4000_1000 0x1 .readWrite HIGH_BASE BITS = .error .tableBacking ∧
      heldSet.mapBlock 0x4040_0000 0x1000 HIGH_BASE BITS = .error .tableBacking ∧
      heldSet.unmapPage 0x4000_1000 HIGH_BASE BITS = .error .tableBacking ∧
      heldSet.lookupPage 0x4000_1000 HIGH_BASE BITS = .error .tableBacking ∧
      heldSet.lookupBlock 0x4040_0000 HIGH_BASE BITS = .error .tableBacking := by
  decide +kernel

/-- Step 4: the physical address `0x100_0000_0001` or `0x100_0000_1000`, off a
page or a block, `Alignment`, before its width, `AddressWidth`. -/
theorem priorityStep4 :
    heldSet.mapPage 0x4000_1000 0x100_0000_0001 .readWrite BASE BITS = .error .alignment ∧
      heldSet.mapBlock 0x4040_0000 0x100_0000_1000 BASE BITS = .error .alignment := by
  decide +kernel

/-- Step 5: the physical address $2^{40}$, `AddressWidth`, before the walk of a
root entry that points outside the pool, `TableBacking`. -/
theorem priorityStep5 :
    (badRoot .lower 1).mapPage 0x4000_0000 0x100_0000_0000 .readWrite BASE BITS =
        .error .addressWidth ∧
      (badRoot .lower 1).mapBlock 0x4000_0000 0x100_0000_0000 BASE BITS = .error .addressWidth := by
  decide +kernel

/-- Step 6: the walk of a root entry that points outside the pool,
`TableBacking`, before the tables that a page or a block needs from a pool
with none free, `OutOfTables`, and before an address without a page or a
block, `NotMapped`. -/
theorem priorityStep6 :
    (badRoot .lower 1).mapPage 0x4000_0000 0x1000 .readWrite BASE BITS = .error .tableBacking ∧
      (badRoot .lower 1).mapBlock 0x4000_0000 0x0 BASE BITS = .error .tableBacking ∧
      (badRoot .lower 1).unmapPage 0x4000_0000 BASE BITS = .error .tableBacking ∧
      (badRoot .lower 1).lookupPage 0x4000_0000 BASE BITS = .error .tableBacking ∧
      (badRoot .lower 1).lookupBlock 0x4000_0000 BASE BITS = .error .tableBacking := by
  decide +kernel

/-- Step 1 of the order of `kernel_map` and `direct_map`: the base
`0x1_0000_0001`, `Alignment`, before the width 31, `AddressWidth`. -/
theorem priorityMapStep1 :
    (emptySet .lower 4).kernelMap (lay [lr 0x4000_0000 0x1000 .readOnly]) 0x1_0000_0001 31 =
        .error .alignment ∧
      (emptySet .upper 4).directMap dmPlan 0x1_0000_0001 31 = .error .alignment := by
  decide +kernel

/-- Step 2: the width 31, `AddressWidth`, before the pool at `HIGH_BASE`,
`TableBacking`. -/
theorem priorityMapStep2 :
    (emptySet .lower 4).kernelMap (lay [lr 0x4000_0000 0x1000 .readOnly]) HIGH_BASE 31 =
        .error .addressWidth ∧
      (emptySet .upper 4).directMap dmPlan HIGH_BASE 31 = .error .addressWidth := by
  decide +kernel

/-- Step 3: the pool at `HIGH_BASE`, `TableBacking`, before the checks of the
ranges: a range that ends 2 KiB into a page, `Alignment`, and a usable range
that ends above $2^{39}$, `AddressWidth`. -/
theorem priorityMapStep3 :
    (emptySet .lower 4).kernelMap (lay [lr 0x4000_0000 0x800 .readOnly]) HIGH_BASE BITS =
        .error .tableBacking ∧
      (emptySet .upper 4).directMap edgePlan HIGH_BASE BITS = .error .tableBacking := by
  decide +kernel

/-- Step 4, the ends of a range of `kernel_map` off a page, `Alignment`, before
its end above $2^{39}$, `AddressWidth`: `[0x7f_ffff_f000, +0x1001)`. -/
theorem priorityMapStep4 :
    (emptySet .lower 4).kernelMap (lay [lr 0x7f_ffff_f000 0x1001 .readOnly]) BASE BITS =
      .error .alignment := by
  decide +kernel

/-- Step 5: the end of a range above $2^{32}$ at the width 32, `AddressWidth`,
before the walk of its first page through a root entry that points outside
the pool, `TableBacking`. -/
theorem priorityMapStep5 :
    (badRoot .lower 3).kernelMap (lay [lr 0xffff_f000 0x2000 .readOnly]) 0x1000_0000 32 =
        .error .addressWidth ∧
      (badRoot .upper 4).directMap highPlan 0x8_0000 32 = .error .addressWidth := by
  decide +kernel

/-- Step 6, the leaves in address order: the walk of the first leaf through an
entry that points outside the tables in use, `TableBacking`, before a later
leaf that is not free, `AlreadyMapped`: for `kernel_map` a second range on the
page `0x4000_0000`, for `direct_map` a set that maps the page `0x40_0000`. -/
theorem priorityMapStep6 :
    (badRoot .lower 1).kernelMap
        (lay [lr 0x4000_0000 0x1000 .readOnly, lr 0x4000_0000 0x2000 .readWrite]) BASE BITS =
        .error .tableBacking ∧
      (⟨⟨#[table [(0, 0x1_0000_1003)], table [(0, 0x1_0000_3003), (2, 0x1_0000_2003)],
          table [(0, 0x60_0000_0040_0707)], Table.zero], rfl⟩, 3⟩ : Tables .upper 4).directMap
        dmPlan BASE BITS =
        .error .tableBacking := by
  decide +kernel

/-- Step 7: a leaf that is not free, `AlreadyMapped`, before the tables that the
whole plan needs from a pool with too few free, `OutOfTables`. -/
theorem priorityMapStep7 :
    pageSet3.kernelMap (lay [lr 0x4000_0000 0x1000 .readOnly, lr 0x8000_0000 0x1000 .readOnly])
        BASE BITS = .error .alreadyMapped ∧
      upperPage3.directMap dmPlan BASE BITS = .error .alreadyMapped := by
  decide +kernel

/-- Step 8, the ranges in address order, each checked before the next: for
`kernel_map` a range at `0x8000_0000` that ends off a page, `Alignment`, given
before a range at `0x4000_0000` that the set maps, `AlreadyMapped`; for
`direct_map` the usable range `[0x40_0000, +0x1000)` of a page that the set
maps, `AlreadyMapped`, before the usable range that ends above $2^{39}$,
`AddressWidth`. -/
theorem priorityMapStep8 :
    pageSet.kernelMap (lay [lr 0x8000_0000 0x800 .readOnly, lr 0x4000_0000 0x1000 .readOnly])
        BASE BITS = .error .alreadyMapped ∧
      upperPage.directMap twoPlan BASE BITS = .error .alreadyMapped := by
  decide +kernel

/-- Step 1 of the order of `clone_kernel_from`: the source base off a page,
`Alignment`, before the width 31, `AddressWidth`. -/
theorem priorityCloneStep1 :
    (emptySet .lower 4).cloneKernelFrom pageSet 0x1_0000_0001 TARGET_BASE 31 =
      .error .alignment := by
  decide +kernel

/-- Step 2: the width 31, `AddressWidth`, before the source pool at
`HIGH_BASE`, `TableBacking`. -/
theorem priorityCloneStep2 :
    (emptySet .lower 4).cloneKernelFrom pageSet HIGH_BASE TARGET_BASE 31 =
      .error .addressWidth := by
  decide +kernel

/-- Step 3: the source pool at `HIGH_BASE`, `TableBacking`, before the target
base off a page, `Alignment`. -/
theorem priorityCloneStep3 :
    (emptySet .lower 4).cloneKernelFrom pageSet HIGH_BASE 0x1_0000_4001 BITS =
      .error .tableBacking := by
  decide +kernel

/-- Step 4: the target base `0xff_ffff_e001`, off a page, `Alignment`, before
its pool, which ends above $2^{40}$, `TableBacking`. -/
theorem priorityCloneStep4 :
    (emptySet .lower 4).cloneKernelFrom pageSet BASE 0xff_ffff_e001 BITS =
      .error .alignment := by
  decide +kernel

/-- Step 5: the target pool at `HIGH_BASE`, the overlap of the two pools and a
record of 5 tables, each `TableBacking`, before the walk of a source whose
leaf is of `KernelPrivateReadWrite`, `InvalidDescriptor`. -/
theorem priorityCloneStep5 :
    (emptySet .lower 4).cloneKernelFrom (sourceWith PRIVATE_LEAF) BASE HIGH_BASE BITS =
        .error .tableBacking ∧
      (emptySet .lower 4).cloneKernelFrom (sourceWith PRIVATE_LEAF) BASE 0x1_0000_2000 BITS =
        .error .tableBacking ∧
      (emptySet .lower 4).cloneKernelFrom (sourceWith PRIVATE_LEAF 5) BASE TARGET_BASE BITS =
        .error .tableBacking := by
  decide +kernel

/-- Step 6, the walk entry by entry in index order, each table under its entry
before the next entry: the leaf of `KernelPrivateReadWrite` under root entry
1, `InvalidDescriptor`, before root entry 2, which points outside the tables
in use, `TableBacking`; and root entry 0, which points outside them,
`TableBacking`, before that leaf. -/
theorem priorityCloneStep6 :
    (emptySet .lower 4).cloneKernelFrom (sourceWith PRIVATE_LEAF 3 [(2, 0x1_0000_3003)])
        BASE TARGET_BASE BITS = .error .invalidDescriptor ∧
      (emptySet .lower 4).cloneKernelFrom (sourceWith PRIVATE_LEAF 3 [(0, 0x1_0000_3003)])
        BASE TARGET_BASE BITS = .error .tableBacking := by
  decide +kernel

/-- Step 7: the walk, the leaf of `KernelPrivateReadWrite`,
`InvalidDescriptor`, before a record of 4 tables, one of which the walk does
not reach, `TableBacking`. -/
theorem priorityCloneStep7 :
    (emptySet .lower 4).cloneKernelFrom (sourceWith PRIVATE_LEAF 4) BASE TARGET_BASE BITS =
      .error .invalidDescriptor := by
  decide +kernel

/-! ## Unreachable error branches

Branches of the entries that fail with an error, but that no input of the
entry reaches under its machine widths or on the boot memory maps that the
fdt entries build. Each proposition states the fact that keeps the entry from
the branch, with its reason; a planned theorem below
`Krepi.Proofs.PageTables.Witnesses.TableSets` proves it. The error of each
branch is witnessed above where another branch of the same entry gives it. -/

/-- A boot memory map that an entry of the fdt specification builds:
`MemoryPlan::all_ram`, or `MemoryPlan::new`, which `from_pi5` calls. -/
def BuiltPlan (p : Fdt.MemoryPlan) : Prop :=
  (∃ ram boot firmware, Fdt.MemoryPlan.allRam ram boot firmware = .ok p) ∨
    ∃ window ram boot firmware, Fdt.MemoryPlan.new window ram boot firmware = .ok p

/-- **Planned.** `direct_map` never fails with `Alignment` at a usable range:
every usable range of a boot memory map that the fdt entries build starts and
ends on a page boundary, since its managed banks and its reservations are
whole pages. Its `Alignment` is that of `base` (`directMapAlignment`). -/
def DirectMapRangesOnPages : Prop :=
  ∀ p, BuiltPlan p → ∀ u ∈ p.availableRanges,
    u.start.toNat % PAGE_SIZE = 0 ∧ u.endNat % PAGE_SIZE = 0

/-- **Planned.** `direct_map` never fails with `AlreadyMapped` for a leaf that
an earlier usable range shares an address with: the usable ranges of a boot
memory map that the fdt entries build, in address order, each end at or
before the start of the next, since they are disjoint parts of disjoint
managed banks, and every leaf lies inside its range. Its `AlreadyMapped` is
that of the walk (`directMapAlreadyMapped`). -/
def DirectMapRangesApart : Prop :=
  ∀ p, BuiltPlan p →
    (sortByKey (·.start.toNat) p.availableRanges).Pairwise fun a b => a.endNat ≤ b.start.toNat

/-- **Planned.** The check of the target pool of `clone_kernel_from` never fails
with `AddressWidth`: it takes the width that the check of the source pool has
accepted. Its `AddressWidth` is that of the source
(`cloneKernelFromAddressWidth`). -/
def CloneTargetWidthChecked : Prop :=
  ∀ (N : Nat) (sourceBase base : UInt64) (bits : UInt8),
    checkPool N sourceBase bits = .ok () → checkPool N base bits ≠ .error .addressWidth

/-! ## The two variants -/

/-- **The variant that rejects every input is refuted.** Each frozen function of
rows 106 to 111 that can fail succeeds on an input, by the success witnesses
above. -/
theorem notAlwaysRejecting :
    (∃ a n r, PhysRange.new a n = .ok r) ∧
    (∃ r N, ∃ s : Tables r N, ∃ v b w d, s.lookupPage v b w = .ok d) ∧
    (∃ r N, ∃ s : Tables r N, ∃ v b w d, s.lookupBlock v b w = .ok d) ∧
    (∃ r N, ∃ t s : Tables r N, ∃ sb b w x, t.cloneKernelFrom s sb b w = .ok x) ∧
    (∃ r N, ∃ s : Tables r N, ∃ v p k b w x, s.mapPage v p k b w = .ok x) ∧
    (∃ r N, ∃ s : Tables r N, ∃ v p b w x, s.mapBlock v p b w = .ok x) ∧
    (∃ r N, ∃ s : Tables r N, ∃ v b w x, s.unmapPage v b w = .ok x) ∧
    (∃ N, ∃ s : Tables .lower N, ∃ l b w x, s.kernelMap l b w = .ok x) ∧
    (∃ N, ∃ s : Tables .upper N, ∃ m b w x, BuiltPlan m ∧ s.directMap m b w = .ok x) :=
  ⟨⟨_, _, _, physRangeNewOk.1⟩, ⟨_, _, _, _, _, _, _, lookupPageOk⟩,
    ⟨_, _, _, _, _, _, _, lookupBlockOk⟩, ⟨_, _, _, _, _, _, _, ok_of_outcome cloneKernelFromOk⟩,
    ⟨_, _, _, _, _, _, _, _, ok_of_outcome mapPageOk⟩,
    ⟨_, _, _, _, _, _, _, ok_of_outcome mapBlockOk.1⟩,
    ⟨_, _, _, _, _, _, _, unmapPageOk⟩, ⟨_, _, _, _, _, ok_of_outcome kernelMapOk⟩,
    (ok_of_outcome directMapOk).elim fun x h => ⟨_, _, _, _, _, x, Or.inl ⟨_, _, _, plansBuilt.1⟩, h⟩⟩

/-- **The variant that accepts every input is refuted.** Each frozen function
of rows 106 to 111 that can fail fails on an input, by the rejection
witnesses above. -/
theorem notAlwaysSucceeding :
    (∃ a n e, PhysRange.new a n = .error e) ∧
    (∃ r N, ∃ s : Tables r N, ∃ v b w e, s.lookupPage v b w = .error e) ∧
    (∃ r N, ∃ s : Tables r N, ∃ v b w e, s.lookupBlock v b w = .error e) ∧
    (∃ r N, ∃ t s : Tables r N, ∃ sb b w e, t.cloneKernelFrom s sb b w = .error e) ∧
    (∃ r N, ∃ s : Tables r N, ∃ v p k b w e, s.mapPage v p k b w = .error e) ∧
    (∃ r N, ∃ s : Tables r N, ∃ v p b w e, s.mapBlock v p b w = .error e) ∧
    (∃ r N, ∃ s : Tables r N, ∃ v b w e, s.unmapPage v b w = .error e) ∧
    (∃ N, ∃ s : Tables .lower N, ∃ l b w e, s.kernelMap l b w = .error e) ∧
    (∃ N, ∃ s : Tables .upper N, ∃ m b w e, BuiltPlan m ∧ s.directMap m b w = .error e) :=
  ⟨⟨_, _, _, physRangeNewInvalidRange⟩, ⟨_, _, _, _, _, _, _, lookupPageNotMapped.1⟩,
    ⟨_, _, _, _, _, _, _, lookupBlockNotMapped.1⟩,
    ⟨_, _, _, _, _, _, _, _, cloneKernelFromInvalidDescriptor.2.2.1⟩,
    ⟨_, _, _, _, _, _, _, _, _, mapPageAlreadyMapped.1⟩,
    ⟨_, _, _, _, _, _, _, _, mapBlockAlreadyMapped.1⟩,
    ⟨_, _, _, _, _, _, _, unmapPageNotMapped.1⟩, ⟨_, _, _, _, _, _, kernelMapOutOfTables⟩,
    ⟨_, _, _, _, _, _, Or.inl ⟨_, _, _, plansBuilt.1⟩, directMapOutOfTables⟩⟩

end Krepi.Spec.PageTables.Witnesses.TableSets
