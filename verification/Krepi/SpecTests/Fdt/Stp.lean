module

public import Krepi.SpecTests.Fdt.Builder
public import Krepi.SpecTests.Fdt.Boards

/-!
# Device tree: specification tests

The specification tests of the `fdt` component: for each requirement of
`docs/domains/boot-platform/fdt/requirements.md`, FDT-R01 to FDT-R10, one
input that the specification must accept, with the result that it must give,
and one that it must reject, with the error that it must give. Each test is a
proposition on concrete inputs, most of them trees that `Builder` writes,
and a planned theorem below `Krepi.Proofs.Fdt.Stp` proves it. The docstring
of each names its requirement and the part of the requirement's criterion
that it instantiates.

The expected results are literals written from the requirements and the
contract: the spans, regions, counts and errors that the rules give for the
input, worked out by hand. None is computed by the specification. Where a
test compares two runs, as for FDT-R10, it also states their common result.

Two requirements have no rejection of their own. FDT-R02's rule that no byte
string makes an entry panic holds of every total function, and FDT-R10's
rule that results are functions of the bytes and the arguments holds of
every function. Their rejecting tests take the rest of each requirement: a
prefix of a valid tree is rejected (FDT-R02), and a broken `device_type` of
`/chosen`, the one value of `/chosen` that the memory discovery reads of a
QEMU virt tree, makes the discovery fail (FDT-R10), so that the values of
`/chosen` that it does not read are exactly the others.

All inputs are below 1 KiB, except the two trees of FDT-R05, which are the
limit itself: 128 KiB and 128 KiB and 1 byte, the tree of the 8 GB model
followed by zero bytes up to that `totalsize`. The tests of the Pi 5 and of
QEMU virt give the entries the profiles of those boards
(`Krepi.SpecTests.Fdt.Boards`).
-/

@[expose] public section

namespace Krepi.SpecTests.Fdt

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

/-! ## Helpers -/

/-- The span of an address and a size. -/
def spanOf (p : Nat × Nat) : Span := ⟨UInt64.ofNat p.1, UInt64.ofNat p.2⟩

/-- The result of `f` on the node of the absolute path `path` in the tree that
the parse gives for `bytes`: the error of the parse, of the lookup or of `f`,
and none when no node has that path. -/
def onNode {α : Type} (bytes : ByteArray) (path : String) (f : Node → Except Error α) :
    Except Error (Option α) := do
  match ← (← Fdt.parse bytes).findNode path with
  | none => pure none
  | some n => some <$> f n

/-! ## FDT-R01: bounded parse of an untrusted tree -/

/-- A property name of `MAX_PROPERTY_NAME`, 64, bytes, with each character
other than letters and digits that a property name may hold. -/
def nameAtLimit : String := "#vendor,name-at.the_limit+of?property-names-0123456789abcdefghij"

/-- The root alone with two properties: the `model` of QEMU virt, a string of
17 bytes whose padding holds the bytes `0, 0, 2` that QEMU leaves there, and a
property named `name` without a value. -/
def namedTree (name : String) : ByteArray :=
  (Builder.empty.beginNode "" |>.string "model" "linux,dummy-virt" |>.overwrite [0, 0, 2]
    |>.flag name |>.endNode).finish

/-- **FDT-R01, accepted.** Criterion: "for each of these limits, an input at
the limit is accepted", for the bytes of a property name, on a tree with the
bytes that QEMU leaves in the padding after a property value, which the
requirement also accepts. The tree of 187 bytes with a property name of
exactly 64 bytes is accepted; its value is the root with its two properties,
the value of `model` exactly its 17 bytes, without the padding. -/
def ParseAcceptsNameAtLimit : Prop :=
  Fdt.parse (namedTree nameAtLimit) =
    .ok { totalSize := 187
          reservations := []
          records := #[{ name := ""
                         parent := none
                         properties := [("model", bytesOf (stringBytes "linux,dummy-virt")),
                           (nameAtLimit, ByteArray.empty)] }] }

/-- **FDT-R01, rejected.** Criterion: "one 1 above it fails with the error of
the contract", for the bytes of a property name: the same tree with a name
of 65 bytes fails with `BadString` (Format and bounds, Names). -/
def ParseRejectsNameAboveLimit : Prop :=
  Fdt.parse (namedTree (nameAtLimit ++ "k")) = .error .badString

/-! ## FDT-R02: rejection without partial results -/

/-- **FDT-R02, accepted.** Criterion: "every tree with one byte changed
returns from the parse and from the entries on it". `minimal` with its byte
at offset 165 inverted, the byte `0x20` of the size cell `0x0020_0000` of the
`reg` of `/memory@100000000`, which becomes `0x00df_0000`, is accepted, and
the memory discovery on it returns the one RAM range of that size. -/
def EntriesReturnOnChangedByte : Prop :=
  (Fdt.parse (flipByte minimal 165)).bind Fdt.discoverMemory =
    .ok { ram := [⟨0x1_0000_0000, 0xdf_0000⟩], reserved := [], dynamic := 0 }

/-- **FDT-R02, rejected.** Criterion: "every prefix of a valid tree is
rejected", here as the rejecting test of the requirement, whose rule that no
byte string makes an entry panic no total function can break. `minimal`
without its last byte, the NUL of the last name of its strings block, fails
with `Truncated` and no tree: its header declares 223 bytes. -/
def ParseRejectsPrefix : Prop :=
  Fdt.parse (minimal.extract 0 (minimal.size - 1)) = .error .truncated

/-! ## FDT-R03: memory discovery -/

/-- A tree whose root has 1 address cell and 1 size cell and whose node
`memory@0` has `n` RAM ranges, `[i * 0x2000, i * 0x2000 + 0x1000)` for each
`i < n`, with one entry of the reservation map, `[0x1000, 0x2000)`, in the
hole between the first two ranges. -/
def ramRangesTree (n : Nat) : ByteArray :=
  (Builder.empty.reserve 0x1000 0x1000 |>.beginNode "" |>.cells "#address-cells" [1]
    |>.cells "#size-cells" [1] |>.beginNode "memory@0" |>.string "device_type" "memory"
    |>.cells "reg" ((List.range n).flatMap fun i => [i * 0x2000, 0x1000])
    |>.endNode |>.endNode).finish

/-- **FDT-R03, accepted.** Criterion: "32 RAM ranges ... are accepted", with
a reserved region outside every RAM range, which the discovery "accepts".
The 32 RAM ranges come in tree order, and the entry of the reservation map is
a reserved region with `no-map` set and `reusable` clear, kept although it
lies in a hole. -/
def DiscoveryAcceptsMaxRamRanges : Prop :=
  (Fdt.parse (ramRangesTree 32)).bind Fdt.discoverMemory =
    .ok { ram := (List.range 32).map fun i => ⟨UInt64.ofNat (i * 0x2000), 0x1000⟩,
          reserved := [⟨⟨0x1000, 0x1000⟩, true, false⟩], dynamic := 0 }

/-- **FDT-R03, rejected.** Criterion: "33 ... fail with `LimitExceeded`": the
same tree with 33 RAM ranges. -/
def DiscoveryRejectsExcessRamRanges : Prop :=
  (Fdt.parse (ramRangesTree 33)).bind Fdt.discoverMemory = .error .limitExceeded

/-! ## FDT-R04: dynamic reservations -/

/-- A tree with the root of 2 address cells and 2 size cells, the RAM range
`[0x4000_0000, 0x4800_0000)` and a `/reserved-memory` with the cells of the
root and an empty `ranges`, whose children `children` writes. -/
def reservedTree (children : Builder → Builder) : ByteArray :=
  (Builder.empty.root
    |>.beginNode "memory@40000000" |>.string "device_type" "memory"
    |>.cells "reg" [0, 0x4000_0000, 0, 0x800_0000] |>.endNode
    |>.beginNode "reserved-memory" |>.cells "#address-cells" [2] |>.cells "#size-cells" [2]
    |>.flag "ranges" |> children |>.endNode |>.endNode).finish

/-- **FDT-R04, accepted.** Criterion: "the tests of dynamic reservations of
the testing obligations pass": enabled children of `/reserved-memory` with a
`size` and without a `reg`, one of one cell below `#size-cells` 2, with
`reusable` and `alloc-ranges` of 3 bytes, as the shipped Pi 5 tree has its
`linux,cma`, and one of two cells with `no-map`, are counted as 2 dynamic
reservations and give no reserved region; a disabled one is ignored. -/
def DiscoveryRecordsDynamicReservations : Prop :=
  (Fdt.parse (reservedTree fun b => b
      |>.beginNode "linux,cma" |>.string "compatible" "shared-dma-pool" |>.flag "reusable"
      |>.cells "size" [0x400_0000] |>.property "alloc-ranges" [0x12, 0x34, 0x56] |>.endNode
      |>.beginNode "pool" |>.flag "no-map" |>.cells "size" [0, 0x10_0000] |>.endNode
      |>.beginNode "disabled-pool" |>.string "status" "disabled" |>.cells "size" [0x1000]
      |>.endNode)).bind Fdt.discoverMemory =
    .ok { ram := [⟨0x4000_0000, 0x800_0000⟩], reserved := [], dynamic := 2 }

/-- **FDT-R04, rejected.** Criterion: "a child with both `reg` and `size` is a
static region", as the testing obligations state it: a child with `size` and
a `reg` of size 0 is static, so its `reg` is read and its empty span fails
with `EmptyRegion`, where a dynamic reservation would be counted. -/
def DiscoveryRejectsEmptyStaticReservation : Prop :=
  (Fdt.parse (reservedTree fun b => b
      |>.beginNode "pool@10000000" |>.cells "reg" [0, 0x1000_0000, 0, 0]
      |>.cells "size" [0, 0x1000] |>.endNode)).bind Fdt.discoverMemory =
    .error .emptyRegion

/-! ## FDT-R05: Pi 5 hand-over checks -/

/-- The address of the Pi 5 hand-over trees of the tests, a multiple of 8
inside the first RAM range. -/
def PI5_DTB : UInt64 := 0x800_0000

/-- The span of the image of the Pi 5 tests, inside the first RAM range and
disjoint from the tree and from `atf@0`. -/
def PI5_IMAGE : Span := ⟨0x20_0000, 0x40_0000⟩

/-- A Pi 5 hand-over tree with the reservation entries `entries` and the RAM
ranges `ranges`: the root with 2 address cells, 2 size cells and the
`compatible` `raspberrypi,5-model-b`, `brcm,bcm2712`; the node `memory@0`
with the ranges in 2 cells each; and `/reserved-memory` with the cells of the
root, an empty `ranges` and the child `atf@0`, `[0, 0x8_0000)` with
`no-map`, as the 8 GB hand-over tree has it. -/
def pi5Builder (entries ranges : List (Nat × Nat)) : Builder :=
  (entries.foldl (fun b e => b.reserve e.1 e.2) Builder.empty).root
    |>.strings "compatible" ["raspberrypi,5-model-b", "brcm,bcm2712"]
    |>.beginNode "memory@0" |>.string "device_type" "memory"
    |>.property "reg" (ranges.flatMap fun r => be64 r.1 ++ be64 r.2) |>.endNode
    |>.beginNode "reserved-memory" |>.cells "#address-cells" [2] |>.cells "#size-cells" [2]
    |>.flag "ranges" |>.beginNode "atf@0" |>.flag "no-map" |>.cells "reg" [0, 0, 0, 0x8_0000]
    |>.endNode |>.endNode |>.endNode

/-- The RAM ranges of the 8 GB model, as the prototype measured them. -/
def ram8GB : List (Nat × Nat) :=
  [(0, 0x3fc0_0000), (0x4000_0000, 0xc000_0000), (0x1_0000_0000, 0x1_0000_0000)]

/-- The boot memory of the tree of the 8 GB model at `PI5_DTB`, with the
image `PI5_IMAGE` and the hand-over profile of the Pi 5, at a `totalsize` of
`size`. -/
def pi5BootOfSize (size : Nat) : Except Error BootMemory :=
  (Fdt.parse ((pi5Builder [(0x3fd2_31e0, 0x3e)] ram8GB).finishTo size)).bind
    (·.discoverBootMemory pi5HandOver PI5_DTB PI5_IMAGE)

/-- **FDT-R05, accepted.** Criterion: "a hand-over tree of exactly 128 KiB is
accepted". The tree of the 8 GB model, with its three measured RAM ranges,
`atf@0` and the reservation entry of 62 bytes at `0x3fd2_31e0`, in the hole
below 1 GiB, padded to a `totalsize` of `0x2_0000`, is accepted at
`0x800_0000` with the image `[0x20_0000, 0x60_0000)`: the memory map keeps
both reserved regions, the entry of the map first; the tree spans its 128 KiB;
and `ram_bytes` is 8 GiB less 4 MiB; the value holds the limit and the
alignment of the profile. The input is 128 KiB long. -/
def Pi5AcceptsTreeAtLimit : Prop :=
  pi5BootOfSize 0x2_0000 =
    .ok { memory := { ram := ram8GB.map spanOf,
                      reserved := [⟨⟨0x3fd2_31e0, 0x3e⟩, true, false⟩, ⟨⟨0, 0x8_0000⟩, true, false⟩],
                      dynamic := 0 },
          dtb := ⟨0x800_0000, 0x2_0000⟩, image := PI5_IMAGE, ramBytes := 0x1_ffc0_0000,
          maxBlobSize := 0x2_0000, alignmentLog2 := 3 }

/-- **FDT-R05, rejected.** Criterion: "one of 1 byte more fails with
`LimitExceeded`": the same tree at a `totalsize` of `0x2_0001`, which the
parse accepts. The input is 128 KiB and 1 byte long. -/
def Pi5RejectsTreeAboveLimit : Prop :=
  pi5BootOfSize 0x2_0001 = .error .limitExceeded

/-! ## FDT-R06: every RAM model of the Pi 5 -/

/-- A RAM model of the Pi 5 in a test: the RAM ranges of its hand-over tree,
its RAM, the installed size less 4 MiB, and the usable ranges of its boot
memory map with the image, the tree and `atf@0` left out. -/
structure RamModel where
  ranges : List (Nat × Nat)
  ramBytes : UInt64
  usable : List Span

/-- The usable ranges of the first RAM range `[0, 0x3fc0_0000)` of every model:
`atf@0`, the image and the page of the tree left out. -/
def firstRangeUsable : List Span :=
  [⟨0x8_0000, 0x18_0000⟩, ⟨0x60_0000, 0x7a0_0000⟩, ⟨0x800_1000, 0x37bf_f000⟩]

/-- The five RAM models, 1, 2, 4, 8 and 16 GB, with the ranges of the
contract's table, inferred but for the measured 8 GB. -/
def ramModels : List RamModel :=
  [⟨[(0, 0x3fc0_0000)], 0x3fc0_0000, firstRangeUsable⟩,
   ⟨[(0, 0x3fc0_0000), (0x4000_0000, 0x4000_0000)], 0x7fc0_0000,
     firstRangeUsable ++ [⟨0x4000_0000, 0x4000_0000⟩]⟩,
   ⟨[(0, 0x3fc0_0000), (0x4000_0000, 0xc000_0000)], 0xffc0_0000,
     firstRangeUsable ++ [⟨0x4000_0000, 0xc000_0000⟩]⟩,
   ⟨ram8GB, 0x1_ffc0_0000,
     firstRangeUsable ++ [⟨0x4000_0000, 0xc000_0000⟩, ⟨0x1_0000_0000, 0x1_0000_0000⟩]⟩,
   ⟨[(0, 0x3fc0_0000), (0x4000_0000, 0xc000_0000), (0x1_0000_0000, 0x3_0000_0000)], 0x3_ffc0_0000,
     firstRangeUsable ++ [⟨0x4000_0000, 0xc000_0000⟩, ⟨0x1_0000_0000, 0x3_0000_0000⟩]⟩]

/-- The boot memory of the hand-over tree with the RAM ranges `ranges` and
`atf@0` at `PI5_DTB`, with the image `PI5_IMAGE` and the hand-over profile of
the Pi 5, and the boot memory map that the testing obligations build from it:
`MemoryPlan::all_ram` with its RAM ranges, the image and the tree as boot
storage, and its reserved regions. -/
def pi5Plan (ranges : List (Nat × Nat)) : Except Error (BootMemory × Except PlanError MemoryPlan) :=
  ((Fdt.parse (pi5Builder [] ranges).finish).bind
    (·.discoverBootMemory pi5HandOver PI5_DTB PI5_IMAGE)).map
    fun m => (m, MemoryPlan.allRam m.ram [m.image, m.dtb] m.reserved)

/-- **FDT-R06, accepted.** Criterion: "for each of the 1, 2, 4 and 16 GB
models, a host test parses a hand-over tree of its inferred ranges and builds
its boot memory map, with the installed size less 4 MiB as RAM and the hole
left out of the usable ranges", here with the measured 8 GB model as well.
For each model, the discovery gives its RAM ranges and `ram_bytes`, and the
usable ranges of the boot memory map are those of `RamModel.usable`: none
reaches into the hole `[0x3fc0_0000, 0x4000_0000)`. -/
def Pi5ModelsBuildBootMemoryMaps : Prop :=
  ∀ model ∈ ramModels,
    (pi5Plan model.ranges).map (fun r => (r.1.ram, r.1.ramBytes, r.2.map (·.availableRanges))) =
      .ok (model.ranges.map spanOf, model.ramBytes, .ok model.usable)

/-- **FDT-R06, rejected.** Criterion: "at most 16 GiB less 4 MiB, within the
16 GiB of the boot memory map", with the scope's "RAM above 16 GiB in all is
not supported". A hand-over tree of the shape of the models with 32 GB, the
third range up to `0x8_0000_0000`, passes the discovery with `ram_bytes`
32 GiB less 4 MiB, and its boot memory map fails with `ArenaTooLarge`. -/
def BootMemoryMapRejectsRamAboveCapacity : Prop :=
  (pi5Plan [(0, 0x3fc0_0000), (0x4000_0000, 0xc000_0000), (0x1_0000_0000, 0x7_0000_0000)]).map
      (fun r => (r.1.ramBytes, r.2)) =
    .ok (0x7_ffc0_0000, .error .arenaTooLarge)

/-! ## FDT-R07: boot memory map -/

/-- The RAM bank of QEMU virt, 128 MiB at 1 GiB. -/
def qemuBank : Span := ⟨0x4000_0000, 0x800_0000⟩

/-- Four spans of boot storage in the bank: the tree, the image, a boot bundle
and a span that does not start on a page. -/
def fourBootSpans : List Span :=
  [⟨0x4000_0000, 0x1234⟩, ⟨0x4020_0000, 0x12_3456⟩, ⟨0x4040_0000, 0x1000⟩, ⟨0x4050_0800, 0x800⟩]

/-- One firmware reservation of 16 bytes at the last page of the bank,
`reusable`. -/
def lastPageReusable : List ReservedRegion := [⟨⟨0x47ff_f000, 0x10⟩, false, true⟩]

/-- **FDT-R07, accepted.** Criterion: "boot storage of 4 spans is accepted".
The map keeps the bank and manages it whole; it rounds each span of boot
storage and the reservation outward to whole pages, in input order; and its
usable ranges leave out every page of both, the `reusable` reservation
included. -/
def AllRamAcceptsMaxBootStorage : Prop :=
  (MemoryPlan.allRam [qemuBank] fourBootSpans lastPageReusable).map
      (fun p => (p, p.availableRanges)) =
    .ok ({ ram := [qemuBank], managed := [qemuBank],
           boot := [⟨0x4000_0000, 0x2000⟩, ⟨0x4020_0000, 0x12_4000⟩, ⟨0x4040_0000, 0x1000⟩,
             ⟨0x4050_0000, 0x1000⟩],
           firmware := [⟨0x47ff_f000, 0x1000⟩] },
         [⟨0x4000_2000, 0x1f_e000⟩, ⟨0x4032_4000, 0xd_c000⟩, ⟨0x4040_1000, 0xf_f000⟩,
           ⟨0x4050_1000, 0x7af_e000⟩])

/-- **FDT-R07, rejected.** Criterion: "of 5 fails with `Capacity`": the same
map with a fifth span of boot storage. -/
def AllRamRejectsExcessBootStorage : Prop :=
  MemoryPlan.allRam [qemuBank] (fourBootSpans ++ [⟨0x4060_0000, 0x1000⟩]) lastPageReusable =
    .error .capacity

/-! ## FDT-R08: CPU nodes -/

/-- A QEMU virt tree with two CPU nodes below a `/cpus` of 1 address cell and
0 size cells, `cpu@0` with the `reg` 0 and without an `enable-method`, and
`cpu@1` with the `reg` `reg1` and the `enable-method` `psci`, both enabled
Cortex-A76 CPUs; and `/psci` with the `compatible` `arm,psci-1.0`,
`arm,psci-0.2` and the `method` `hvc`. -/
def cpusTree (reg1 : Nat) : ByteArray :=
  (Builder.empty.root |>.string "compatible" "linux,dummy-virt"
    |>.beginNode "cpus" |>.cells "#address-cells" [1] |>.cells "#size-cells" [0]
    |>.beginNode "cpu@0" |>.string "device_type" "cpu" |>.string "compatible" "arm,cortex-a76"
    |>.cells "reg" [0] |>.endNode
    |>.beginNode "cpu@1" |>.string "device_type" "cpu" |>.string "compatible" "arm,cortex-a76"
    |>.cells "reg" [reg1] |>.string "enable-method" "psci" |>.endNode
    |>.endNode
    |>.beginNode "psci" |>.strings "compatible" ["arm,psci-1.0", "arm,psci-0.2"]
    |>.string "method" "hvc" |>.endNode
    |>.endNode).finish

/-- **FDT-R08, accepted.** Criterion: "the vectors of the CPU nodes give their
expected outputs", on a tree of the shape of those vectors: the QEMU virt
profile with PSCI over HVC accepts the two CPUs, whose IDs are affinity level
0, CPU 0 without an `enable-method`, with a count of 2; and the timer records
of QEMU virt for two CPUs, type 1, the interrupts 13, 14, 11 and 10 and the
flags `0x304`, are accepted for that topology. -/
def CpusAcceptsQemuPair : Prop :=
  ((Fdt.parse (cpusTree 1)).bind (·.discoverCpus qemuHvcCpus)).map
      (fun t => (t, t.validateTimers
        (bytesOf (cellBytes [1, 13, 0x304, 1, 14, 0x304, 1, 11, 0x304, 1, 10, 0x304])))) =
    .ok (⟨qemuHvcCpus, 2⟩, .ok ())

/-- **FDT-R08, rejected.** Criterion: the logical IDs "run from 0 to
`count - 1` without a gap or a repeat": the same tree with the `reg` 0 for
`cpu@1` repeats the ID 0 and fails with `BadProperty`, where keeping one of
the two would give a count of 1. -/
def CpusRejectsRepeatedId : Prop :=
  (Fdt.parse (cpusTree 0)).bind (·.discoverCpus qemuHvcCpus) = .error .badProperty

/-! ## FDT-R09: address translation -/

/-- A tree with a bus `soc` of 1 address cell and 1 size cell below a root of
2 and 2, whose `ranges` maps `[0x7c00_0000, 0x8000_0000)` to `0xfc00_0000`
and whose `dma-ranges` maps `[0xc000_0000, 0x1_0000_0000)` to 0, with the
device `serial@7d001000`, whose `reg` is `[0x7d00_1000, 0x7d00_1200)` in the
cells of `soc`. -/
def busTree : ByteArray :=
  (Builder.empty.root
    |>.beginNode "soc" |>.string "compatible" "simple-bus" |>.cells "#address-cells" [1]
    |>.cells "#size-cells" [1] |>.cells "ranges" [0x7c00_0000, 0, 0xfc00_0000, 0x400_0000]
    |>.cells "dma-ranges" [0xc000_0000, 0, 0, 0x4000_0000]
    |>.beginNode "serial@7d001000" |>.cells "reg" [0x7d00_1000, 0x200] |>.endNode
    |>.endNode |>.endNode).finish

/-- **FDT-R09, accepted.** Criterion: "the vectors of the translation give
their expected outputs", on a tree of their shape: the `reg` of the device is
read in the cells of its bus, not of the root, and `translate_reg` takes its
span through the one window of the bus's `ranges`, not its `dma-ranges`, to
`[0xfd00_1000, 0xfd00_1200)`. -/
def TranslateRegThroughBus : Prop :=
  onNode busTree "/soc/serial@7d001000" (fun n => do (← n.reg).entries.mapM n.translateReg) =
    .ok (some [⟨0xfd00_1000, 0x200⟩])

/-- **FDT-R09, rejected.** Criterion: "a request that two windows hold ...
fails": a map of 1 child cell, 1 parent cell and 1 size cell with the windows
`[0x1000, 0x2000)` to `0x1_0000` and `[0x1800, 0x2800)` to `0x2_0000`, which
both hold the request `[0x1800, 0x1900)`, fails with `AmbiguousMapping`
(rule 3), where taking either window would give a span. -/
def TranslationRejectsTwoWindows : Prop :=
  (AddressMap.new (some (bytesOf (cellBytes [0x1000, 0x1_0000, 0x1000, 0x1800, 0x2_0000, 0x1000])))
      1 1 1).bind (·.toParent ⟨0x1800, 0x100⟩) =
    .error .ambiguousMapping

/-! ## FDT-R10: the same result on every boot -/

/-- A QEMU virt tree with `/chosen`, whose properties are `chosen`, and the
memory node of 128 MiB at 1 GiB, as QEMU's loader writes it. -/
def qemuTree (chosen : List (String × List UInt8)) : ByteArray :=
  (Builder.empty.root |>.string "compatible" "linux,dummy-virt" |>.beginNode "chosen"
    |> (fun b => chosen.foldl (fun b p => b.property p.1 p.2) b) |>.endNode
    |>.beginNode "memory@40000000" |>.string "device_type" "memory"
    |>.cells "reg" [0, 0x4000_0000, 0, 0x800_0000] |>.endNode |>.endNode).finish

/-- The seeds of one boot of QEMU virt: a `kaslr-seed` of 8 bytes and an
`rng-seed` of 32 bytes. -/
def seeds (kaslr rng : List UInt8) : List (String × List UInt8) :=
  [("kaslr-seed", kaslr), ("rng-seed", rng)]

/-- The seeds of a first boot. -/
def seedsA : List (String × List UInt8) :=
  seeds [0x9d, 0x3c, 0x51, 0xe2, 0x07, 0xa8, 0x6f, 0x14]
    [0x5e, 0x1f, 0xc2, 0x88, 0x30, 0x4b, 0xd7, 0x92, 0x06, 0xee, 0x7a, 0x13, 0xb5, 0x61, 0x2c, 0xf0,
     0x48, 0x9a, 0x05, 0xd3, 0x7e, 0x21, 0xbc, 0x64, 0x0f, 0xa1, 0x57, 0xc8, 0x3d, 0x96, 0xe9, 0x02]

/-- The seeds of a second boot, every byte other than in `seedsA`. -/
def seedsB : List (String × List UInt8) :=
  seeds [0x11, 0xf4, 0x2b, 0x60, 0xca, 0x95, 0x3e, 0xd1]
    [0xa7, 0x40, 0x19, 0xfc, 0x6d, 0x82, 0x3b, 0x55, 0xe0, 0x0c, 0x9f, 0x76, 0x28, 0xb3, 0xd4, 0x4e,
     0x81, 0x37, 0xea, 0x1c, 0x63, 0xbf, 0x0a, 0x9d, 0xf2, 0x45, 0x8c, 0x27, 0xd9, 0x70, 0x16, 0xab]

/-- The image of QEMU virt in the tests, 1 MiB at `0x4020_0000`. -/
def QEMU_IMAGE : Span := ⟨0x4020_0000, 0x10_0000⟩

/-- The boot of QEMU virt on the tree with the seeds `chosen`: the parse, the
memory discovery and the boot memory map of `MemoryPlan::all_ram` with the
RAM ranges, the tree at the start of RAM and the image as boot storage, and
the reserved regions as firmware reservations. -/
def qemuBoot (chosen : List (String × List UInt8)) :
    Except Error (MemoryMap × Except PlanError MemoryPlan) :=
  (Fdt.parse (qemuTree chosen)).bind fun t => t.discoverMemory.map fun m =>
    (m, MemoryPlan.allRam m.ram [⟨0x4000_0000, t.totalSize⟩, QEMU_IMAGE] m.reserved)

/-- **FDT-R10, accepted.** Criterion: "three cold boots of QEMU virt ... give
the same results of the parse and of the boot memory map", here two boots
whose trees differ only in the seeds of `/chosen`: both give the same memory
map, one RAM range and nothing reserved, and the same boot memory map, the
page of the tree and the image as boot storage. The parse accepts both
trees, and the trees that it gives differ at most in values that no rule
reads (`unreadByDiscoveries`), here the seeds. -/
def SeedsDoNotReachResults : Prop :=
  (∀ chosen ∈ [seedsA, seedsB],
    qemuBoot chosen =
      .ok (⟨[qemuBank], [], 0⟩,
        .ok { ram := [qemuBank], managed := [qemuBank],
              boot := [⟨0x4000_0000, 0x1000⟩, QEMU_IMAGE], firmware := [] })) ∧
  ∃ t t', Fdt.parse (qemuTree seedsA) = .ok t ∧ Fdt.parse (qemuTree seedsB) = .ok t' ∧
    t.SameExceptValues (unreadByDiscoveries t) t'

/-- **FDT-R10, rejected.** The criterion, the same results on three cold
boots, has no rejection, and the results are functions of their inputs by
construction; this test takes the requirement's rule that no entry reads a
value of `/chosen` other than its `device_type` and, when that is `memory`,
its `status`: the memory discovery reads the `device_type` of every child of
the root. The tree of `seedsA` with a `device_type` of `/chosen` that is not
UTF-8, the bytes `0xff, 0`, fails with `BadString`: the results depend on
that value of `/chosen`, and not on its seeds (`SeedsDoNotReachResults`). -/
def ChosenDeviceTypeIsRead : Prop :=
  (Fdt.parse (qemuTree (seedsA ++ [("device_type", [0xff, 0])]))).bind Fdt.discoverMemory =
    .error .badString

end Krepi.SpecTests.Fdt
