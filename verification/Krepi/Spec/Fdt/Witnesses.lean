module

public import Krepi.SpecTests.Fdt.Builder
public import Krepi.SpecTests.Fdt.Boards

/-!
# Device tree: witnesses

Theorems that witness that the specification of the `fdt` component is not
vacuous: for every frozen function of the entry table of its contract
(`docs/domains/boot-platform/fdt/contract.md`, rows `Fdt::parse` to
`Span::new`), one input on which it succeeds, with the value that it gives,
and for every error that the contract gives that function, one input on which
it fails with that error. The value types and the limits of the table are
read through these functions and have no witness of their own. Every expected
value is a literal worked out from the contract, never computed by the
specification.

Each witness is proved here by `decide +kernel`: the kernel evaluates both
sides. Lean core decides no equality of `Except`, so the module states each
witness as an equation `f x = .ok v` or `f x = .error e` and decides it with
a local instance that compares the constructors and their payloads; the
instance appears in no statement.

The parse reads the inputs of its witnesses as bytes, which the builder of
the specification tests writes (`Krepi.SpecTests.Fdt.Builder`). The witnesses
of the entries on a tree read trees of records written in preorder
(`outline`), each of which the check of the structural invariant of trees
accepts (`treesWellFormed`), the invariant that every tree of the parse has.

For each step of the two error orders of the contract, one more witness
gives an input that breaks a rule of that step and a later rule, and states
the error of the step (`priorityStep1` to `priorityStep8`, `priorityPlanStep1`
to `priorityPlanStep7`).

Error branches that no input of an entry reaches have no witness; for each,
a proposition below states that the entry never takes it, with its reason,
and a planned theorem proves it. The two variants of the specification that
reject every input or accept every input are refuted by `notAlwaysRejecting`
and `notAlwaysSucceeding`.
-/

@[expose] public section

namespace Krepi.Spec.Fdt.Witnesses

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt Krepi.SpecTests.Fdt

/-- Equality of two `Except` values, decided by their constructors and
payloads; Lean core has no such instance. -/
local instance instDecidableEqExcept {ε α : Type} [DecidableEq ε] [DecidableEq α] :
    DecidableEq (Except ε α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (Except.ok.inj e)
  | .error a, .error b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (Except.error.inj e)
  | .ok _, .error _ => isFalse nofun
  | .error _, .ok _ => isFalse nofun

/-! ## Inputs

The bytes of a device tree for the parse, and trees of records, property
values, maps, boot memory and topologies for the entries that take them. The
entries that take a profile take those of the Pi 5 and of QEMU virt
(`Krepi.SpecTests.Fdt.Boards`). -/

/-- The root alone, 72 bytes. -/
def rootBytes : ByteArray := (Builder.empty.beginNode "" |>.endNode).finish

/-- The root alone after the reservation entries `map`, each an address and a
size. -/
def reservedRoot (map : List (Nat × Nat)) : ByteArray :=
  (map.foldl (fun b e => b.reserve e.1 e.2) Builder.empty |>.beginNode "" |>.endNode).finish

/-- 118 bytes: a reservation entry `[0x1000, 0x3000)`, and the root with the
property `a` of the value `1` and a child `a`. -/
def richBytes : ByteArray :=
  (Builder.empty.reserve 0x1000 0x2000 |>.beginNode "" |>.property "a" [1] |>.beginNode "a"
    |>.endNode |>.endNode).finish

/-- The tree of `richBytes`. -/
def richTree : Fdt :=
  ⟨118, [⟨0x1000, 0x2000⟩], #[⟨"", none, [("a", bytesOf [1])]⟩, ⟨"a", some 0, []⟩]⟩

/-- A property value: a NUL-terminated string. -/
def str (s : String) : ByteArray := bytesOf (stringBytes s)

/-- A property value: the NUL-terminated strings `ss`, in order. -/
def strs (ss : List String) : ByteArray := bytesOf (ss.flatMap stringBytes)

/-- A property value: big-endian cells. -/
def cells (values : List Nat) : ByteArray := bytesOf (cellBytes values)

/-- A node of a tree in preorder: its depth below the root, its name and its
properties. -/
abbrev Line := Nat × String × List (String × ByteArray)

/-- The records of the nodes `lines` after the records `acc`: the parent of a
node is the last node before it one level up, whose index `stack` holds at
that level. -/
def outlineRecords : List Line → List Nat → Array NodeRecord → Array NodeRecord
  | [], _, acc => acc
  | (depth, name, properties) :: rest, stack, acc =>
    outlineRecords rest (stack.take depth ++ [acc.size])
      (acc.push ⟨name, if depth = 0 then none else stack[depth - 1]?, properties⟩)

/-- The tree of the nodes `lines` in preorder, with the reservation entries
`reservations` and the `totalsize` `size`. -/
def outline (lines : List Line) (reservations : List Span := []) (size : UInt64 := 0x1000) :
    Fdt :=
  ⟨size, reservations, outlineRecords lines [] #[]⟩

/-- The result of `f` on the node of the path `path` of `t`; none when the
lookup fails or finds no node. -/
def atPath {β : Type} (t : Fdt) (path : String) (f : Node → β) : Option β :=
  match t.findNode path with
  | .ok (some n) => some (f n)
  | _ => none

/-- The cells of the root of the trees below, 2 address cells and 2 size
cells. -/
def cells22 : List (String × ByteArray) :=
  [("#address-cells", cells [2]), ("#size-cells", cells [2])]

/-- The tree of the node access and the translation: the root with 2 and 2
cells; `bus`, of 1 and 1 cells, with a window of `ranges` from `[0, 0x1000)`
to `0xfd00_0000`, a window of `dma-ranges` to `0x1000_0000`, a `model` and a
`status`, and below it `dev`; `nbus`, without `ranges`, and below it `ndev`;
`abus`, with two windows from `[0, 0x100)`, and below it `adev`; `bad`, with
cell counts of 3 bytes, a `status` without a NUL and a `model` with a byte
after its NUL, and below it `bdev`; `wide`, of 3 address cells, and below it
`wdev`; `ebus` with windows of size 0; `obus` with windows whose child span
leaves 64 bits; `off`, disabled; `nul`, with a `status` with a byte after
its NUL; `big`, whose `reg` leaves 64 bits; and two siblings `twin`. -/
def accessTree : Fdt := outline [
  (0, "", cells22),
  (1, "bus", [("#address-cells", cells [1]), ("#size-cells", cells [1]),
    ("ranges", cells [0, 0, 0xfd00_0000, 0x1000]),
    ("dma-ranges", cells [0, 0, 0x1000_0000, 0x1000]),
    ("model", str "rp1"), ("status", str "okay")]),
  (2, "dev", [("reg", cells [0x10, 0x20])]),
  (1, "nbus", [("#address-cells", cells [1]), ("#size-cells", cells [1])]),
  (2, "ndev", [("reg", cells [0x10, 0x20])]),
  (1, "abus", [("#address-cells", cells [1]), ("#size-cells", cells [1]),
    ("ranges", cells [0, 0, 0x1000, 0x100, 0, 0, 0x2000, 0x100])]),
  (2, "adev", [("reg", cells [0x10, 0x20])]),
  (1, "bad", [("#address-cells", bytesOf [0, 0, 1]), ("#size-cells", bytesOf [0, 0, 1]),
    ("status", bytesOf [0x6f, 0x6b]), ("model", bytesOf [0x61, 0, 0x62])]),
  (2, "bdev", [("reg", cells [0x10, 0x20])]),
  (1, "wide", [("#address-cells", cells [3]), ("#size-cells", cells [1])]),
  (2, "wdev", [("reg", cells [0, 0, 0x10, 0x20])]),
  (1, "ebus", [("#address-cells", cells [1]), ("#size-cells", cells [1]),
    ("ranges", cells [0, 0, 0x1000, 0]), ("dma-ranges", cells [0, 0, 0x1000, 0])]),
  (1, "obus", [("#address-cells", cells [2]), ("#size-cells", cells [1]),
    ("ranges", cells [0xffff_ffff, 0xffff_f000, 0, 0, 0x2000]),
    ("dma-ranges", cells [0xffff_ffff, 0xffff_f000, 0, 0, 0x2000])]),
  (1, "off", [("status", str "disabled")]),
  (1, "nul", [("status", bytesOf (stringBytes "okay" ++ [0x78]))]),
  (1, "big", [("reg", cells [0xffff_ffff, 0xffff_ffff, 0, 2])]),
  (1, "twin", []),
  (1, "twin", [])]

/-- A memory node `memory` with the `device_type` `memory` and the properties
`more`. -/
def memoryLine (more : List (String × ByteArray)) : Line :=
  (1, "memory", ("device_type", str "memory") :: more)

/-- The RAM range `[0, 0x4000_0000)` in 2 and 2 cells. -/
def ramReg : String × ByteArray := ("reg", cells [0, 0, 0, 0x4000_0000])

/-- The tree of the memory discovery: a reservation entry `[0x1000, 0x2000)`,
the root with 2 and 2 cells and the memory node of the RAM range
`[0, 0x4000_0000)`. -/
def memoryTree : Fdt := outline [(0, "", cells22), memoryLine [ramReg]] [⟨0x1000, 0x1000⟩]

/-- The memory map of `memoryTree`. -/
def memoryMap : MemoryMap := ⟨[⟨0, 0x4000_0000⟩], [⟨⟨0x1000, 0x1000⟩, true, false⟩], 0⟩

/-- The root of a tree with 2 and 2 cells and the memory node with the
properties `more` after its `device_type`. -/
def memoryWith (more : List (String × ByteArray)) : Fdt :=
  outline [(0, "", cells22), memoryLine more]

/-- 33 RAM ranges of 4 KiB, 8 KiB apart, in 1 and 1 cells. -/
def ram33Tree : Fdt :=
  outline [(0, "", [("#address-cells", cells [1]), ("#size-cells", cells [1])]),
    memoryLine [("reg", cells ((List.range 33).flatMap fun i => [i * 0x2000, 0x1000]))]]

/-- The root alone, with 2 and 2 cells. -/
def rootTree : Fdt := outline [(0, "", cells22)]

/-- The `compatible` of the root of a Pi 5 hand-over tree:
`raspberrypi,5-model-b`, `brcm,bcm2712`. -/
def pi5Compatible : String × ByteArray :=
  ("compatible", strs ["raspberrypi,5-model-b", "brcm,bcm2712"])

/-- The root of a Pi 5 hand-over tree: 2 and 2 cells and `pi5Compatible`. -/
def pi5Root : List (String × ByteArray) := cells22 ++ [pi5Compatible]

/-- A Pi 5 hand-over tree: the root `root`, the nodes `more`, the reservation
entry `[0x1000, 0x2000)` and the `totalsize` `size`. -/
def pi5Tree (root : List (String × ByteArray) := pi5Root)
    (more : List Line := [memoryLine [ramReg]]) (size : UInt64 := 0x1000) : Fdt :=
  outline ((0, "", root) :: more) [⟨0x1000, 0x1000⟩] size

/-- The span of the image given with the Pi 5 hand-over tree. -/
def image : Span := ⟨0x20_0000, 0x10_0000⟩

/-- The boot memory of `pi5Tree` at `0x10_0000` with `image`, checked with the
hand-over profile of the Pi 5. -/
def pi5Memory : BootMemory := ⟨memoryMap, ⟨0x10_0000, 0x1000⟩, image, 0x4000_0000, 0x2_0000, 3⟩

/-- The tree of the CPU nodes: the root and `/cpus` with the properties
`cpus` and the nodes `more` below the root. -/
def cpusTree (cpus : List (String × ByteArray)) (more : List Line := []) : Fdt :=
  outline ((0, "", cells22) :: (1, "cpus", cpus) :: more)

/-- QEMU virt with two CPUs and PSCI over HVC. -/
def qemuPair : CpuTopology := ⟨qemuHvcCpus, 2⟩

/-- The Pi 5 with four CPUs. -/
def pi5Four : CpuTopology := ⟨pi5Cpus, 4⟩

/-- A map of one window from `[0, 0x1000)` of 1 child address cell to
`0xfd00_0000` of 2 parent address cells, with 1 size cell. -/
def windowMap : AddressMap := ⟨some [⟨⟨0, 0x1000⟩, ⟨0xfd00_0000, 0x1000⟩⟩], 1, 2, 1⟩

/-- A map of two equal windows from `[0, 0x100)` to `[0x1000, 0x1100)`. -/
def twinMap : AddressMap :=
  ⟨some [⟨⟨0, 0x100⟩, ⟨0x1000, 0x100⟩⟩, ⟨⟨0, 0x100⟩, ⟨0x1000, 0x100⟩⟩], 1, 2, 1⟩

/-- Two RAM banks, the second first: `[0x4000_0000, +1 MiB)` and
`[0, 0x10_0800)`, which ends 2 KiB into a page. -/
def banks : List Span := [⟨0x4000_0000, 0x10_0000⟩, ⟨0, 0x10_0800⟩]

/-- One span of boot storage, 16 bytes at `0x1000`. -/
def boot : List Span := [⟨0x1000, 0x10⟩]

/-- One firmware reservation, 16 bytes at `0x8000`, `no-map`. -/
def firmware : List ReservedRegion := [⟨⟨0x8000, 0x10⟩, true, false⟩]

/-- The boot memory map of `all_ram` on `banks`, `boot` and `firmware`. -/
def allRamPlan : MemoryPlan :=
  ⟨[⟨0, 0x10_0800⟩, ⟨0x4000_0000, 0x10_0000⟩], [⟨0, 0x10_0000⟩, ⟨0x4000_0000, 0x10_0000⟩],
    [⟨0x1000, 0x1000⟩], [⟨0x8000, 0x1000⟩]⟩

/-- The boot memory map of `new` that manages `[0, 0x8_0000)` of the same. -/
def newPlan : Except PlanError MemoryPlan := MemoryPlan.new ⟨0, 0x8_0000⟩ banks boot firmware

/-- `/reserved-memory` with 2 and 2 cells and an empty `ranges`. -/
def reservedLine : Line := (1, "reserved-memory", cells22 ++ [("ranges", ByteArray.empty)])

/-- A memory node whose `device_type` `memory` has no NUL. -/
def typeWithoutNulTree : Fdt :=
  outline [(0, "", cells22), (1, "memory", [("device_type", bytesOf "memory".toByteArray.toList)])]

/-- A node named `memory` without a `device_type`. -/
def untypedMemoryTree : Fdt := outline [(0, "", cells22), (1, "memory", [ramReg])]

/-- A memory node without `reg`. -/
def noRegTree : Fdt := memoryWith []

/-- A root of 3 address cells. -/
def threeCellsTree : Fdt :=
  outline [(0, "", [("#address-cells", cells [3]), ("#size-cells", cells [2])]),
    memoryLine [ramReg]]

/-- A RAM range from `2 ^ 64 - 1` of 2 bytes. -/
def wideRamTree : Fdt := memoryWith [("reg", cells [0xffff_ffff, 0xffff_ffff, 0, 2])]

/-- A RAM range of size 0. -/
def emptyRamTree : Fdt := memoryWith [("reg", cells [0, 0, 0, 0])]

/-- Two RAM ranges that share `[0x1000, 0x2000)`. -/
def overlapRamTree : Fdt := memoryWith [("reg", cells [0, 0, 0, 0x2000, 0, 0x1000, 0, 0x2000])]

/-- Two siblings `reserved-memory` after the memory node. -/
def reservedTwinsTree : Fdt :=
  outline [(0, "", cells22), memoryLine [ramReg], reservedLine, reservedLine]

/-- A Pi 5 hand-over tree of 128 KiB and 1 byte. -/
def pi5LargeTree : Fdt := pi5Tree (size := 0x2_0001)

/-- A Pi 5 root whose `#address-cells` has 3 bytes. -/
def pi5ShortCellsTree : Fdt :=
  pi5Tree [("#address-cells", bytesOf [0, 0, 2]), ("#size-cells", cells [2]), pi5Compatible]

/-- A Pi 5 root of 1 address cell. -/
def pi5OneCellTree : Fdt :=
  pi5Tree [("#address-cells", cells [1]), ("#size-cells", cells [2]), pi5Compatible]

/-- A Pi 5 root without `compatible`. -/
def pi5NoCompatibleTree : Fdt := pi5Tree cells22

/-- A Pi 5 root whose `compatible` is the entry `0xff`, not UTF-8. -/
def pi5NotUtf8Tree : Fdt := pi5Tree (cells22 ++ [("compatible", bytesOf [0xff, 0])])

/-- A Pi 5 hand-over tree without a memory node. -/
def pi5NoMemoryTree : Fdt := pi5Tree (more := [])

/-- A Pi 5 hand-over tree with two siblings `reserved-memory`. -/
def pi5ReservedTwinsTree : Fdt :=
  pi5Tree (more := [memoryLine [ramReg], reservedLine, reservedLine])

/-- The cells of `/cpus`, 1 address cell and 0 size cells. -/
def cpusCells : List (String × ByteArray) :=
  [("#address-cells", cells [1]), ("#size-cells", cells [0])]

/-- A CPU node `name` of `/cpus` with the logical ID `id` and the properties
`more`. -/
def cpuLine (name : String) (id : Nat) (more : List (String × ByteArray)) : Line :=
  (2, name, [("device_type", str "cpu"), ("compatible", str "arm,cortex-a76"),
    ("reg", cells [id])] ++ more)

/-- QEMU virt with two CPUs, CPU 0 without an `enable-method`, and `/psci`
over HVC. -/
def qemuPairTree : Fdt :=
  cpusTree cpusCells [cpuLine "cpu@0" 0 [], cpuLine "cpu@1" 1 [("enable-method", str "psci")],
    (1, "psci", [("compatible", strs ["arm,psci-1.0", "arm,psci-0.2", "arm,psci"]),
      ("method", str "hvc")])]

/-- A disabled `/cpus`. -/
def cpusDisabledTree : Fdt := cpusTree [("status", str "disabled")]

/-- A `/cpus` of 3 address cells. -/
def cpusThreeCellsTree : Fdt := cpusTree [("#address-cells", cells [3]), ("#size-cells", cells [0])]

/-- A child of `/cpus` whose `device_type` `cpu` has no NUL. -/
def cpuTypeWithoutNulTree : Fdt :=
  cpusTree cpusCells [(2, "cpu@0", [("device_type", bytesOf "cpu".toByteArray.toList)])]

/-- Two siblings `cpus`. -/
def cpusTwinsTree : Fdt := cpusTree cpusCells [(1, "cpus", cpusCells)]

/-- `memoryTree` with `/reserved-memory` and its children: `linux,cma`, a
dynamic reservation with `reusable` and a `size` of one cell below a
`#size-cells` of 2; `pool`, a dynamic reservation with `no-map` and a `size`
of two cells; `off`, a disabled one; and `atf@0`, a static region with
`no-map`. -/
def dynamicTree : Fdt :=
  outline [(0, "", cells22), memoryLine [ramReg], reservedLine,
    (2, "linux,cma", [("reusable", ByteArray.empty), ("size", cells [0x400_0000])]),
    (2, "pool", [("no-map", ByteArray.empty), ("size", cells [0, 0x10_0000])]),
    (2, "off", [("status", str "disabled"), ("size", cells [0x1000])]),
    (2, "atf@0", [("no-map", ByteArray.empty), ("reg", cells [0, 0, 0, 0x8_0000])])]
  [⟨0x1000, 0x1000⟩]

/-- A Pi 5 hand-over tree with the dynamic reservation `linux,cma` below
`/reserved-memory`. -/
def pi5DynamicTree : Fdt :=
  pi5Tree (more := [memoryLine [ramReg], reservedLine,
    (2, "linux,cma", [("reusable", ByteArray.empty), ("size", cells [0x400_0000])])])

/-- Two memory nodes; the second has a range that shares `[0, 0x1000)` with
the first and then one from `2 ^ 64 - 1`, whose end leaves 64 bits. -/
def priorityMemoryTree : Fdt :=
  outline [(0, "", cells22),
    (1, "memory@0", [("device_type", str "memory"), ("reg", cells [0, 0, 0, 0x1000])]),
    (1, "memory@1", [("device_type", str "memory"),
      ("reg", cells [0, 0, 0, 0x1000, 0xffff_ffff, 0xffff_ffff, 0, 0x10])])]

/-- A `/cpus` of 1 size cell and 3 address cells. -/
def priorityCpusTree : Fdt := cpusTree [("#address-cells", cells [3]), ("#size-cells", cells [1])]

/-- Every tree of records of the witnesses, the planned ones included, passes
the check of the structural invariant of trees. -/
theorem treesWellFormed :
    [accessTree, memoryTree, ram33Tree, rootTree, typeWithoutNulTree, untypedMemoryTree,
      noRegTree, threeCellsTree, wideRamTree, emptyRamTree, overlapRamTree, reservedTwinsTree,
      pi5Tree, pi5LargeTree, pi5ShortCellsTree, pi5OneCellTree, pi5NoCompatibleTree,
      pi5NotUtf8Tree, pi5NoMemoryTree, pi5ReservedTwinsTree, qemuPairTree, cpusDisabledTree,
      cpusThreeCellsTree, cpuTypeWithoutNulTree, cpusTwinsTree, dynamicTree, pi5DynamicTree,
      priorityMemoryTree, priorityCpusTree].all Fdt.checkWellFormed = true := by
  decide +kernel

/-! ## `Fdt::parse` -/

/-- A tree with a reservation entry, a property and a child: the tree of its
entry, its property and its nodes. -/
theorem parseOk : Fdt.parse richBytes = .ok richTree := by decide +kernel

/-- 71 of the 72 bytes of a tree: fewer bytes than `totalsize`. -/
theorem parseTruncated : Fdt.parse (rootBytes.extract 0 71) = .error .truncated := by
  decide +kernel

/-- A magic other than `0xd00d_feed`. -/
theorem parseBadMagic : Fdt.parse (setWord rootBytes 0 0xd00d_feee) = .error .badMagic := by
  decide +kernel

/-- A `totalsize` of 39, below the header. -/
theorem parseBadLayout : Fdt.parse (setWord rootBytes 4 39) = .error .badLayout := by
  decide +kernel

/-- A `totalsize` of 2 MiB and 1 byte, above `MAX_BLOB_SIZE`. -/
theorem parseLimitExceeded : Fdt.parse (setWord rootBytes 4 0x20_0001) = .error .limitExceeded := by
  decide +kernel

/-- A `version` of 16. -/
theorem parseUnsupportedVersion :
    Fdt.parse (setWord rootBytes 20 16) = .error .unsupportedVersion := by
  decide +kernel

/-- A structure block at offset 58, not a multiple of 4. -/
theorem parseBadAlignment : Fdt.parse (setWord rootBytes 8 58) = .error .badAlignment := by
  decide +kernel

/-- A reservation entry from `2 ^ 64 - 1` of 1 byte, whose end leaves 64 bits. -/
theorem parseOverflow :
    Fdt.parse (reservedRoot [(0xffff_ffff_ffff_ffff, 1)]) = .error .overflow := by
  decide +kernel

/-- A reservation entry of size 0 at `0x1000`. -/
theorem parseEmptyRegion :
    Fdt.parse (reservedRoot [(0x1000, 0)]) = .error .emptyRegion := by
  decide +kernel

/-- Two reservation entries that share `[0x1800, 0x2000)`. -/
theorem parseOverlap :
    Fdt.parse (reservedRoot [(0x1000, 0x1000), (0x1800, 0x1000)]) = .error .overlap := by
  decide +kernel

/-- A token 5 in the root. -/
theorem parseBadToken :
    Fdt.parse (Builder.empty.beginNode "" |>.word 5 |>.endNode).finish = .error .badToken := by
  decide +kernel

/-- A root with the name `a`. -/
theorem parseBadTree :
    Fdt.parse (Builder.empty.beginNode "a" |>.endNode).finish = .error .badTree := by
  decide +kernel

/-- A child named `a b`, whose space is no character of a node name. -/
theorem parseBadString :
    Fdt.parse (Builder.empty.beginNode "" |>.beginNode "a b" |>.endNode |>.endNode).finish =
      .error .badString := by
  decide +kernel

/-- A child named `a` with a byte 1 in the padding after its name. -/
theorem parseBadPadding :
    Fdt.parse (Builder.empty.beginNode "" |>.beginNode "a" |>.overwrite [0x61, 0, 1, 0]
      |>.endNode |>.endNode).finish = .error .badPadding := by
  decide +kernel

/-- Two properties `a` in the root. -/
theorem parseDuplicateProperty :
    Fdt.parse (Builder.empty.beginNode "" |>.flag "a" |>.flag "a" |>.endNode).finish =
      .error .duplicateProperty := by
  decide +kernel


/-! ## The node access -/

/-- `Fdt::nodes`: the root and its child `a` of `richBytes`, in the order of
the structure block. -/
theorem nodesOk : (Fdt.parse richBytes).map (·.nodes.map Node.name) = .ok ["", "a"] := by
  decide +kernel

/-- `Fdt::find_node`: `/bus/dev` is the node of index 2. -/
theorem findNodeOk :
    (accessTree.findNode "/bus/dev").map (·.map (·.index.val)) = .ok (some 2) := by
  decide +kernel

/-- `Fdt::find_node`: a path that ends in `/` other than the root. -/
theorem findNodeBadPath :
    (accessTree.findNode "/bus/").map (·.map (·.index.val)) = .error .badPath := by
  decide +kernel

/-- `Fdt::find_node`: a path that matches the two siblings `twin`. -/
theorem findNodeAmbiguousMapping :
    (accessTree.findNode "/twin").map (·.map (·.index.val)) = .error .ambiguousMapping := by
  decide +kernel

/-- `Fdt::reservations`: the entry of the reservation map of `richBytes`. -/
theorem reservationsOk :
    (Fdt.parse richBytes).map Fdt.reservations = .ok [⟨0x1000, 0x2000⟩] := by
  decide +kernel

/-- `Fdt::total_size`: the `totalsize` of `richBytes`. -/
theorem totalSizeOk : (Fdt.parse richBytes).map Fdt.totalSize = .ok 118 := by decide +kernel

/-- `Node::name`. -/
theorem nameOk : atPath accessTree "/bus/dev" Node.name = some "dev" := by decide +kernel

/-- `Node::parent`: `bus` for `/bus/dev`, none for the root. -/
theorem parentOk :
    atPath accessTree "/bus/dev" (·.parent.map Node.name) = some (some "bus") ∧
      atPath accessTree "/" (·.parent.map Node.name) = some none := by
  decide +kernel

/-- `Node::property`: the `reg` of `/bus/dev`; none for its absent `ranges`. -/
theorem propertyOk :
    atPath accessTree "/bus/dev" (·.property "reg") = some (some (cells [0x10, 0x20])) ∧
      atPath accessTree "/bus/dev" (·.property "ranges") = some none := by
  decide +kernel

/-- `Node::string_property`: the `model` `rp1` of `/bus`. -/
theorem stringPropertyOk :
    atPath accessTree "/bus" (·.stringProperty "model") = some (.ok (some "rp1")) := by
  decide +kernel

/-- `Node::string_property`: a value without a NUL. -/
theorem stringPropertyBadString :
    atPath accessTree "/bad" (·.stringProperty "status") = some (.error .badString) := by
  decide +kernel

/-- `Node::string_property`: a byte after the NUL. -/
theorem stringPropertyBadProperty :
    atPath accessTree "/bad" (·.stringProperty "model") = some (.error .badProperty) := by
  decide +kernel

/-- `Node::enabled`: true for `okay` and for an absent `status`, false for
`disabled`. -/
theorem enabledOk :
    atPath accessTree "/bus" Node.enabled = some (.ok true) ∧
      atPath accessTree "/bus/dev" Node.enabled = some (.ok true) ∧
      atPath accessTree "/off" Node.enabled = some (.ok false) := by
  decide +kernel

/-- `Node::enabled`: a `status` without a NUL. -/
theorem enabledBadString : atPath accessTree "/bad" Node.enabled = some (.error .badString) := by
  decide +kernel

/-- `Node::enabled`: a `status` with a byte after its NUL. -/
theorem enabledBadProperty :
    atPath accessTree "/nul" Node.enabled = some (.error .badProperty) := by
  decide +kernel

/-- `Node::address_cells`: 1 for `/bus`, and 2 for `/bus/dev`, which has
none. -/
theorem addressCellsOk :
    atPath accessTree "/bus" Node.addressCells = some (.ok 1) ∧
      atPath accessTree "/bus/dev" Node.addressCells = some (.ok 2) := by
  decide +kernel

/-- `Node::address_cells`: a value of 3 bytes. -/
theorem addressCellsBadProperty :
    atPath accessTree "/bad" Node.addressCells = some (.error .badProperty) := by
  decide +kernel

/-- `Node::size_cells`: 2 for the root, and 1 for `/bus/dev`, which has none.
-/
theorem sizeCellsOk :
    atPath accessTree "/" Node.sizeCells = some (.ok 2) ∧
      atPath accessTree "/bus/dev" Node.sizeCells = some (.ok 1) := by
  decide +kernel

/-- `Node::size_cells`: a value of 3 bytes. -/
theorem sizeCellsBadProperty :
    atPath accessTree "/bad" Node.sizeCells = some (.error .badProperty) := by
  decide +kernel

/-- `Node::reg`: the `reg` of `/bus/dev` in the 1 and 1 cells of `bus`. -/
theorem regOk : atPath accessTree "/bus/dev" Node.reg = some (.ok ⟨[⟨0x10, 0x20⟩]⟩) := by
  decide +kernel

/-- `Node::reg`: the root, which has no parent. -/
theorem regBadTree : atPath accessTree "/" Node.reg = some (.error .badTree) := by
  decide +kernel

/-- `Node::reg`: a node without `reg`. -/
theorem regMissingProperty :
    atPath accessTree "/bus" Node.reg = some (.error .missingProperty) := by
  decide +kernel

/-- `Node::reg`: a parent whose `#address-cells` has 3 bytes. -/
theorem regBadProperty :
    atPath accessTree "/bad/bdev" Node.reg = some (.error .badProperty) := by
  decide +kernel

/-- `Node::reg`: a parent of 3 address cells. -/
theorem regUnsupportedCells :
    atPath accessTree "/wide/wdev" Node.reg = some (.error .unsupportedCells) := by
  decide +kernel

/-- `Node::reg`: a span from `2 ^ 64 - 1` of 2 bytes. -/
theorem regOverflow : atPath accessTree "/big" Node.reg = some (.error .overflow) := by
  decide +kernel

/-- `Node::ranges`: the map of `bus`. -/
theorem rangesOk : atPath accessTree "/bus" Node.ranges = some (.ok windowMap) := by
  decide +kernel

/-- `Node::ranges`: the root, which has no parent. -/
theorem rangesBadTree : atPath accessTree "/" Node.ranges = some (.error .badTree) := by
  decide +kernel

/-- `Node::ranges`: a node whose `#address-cells` has 3 bytes. -/
theorem rangesBadProperty : atPath accessTree "/bad" Node.ranges = some (.error .badProperty) := by
  decide +kernel

/-- `Node::ranges`: a node of 3 address cells. -/
theorem rangesUnsupportedCells :
    atPath accessTree "/wide" Node.ranges = some (.error .unsupportedCells) := by
  decide +kernel

/-- `Node::ranges`: a window of size 0. -/
theorem rangesEmptyRegion : atPath accessTree "/ebus" Node.ranges = some (.error .emptyRegion) := by
  decide +kernel

/-- `Node::ranges`: a window whose child span leaves 64 bits. -/
theorem rangesOverflow : atPath accessTree "/obus" Node.ranges = some (.error .overflow) := by
  decide +kernel

/-- `Node::dma_ranges`: the map of `bus`, to `0x1000_0000`. -/
theorem dmaRangesOk :
    atPath accessTree "/bus" Node.dmaRanges =
      some (.ok ⟨some [⟨⟨0, 0x1000⟩, ⟨0x1000_0000, 0x1000⟩⟩], 1, 2, 1⟩) := by
  decide +kernel

/-- `Node::dma_ranges`: the root, which has no parent. -/
theorem dmaRangesBadTree : atPath accessTree "/" Node.dmaRanges = some (.error .badTree) := by
  decide +kernel

/-- `Node::dma_ranges`: a node whose `#address-cells` has 3 bytes. -/
theorem dmaRangesBadProperty :
    atPath accessTree "/bad" Node.dmaRanges = some (.error .badProperty) := by
  decide +kernel

/-- `Node::dma_ranges`: a node of 3 address cells. -/
theorem dmaRangesUnsupportedCells :
    atPath accessTree "/wide" Node.dmaRanges = some (.error .unsupportedCells) := by
  decide +kernel

/-- `Node::dma_ranges`: a window of size 0. -/
theorem dmaRangesEmptyRegion :
    atPath accessTree "/ebus" Node.dmaRanges = some (.error .emptyRegion) := by
  decide +kernel

/-- `Node::dma_ranges`: a window whose child span leaves 64 bits. -/
theorem dmaRangesOverflow : atPath accessTree "/obus" Node.dmaRanges = some (.error .overflow) := by
  decide +kernel

/-- `Node::translate_reg`: `[0x10, 0x30)` of `bus` is `[0xfd00_0010, 0xfd00_0030)`. -/
theorem translateRegOk :
    atPath accessTree "/bus/dev" (·.translateReg ⟨0x10, 0x20⟩) =
      some (.ok ⟨0xfd00_0010, 0x20⟩) := by
  decide +kernel

/-- `Node::translate_reg`: the root, which has no parent bus. -/
theorem translateRegBadTree :
    atPath accessTree "/" (·.translateReg ⟨0x10, 0x20⟩) = some (.error .badTree) := by
  decide +kernel

/-- `Node::translate_reg`: a bus whose `#address-cells` has 3 bytes. -/
theorem translateRegBadProperty :
    atPath accessTree "/bad/bdev" (·.translateReg ⟨0x10, 0x20⟩) = some (.error .badProperty) := by
  decide +kernel

/-- `Node::translate_reg`: a bus of 3 address cells. -/
theorem translateRegUnsupportedCells :
    atPath accessTree "/wide/wdev" (·.translateReg ⟨0x10, 0x20⟩) =
      some (.error .unsupportedCells) := by
  decide +kernel

/-- `Node::translate_reg`: a request of size 0. -/
theorem translateRegEmptyRegion :
    atPath accessTree "/bus/dev" (·.translateReg ⟨0x10, 0⟩) = some (.error .emptyRegion) := by
  decide +kernel

/-- `Node::translate_reg`: below the root, a span from `2 ^ 64 - 1` of 2
bytes, whose end leaves 64 bits. -/
theorem translateRegOverflow :
    atPath accessTree "/big" (·.translateReg ⟨0xffff_ffff_ffff_ffff, 2⟩) =
      some (.error .overflow) := by
  decide +kernel

/-- `Node::translate_reg`: a bus without `ranges`. -/
theorem translateRegUnmapped :
    atPath accessTree "/nbus/ndev" (·.translateReg ⟨0x10, 0x20⟩) = some (.error .unmapped) := by
  decide +kernel

/-- `Node::translate_reg`: a bus with two windows that hold the request. -/
theorem translateRegAmbiguousMapping :
    atPath accessTree "/abus/adev" (·.translateReg ⟨0x10, 0x20⟩) =
      some (.error .ambiguousMapping) := by
  decide +kernel


/-! ## `Fdt::discover_memory` and the `MemoryMap` readers -/

/-- The RAM range of the memory node and the reservation entry, a reserved
region with `no-map`. -/
theorem discoverMemoryOk : memoryTree.discoverMemory = .ok memoryMap := by decide +kernel

/-- `MemoryMap::ram`. -/
theorem memoryMapRamOk : memoryTree.discoverMemory.map MemoryMap.ram = .ok [⟨0, 0x4000_0000⟩] := by
  decide +kernel

/-- `MemoryMap::reserved`. -/
theorem memoryMapReservedOk :
    memoryTree.discoverMemory.map MemoryMap.reserved = .ok [⟨⟨0x1000, 0x1000⟩, true, false⟩] := by
  decide +kernel

/-- `MemoryMap::dynamic`: no dynamic reservation. -/
theorem memoryMapDynamicOk : memoryTree.discoverMemory.map MemoryMap.dynamic = .ok 0 := by
  decide +kernel

/-- `MemoryMap::dynamic`: the two enabled dynamic reservations of
`dynamicTree`, whatever the cells of their `size`; the disabled one and the
static `atf@0` are not counted. -/
theorem memoryMapDynamicTwo : dynamicTree.discoverMemory.map MemoryMap.dynamic = .ok 2 := by
  decide +kernel

/-- 33 RAM ranges, above `MAX_MEMORY_REGIONS`. -/
theorem discoverMemoryLimitExceeded : ram33Tree.discoverMemory = .error .limitExceeded := by
  decide +kernel

/-- A `device_type` without a NUL. -/
theorem discoverMemoryBadString :
    typeWithoutNulTree.discoverMemory = .error .badString := by
  decide +kernel

/-- An enabled node named `memory` without the `device_type` `memory`. -/
theorem discoverMemoryBadProperty :
    untypedMemoryTree.discoverMemory = .error .badProperty := by
  decide +kernel

/-- A memory node without `reg`. -/
theorem discoverMemoryMissingProperty :
    noRegTree.discoverMemory = .error .missingProperty := by
  decide +kernel

/-- A root of 3 address cells. -/
theorem discoverMemoryUnsupportedCells :
    threeCellsTree.discoverMemory = .error .unsupportedCells := by
  decide +kernel

/-- A RAM range from `2 ^ 64 - 1` of 2 bytes. -/
theorem discoverMemoryOverflow :
    wideRamTree.discoverMemory = .error .overflow := by
  decide +kernel

/-- A RAM range of size 0. -/
theorem discoverMemoryEmptyRegion :
    emptyRamTree.discoverMemory = .error .emptyRegion := by
  decide +kernel

/-- Two RAM ranges that share `[0x1000, 0x2000)`. -/
theorem discoverMemoryOverlap :
    overlapRamTree.discoverMemory = .error .overlap := by
  decide +kernel

/-- The root alone: no RAM range. -/
theorem discoverMemoryNoMemory : rootTree.discoverMemory = .error .noMemory := by decide +kernel

/-- Two siblings `reserved-memory`: the lookup of `/reserved-memory` meets
both. -/
theorem discoverMemoryAmbiguousMapping :
    reservedTwinsTree.discoverMemory = .error .ambiguousMapping := by
  decide +kernel

/-! ## `Fdt::discover_boot_memory`, its readers and `is_available` -/

/-- The result of the discovery with the profile of the Pi 5 on `pi5Tree` at
`0x10_0000` with `image`. -/
def pi5Result : Except Error BootMemory := pi5Tree.discoverBootMemory pi5HandOver 0x10_0000 image

/-- The memory map, the span of the tree of `0x1000` bytes, the image and
the 1 GiB of the RAM range, with the limit and the alignment of the profile. -/
theorem discoverBootMemoryOk : pi5Result = .ok pi5Memory := by decide +kernel

/-- `BootMemory::ram`. -/
theorem bootMemoryRamOk : pi5Result.map BootMemory.ram = .ok [⟨0, 0x4000_0000⟩] := by decide +kernel

/-- `BootMemory::reserved`. -/
theorem bootMemoryReservedOk :
    pi5Result.map BootMemory.reserved = .ok [⟨⟨0x1000, 0x1000⟩, true, false⟩] := by
  decide +kernel

/-- `BootMemory::dynamic`. -/
theorem bootMemoryDynamicOk : pi5Result.map BootMemory.dynamic = .ok 0 := by decide +kernel

/-- `BootMemory::dynamic`: the dynamic reservation `linux,cma` of
`pi5DynamicTree`. -/
theorem bootMemoryDynamicOne :
    (pi5DynamicTree.discoverBootMemory pi5HandOver 0x10_0000 image).map BootMemory.dynamic = .ok 1 := by
  decide +kernel

/-- `BootMemory::dtb`: `totalsize` bytes from the address of the tree. -/
theorem bootMemoryDtbOk : pi5Result.map BootMemory.dtb = .ok ⟨0x10_0000, 0x1000⟩ := by decide +kernel

/-- `BootMemory::image`. -/
theorem bootMemoryImageOk : pi5Result.map BootMemory.image = .ok image := by decide +kernel

/-- `BootMemory::ram_bytes`. -/
theorem bootMemoryRamBytesOk : pi5Result.map BootMemory.ramBytes = .ok 0x4000_0000 := by
  decide +kernel

/-- A `totalsize` of 128 KiB and 1 byte, above the limit of the profile. -/
theorem discoverBootMemoryLimitExceeded :
    pi5LargeTree.discoverBootMemory pi5HandOver 0x10_0000 image = .error .limitExceeded := by
  decide +kernel

/-- A tree at `0x10_0004`, not a multiple of the alignment of the profile, 8. -/
theorem discoverBootMemoryBadAlignment :
    pi5Tree.discoverBootMemory pi5HandOver 0x10_0004 image = .error .badAlignment := by
  decide +kernel

/-- A root `#address-cells` of 3 bytes. -/
theorem discoverBootMemoryBadProperty :
    pi5ShortCellsTree.discoverBootMemory pi5HandOver 0x10_0000 image = .error .badProperty := by
  decide +kernel

/-- A root of 1 address cell. -/
theorem discoverBootMemoryUnsupportedCells :
    pi5OneCellTree.discoverBootMemory pi5HandOver 0x10_0000 image = .error .unsupportedCells := by
  decide +kernel

/-- A root without `compatible`. -/
theorem discoverBootMemoryMissingProperty :
    pi5NoCompatibleTree.discoverBootMemory pi5HandOver 0x10_0000 image = .error .missingProperty := by
  decide +kernel

/-- A `compatible` entry `0xff`, not UTF-8. -/
theorem discoverBootMemoryBadString :
    pi5NotUtf8Tree.discoverBootMemory pi5HandOver 0x10_0000 image = .error .badString := by
  decide +kernel

/-- A tree at `2 ^ 64 - 0x1000`, whose span leaves 64 bits. -/
theorem discoverBootMemoryOverflow :
    pi5Tree.discoverBootMemory pi5HandOver 0xffff_ffff_ffff_f000 image = .error .overflow := by
  decide +kernel

/-- An image of size 0. -/
theorem discoverBootMemoryEmptyRegion :
    pi5Tree.discoverBootMemory pi5HandOver 0x10_0000 ⟨0x20_0000, 0⟩ = .error .emptyRegion := by
  decide +kernel

/-- An image that shares `[0x10_0800, 0x10_1000)` with the tree. -/
theorem discoverBootMemoryOverlap :
    pi5Tree.discoverBootMemory pi5HandOver 0x10_0000 ⟨0x10_0800, 0x1000⟩ = .error .overlap := by
  decide +kernel

/-- A tree at `0x4000_0000`, past the RAM range. -/
theorem discoverBootMemoryUnmapped :
    pi5Tree.discoverBootMemory pi5HandOver 0x4000_0000 image = .error .unmapped := by
  decide +kernel

/-- A hand-over tree without a memory node. -/
theorem discoverBootMemoryNoMemory :
    pi5NoMemoryTree.discoverBootMemory pi5HandOver 0x10_0000 image = .error .noMemory := by
  decide +kernel

/-- Two siblings `reserved-memory`, as in `discoverMemoryAmbiguousMapping`. -/
theorem discoverBootMemoryAmbiguousMapping :
    pi5ReservedTwinsTree.discoverBootMemory pi5HandOver 0x10_0000 image = .error .ambiguousMapping := by
  decide +kernel

/-- `BootMemory::is_available`: true for a span of the RAM range that
touches nothing, false for one on the image. -/
theorem bootMemoryIsAvailableOk :
    pi5Memory.isAvailable ⟨0x40_0000, 0x1000⟩ = .ok true ∧
      pi5Memory.isAvailable ⟨0x20_0000, 0x1000⟩ = .ok false := by
  decide +kernel

/-- `BootMemory::is_available`: an empty span. -/
theorem bootMemoryIsAvailableEmptyRegion :
    pi5Memory.isAvailable ⟨0x40_0000, 0⟩ = .error .emptyRegion := by
  decide +kernel

/-- `BootMemory::is_available`: a span from `2 ^ 64 - 1` of 2 bytes. -/
theorem bootMemoryIsAvailableOverflow :
    pi5Memory.isAvailable ⟨0xffff_ffff_ffff_ffff, 2⟩ = .error .overflow := by
  decide +kernel

/-! ## `BootMemory::find_available` -/

/-- From `0x10_0000`, the first page past the tree; none for 1 GiB, which the
exclusions leave no room for. -/
theorem findAvailableOk :
    pi5Memory.findAvailable 0x1000 0x1000 0x10_0000 0x4000_0000 = .ok (some ⟨0x10_1000, 0x1000⟩) ∧
      pi5Memory.findAvailable 0x4000_0000 0x1000 0 0x4000_0000 = .ok none := by
  decide +kernel

/-- A size of 0. -/
theorem findAvailableEmptyRegion :
    pi5Memory.findAvailable 0 0x1000 0 0x4000_0000 = .error .emptyRegion := by
  decide +kernel

/-- An alignment of `0x1800`, not a power of two. -/
theorem findAvailableBadAlignment :
    pi5Memory.findAvailable 0x1000 0x1800 0 0x4000_0000 = .error .badAlignment := by
  decide +kernel

/-- From `2 ^ 63 + 1` at an alignment of `2 ^ 63`: the aligned start leaves 64
bits. -/
theorem findAvailableOverflow :
    pi5Memory.findAvailable 0x1000 0x8000_0000_0000_0000 0x8000_0000_0000_0001
      0xffff_ffff_ffff_ffff = .error .overflow := by
  decide +kernel

/-! ## `Fdt::discover_cpus` and the topology -/

/-- QEMU virt with two CPUs, CPU 0 without an `enable-method`, and `/psci`
over HVC: the topology `qemuPair`. -/
theorem discoverCpusOk : qemuPairTree.discoverCpus qemuHvcCpus = .ok qemuPair := by
  decide +kernel

/-- No `/cpus`. -/
theorem discoverCpusMissingProperty : rootTree.discoverCpus qemuHvcCpus = .error .missingProperty := by
  decide +kernel

/-- A disabled `/cpus`. -/
theorem discoverCpusBadProperty :
    cpusDisabledTree.discoverCpus qemuHvcCpus = .error .badProperty := by
  decide +kernel

/-- A `/cpus` of 3 address cells. -/
theorem discoverCpusUnsupportedCells :
    cpusThreeCellsTree.discoverCpus qemuHvcCpus = .error .unsupportedCells := by
  decide +kernel

/-- A child of `/cpus` whose `device_type` has no NUL. -/
theorem discoverCpusBadString :
    cpuTypeWithoutNulTree.discoverCpus qemuHvcCpus = .error .badString := by
  decide +kernel

/-- Two siblings `cpus`. -/
theorem discoverCpusAmbiguousMapping :
    cpusTwinsTree.discoverCpus qemuHvcCpus = .error .ambiguousMapping := by
  decide +kernel

/-- `CpuTopology::count`. -/
theorem countOk : qemuPair.count = 2 ∧ pi5Four.count = 4 := by decide +kernel

/-- `CpuTopology::profile`. -/
theorem profileOk : qemuPair.profile = qemuHvcCpus ∧ pi5Four.profile = pi5Cpus := by decide +kernel

/-- `CpuTopology::affinity`: `3 << 8` for CPU 3 of the Pi 5, none for 4. -/
theorem affinityOk : pi5Four.affinity 3 = some 0x300 ∧ pi5Four.affinity 4 = none := by
  decide +kernel

/-- `CpuTopology::validate_timers`: the four records of two CPUs. -/
theorem validateTimersOk :
    qemuPair.validateTimers (cells [1, 13, 0x304, 1, 14, 0x304, 1, 11, 0x304, 1, 10, 0x304]) =
      .ok () := by
  decide +kernel

/-- `CpuTopology::validate_timers`: the flags of four CPUs for two. -/
theorem validateTimersBadProperty :
    qemuPair.validateTimers (cells [1, 13, 0xf04, 1, 14, 0xf04, 1, 11, 0xf04, 1, 10, 0xf04]) =
      .error .badProperty := by
  decide +kernel

/-- `CpuProfile::logical_id`: 3 for the affinity `3 << 8` of the Pi 5 with the
flag bits `0x8100_0000`; none for `4 << 8`. -/
theorem logicalIdOk : pi5Cpus.logicalId 0x8100_0300 = some 3 ∧
    pi5Cpus.logicalId 0x400 = none := by
  decide +kernel

/-- `CpuProfile::affinity_shift`: 8 on the Pi 5, 0 on QEMU virt. -/
theorem affinityShiftOk :
    pi5Cpus.affinityShift = 8 ∧ qemuSmcCpus.affinityShift = 0 := by
  decide +kernel

/-- `CpuProfile::conduit`: HVC for QEMU virt without EL2, SMC with it. -/
theorem conduitOk : qemuHvcCpus.conduit = .hvc ∧ qemuSmcCpus.conduit = .smc := by
  decide +kernel


/-! ## Cells, regions and address maps -/

/-- `cells_u64`: two cells, the high one first. -/
theorem cellsU64Ok : cellsU64 (cells [1, 2]) 2 = .ok 0x1_0000_0002 := by decide +kernel

/-- `cells_u64`: 3 cells. -/
theorem cellsU64UnsupportedCells : cellsU64 (cells [0, 0, 1]) 3 = .error .unsupportedCells := by
  decide +kernel

/-- `cells_u64`: 4 bytes for 2 cells. -/
theorem cellsU64BadProperty : cellsU64 (cells [1]) 2 = .error .badProperty := by decide +kernel

/-- `Reg::new`: two entries of 1 and 1 cells. -/
theorem regNewOk :
    Reg.new (cells [0x10, 0x20, 0x100, 0x10]) 1 1 = .ok ⟨[⟨0x10, 0x20⟩, ⟨0x100, 0x10⟩]⟩ := by
  decide +kernel

/-- `Reg::new`: 3 address cells. -/
theorem regNewUnsupportedCells :
    Reg.new (cells [0, 0, 0x10, 0x20]) 3 1 = .error .unsupportedCells := by
  decide +kernel

/-- `Reg::new`: an empty value. -/
theorem regNewBadProperty : Reg.new ByteArray.empty 1 1 = .error .badProperty := by decide +kernel

/-- `Reg::new`: one address cell, `0xffff_ffff` of 2 bytes, past the first
4 GiB. -/
theorem regNewOverflow : Reg.new (cells [0xffff_ffff, 2]) 1 1 = .error .overflow := by
  decide +kernel

/-- `AddressMap::new`: the window of `windowMap`. -/
theorem addressMapNewOk :
    AddressMap.new (some (cells [0, 0, 0xfd00_0000, 0x1000])) 1 2 1 = .ok windowMap := by
  decide +kernel

/-- `AddressMap::new`: 3 child address cells. -/
theorem addressMapNewUnsupportedCells : AddressMap.new none 3 2 1 = .error .unsupportedCells := by
  decide +kernel

/-- `AddressMap::new`: a nonempty value without size cells. -/
theorem addressMapNewBadProperty :
    AddressMap.new (some (cells [0, 0, 0xfd00_0000])) 1 2 0 = .error .badProperty := by
  decide +kernel

/-- `AddressMap::new`: a window of size 0. -/
theorem addressMapNewEmptyRegion :
    AddressMap.new (some (cells [0, 0, 0xfd00_0000, 0])) 1 2 1 = .error .emptyRegion := by
  decide +kernel

/-- `AddressMap::new`: a child span of one cell, `[0xffff_f000, 0x1_0000_1000)`,
past the first 4 GiB. -/
theorem addressMapNewOverflow :
    AddressMap.new (some (cells [0xffff_f000, 0, 0x1000_0000, 0x2000])) 1 2 1 =
      .error .overflow := by
  decide +kernel

/-- `AddressMap::kind`: absent, identity and windows. -/
theorem kindOk :
    (AddressMap.new none 1 2 1).map AddressMap.kind = .ok .absent ∧
      (AddressMap.new (some ByteArray.empty) 1 2 1).map AddressMap.kind = .ok .identity ∧
      windowMap.kind = .windows := by
  decide +kernel

/-- The maps of the translations are well-formed. -/
theorem mapsWellFormed : windowMap.checkWellFormed = true ∧ twinMap.checkWellFormed = true := by
  decide +kernel

/-- `AddressMap::to_parent`: `[0x10, 0x30)` through the window. -/
theorem toParentOk : windowMap.toParent ⟨0x10, 0x20⟩ = .ok ⟨0xfd00_0010, 0x20⟩ := by
  decide +kernel

/-- `AddressMap::to_parent`: a request of size 0. -/
theorem toParentEmptyRegion : windowMap.toParent ⟨0x10, 0⟩ = .error .emptyRegion := by
  decide +kernel

/-- `AddressMap::to_parent`: a request past the first 4 GiB on a side of one
cell. -/
theorem toParentOverflow : windowMap.toParent ⟨0x1_0000_0000, 0x10⟩ = .error .overflow := by
  decide +kernel

/-- `AddressMap::to_parent`: a request of which the window holds a part. -/
theorem toParentUnmapped : windowMap.toParent ⟨0xff0, 0x20⟩ = .error .unmapped := by
  decide +kernel

/-- `AddressMap::to_parent`: two windows that hold the request. -/
theorem toParentAmbiguousMapping : twinMap.toParent ⟨0x10, 0x20⟩ = .error .ambiguousMapping := by
  decide +kernel

/-- `AddressMap::to_child`: `[0xfd00_0010, 0xfd00_0030)` back to `[0x10, 0x30)`. -/
theorem toChildOk : windowMap.toChild ⟨0xfd00_0010, 0x20⟩ = .ok ⟨0x10, 0x20⟩ := by
  decide +kernel

/-- `AddressMap::to_child`: a request of size 0. -/
theorem toChildEmptyRegion : windowMap.toChild ⟨0xfd00_0010, 0⟩ = .error .emptyRegion := by
  decide +kernel

/-- `AddressMap::to_child`: a request from `2 ^ 64 - 1` of 2 bytes. -/
theorem toChildOverflow : windowMap.toChild ⟨0xffff_ffff_ffff_ffff, 2⟩ = .error .overflow := by
  decide +kernel

/-- `AddressMap::to_child`: a request outside the window. -/
theorem toChildUnmapped : windowMap.toChild ⟨0x10, 0x20⟩ = .error .unmapped := by
  decide +kernel

/-- `AddressMap::to_child`: two windows that hold the request. -/
theorem toChildAmbiguousMapping : twinMap.toChild ⟨0x1010, 0x20⟩ = .error .ambiguousMapping := by
  decide +kernel

/-! ## `MemoryPlan::all_ram`, `new` and `from_boot_memory` -/

/-- The banks sorted, the complete pages of each, and the boot storage and the
firmware reservation rounded outward to pages. -/
theorem allRamOk : MemoryPlan.allRam banks boot firmware = .ok allRamPlan := by decide +kernel

/-- No boot storage. -/
theorem allRamCapacity : MemoryPlan.allRam banks [] firmware = .error .capacity := by
  decide +kernel

/-- A bank of size 0. -/
theorem allRamInvalidRange : MemoryPlan.allRam [⟨0, 0⟩] boot firmware = .error .invalidRange := by
  decide +kernel

/-- A bank from `2 ^ 64 - 1` of 2 bytes. -/
theorem allRamOverflow :
    MemoryPlan.allRam [⟨0xffff_ffff_ffff_ffff, 2⟩] boot firmware = .error .overflow := by
  decide +kernel

/-- Two banks that share `[0x1000, 0x2000)`. -/
theorem allRamOverlap :
    MemoryPlan.allRam [⟨0, 0x2000⟩, ⟨0x1000, 0x2000⟩] boot firmware = .error .overlap := by
  decide +kernel

/-- A bank of 16 GiB and 4 KiB. -/
theorem allRamArenaTooLarge :
    MemoryPlan.allRam [⟨0, 0x4_0000_1000⟩] boot firmware = .error .arenaTooLarge := by
  decide +kernel

/-- A bank of 256 bytes, without a complete page. -/
theorem allRamAlignment : MemoryPlan.allRam [⟨0x10, 0x100⟩] boot firmware = .error .alignment := by
  decide +kernel

/-- Boot storage outside both banks. -/
theorem allRamOutsideRam :
    MemoryPlan.allRam banks [⟨0x20_0000, 0x10⟩] firmware = .error .outsideRam := by
  decide +kernel

/-- `MemoryPlan::new`: the map of `all_ram` that manages `[0, 0x8_0000)`. -/
theorem newOk :
    newPlan = .ok ⟨allRamPlan.ram, [⟨0, 0x8_0000⟩], allRamPlan.boot, allRamPlan.firmware⟩ := by
  decide +kernel

/-- `MemoryPlan::new`: a window of size 0. -/
theorem newInvalidRange : MemoryPlan.new ⟨0, 0⟩ banks boot firmware = .error .invalidRange := by
  decide +kernel

/-- `MemoryPlan::new`: a window whose end leaves 64 bits. -/
theorem newOverflow :
    MemoryPlan.new ⟨0xffff_ffff_ffff_f000, 0x2000⟩ banks boot firmware = .error .overflow := by
  decide +kernel

/-- `MemoryPlan::new`: a window off its page. -/
theorem newAlignment : MemoryPlan.new ⟨0x10, 0x1000⟩ banks boot firmware = .error .alignment := by
  decide +kernel

/-- `MemoryPlan::new`: a window of 128 MiB and 4 KiB. -/
theorem newArenaTooLarge :
    MemoryPlan.new ⟨0, 0x800_1000⟩ banks boot firmware = .error .arenaTooLarge := by
  decide +kernel

/-- `MemoryPlan::new`: no boot storage. -/
theorem newCapacity : MemoryPlan.new ⟨0, 0x8_0000⟩ banks [] firmware = .error .capacity := by
  decide +kernel

/-- `MemoryPlan::new`: a firmware reservation on the page of the boot storage.
-/
theorem newOverlap :
    MemoryPlan.new ⟨0, 0x8_0000⟩ banks boot [⟨⟨0x1800, 0x10⟩, true, false⟩] = .error .overlap := by
  decide +kernel

/-- `MemoryPlan::new`: a window outside both banks. -/
theorem newOutsideRam :
    MemoryPlan.new ⟨0x20_0000, 0x1000⟩ banks boot firmware = .error .outsideRam := by
  decide +kernel

/-- `MemoryPlan::from_boot_memory`: the RAM range, the window, the image and
the tree as boot storage, and the reserved region as a firmware reservation.
-/
theorem fromBootMemoryOk :
    MemoryPlan.fromBootMemory pi5Memory ⟨0x40_0000, 0x10_0000⟩ [] =
      .ok ⟨[⟨0, 0x4000_0000⟩], [⟨0x40_0000, 0x10_0000⟩], [image, ⟨0x10_0000, 0x1000⟩],
        [⟨0x1000, 0x1000⟩]⟩ := by
  decide +kernel

/-- `MemoryPlan::from_boot_memory`: a window of size 0. -/
theorem fromBootMemoryInvalidRange :
    MemoryPlan.fromBootMemory pi5Memory ⟨0x40_0000, 0⟩ [] = .error .invalidRange := by
  decide +kernel

/-- `MemoryPlan::from_boot_memory`: a window whose end leaves 64 bits. -/
theorem fromBootMemoryOverflow :
    MemoryPlan.fromBootMemory pi5Memory ⟨0xffff_ffff_ffff_f000, 0x2000⟩ [] = .error .overflow := by
  decide +kernel

/-- `MemoryPlan::from_boot_memory`: a window off its page. -/
theorem fromBootMemoryAlignment :
    MemoryPlan.fromBootMemory pi5Memory ⟨0x40_0010, 0x1000⟩ [] = .error .alignment := by
  decide +kernel

/-- `MemoryPlan::from_boot_memory`: a window of 128 MiB and 4 KiB. -/
theorem fromBootMemoryArenaTooLarge :
    MemoryPlan.fromBootMemory pi5Memory ⟨0, 0x800_1000⟩ [] = .error .arenaTooLarge := by
  decide +kernel

/-- `MemoryPlan::from_boot_memory`: three further spans, 5 spans of boot storage. -/
theorem fromBootMemoryCapacity :
    MemoryPlan.fromBootMemory pi5Memory ⟨0x40_0000, 0x10_0000⟩
      [⟨0x50_0000, 0x1000⟩, ⟨0x60_0000, 0x1000⟩, ⟨0x70_0000, 0x1000⟩] = .error .capacity := by
  decide +kernel

/-- `MemoryPlan::from_boot_memory`: a further span on a page of the image. -/
theorem fromBootMemoryOverlap :
    MemoryPlan.fromBootMemory pi5Memory ⟨0x40_0000, 0x10_0000⟩ [⟨0x20_0800, 0x10⟩] = .error .overlap := by
  decide +kernel

/-- `MemoryPlan::from_boot_memory`: a window past the RAM range. -/
theorem fromBootMemoryOutsideRam :
    MemoryPlan.fromBootMemory pi5Memory ⟨0x4000_0000, 0x1000⟩ [] = .error .outsideRam := by
  decide +kernel

/-! ## The queries of the boot memory map -/

/-- `MemoryPlan::managed_banks`: the window. -/
theorem managedBanksOk : newPlan.map MemoryPlan.managedBanks = .ok [⟨0, 0x8_0000⟩] := by
  decide +kernel

/-- `MemoryPlan::ram`: the banks sorted by their start. -/
theorem planRamOk :
    newPlan.map MemoryPlan.ram = .ok [⟨0, 0x10_0800⟩, ⟨0x4000_0000, 0x10_0000⟩] := by
  decide +kernel

/-- `MemoryPlan::reservations`: the boot storage, then the firmware
reservation. -/
theorem reservationsOfPlanOk :
    newPlan.map MemoryPlan.reservations = .ok [⟨0x1000, 0x1000⟩, ⟨0x8000, 0x1000⟩] := by
  decide +kernel

/-- `MemoryPlan::boot_ranges`. -/
theorem bootRangesOk : newPlan.map MemoryPlan.bootRanges = .ok [⟨0x1000, 0x1000⟩] := by
  decide +kernel

/-- `MemoryPlan::firmware_ranges`. -/
theorem firmwareRangesOk : newPlan.map MemoryPlan.firmwareRanges = .ok [⟨0x8000, 0x1000⟩] := by
  decide +kernel

/-- `MemoryPlan::described_bytes`: the two banks. -/
theorem describedBytesOk : newPlan.map MemoryPlan.describedBytes = .ok 0x20_0800 := by
  decide +kernel

/-- `MemoryPlan::managed_bytes`: the window. -/
theorem managedBytesOk : newPlan.map MemoryPlan.managedBytes = .ok 0x8_0000 := by
  decide +kernel

/-- `MemoryPlan::contains_ram`: true inside the second bank, false across the
end of the first. -/
theorem containsRamOk :
    newPlan.map (·.containsRam ⟨0x4000_0000, 0x1000⟩) = .ok true ∧
      newPlan.map (·.containsRam ⟨0x10_0000, 0x1000⟩) = .ok false := by
  decide +kernel

/-- `MemoryPlan::is_available`: true inside the second bank, false on the boot
storage. -/
theorem planIsAvailableOk :
    newPlan.map (·.isAvailable ⟨0x4000_0000, 0x1000⟩) = .ok true ∧
      newPlan.map (·.isAvailable ⟨0x1000, 0x10⟩) = .ok false := by
  decide +kernel

/-- `MemoryPlan::permits_backing`: true in the window, false in the second
bank, which it does not manage. -/
theorem permitsBackingOk :
    newPlan.map (·.permitsBacking ⟨0x2000, 0x1000⟩) = .ok true ∧
      newPlan.map (·.permitsBacking ⟨0x4000_0000, 0x1000⟩) = .ok false := by
  decide +kernel

/-- `MemoryPlan::available_ranges`: the window without the two reservations.
-/
theorem availableRangesOk :
    newPlan.map MemoryPlan.availableRanges =
      .ok [⟨0, 0x1000⟩, ⟨0x2000, 0x6000⟩, ⟨0x9000, 0x7_7000⟩] := by
  decide +kernel

/-! ## `Span::new`, `end` and `contains` -/

/-- `Span::new`: a span that ends at `2 ^ 64 - 1`. -/
theorem spanNewOk :
    Span.new 0xffff_ffff_ffff_fff0 0xf = .ok ⟨0xffff_ffff_ffff_fff0, 0xf⟩ := by
  decide +kernel

/-- `Span::new`: a span that ends at `2 ^ 64`. -/
theorem spanNewOverflow : Span.new 0xffff_ffff_ffff_fff0 0x10 = .error .overflow := by
  decide +kernel

/-- `Span::end`. -/
theorem spanEndOk : (⟨0x1000, 0x10⟩ : Span).endAddr = .ok 0x1010 := by decide +kernel

/-- `Span::end`: an end of `2 ^ 64`. -/
theorem spanEndOverflow : (⟨0xffff_ffff_ffff_fff0, 0x10⟩ : Span).endAddr = .error .overflow := by
  decide +kernel

/-- `Span::contains`: true for the last 2 KiB, false for 1 byte more. -/
theorem spanContainsOk :
    (⟨0x1000, 0x1000⟩ : Span).contains ⟨0x1800, 0x800⟩ = .ok true ∧
      (⟨0x1000, 0x1000⟩ : Span).contains ⟨0x1800, 0x801⟩ = .ok false := by
  decide +kernel

/-- `Span::contains`: another span that ends at `2 ^ 64`. -/
theorem spanContainsOverflow :
    (⟨0x1000, 0x1000⟩ : Span).contains ⟨0xffff_ffff_ffff_fff0, 0x10⟩ = .error .overflow := by
  decide +kernel

/-! ## Error priority

For each step of the two error orders of the contract, one input that breaks
a rule of that step and a later rule of the same entry, and gives the error
of the step: the error of the later rule is the one that the input gives once
the earlier rule is repaired. The steps are those of the order of the parse
and the entries on a tree, 1 to 8, and of the order of the boot memory map,
1 to 7; its step 8, the last check of `MemoryPlan::new`, has no later rule. -/

/-- Step 1: a `version` of 16, `UnsupportedVersion`, before the reservation
entry of size 0 of step 2, `EmptyRegion`. -/
theorem priorityStep1 :
    Fdt.parse (setWord (reservedRoot [(0x1000, 0)]) 20 16) = .error .unsupportedVersion := by
  decide +kernel

/-- Step 2: two reservation entries that share `[0x1800, 0x2000)`, `Overlap`,
before the token 5 of step 3, `BadToken`. -/
theorem priorityStep2 :
    Fdt.parse (Builder.empty.reserve 0x1000 0x1000 |>.reserve 0x1800 0x1000 |>.beginNode ""
      |>.word 5 |>.endNode).finish = .error .overlap := by
  decide +kernel

/-- Step 3: the encoding of a token before its place in the tree; a property
named `a b` after the child `a` of the root fails on its name, `BadString`,
before its place after a child, `BadTree`. -/
theorem priorityStep3 :
    Fdt.parse (Builder.empty.beginNode "" |>.beginNode "a" |>.endNode |>.flag "a b"
      |>.endNode).finish = .error .badString := by
  decide +kernel

/-- Step 4: the whole `reg` of a memory node before its ranges; the second
range of `memory@1` leaves 64 bits, `Overflow`, before its first range,
which shares an address with that of `memory@0`, `Overlap`. -/
theorem priorityStep4 : priorityMemoryTree.discoverMemory = .error .overflow := by
  decide +kernel

/-- Step 5: an empty image, `EmptyRegion`, before the memory discovery of a
tree without RAM, `NoMemory`. -/
theorem priorityStep5 :
    pi5NoMemoryTree.discoverBootMemory pi5HandOver 0x10_0000 ⟨0x20_0000, 0⟩ = .error .emptyRegion := by
  decide +kernel

/-- Step 6: the size cells of `/cpus`, 1, `BadProperty`, before its 3
address cells, `UnsupportedCells`. -/
theorem priorityStep6 : priorityCpusTree.discoverCpus qemuHvcCpus = .error .badProperty := by
  decide +kernel

/-- Step 7: the windows of a translation in order; the first two hold the
request, `AmbiguousMapping` at the second, before the third, which holds part
of it, `Unmapped`. -/
theorem priorityStep7 :
    (AddressMap.new (some (cells [0, 0x2000, 0x100, 0, 0x3000, 0x100, 0x10, 0x1000, 0x10])) 1 1 1).bind
      (·.toParent ⟨0x18, 0x10⟩) = .error .ambiguousMapping := by
  decide +kernel

/-- Step 8: a selection of size 0, `EmptyRegion`, before its alignment of 3,
`BadAlignment`. -/
theorem priorityStep8 : pi5Memory.findAvailable 0 3 0 0x1000 = .error .emptyRegion := by
  decide +kernel

/-- Step 1 of the boot memory map: a managed window of size 0, `InvalidRange`,
before the missing RAM bank of step 2, `Capacity`. -/
theorem priorityPlanStep1 : MemoryPlan.new ⟨0, 0⟩ [] boot firmware = .error .invalidRange := by
  decide +kernel

/-- Step 2: 33 RAM banks, `Capacity`, before the first of them, of size 0, in
step 3, `InvalidRange`. -/
theorem priorityPlanStep2 :
    MemoryPlan.allRam (⟨0, 0⟩ :: (List.range 32).map fun i =>
      ⟨UInt64.ofNat ((i + 1) * 0x10000), 0x1000⟩) boot firmware = .error .capacity := by
  decide +kernel

/-- Step 3: a bank that shares `[0x1000, 0x2000)` with an earlier one,
`Overlap`, before the 16 GiB and 4 KiB of the banks in step 4,
`ArenaTooLarge`. -/
theorem priorityPlanStep3 :
    MemoryPlan.allRam [⟨0, 0x4_0000_0000⟩, ⟨0x1000, 0x1000⟩] boot firmware = .error .overlap := by
  decide +kernel

/-- Step 4: a bank of 16 GiB and 4 KiB, `ArenaTooLarge`, before the boot
storage outside every bank of step 6, `OutsideRam`. -/
theorem priorityPlanStep4 :
    MemoryPlan.allRam [⟨0, 0x4_0000_1000⟩] [⟨0x8_0000_0000, 0x10⟩] [] = .error .arenaTooLarge := by
  decide +kernel

/-- Step 5: a bank without a complete page, `Alignment`, before the boot
storage outside every bank of step 6, `OutsideRam`. -/
theorem priorityPlanStep5 :
    MemoryPlan.allRam [⟨1, 0x800⟩] [⟨0x10_0000, 0x10⟩] [] = .error .alignment := by
  decide +kernel

/-- Step 6: boot storage outside every bank, `OutsideRam`, before the firmware
reservation on its page in step 7, `Overlap`. -/
theorem priorityPlanStep6 :
    MemoryPlan.allRam [⟨0, 0x800_0000⟩] [⟨0x1000_0000, 0x10⟩] [⟨⟨0x1000_0000, 1⟩, true, false⟩] =
      .error .outsideRam := by
  decide +kernel

/-- Step 7: a firmware reservation on a page of the boot storage, `Overlap`,
before the managed window outside every bank of step 8, `OutsideRam`. -/
theorem priorityPlanStep7 :
    MemoryPlan.new ⟨0x1000_0000, 0x1000⟩ [⟨0, 0x800_0000⟩] [⟨0x8_0000, 0x3_8000⟩]
      [⟨⟨0x8_0000, 1⟩, true, false⟩] = .error .overlap := by
  decide +kernel


/-! ## Unreachable error branches

Branches of the entries that fail with an error, but that no input of the
entry reaches under 64-bit arithmetic or on the trees that the parse
accepts. Each proposition states that the entry, or the step of it where the
branch lies, never takes the branch, and gives the reason; a planned theorem
below `Krepi.Proofs.Fdt.Witnesses` proves it. The error of each branch is
still witnessed above where another branch of the same entry gives it. -/

/-- **Planned.** Step 1 of the parse never fails with `Overflow`: the offset
and the size of each block are 32-bit words, so the end of a block fits in
64 bits. -/
def HeaderNoOverflow : Prop := ∀ input, header input ≠ .error .overflow

/-- **Planned.** No entry of the reservation map runs past 64 bits, so its
`Overflow` of an entry past the tree is never reached: the map starts at a
32-bit offset and the parse reads at most `MAX_RESERVATIONS + 1` entries of 16
bytes. The entry `k`, from 0, starts at `reserveStart + 16 * k`, and the end
`cursor + 16` that step 2 checks with `checkedAdd` is therefore at most
`reserveStart + 16 * (MAX_RESERVATIONS + 1)`, which this states to be below
`2 ^ 64`, so that check never fails. The other `Overflow` of the step, the
end of the span of an entry, is reached (`parseOverflow`). -/
def ReservationEntriesFit : Prop :=
  ∀ input h, header input = .ok h →
    h.layout.reserveStart + 16 * (MAX_RESERVATIONS.toNat + 1) < 2 ^ 64

/-- **Planned.** The tokens never fail with `Overflow`: a value starts within
the structure block, of at most `MAX_BLOB_SIZE` bytes, and its length is a
32-bit word, so its end fits in 64 bits. -/
def TokensNoOverflow : Prop := ∀ input h, header input = .ok h → structureNodes h ≠ .error .overflow

/-- **Planned.** The reservation map never runs out of its fuel: more fuel
gives the same result, since `MAX_RESERVATIONS` entries and the terminator, or
the entry after them, end it first. Its `LimitExceeded` is that of the limit.
-/
def ReservationFuelSuffices : Prop :=
  ∀ (h : Header) (n : Nat),
    reservationsFrom h (MAX_RESERVATIONS.toNat + 1 + n) h.layout.reserveStart [] = reservationMap h

/-- **Planned.** The memory discovery never fails with `BadTree` on a
well-formed tree: such a tree has a root, and every node whose `reg` the
discovery reads has a parent. -/
def DiscoverMemoryNoBadTree : Prop := ∀ t : Fdt, t.WellFormed → t.discoverMemory ≠ .error .badTree

/-- **Planned.** The discovery of the boot memory never fails with `BadTree`
on a well-formed tree, for the reason of `DiscoverMemoryNoBadTree`. -/
def DiscoverBootMemoryNoBadTree : Prop :=
  ∀ (t : Fdt) (handOver : HandOverProfile) (dtbAddress : UInt64) (image : Span), t.WellFormed →
    t.discoverBootMemory handOver dtbAddress image ≠ .error .badTree

/-- **Planned.** The sum of the RAM ranges of a memory discovery fits in 64
bits, so the discovery of the boot memory never fails with `Overflow` at that
sum: the ranges are disjoint spans that end within 64 bits. The discovery adds
them one at a time with `checkedAdd`, and each partial sum is at most the sum
of all of them, which this bounds, so no addition fails. -/
def RamBytesFit : Prop :=
  ∀ (t : Fdt) (m : MemoryMap), t.discoverMemory = .ok m → spansBytes m.ram < 2 ^ 64

/-- **Planned.** The climb of a translation never fails with `BadTree`: it
reads the `ranges` of a bus only when the bus has a parent. -/
def ClimbRangesNoBadTree : Prop :=
  ∀ (fuel : Nat) (bus : Node) (s : Span), climbRanges fuel bus s ≠ .error .badTree

/-- **Planned.** `Node::translate_reg` never runs out of its fuel on a
well-formed tree: no node lies deeper than `MAX_DEPTH - 1`. -/
def TranslateRegFuelSuffices : Prop :=
  ∀ (n : Node) (s : Span), n.fdt.WellFormed → n.translateReg s ≠ .error .limitExceeded

/-- **Planned.** A translation through the windows of a well-formed map never
fails with `Overflow` once its request is within the width of its side: the
translated span lies inside the target side of its window, which ends within
64 bits, so neither its start nor its end leaves 64 bits. -/
def WindowTranslationNoOverflow : Prop :=
  ∀ (m : AddressMap) (s : Span) (reverse : Bool) (w : Window) (ws : List Window),
    m.WellFormed → m.windows = some (w :: ws) →
    s.WithinWidth (if reverse then m.parentCells else m.childCells) →
    m.translate s reverse ≠ .error .overflow

/-- **Planned.** A CPU node never fails with `UnsupportedCells` at its `reg`:
step 6 reads that value in the address cells of `/cpus`, which it has checked
to be 1 or 2 before it reads any child, and `cells_u64` fails with
`UnsupportedCells` only for more than 2 cells. The `UnsupportedCells` of
`discover_cpus` is that of the address cells of `/cpus`
(`discoverCpusUnsupportedCells`). -/
def CpuRegNoUnsupportedCells : Prop :=
  ∀ (profile : CpuProfile) (cells : UInt32) (ids : List UInt64) (n : Node),
    (cells = 1 ∨ cells = 2) → cpuOfChild profile cells ids n ≠ .error .unsupportedCells

/-- **Planned.** `BootMemory::find_available` never runs out of its fuel:
each candidate after the first lies past every exclusion that an earlier one
touched, so `Q + 3` candidates for `Q` reserved regions end the search of a
range first. -/
def FindAvailableNoLimitExceeded : Prop :=
  ∀ (m : BootMemory) (size alignment minimum limit : UInt64),
    m.findAvailable size alignment minimum limit ≠ .error .limitExceeded

/-- **Planned.** The banks that pass step 3 of the boot memory map hold fewer
than `2 ^ 64` bytes, so the sum of step 4 never fails with `Overflow` in
`all_ram`, `new` or `from_boot_memory`: they are disjoint spans that end
within 64 bits. Step 4 adds the sorted banks one at a time, and each partial sum is at
most the sum of all of them, which this bounds, so its check of the sum
never fails. -/
def BankBytesFit : Prop :=
  ∀ ram banks : List Span, ram.foldlM addBank [] = .ok banks →
    spansBytes (sortByStart banks) < 2 ^ 64

/-! ## The two variants -/

/-- A success under `Except.map` is one of the mapped value. -/
theorem ok_of_map_ok {ε α β : Type} {f : α → β} {x : Except ε α} {v : β}
    (h : x.map f = .ok v) : ∃ r, x = .ok r := by
  cases x with
  | error e => cases h
  | ok r => exact ⟨r, rfl⟩

/-- An error under `Except.map` is one of the mapped value. -/
theorem error_of_map_error {ε α β : Type} {f : α → β} {x : Except ε α} {e : ε}
    (h : x.map f = .error e) : x = .error e := by
  cases x with
  | error e' => cases h; rfl
  | ok r => cases h

/-- A result of `atPath` is a result of its function on a node. -/
theorem exists_of_atPath {β : Type} {t : Fdt} {path : String} {f : Node → β} {r : β}
    (h : atPath t path f = some r) : ∃ n, f n = r := by
  unfold atPath at h
  split at h
  · exact ⟨_, Option.some.inj h⟩
  · cases h

/-- **The variant that rejects every input is refuted.** Each frozen function
that can fail succeeds on an input, by the success witnesses above. -/
theorem notAlwaysRejecting :
    (∃ b t, Fdt.parse b = .ok t) ∧
    (∃ t : Fdt, ∃ p r, t.findNode p = .ok r) ∧
    (∃ n : Node, ∃ p r, n.stringProperty p = .ok r) ∧
    (∃ n : Node, ∃ r, n.enabled = .ok r) ∧
    (∃ n : Node, ∃ r, n.addressCells = .ok r) ∧
    (∃ n : Node, ∃ r, n.sizeCells = .ok r) ∧
    (∃ n : Node, ∃ r, n.reg = .ok r) ∧
    (∃ n : Node, ∃ r, n.ranges = .ok r) ∧
    (∃ n : Node, ∃ r, n.dmaRanges = .ok r) ∧
    (∃ n : Node, ∃ s r, n.translateReg s = .ok r) ∧
    (∃ t : Fdt, ∃ r, t.discoverMemory = .ok r) ∧
    (∃ t : Fdt, ∃ h a i r, t.discoverBootMemory h a i = .ok r) ∧
    (∃ m : BootMemory, ∃ s r, m.isAvailable s = .ok r) ∧
    (∃ m : BootMemory, ∃ z a lo hi r, m.findAvailable z a lo hi = .ok r) ∧
    (∃ t : Fdt, ∃ p r, t.discoverCpus p = .ok r) ∧
    (∃ t : CpuTopology, ∃ b, t.validateTimers b = .ok ()) ∧
    (∃ b c r, cellsU64 b c = .ok r) ∧
    (∃ b ac sc r, Reg.new b ac sc = .ok r) ∧
    (∃ b cc pc sc r, AddressMap.new b cc pc sc = .ok r) ∧
    (∃ m : AddressMap, ∃ s r, m.toParent s = .ok r) ∧
    (∃ m : AddressMap, ∃ s r, m.toChild s = .ok r) ∧
    (∃ ram boot firmware r, MemoryPlan.allRam ram boot firmware = .ok r) ∧
    (∃ w ram boot firmware r, MemoryPlan.new w ram boot firmware = .ok r) ∧
    (∃ m w more r, MemoryPlan.fromBootMemory m w more = .ok r) ∧
    (∃ a z r, Span.new a z = .ok r) ∧
    (∃ s : Span, ∃ r, s.endAddr = .ok r) ∧
    (∃ s o : Span, ∃ r, s.contains o = .ok r) :=
  ⟨⟨_, _, parseOk⟩, ⟨_, _, ok_of_map_ok findNodeOk⟩,
    (exists_of_atPath stringPropertyOk).elim fun n h => ⟨n, _, _, h⟩,
    (exists_of_atPath enabledOk.1).elim fun n h => ⟨n, _, h⟩,
    (exists_of_atPath addressCellsOk.1).elim fun n h => ⟨n, _, h⟩,
    (exists_of_atPath sizeCellsOk.1).elim fun n h => ⟨n, _, h⟩,
    (exists_of_atPath regOk).elim fun n h => ⟨n, _, h⟩,
    (exists_of_atPath rangesOk).elim fun n h => ⟨n, _, h⟩,
    (exists_of_atPath dmaRangesOk).elim fun n h => ⟨n, _, h⟩,
    (exists_of_atPath translateRegOk).elim fun n h => ⟨n, _, _, h⟩,
    ⟨_, _, discoverMemoryOk⟩, ⟨_, _, _, _, _, discoverBootMemoryOk⟩,
    ⟨_, _, _, bootMemoryIsAvailableOk.1⟩, ⟨_, _, _, _, _, _, findAvailableOk.1⟩,
    ⟨_, _, _, discoverCpusOk⟩, ⟨_, _, validateTimersOk⟩, ⟨_, _, _, cellsU64Ok⟩,
    ⟨_, _, _, _, regNewOk⟩,
    ⟨_, _, _, _, _, addressMapNewOk⟩, ⟨_, _, _, toParentOk⟩, ⟨_, _, _, toChildOk⟩,
    ⟨_, _, _, _, allRamOk⟩, ⟨_, _, _, _, _, newOk⟩, ⟨_, _, _, _, fromBootMemoryOk⟩,
    ⟨_, _, _, spanNewOk⟩, ⟨_, _, spanEndOk⟩, ⟨_, _, _, spanContainsOk.1⟩⟩

/-- **The variant that accepts every input is refuted.** Each frozen function
that can fail fails on an input, by the rejection witnesses above. -/
theorem notAlwaysSucceeding :
    (∃ b e, Fdt.parse b = .error e) ∧
    (∃ t : Fdt, ∃ p e, t.findNode p = .error e) ∧
    (∃ n : Node, ∃ p e, n.stringProperty p = .error e) ∧
    (∃ n : Node, ∃ e, n.enabled = .error e) ∧
    (∃ n : Node, ∃ e, n.addressCells = .error e) ∧
    (∃ n : Node, ∃ e, n.sizeCells = .error e) ∧
    (∃ n : Node, ∃ e, n.reg = .error e) ∧
    (∃ n : Node, ∃ e, n.ranges = .error e) ∧
    (∃ n : Node, ∃ e, n.dmaRanges = .error e) ∧
    (∃ n : Node, ∃ s e, n.translateReg s = .error e) ∧
    (∃ t : Fdt, ∃ e, t.discoverMemory = .error e) ∧
    (∃ t : Fdt, ∃ h a i e, t.discoverBootMemory h a i = .error e) ∧
    (∃ m : BootMemory, ∃ s e, m.isAvailable s = .error e) ∧
    (∃ m : BootMemory, ∃ z a lo hi e, m.findAvailable z a lo hi = .error e) ∧
    (∃ t : Fdt, ∃ p e, t.discoverCpus p = .error e) ∧
    (∃ t : CpuTopology, ∃ b e, t.validateTimers b = .error e) ∧
    (∃ b c e, cellsU64 b c = .error e) ∧
    (∃ b ac sc e, Reg.new b ac sc = .error e) ∧
    (∃ b cc pc sc e, AddressMap.new b cc pc sc = .error e) ∧
    (∃ m : AddressMap, ∃ s e, m.toParent s = .error e) ∧
    (∃ m : AddressMap, ∃ s e, m.toChild s = .error e) ∧
    (∃ ram boot firmware e, MemoryPlan.allRam ram boot firmware = .error e) ∧
    (∃ w ram boot firmware e, MemoryPlan.new w ram boot firmware = .error e) ∧
    (∃ m w more e, MemoryPlan.fromBootMemory m w more = .error e) ∧
    (∃ a z e, Span.new a z = .error e) ∧
    (∃ s : Span, ∃ e, s.endAddr = .error e) ∧
    (∃ s o : Span, ∃ e, s.contains o = .error e) :=
  ⟨⟨_, _, parseTruncated⟩, ⟨_, _, _, error_of_map_error findNodeBadPath⟩,
    (exists_of_atPath stringPropertyBadString).elim fun n h => ⟨n, _, _, h⟩,
    (exists_of_atPath enabledBadString).elim fun n h => ⟨n, _, h⟩,
    (exists_of_atPath addressCellsBadProperty).elim fun n h => ⟨n, _, h⟩,
    (exists_of_atPath sizeCellsBadProperty).elim fun n h => ⟨n, _, h⟩,
    (exists_of_atPath regBadTree).elim fun n h => ⟨n, _, h⟩,
    (exists_of_atPath rangesBadTree).elim fun n h => ⟨n, _, h⟩,
    (exists_of_atPath dmaRangesBadTree).elim fun n h => ⟨n, _, h⟩,
    (exists_of_atPath translateRegUnmapped).elim fun n h => ⟨n, _, _, h⟩,
    ⟨_, _, discoverMemoryNoMemory⟩, ⟨_, _, _, _, _, discoverBootMemoryUnmapped⟩,
    ⟨_, _, _, bootMemoryIsAvailableEmptyRegion⟩, ⟨_, _, _, _, _, _, findAvailableBadAlignment⟩,
    ⟨_, _, _, discoverCpusMissingProperty⟩, ⟨_, _, _, validateTimersBadProperty⟩,
    ⟨_, _, _, cellsU64BadProperty⟩, ⟨_, _, _, _, regNewOverflow⟩,
    ⟨_, _, _, _, _, addressMapNewEmptyRegion⟩, ⟨_, _, _, toParentUnmapped⟩,
    ⟨_, _, _, toChildUnmapped⟩, ⟨_, _, _, _, allRamCapacity⟩, ⟨_, _, _, _, _, newOutsideRam⟩,
    ⟨_, _, _, _, fromBootMemoryCapacity⟩, ⟨_, _, _, spanNewOverflow⟩, ⟨_, _, spanEndOverflow⟩,
    ⟨_, _, _, spanContainsOverflow⟩⟩

end Krepi.Spec.Fdt.Witnesses
