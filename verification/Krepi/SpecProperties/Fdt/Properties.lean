module

public import Krepi.SpecProperties.Fdt.Invariants

/-!
# Device tree: properties

The cross-cutting properties of the `fdt` component, each a proposition that
a theorem below `Krepi.Proofs.Fdt` proves, drawn from its requirements
(`docs/domains/boot-platform/fdt/requirements.md`):

1. `ParseLimitsExact`: each limit of the parse accepts a tree at the limit
   and rejects one 1 above it with the error of the contract (FDT-R01).
2. `PrefixesRejected`: every prefix of an accepted tree shorter than its
   `totalsize` fails with `Truncated` (FDT-R02).
3. `NoChoiceAmongDuplicates`: where an entry looks for one item and finds
   two, it rejects the input and never picks one (FDT-R02, FDT-R03,
   FDT-R07, FDT-R08).
4. `UsableRangesExact`: the usable ranges are exactly the managed banks
   without the reservations, each inside one managed bank and maximal
   (FDT-R06, FDT-R07).
5. `FindAvailableLowest`: the span of `Pi5BootMemory::find_available` is
   available and has the lowest aligned start in the first RAM range that
   has one, and none means that no range has one (FDT-R05).
6. `UnreadValuesIgnored`: the values of `/chosen` but its `device_type` and,
   when that is `memory`, its `status`, and those of a dynamic reservation
   but its `status` and flags, do not reach the results of the discoveries
   (FDT-R04, FDT-R10).
7. `AffinityRoundTrip`: the logical ID of the affinity of a CPU of a topology
   is that CPU, whatever the flag bits of `MPIDR_EL1` (FDT-R08).
8. `TranslationThroughOneWindow`: a translation succeeds exactly through the
   one window that holds the whole request, adding its offset (FDT-R09).

The invariants of `Krepi.SpecProperties.Fdt.Invariants` state the rest of the
limits: every tree that the parse accepts lies within them
(`ParseWellFormed`). The definitions that the properties need on the values
of the specification extend its namespace.
-/

@[expose] public section

namespace Krepi.Spec.Fdt

/-! ## Paths, values and selections -/

/-- The names of the nodes from the root, excluded, down to the node of index
`i`, following at most `fuel` parents. -/
def Fdt.namesFrom (t : Fdt) : (fuel i : Nat) → List String
  | 0, _ => []
  | fuel + 1, i =>
    match t.records[i]? with
    | some r =>
      match r.parent with
      | some p => t.namesFrom fuel p ++ [r.name]
      | none => []
    | none => []

/-- The absolute path of a node: `/` and the names of the nodes from the root
down to it, joined by `/`; `/` for the root. -/
def Node.path (n : Node) : String :=
  "/" ++ "/".intercalate (n.fdt.namesFrom (n.index.val + 1) n.index.val)

/-- The spans of the `reg` of each enabled child of `root` whose name is a
memory name, in tree order: the RAM ranges that the rules of the discovery
give, lines 448 to 457 of the contract. -/
def Fdt.memoryNodeSpans (t : Fdt) (root : Node) : List Span :=
  let enabled (n : Node) : Bool := match n.enabled with
    | .ok b => b
    | .error _ => false
  let nodes := t.nodes.filter fun n => n.isChildOf root && isMemoryName n.name && enabled n
  nodes.flatMap fun n =>
    match n.reg with
    | .ok r => r.entries
    | .error _ => []

/-- The value of the property `name` of a record, or none. -/
def NodeRecord.value (r : NodeRecord) (name : String) : Option ByteArray :=
  (r.properties.find? (·.1 == name)).map (·.2)

/-- Whether the discoveries leave the value of the property `name` of the
record of index `i` of `t` unread, by the rules of the contract:

- a property of `/chosen`, the child of the root named `chosen`, other than
  its `device_type` and, when that `device_type` is `memory`, its `status`:
  the discovery of memory reads the `device_type` of each child of the root
  and the `status` of each memory node, which a `device_type` of `memory`
  makes `/chosen`; it skips such a `/chosen` when it is disabled and fails
  with `BadProperty` on its name when it is enabled, so it reads nothing
  else of it (lines 448 to 453 and 808 to 811 of the contract);
- a property of a dynamic reservation, a child of `/reserved-memory` with
  `size` and without `reg`, other than its `status`, `no-map` and
  `reusable`: the discovery checks only that form and counts the node
  (lines 469 to 475). -/
def unreadByDiscoveries (t : Fdt) (i : Nat) (name : String) : Bool :=
  match t.records[i]? with
  | none => false
  | some r =>
    (r.parent == some 0 && r.name == "chosen" && name != "device_type" &&
        (r.value "device_type" != some ("memory".toByteArray.push 0) || name != "status")) ||
      match (r.parent.bind fun p => t.records[p]?) with
      | some parent =>
        parent.name == "reserved-memory" && parent.parent == some 0 &&
          (r.value "size").isSome && (r.value "reg").isNone &&
          !["status", "no-map", "reusable"].contains name
      | none => false

/-- Two trees that differ at most in the values of the properties that
`free` names: the same `totalsize`, reservation entries and nodes, each node
with the same name, parent and property names in the same order, and the
same value of each property that `free` does not name. -/
def Fdt.SameExceptValues (free : Nat → String → Bool) (t t' : Fdt) : Prop :=
  t.totalSize = t'.totalSize ∧ t.reservations = t'.reservations ∧
  t.records.size = t'.records.size ∧
  ∀ i r r', t.records[i]? = some r → t'.records[i]? = some r' →
    r.name = r'.name ∧ r.parent = r'.parent ∧
      r.properties.map (·.1) = r'.properties.map (·.1) ∧
      ∀ q ∈ r.properties.zip r'.properties, free i q.1.1 = false → q.1.2 = q.2.2

/-- Whether `s` is a span that `find_available(size, alignment, minimum,
limit)` may give from the RAM range `r` of `m`: of `size` bytes, at a
multiple of `alignment`, within `[minimum, limit)` and 64 bits, inside `r`,
and touching none of the image, the tree and the reserved regions (lines 606
to 611 of the contract). -/
def Pi5BootMemory.Fits (m : Pi5BootMemory) (size alignment minimum limit : UInt64)
    (r s : Span) : Prop :=
  s.size = size ∧ s.start.toNat % alignment.toNat = 0 ∧ minimum.toNat ≤ s.start.toNat ∧
    s.endNat ≤ limit.toNat ∧ s.Valid ∧ r.holds s = true ∧
    ∀ x ∈ m.exclusions, x.touches s = false

/-- The side of a window that a translation reads: the child side for
`to_parent`, the parent side for `to_child` (`reverse`). -/
def Window.source (w : Window) (reverse : Bool) : Span := if reverse then w.parent else w.child

/-- The side of a window that a translation gives. -/
def Window.target (w : Window) (reverse : Bool) : Span := if reverse then w.child else w.parent

end Krepi.Spec.Fdt

namespace Krepi.SpecProperties.Fdt

open Krepi.Spec.Fdt

/-! ## Trees built for the statements

A small encoder of device trees in the format of chapter 5 of DTSpec v0.4,
from which the limits are stated: a header of version 17, compatible with
16; the reservation map at offset 40 with its terminator; the structure block
right after it, ended by the end token; and the strings block right after
that, the names of the tree in their order, each with its NUL and as often
as the tree lists it. The builder of the specification tests,
`Krepi.SpecTests.Fdt.Builder`, writes its trees through this encoder, so
the two share one encoding. -/

/-- The bytes of a 64-bit big-endian word, the low 64 bits of `n`. -/
def be64 (n : Nat) : List UInt8 := be32 (n / 2 ^ 32) ++ be32 n

/-- `bytes` and zero bytes up to the next multiple of 4. -/
def padTo4 (bytes : List UInt8) : List UInt8 :=
  bytes ++ List.replicate ((4 - bytes.length % 4) % 4) 0

/-- An item of the structure block of a built tree: a begin node with its
name, a property with the index of its name among the names of the tree and
its value, an end node, or a no-operation. -/
inductive Item where
  | beginNode (name : String)
  | property (name : Nat) (value : List UInt8)
  | endNode
  | nop

/-- The offsets of the names `names` in a strings block that holds them in
order from `offset`, each with its NUL. -/
def nameOffsets (offset : Nat) : List String → List Nat
  | [] => []
  | name :: rest => offset :: nameOffsets (offset + name.utf8ByteSize + 1) rest

/-- The token of an item, the names of the tree at `offsets`. -/
def Item.bytes (offsets : List Nat) : Item → List UInt8
  | .beginNode name => be32 1 ++ padTo4 (name.toByteArray.toList ++ [0])
  | .property name value => be32 3 ++ be32 value.length ++ be32 (offsets.getD name 0) ++ padTo4 value
  | .endNode => be32 2
  | .nop => be32 4

/-- A built tree: its reservation entries, each an address and a size, the
names of its properties, and the items of its structure block. -/
structure BuiltTree where
  reservations : List (Nat × Nat)
  names : List String
  items : List Item

/-- The bytes of a built tree, followed by zero bytes up to `size` when it is
shorter, with `totalsize` the length of the whole. -/
def BuiltTree.bytes (b : BuiltTree) (size : Nat) : ByteArray :=
  let map := b.reservations.flatMap (fun e => be64 e.1 ++ be64 e.2) ++ List.replicate 16 0
  let structure_ := b.items.flatMap (Item.bytes (nameOffsets 0 b.names)) ++ be32 9
  let strings := b.names.flatMap fun name => name.toByteArray.toList ++ [0]
  let structStart := 40 + map.length
  let stringsStart := structStart + structure_.length
  let natural := stringsStart + strings.length
  let total := max natural size
  let header := be32 0xd00d_feed ++ be32 total ++ be32 structStart ++ be32 stringsStart ++
    be32 40 ++ be32 17 ++ be32 16 ++ be32 0 ++ be32 strings.length ++ be32 structure_.length
  ByteArray.mk (header ++ map ++ structure_ ++ strings ++ List.replicate (total - natural) 0).toArray

/-- The root alone: a begin node with the empty name and its end node. -/
def rootOnly : List Item := [.beginNode "", .endNode]

/-- The root alone, padded with zero bytes to a `totalsize` of `n`. -/
def treeOfSize (n : Nat) : ByteArray := (BuiltTree.mk [] [] rootOnly).bytes n

/-- `n` nodes on one path, the root and below it nodes named `a`, each the
child of the one before. -/
def treeOfDepth (n : Nat) : ByteArray :=
  let items := Item.beginNode "" :: List.replicate (n - 1) (.beginNode "a") ++
    List.replicate n .endNode
  (BuiltTree.mk [] [] items).bytes 0

/-- A structure block of `n` tokens, the end token included: the root with
`n - 3` no-operations before its end node. -/
def treeOfTokens (n : Nat) : ByteArray :=
  let items := Item.beginNode "" :: List.replicate (n - 3) .nop ++ [.endNode]
  (BuiltTree.mk [] [] items).bytes 0

/-- The root with `n` properties of the distinct names `p0`, `p1`, ..., each
with an empty value. -/
def treeOfProperties (n : Nat) : ByteArray :=
  let names := (List.range n).map fun i => "p" ++ toString i
  let items := Item.beginNode "" :: (List.range n).map (fun i => Item.property i []) ++ [.endNode]
  (BuiltTree.mk [] names items).bytes 0

/-- The root with one property whose name is `n` bytes `a`. -/
def treeOfNameBytes (n : Nat) : ByteArray :=
  let name := String.ofList (List.replicate n 'a')
  (BuiltTree.mk [] [name] [.beginNode "", .property 0 [], .endNode]).bytes 0

/-- The root alone with `n` reservation entries of 4 KiB, the one of index
`i` at `(i + 1) * 0x1000`. -/
def treeOfReservations (n : Nat) : ByteArray :=
  (BuiltTree.mk ((List.range n).map fun i => ((i + 1) * 0x1000, 0x1000)) [] rootOnly).bytes 0

/-! ## Properties -/

/-- **Each limit of the parse is exact** (FDT-R01). For each of the six
limits of the parse, `totalsize`, the nodes on a path, the tokens, the
properties of a node, the bytes of a property name and the reservation
entries, a tree at the limit is accepted and one 1 above it fails with the
error of the contract: `LimitExceeded`, and `BadString` for a property name
(lines 170 to 179 of the contract). That every accepted tree lies within the
limits is `ParseWellFormed`. -/
def ParseLimitsExact : Prop :=
  (∃ t, Fdt.parse (treeOfSize MAX_BLOB_SIZE.toNat) = .ok t) ∧
    Fdt.parse (treeOfSize (MAX_BLOB_SIZE.toNat + 1)) = .error .limitExceeded ∧
  (∃ t, Fdt.parse (treeOfDepth MAX_DEPTH.toNat) = .ok t) ∧
    Fdt.parse (treeOfDepth (MAX_DEPTH.toNat + 1)) = .error .limitExceeded ∧
  (∃ t, Fdt.parse (treeOfTokens MAX_TOKENS.toNat) = .ok t) ∧
    Fdt.parse (treeOfTokens (MAX_TOKENS.toNat + 1)) = .error .limitExceeded ∧
  (∃ t, Fdt.parse (treeOfProperties MAX_PROPERTIES.toNat) = .ok t) ∧
    Fdt.parse (treeOfProperties (MAX_PROPERTIES.toNat + 1)) = .error .limitExceeded ∧
  (∃ t, Fdt.parse (treeOfNameBytes MAX_PROPERTY_NAME.toNat) = .ok t) ∧
    Fdt.parse (treeOfNameBytes (MAX_PROPERTY_NAME.toNat + 1)) = .error .badString ∧
  (∃ t, Fdt.parse (treeOfReservations MAX_RESERVATIONS.toNat) = .ok t) ∧
    Fdt.parse (treeOfReservations (MAX_RESERVATIONS.toNat + 1)) = .error .limitExceeded

/-- **Every prefix of an accepted tree is rejected** (FDT-R02). Each prefix
of the bytes of an accepted tree that is shorter than its `totalsize` fails
with `Truncated`. -/
def PrefixesRejected : Prop :=
  ∀ (input : ByteArray) (t : Fdt), Fdt.parse input = .ok t →
    ∀ n, n < t.totalSize.toNat → Fdt.parse (input.extract 0 n) = .error .truncated

/-- **No choice among duplicates** (FDT-R02, with FDT-R03, FDT-R07 and
FDT-R08): where an entry looks for one item and finds two, it rejects the
input and never picks one (rule 3, lines 246 to 253 of the contract).

- **Paths.** On a well-formed tree, two nodes of one path make the lookup of
  that path fail with `AmbiguousMapping`, and a node that the lookup finds is
  the only node of its path.
- **CPU nodes.** When `Fdt::discover_cpus` accepts a tree, no two CPU nodes
  of `/cpus` have one `reg`, so none has the logical ID of another.
- **RAM ranges.** The RAM ranges of `Fdt::discover_memory` are all the spans
  of the enabled memory nodes, in tree order, none dropped or merged; with
  `MemoryMap.WellFormed`, two of them that share an address are rejected.
- **RAM banks.** The banks of `MemoryPlan::all_ram` are all the banks given,
  none dropped or merged; with `MemoryPlan.WellFormed`, two that share an
  address are rejected.

No accepted tree holds two properties of one name in a node
(`ParseWellFormed`), and two windows that hold a request are rejected by
`TranslationThroughOneWindow`. -/
def NoChoiceAmongDuplicates : Prop :=
  (∀ t : Fdt, t.WellFormed →
    (∀ n ∈ t.nodes, ∀ m ∈ t.nodes, n.index.val ≠ m.index.val → n.path = m.path →
      t.findNode n.path = .error .ambiguousMapping) ∧
    ∀ (path : String) (n : Node), t.findNode path = .ok (some n) →
      ∀ m ∈ t.nodes, m.path = path → m.index.val = n.index.val) ∧
  (∀ (t : Fdt) (profile : CpuProfile) (topology : CpuTopology) (cpus : Node),
    t.discoverCpus profile = .ok topology → t.findNode "/cpus" = .ok (some cpus) →
    ∀ n ∈ t.nodes, ∀ m ∈ t.nodes, n.isChildOf cpus = true → m.isChildOf cpus = true →
      n.stringProperty "device_type" = .ok (some "cpu") →
      m.stringProperty "device_type" = .ok (some "cpu") →
      n.index.val ≠ m.index.val → n.property "reg" ≠ m.property "reg") ∧
  (∀ (t : Fdt) (m : MemoryMap) (root : Node),
    t.discoverMemory = .ok m → t.findNode "/" = .ok (some root) →
      m.ram = t.memoryNodeSpans root) ∧
  ∀ (ram boot : List Span) (firmware : List ReservedRegion) (p : MemoryPlan),
    MemoryPlan.allRam ram boot firmware = .ok p → p.ram.Perm ram

/-- **The usable ranges are exact** (FDT-R07, FDT-R06). On a well-formed boot
memory map, each usable range lies inside one managed bank and touches no
reservation, so none bridges two banks or a hole; every address of a managed
bank that no reservation holds lies in a usable range; and each usable range
starts at the start of its bank or at the end of a reservation and ends at
the end of its bank or at the start of a reservation, so it is maximal
(lines 583 to 595 and 775 and 776 of the contract). -/
def UsableRangesExact : Prop :=
  ∀ p : MemoryPlan, p.WellFormed →
    (∀ r ∈ p.availableRanges,
      inOneRange p.managed r = true ∧ ∀ x ∈ p.reservations, x.touches r = false) ∧
    (∀ b ∈ p.managed, ∀ a, b.start.toNat ≤ a → a < b.endNat →
      (∀ x ∈ p.reservations, ¬ (x.start.toNat ≤ a ∧ a < x.endNat)) →
      ∃ r ∈ p.availableRanges, r.start.toNat ≤ a ∧ a < r.endNat) ∧
    ∀ r ∈ p.availableRanges,
      ((∃ b ∈ p.managed, b.start = r.start) ∨
        ∃ x ∈ p.reservations, x.endNat = r.start.toNat) ∧
      ((∃ b ∈ p.managed, b.endNat = r.endNat) ∨
        ∃ x ∈ p.reservations, x.start.toNat = r.endNat)

/-- **`find_available` gives the lowest available span** (FDT-R05). A span
that `Pi5BootMemory::find_available` gives is available, fits the request in
a RAM range, no RAM range before it in tree order has a span that fits, and
no span that fits in its range starts lower; none means that no RAM range has
a span that fits (lines 606 to 611 of the contract). -/
def FindAvailableLowest : Prop :=
  ∀ (m : Pi5BootMemory) (size alignment minimum limit : UInt64),
    (∀ s, m.findAvailable size alignment minimum limit = .ok (some s) →
      m.isAvailable s = .ok true ∧
      ∃ i r, m.ram[i]? = some r ∧ m.Fits size alignment minimum limit r s ∧
        (∀ r' ∈ m.ram.take i, ∀ s', ¬ m.Fits size alignment minimum limit r' s') ∧
        ∀ s', m.Fits size alignment minimum limit r s' → s.start.toNat ≤ s'.start.toNat) ∧
    (m.findAvailable size alignment minimum limit = .ok none →
      ∀ r ∈ m.ram, ∀ s, ¬ m.Fits size alignment minimum limit r s)

/-- **Values that no rule reads do not reach the results** (FDT-R10, FDT-R04).
Two trees that differ only in values that the discoveries leave unread
(`unreadByDiscoveries`): every value of `/chosen` but its `device_type` and,
when that is `memory`, its `status`, such as the seeds that QEMU virt writes
into `/chosen` at every boot; and every value of a dynamic reservation but
its `status` and flags, such as its `size`, whatever its cells. They give
the same memory map, Pi 5 boot memory and CPU topology, and so the same boot
memory map. -/
def UnreadValuesIgnored : Prop :=
  ∀ t t' : Fdt, t.WellFormed → t.SameExceptValues (unreadByDiscoveries t) t' →
    t.discoverMemory = t'.discoverMemory ∧
    (∀ (dtbAddress : UInt64) (image : Span),
      t.discoverPi5BootMemory dtbAddress image = t'.discoverPi5BootMemory dtbAddress image) ∧
    ∀ profile : CpuProfile, t.discoverCpus profile = t'.discoverCpus profile

/-- **The affinity of a CPU gives back its logical ID** (FDT-R08). For every
CPU of a supported topology, `CpuProfile::logical_id` of its affinity with
any flag bits of `MPIDR_EL1` is its index; and flag bits outside the
affinity fields never change a logical ID (lines 642 to 646 of the
contract). -/
def AffinityRoundTrip : Prop :=
  (∀ (t : CpuTopology) (i flags : UInt64), t.Supported → i < t.count →
    flags &&& AFFINITY_MASK = 0 →
    ∃ a, t.affinity i = some a ∧ t.profile.logicalId (a ||| flags) = some i) ∧
  ∀ (p : CpuProfile) (mpidr flags : UInt64), flags &&& AFFINITY_MASK = 0 →
    p.logicalId (mpidr ||| flags) = p.logicalId mpidr

/-- **A translation goes through the one window that holds the request**
(FDT-R09). For a well-formed map and a nonempty request within the width of
its side, `to_parent` (`reverse` false) and `to_child` (`reverse` true): an
absent map translates nothing; an empty one gives the request itself, and
does so within the width of the other side; and a map of windows succeeds
exactly when one window, and no other, shares an address with the request
and that window holds all of it, and then gives the span of the request's
size at the request's offset in that window (lines 673 to 680 of the
contract). Two windows that hold the request, or one that holds part of it,
make it fail. -/
def TranslationThroughOneWindow : Prop :=
  ∀ (m : AddressMap) (s : Span) (reverse : Bool), m.WellFormed → s.size ≠ 0 →
    s.WithinWidth (if reverse then m.parentCells else m.childCells) →
    (m.windows = none → ∀ r, m.translate s reverse ≠ .ok r) ∧
    (m.windows = some [] →
      (∀ r, m.translate s reverse = .ok r → r = s) ∧
      (s.WithinWidth (if reverse then m.childCells else m.parentCells) →
        m.translate s reverse = .ok s)) ∧
    ∀ w₀ ws₀, m.windows = some (w₀ :: ws₀) →
      let touching := (w₀ :: ws₀).filter fun w => (w.source reverse).overlaps s
      ((∃ r, m.translate s reverse = .ok r) ↔
        ∃ w, touching = [w] ∧ (w.source reverse).holds s = true) ∧
      ∀ r w, m.translate s reverse = .ok r → touching = [w] →
        r.size = s.size ∧
          r.start.toNat =
            (w.target reverse).start.toNat + (s.start.toNat - (w.source reverse).start.toNat)

end Krepi.SpecProperties.Fdt
