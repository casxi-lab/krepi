module

public import Krepi.Spec.Fdt.Boot

/-!
# Device tree: invariants

The invariants of the values of the `fdt` component and of the boot state
that holds its shared results, and the statements that the entries establish
and the transactions preserve them. The component writes no state of its
own: a tree, a memory map, a Pi 5 boot memory, a CPU topology and a boot
memory map are values that never change once an entry returned them, so an
invariant of such a value is established by the entries that build it and
read by the entries and the components that take it. Only the boot state
changes, by its three transactions.

The invariants are of two kinds:

- **Structural**, each quantified over a whole table of a value: the nodes
  and the reservation entries of a tree (`Fdt.WellFormed`), the entries of a
  `Reg` (`Reg.WellFormed`), the windows of an address map
  (`AddressMap.WellFormed`), the RAM ranges and the reserved regions of a
  memory map (`MemoryMap.WellFormed`), the banks, the managed banks, the boot
  storage and the firmware reservations of a boot memory map
  (`MemoryPlan.WellFormed`), and the published boot memory map of the boot
  state (`BootState.WellFormed`).
- **Functional**, what a value means beyond the shape of its tables: the
  spans of a Pi 5 boot memory against its memory map
  (`Pi5BootMemory.Consistent`), the CPU counts of a topology
  (`CpuTopology.Supported`), the published topology as the result of
  `Fdt::discover_cpus` on the hand-over bytes (`BootState.FromHandOver`), and
  the start of the secondary CPUs after both publications
  (`BootState.StartOrder`).

Each invariant is a proposition, and each has a computable check,
`check...`, whose agreement with it is a statement below. The statements
are propositions that theorems below `Krepi.Proofs.Fdt` prove; they are of
four groups: the checks; the establishment of the functional invariants by
the entries that build their values and by the cold entry; the preservation
of each functional invariant of the boot state by each transaction; and one
lemma for each operation that it preserves well-formedness, apart from the
functional theorems. The definitions extend the namespace of the
specification, so that they read as fields of its values.
-/

@[expose] public section

namespace Krepi.Spec.Fdt

/-! ## Helpers -/

/-- Whether `r a b` holds for every entry `a` of a list and every entry `b`
after it: the check of `List.Pairwise r`. -/
def allPairs {α : Type} (r : α → α → Bool) : List α → Bool
  | [] => true
  | a :: rest => rest.all (r a) && allPairs r rest

/-- The sum of the sizes of spans, exact. -/
def spansBytes (spans : List Span) : Nat :=
  spans.foldl (fun sum s => sum + s.size.toNat) 0

/-- A span within the width of an address of `cells` cells: its end within
64 bits and, with one cell, the span within the first 4 GiB, as `checkWidth`
accepts it. -/
def Span.WithinWidth (s : Span) (cells : UInt32) : Prop :=
  s.Valid ∧ (cells = 1 → s.start.toNat < 2 ^ 32 ∧ s.endNat ≤ 2 ^ 32)

/-- The check of `Span.WithinWidth`. -/
def Span.withinWidth (s : Span) (cells : UInt32) : Bool :=
  decide s.Valid && (cells != 1 || (decide (s.start.toNat < 2 ^ 32) && decide (s.endNat ≤ 2 ^ 32)))

/-- A span whose start and end lie on 4 KiB pages. -/
def Span.OnPages (s : Span) : Prop :=
  s.start.toNat % MemoryPlan.PAGE_SIZE = 0 ∧ s.endNat % MemoryPlan.PAGE_SIZE = 0

/-- The check of `Span.OnPages`. -/
def Span.onPages (s : Span) : Bool :=
  s.start.toNat % MemoryPlan.PAGE_SIZE == 0 && s.endNat % MemoryPlan.PAGE_SIZE == 0

/-- A span of the contract that is not empty. -/
def Span.Nonempty (s : Span) : Prop := s.size ≠ 0 ∧ s.Valid

/-- The check of `Span.Nonempty`. -/
def Span.nonempty (s : Span) : Bool := s.size != 0 && decide s.Valid

/-! ## The tree -/

/-- The number of ancestors of the node of index `i` of a tree, following at
most `fuel` parents. -/
def Fdt.depthFrom (t : Fdt) : (fuel i : Nat) → Nat
  | 0, _ => 0
  | fuel + 1, i =>
    match (t.records[i]?).bind (·.parent) with
    | some p => t.depthFrom fuel p + 1
    | none => 0

/-- The depth of the node of index `i`: the number of nodes above it on its
path from the root. Where every parent precedes its child, `i + 1` parents
are more than the path holds, so the fuel does not cut it short. -/
def Fdt.depth (t : Fdt) (i : Nat) : Nat := t.depthFrom (i + 1) i

/-- The rules of the node of index `i` of a tree, whose record is `r`
(format and bounds, lines 164 to 182 of the contract): the root, first,
has no parent and the empty name; every other node has a parent before it
and a name that is not empty; the characters of the name; the depth; at most
`MAX_PROPERTIES` properties, no two of one name; and each property name of 1
to `MAX_PROPERTY_NAME` bytes of its characters. -/
def Fdt.NodeWellFormed (t : Fdt) (i : Nat) (r : NodeRecord) : Prop :=
  (if i = 0 then r.parent = none ∧ r.name = ""
   else (∃ p, r.parent = some p ∧ p < i) ∧ r.name ≠ "") ∧
  r.name.toList.all isNodeNameChar = true ∧
  t.depth i < MAX_DEPTH.toNat ∧
  r.properties.length ≤ MAX_PROPERTIES.toNat ∧
  (r.properties.map (·.1)).Pairwise (· ≠ ·) ∧
  ∀ q ∈ r.properties,
    q.1 ≠ "" ∧ q.1.utf8ByteSize ≤ MAX_PROPERTY_NAME.toNat ∧
      q.1.toList.all isPropertyNameChar = true

/-- **Structural invariant of a tree.** The header's `totalsize` from 40 to
`MAX_BLOB_SIZE`; at most `MAX_RESERVATIONS` reservation entries, each
nonempty, within 64 bits and disjoint from the others; and at least one and
at most `MAX_TOKENS` nodes, each of which keeps the rules of its node
(`Fdt.NodeWellFormed`). These are the rules of format and bounds, lines 146
to 182 of the contract, that the parse checks before it returns a tree. -/
def Fdt.WellFormed (t : Fdt) : Prop :=
  HEADER_SIZE ≤ t.totalSize.toNat ∧ t.totalSize ≤ MAX_BLOB_SIZE ∧
  t.reservations.length ≤ MAX_RESERVATIONS.toNat ∧
  (∀ s ∈ t.reservations, s.Nonempty) ∧
  t.reservations.Pairwise (fun a b => a.overlaps b = false) ∧
  0 < t.records.size ∧ t.records.size ≤ MAX_TOKENS.toNat ∧
  ∀ i (h : i < t.records.size), t.NodeWellFormed i t.records[i]

/-- The check of `Fdt.NodeWellFormed`. -/
def Fdt.checkNode (t : Fdt) (i : Nat) (r : NodeRecord) : Bool :=
  (if i = 0 then r.parent == none && r.name == ""
   else (match r.parent with | some p => decide (p < i) | none => false) && r.name != "") &&
  r.name.toList.all isNodeNameChar &&
  decide (t.depth i < MAX_DEPTH.toNat) &&
  decide (r.properties.length ≤ MAX_PROPERTIES.toNat) &&
  allPairs (· != ·) (r.properties.map (·.1)) &&
  r.properties.all fun q =>
    q.1 != "" && decide (q.1.utf8ByteSize ≤ MAX_PROPERTY_NAME.toNat) &&
      q.1.toList.all isPropertyNameChar

/-- The check of `Fdt.WellFormed`. -/
def Fdt.checkWellFormed (t : Fdt) : Bool :=
  decide (HEADER_SIZE ≤ t.totalSize.toNat) && decide (t.totalSize ≤ MAX_BLOB_SIZE) &&
  decide (t.reservations.length ≤ MAX_RESERVATIONS.toNat) &&
  t.reservations.all Span.nonempty &&
  allPairs (fun a b => !a.overlaps b) t.reservations &&
  decide (0 < t.records.size) && decide (t.records.size ≤ MAX_TOKENS.toNat) &&
  (List.range t.records.size).all fun i =>
    match t.records[i]? with
    | some r => t.checkNode i r
    | none => false

/-! ## Regions and address maps -/

/-- **Structural invariant of a `Reg`**, read in `cells` address cells: at
least one entry, and each within the width of its address. `Reg::new`
checks every entry before it gives one, lines 660 to 664 of the contract,
and the entries of a `Reg` read only what it checked, lines 707 to 710. -/
def Reg.WellFormed (r : Reg) (cells : UInt32) : Prop :=
  r.entries ≠ [] ∧ ∀ s ∈ r.entries, s.WithinWidth cells

/-- The check of `Reg.WellFormed`. -/
def Reg.checkWellFormed (r : Reg) (cells : UInt32) : Bool :=
  !r.entries.isEmpty && r.entries.all (·.withinWidth cells)

/-- A window of a map whose sides have `childCells` and `parentCells` address
cells: nonempty, of one size on both sides, and each side within its width.
-/
def Window.WellFormed (w : Window) (childCells parentCells : UInt32) : Prop :=
  w.child.size ≠ 0 ∧ w.child.size = w.parent.size ∧
    w.child.WithinWidth childCells ∧ w.parent.WithinWidth parentCells

/-- **Structural invariant of an address map.** Child and parent address
cells of 1 or 2 and at most 2 size cells, and every window well-formed: the
rules that `AddressMap::new` checks at construction, lines 666 to 672 of the
contract. -/
def AddressMap.WellFormed (m : AddressMap) : Prop :=
  (m.childCells = 1 ∨ m.childCells = 2) ∧ (m.parentCells = 1 ∨ m.parentCells = 2) ∧
  m.sizeCells.toNat ≤ 2 ∧
  ∀ ws, m.windows = some ws → ∀ w ∈ ws, w.WellFormed m.childCells m.parentCells

/-- The check of `AddressMap.WellFormed`. -/
def AddressMap.checkWellFormed (m : AddressMap) : Bool :=
  (m.childCells == 1 || m.childCells == 2) && (m.parentCells == 1 || m.parentCells == 2) &&
  decide (m.sizeCells.toNat ≤ 2) &&
  (m.windows.getD []).all fun w =>
    w.child.size != 0 && w.child.size == w.parent.size &&
      w.child.withinWidth m.childCells && w.parent.withinWidth m.parentCells

/-! ## The memory map -/

/-- **Structural invariant of a memory map.** 1 to `MAX_MEMORY_REGIONS` RAM
ranges, each nonempty and within 64 bits, no two sharing an address; at most
`MAX_RESERVED_REGIONS` reserved regions, each nonempty and within 64 bits,
none with both `no-map` and `reusable`; and a number of dynamic reservations
that is at most the number of nodes a tree may have, so that it fits its
width. The rules of memory discovery, lines 446 to 479 of the contract. -/
def MemoryMap.WellFormed (m : MemoryMap) : Prop :=
  m.ram ≠ [] ∧ m.ram.length ≤ MAX_MEMORY_REGIONS.toNat ∧
  (∀ s ∈ m.ram, s.Nonempty) ∧ m.ram.Pairwise (fun a b => a.touches b = false) ∧
  m.reserved.length ≤ MAX_RESERVED_REGIONS.toNat ∧
  (∀ r ∈ m.reserved, r.span.Nonempty ∧ (r.noMap && r.reusable) = false) ∧
  m.dynamic.toNat ≤ MAX_TOKENS.toNat

/-- The check of `MemoryMap.WellFormed`. -/
def MemoryMap.checkWellFormed (m : MemoryMap) : Bool :=
  !m.ram.isEmpty && decide (m.ram.length ≤ MAX_MEMORY_REGIONS.toNat) &&
  m.ram.all Span.nonempty && allPairs (fun a b => !a.touches b) m.ram &&
  decide (m.reserved.length ≤ MAX_RESERVED_REGIONS.toNat) &&
  m.reserved.all (fun r => r.span.nonempty && !(r.noMap && r.reusable)) &&
  decide (m.dynamic.toNat ≤ MAX_TOKENS.toNat)

/-! ## The Pi 5 boot memory -/

/-- **Functional invariant of a Pi 5 boot memory.** The span of the tree
within 64 bits, at a multiple of 8 and at most `PI5_MAX_BLOB_SIZE` long; the
image nonempty, within 64 bits and sharing no address with the tree; the
tree and the image each inside one RAM range; and `ram_bytes` the exact sum
of the RAM ranges. The hand-over checks of lines 497 to 507 of the
contract. -/
def Pi5BootMemory.Consistent (m : Pi5BootMemory) : Prop :=
  m.dtb.Valid ∧ m.dtb.start.toNat % 8 = 0 ∧ m.dtb.size ≤ PI5_MAX_BLOB_SIZE ∧
  m.image.Nonempty ∧ m.image.touches m.dtb = false ∧
  inOneRange m.ram m.dtb = true ∧ inOneRange m.ram m.image = true ∧
  m.ramBytes.toNat = spansBytes m.ram

/-- The check of `Pi5BootMemory.Consistent`. -/
def Pi5BootMemory.checkConsistent (m : Pi5BootMemory) : Bool :=
  decide m.dtb.Valid && m.dtb.start.toNat % 8 == 0 && decide (m.dtb.size ≤ PI5_MAX_BLOB_SIZE) &&
  m.image.nonempty && !m.image.touches m.dtb &&
  inOneRange m.ram m.dtb && inOneRange m.ram m.image &&
  m.ramBytes.toNat == spansBytes m.ram

/-! ## The CPU topology -/

/-- **Functional invariant of a CPU topology.** 1, 2 or 4 CPUs, and 4 on the
Pi 5: the counts of lines 635 and 636 of the contract, for which the timer
flags of `validate_qemu_timers` are exact. -/
def CpuTopology.Supported (t : CpuTopology) : Prop :=
  (t.count = 1 ∨ t.count = 2 ∨ t.count = 4) ∧ (t.profile = .pi5 → t.count = 4)

/-- The check of `CpuTopology.Supported`. -/
def CpuTopology.checkSupported (t : CpuTopology) : Bool :=
  (t.count == 1 || t.count == 2 || t.count == 4) && (t.profile != .pi5 || t.count == 4)

/-! ## The boot memory map -/

/-- **Structural invariant of a boot memory map.** 1 to 32 banks, each
nonempty and within 64 bits, sorted by their start and disjoint, adjacent
ones kept apart, of at most 16 GiB together; at least one managed bank, each
nonempty, on pages and inside one bank, in address order; 1 to 4 spans of
boot storage, each nonempty, on pages and inside one bank, no two sharing a
page; and at most 128 firmware reservations, each nonempty and on pages, none
sharing a page with boot storage. The rules of the boot memory map, lines
565 to 582, 598 and 599 of the contract. -/
def MemoryPlan.WellFormed (p : MemoryPlan) : Prop :=
  p.ram ≠ [] ∧ p.ram.length ≤ MemoryPlan.MAX_BANKS ∧
  (∀ b ∈ p.ram, b.Nonempty) ∧ p.ram.Pairwise (fun a b => a.endNat ≤ b.start.toNat) ∧
  spansBytes p.ram ≤ MemoryPlan.MAX_RAM_BYTES ∧
  p.managed ≠ [] ∧
  (∀ s ∈ p.managed, s.Nonempty ∧ s.OnPages ∧ inOneRange p.ram s = true) ∧
  p.managed.Pairwise (fun a b => a.endNat ≤ b.start.toNat) ∧
  p.boot ≠ [] ∧ p.boot.length ≤ MemoryPlan.MAX_BOOT_SPANS ∧
  (∀ s ∈ p.boot, s.Nonempty ∧ s.OnPages ∧ inOneRange p.ram s = true) ∧
  p.boot.Pairwise (fun a b => a.touches b = false) ∧
  p.firmware.length ≤ MemoryPlan.MAX_FIRMWARE ∧
  ∀ f ∈ p.firmware, f.Nonempty ∧ f.OnPages ∧ ∀ s ∈ p.boot, s.touches f = false

/-- The check of `MemoryPlan.WellFormed`. -/
def MemoryPlan.checkWellFormed (p : MemoryPlan) : Bool :=
  !p.ram.isEmpty && decide (p.ram.length ≤ MemoryPlan.MAX_BANKS) &&
  p.ram.all Span.nonempty && allPairs (fun a b => decide (a.endNat ≤ b.start.toNat)) p.ram &&
  decide (spansBytes p.ram ≤ MemoryPlan.MAX_RAM_BYTES) &&
  !p.managed.isEmpty &&
  p.managed.all (fun s => s.nonempty && s.onPages && inOneRange p.ram s) &&
  allPairs (fun a b => decide (a.endNat ≤ b.start.toNat)) p.managed &&
  !p.boot.isEmpty && decide (p.boot.length ≤ MemoryPlan.MAX_BOOT_SPANS) &&
  p.boot.all (fun s => s.nonempty && s.onPages && inOneRange p.ram s) &&
  allPairs (fun a b => !a.touches b) p.boot &&
  decide (p.firmware.length ≤ MemoryPlan.MAX_FIRMWARE) &&
  p.firmware.all fun f => f.nonempty && f.onPages && p.boot.all fun s => !s.touches f

/-- The usable ranges `rs` of a boot memory map well-formed as a table: each
nonempty, within 64 bits and on pages; in address order and disjoint; and at
most one for each managed bank and each reservation (Work bounds, lines 775
and 776 of the contract). -/
def MemoryPlan.UsableWellFormed (p : MemoryPlan) (rs : List Span) : Prop :=
  (∀ r ∈ rs, r.Nonempty ∧ r.OnPages) ∧ rs.Pairwise (fun a b => a.endNat ≤ b.start.toNat) ∧
  rs.length ≤ p.managed.length + p.reservations.length

/-! ## The boot state -/

/-- **Structural invariant of the boot state.** The published boot memory
map, if any, is well-formed: what every CPU reads once it is published,
line 827 of the contract. -/
def BootState.WellFormed (s : BootState) : Prop :=
  ∀ p, s.plan = some p → p.WellFormed

/-- The check of `BootState.WellFormed`. -/
def BootState.checkWellFormed (s : BootState) : Bool :=
  match s.plan with
  | some p => p.checkWellFormed
  | none => true

/-- **Functional invariant of the boot state: the topology of the hand-over.**
The published CPU topology, if any, is what `Fdt::discover_cpus` gives for
the tree of the hand-over bytes with one of the profiles: the topology is
built from the bytes that the firmware or the loader handed over, lines 825
and 828 of the contract. -/
def BootState.FromHandOver (s : BootState) : Prop :=
  ∀ t, s.topology = some t → ∃ profile, (s.tree.bind fun f => f.discoverCpus profile) = .ok t

/-- The check of `BootState.FromHandOver`, which tries the three profiles. -/
def BootState.checkFromHandOver (s : BootState) : Bool :=
  match s.topology with
  | none => true
  | some t =>
    [CpuProfile.qemuHvc, .qemuSmc, .pi5].any fun profile =>
      match s.tree.bind fun f => f.discoverCpus profile with
      | .ok found => found == t
      | .error _ => false

/-- **Functional invariant of the boot state: the order of the start.** Once
the secondary CPUs have started, the boot memory map and the CPU topology
are both published: each is published before the secondary CPUs start,
lines 827 to 832 of the contract. -/
def BootState.StartOrder (s : BootState) : Prop :=
  s.secondaries = true → s.plan.isSome = true ∧ s.topology.isSome = true

/-- The check of `BootState.StartOrder`. -/
def BootState.checkStartOrder (s : BootState) : Bool :=
  !s.secondaries || (s.plan.isSome && s.topology.isSome)

end Krepi.Spec.Fdt

namespace Krepi.SpecProperties.Fdt

open Krepi.Spec.Fdt

/-! ## The checks

Each check agrees with its invariant on every value, also one that no entry
builds. -/

/-- `Fdt.checkWellFormed` decides `Fdt.WellFormed`. -/
def CheckFdtWellFormed : Prop := ∀ t : Fdt, t.checkWellFormed = true ↔ t.WellFormed

/-- `Reg.checkWellFormed` decides `Reg.WellFormed`. -/
def CheckRegWellFormed : Prop :=
  ∀ (r : Reg) (cells : UInt32), r.checkWellFormed cells = true ↔ r.WellFormed cells

/-- `AddressMap.checkWellFormed` decides `AddressMap.WellFormed`. -/
def CheckAddressMapWellFormed : Prop :=
  ∀ m : AddressMap, m.checkWellFormed = true ↔ m.WellFormed

/-- `MemoryMap.checkWellFormed` decides `MemoryMap.WellFormed`. -/
def CheckMemoryMapWellFormed : Prop :=
  ∀ m : MemoryMap, m.checkWellFormed = true ↔ m.WellFormed

/-- `Pi5BootMemory.checkConsistent` decides `Pi5BootMemory.Consistent`. -/
def CheckPi5BootMemoryConsistent : Prop :=
  ∀ m : Pi5BootMemory, m.checkConsistent = true ↔ m.Consistent

/-- `CpuTopology.checkSupported` decides `CpuTopology.Supported`. -/
def CheckCpuTopologySupported : Prop :=
  ∀ t : CpuTopology, t.checkSupported = true ↔ t.Supported

/-- `MemoryPlan.checkWellFormed` decides `MemoryPlan.WellFormed`. -/
def CheckMemoryPlanWellFormed : Prop :=
  ∀ p : MemoryPlan, p.checkWellFormed = true ↔ p.WellFormed

/-- `BootState.checkWellFormed` decides `BootState.WellFormed`. -/
def CheckBootStateWellFormed : Prop :=
  ∀ s : BootState, s.checkWellFormed = true ↔ s.WellFormed

/-- `BootState.checkFromHandOver` decides `BootState.FromHandOver`. -/
def CheckBootStateFromHandOver : Prop :=
  ∀ s : BootState, s.checkFromHandOver = true ↔ s.FromHandOver

/-- `BootState.checkStartOrder` decides `BootState.StartOrder`. -/
def CheckBootStateStartOrder : Prop :=
  ∀ s : BootState, s.checkStartOrder = true ↔ s.StartOrder

/-! ## Establishment

The functional invariants hold of every value that their entries return,
and the boot state of the cold entry satisfies the three invariants of the
boot state. The structural invariants that the entries establish are the
well-formedness lemmas of these entries, in the last group. -/

/-- The Pi 5 boot memory of `Fdt::discover_pi5_boot_memory` is consistent. -/
def DiscoverPi5BootMemoryConsistent : Prop :=
  ∀ (t : Fdt) (dtbAddress : UInt64) (image : Span) (m : Pi5BootMemory),
    t.discoverPi5BootMemory dtbAddress image = .ok m → m.Consistent

/-- The CPU topology of `Fdt::discover_cpus` has a supported count. -/
def DiscoverCpusSupported : Prop :=
  ∀ (t : Fdt) (profile : CpuProfile) (topology : CpuTopology),
    t.discoverCpus profile = .ok topology → topology.Supported

/-- The boot state of the cold entry is well-formed. -/
def ColdEntryWellFormed : Prop :=
  ∀ (token : BootToken) (bytes : ByteArray), (BootState.coldEntry token bytes).WellFormed

/-- The boot state of the cold entry has the topology of its hand-over. -/
def ColdEntryFromHandOver : Prop :=
  ∀ (token : BootToken) (bytes : ByteArray), (BootState.coldEntry token bytes).FromHandOver

/-- The boot state of the cold entry keeps the order of the start. -/
def ColdEntryStartOrder : Prop :=
  ∀ (token : BootToken) (bytes : ByteArray), (BootState.coldEntry token bytes).StartOrder

/-! ## Preservation

Each transaction of the boot state preserves each of its functional
invariants. -/

/-- The publication of the boot memory map keeps the topology of the
hand-over. -/
def PublishPlanFromHandOver : Prop :=
  ∀ (token : BootToken) (s : BootState) (build : PlanBuild) (s' : BootState),
    s.FromHandOver → BootState.publishPlan token s build = some (.ok s') → s'.FromHandOver

/-- The publication of the boot memory map keeps the order of the start. -/
def PublishPlanStartOrder : Prop :=
  ∀ (token : BootToken) (s : BootState) (build : PlanBuild) (s' : BootState),
    s.StartOrder → BootState.publishPlan token s build = some (.ok s') → s'.StartOrder

/-- The publication of the CPU topology keeps the topology of the hand-over.
-/
def PublishTopologyFromHandOver : Prop :=
  ∀ (token : BootToken) (s : BootState) (profile : CpuProfile) (s' : BootState),
    s.FromHandOver → BootState.publishTopology token s profile = some (.ok s') → s'.FromHandOver

/-- The publication of the CPU topology keeps the order of the start. -/
def PublishTopologyStartOrder : Prop :=
  ∀ (token : BootToken) (s : BootState) (profile : CpuProfile) (s' : BootState),
    s.StartOrder → BootState.publishTopology token s profile = some (.ok s') → s'.StartOrder

/-- The start of the secondary CPUs keeps the topology of the hand-over. -/
def StartSecondariesFromHandOver : Prop :=
  ∀ (token : BootToken) (s s' : BootState),
    s.FromHandOver → BootState.startSecondaries token s = some s' → s'.FromHandOver

/-- The start of the secondary CPUs keeps the order of the start. -/
def StartSecondariesStartOrder : Prop :=
  ∀ (token : BootToken) (s s' : BootState),
    s.StartOrder → BootState.startSecondaries token s = some s' → s'.StartOrder

/-! ## Well-formedness

One lemma for each operation: on well-formed inputs, the value that it
returns is well-formed. The operations are the entries that build a value
with a structural invariant, the entries that derive a span or a table of
spans from such a value, and the transactions of the boot state. An entry
that builds its value from unchecked input, such as the parse, has no
hypothesis: its lemma is the establishment of the invariant of its value. -/

/-- `Span::new` gives a span of the contract. -/
def SpanNewWellFormed : Prop :=
  ∀ (start size : UInt64) (s : Span), Span.new start size = .ok s → s.Valid

/-- The tree of `Fdt::parse` is well-formed. -/
def ParseWellFormed : Prop :=
  ∀ (input : ByteArray) (t : Fdt), Fdt.parse input = .ok t → t.WellFormed

/-- The `Reg` of `Reg::new` is well-formed in its address cells. -/
def RegNewWellFormed : Prop :=
  ∀ (bytes : ByteArray) (addressCells sizeCells : UInt32) (r : Reg),
    Reg.new bytes addressCells sizeCells = .ok r → r.WellFormed addressCells

/-- The map of `AddressMap::new` is well-formed. -/
def AddressMapNewWellFormed : Prop :=
  ∀ (bytes : Option ByteArray) (childCells parentCells sizeCells : UInt32) (m : AddressMap),
    AddressMap.new bytes childCells parentCells sizeCells = .ok m → m.WellFormed

/-- The `Reg` of `Node::reg` is well-formed in the address cells of the
parent. -/
def NodeRegWellFormed : Prop :=
  ∀ (n parent : Node) (cells : UInt32) (r : Reg),
    n.parent = some parent → parent.addressCells = .ok cells → n.reg = .ok r → r.WellFormed cells

/-- The map of `Node::ranges` is well-formed. -/
def NodeRangesWellFormed : Prop :=
  ∀ (n : Node) (m : AddressMap), n.ranges = .ok m → m.WellFormed

/-- The map of `Node::dma_ranges` is well-formed. -/
def NodeDmaRangesWellFormed : Prop :=
  ∀ (n : Node) (m : AddressMap), n.dmaRanges = .ok m → m.WellFormed

/-- `AddressMap::to_parent` of a well-formed map gives a nonempty span of the
size of the request within the width of the parent's addresses. -/
def ToParentWellFormed : Prop :=
  ∀ (m : AddressMap) (s r : Span), m.WellFormed → m.toParent s = .ok r →
    r.size = s.size ∧ r.size ≠ 0 ∧ r.WithinWidth m.parentCells

/-- `AddressMap::to_child` of a well-formed map gives a nonempty span of the
size of the request within the width of the child's addresses. -/
def ToChildWellFormed : Prop :=
  ∀ (m : AddressMap) (s r : Span), m.WellFormed → m.toChild s = .ok r →
    r.size = s.size ∧ r.size ≠ 0 ∧ r.WithinWidth m.childCells

/-- `Node::translate_reg` gives a span within 64 bits of the size of the
request. -/
def TranslateRegWellFormed : Prop :=
  ∀ (n : Node) (s r : Span), n.translateReg s = .ok r → r.Valid ∧ r.size = s.size

/-- The memory map of `Fdt::discover_memory` on a well-formed tree is
well-formed. -/
def DiscoverMemoryWellFormed : Prop :=
  ∀ (t : Fdt) (m : MemoryMap), t.WellFormed → t.discoverMemory = .ok m → m.WellFormed

/-- The memory map of a Pi 5 boot memory of
`Fdt::discover_pi5_boot_memory` on a well-formed tree is well-formed. -/
def DiscoverPi5BootMemoryWellFormed : Prop :=
  ∀ (t : Fdt) (dtbAddress : UInt64) (image : Span) (m : Pi5BootMemory),
    t.WellFormed → t.discoverPi5BootMemory dtbAddress image = .ok m → m.memory.WellFormed

/-- `Pi5BootMemory::find_available` gives a nonempty span of the size asked
within 64 bits. -/
def FindAvailableWellFormed : Prop :=
  ∀ (m : Pi5BootMemory) (size alignment minimum limit : UInt64) (s : Span),
    m.findAvailable size alignment minimum limit = .ok (some s) → s.size = size ∧ s.Nonempty

/-- The boot memory map of `MemoryPlan::all_ram` is well-formed. -/
def AllRamWellFormed : Prop :=
  ∀ (ram boot : List Span) (firmware : List ReservedRegion) (p : MemoryPlan),
    MemoryPlan.allRam ram boot firmware = .ok p → p.WellFormed

/-- The boot memory map of `MemoryPlan::new` is well-formed. -/
def MemoryPlanNewWellFormed : Prop :=
  ∀ (window : Span) (ram boot : List Span) (firmware : List ReservedRegion) (p : MemoryPlan),
    MemoryPlan.new window ram boot firmware = .ok p → p.WellFormed

/-- The boot memory map of `MemoryPlan::from_pi5` is well-formed. -/
def FromPi5WellFormed : Prop :=
  ∀ (memory : Pi5BootMemory) (window : Span) (more : List Span) (p : MemoryPlan),
    MemoryPlan.fromPi5 memory window more = .ok p → p.WellFormed

/-- The usable ranges of a well-formed boot memory map are well-formed as a
table. -/
def AvailableRangesWellFormed : Prop :=
  ∀ p : MemoryPlan, p.WellFormed → p.UsableWellFormed p.availableRanges

/-- The publication of the boot memory map keeps the boot state well-formed.
-/
def PublishPlanWellFormed : Prop :=
  ∀ (token : BootToken) (s : BootState) (build : PlanBuild) (s' : BootState),
    s.WellFormed → BootState.publishPlan token s build = some (.ok s') → s'.WellFormed

/-- The publication of the CPU topology keeps the boot state well-formed. -/
def PublishTopologyWellFormed : Prop :=
  ∀ (token : BootToken) (s : BootState) (profile : CpuProfile) (s' : BootState),
    s.WellFormed → BootState.publishTopology token s profile = some (.ok s') → s'.WellFormed

/-- The start of the secondary CPUs keeps the boot state well-formed. -/
def StartSecondariesWellFormed : Prop :=
  ∀ (token : BootToken) (s s' : BootState),
    s.WellFormed → BootState.startSecondaries token s = some s' → s'.WellFormed

end Krepi.SpecProperties.Fdt
