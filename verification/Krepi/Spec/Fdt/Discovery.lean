module

public import Krepi.Spec.Fdt.Translate

/-!
# Device tree: memory discovery

`Fdt::discover_memory` of the contract's `Memory discovery`: the RAM ranges of
the enabled memory nodes below the root, the reserved regions of the
reservation map and of the static children of `/reserved-memory`, and the
number of dynamic reservations, with step 4 of the error order of the parse
and the entries on a tree in `Rejection and error priority`.

The discovery reads a tree that the parse built, through the node access and
`Node::reg`; it reads no byte of the tree again. It checks its rules in the
order of step 4 and builds its result while it checks, so that the first
broken rule decides the error and a failure returns that error and nothing
else. A `MemoryMap` holds only what passed the checks.

The loops are structural recursion on lists that the contract bounds: the
entries of the reservation map, the nodes of the tree, which the discovery
walks twice, and the spans of one `reg`.
-/

@[expose] public section

namespace Krepi.Spec.Fdt

/-! ## Values -/

/-- `ReservedRegion`: a span that the kernel does not hand out, with the flags
`no-map` and `reusable`. -/
structure ReservedRegion where
  span : Span
  noMap : Bool
  reusable : Bool
  deriving DecidableEq, Repr, Inhabited

/-- `MemoryMap`, the result of `Fdt::discover_memory`: the RAM ranges in tree
order (`MemoryMap::ram`), the reserved regions, those of the reservation map
first and then those of `/reserved-memory` in tree order
(`MemoryMap::reserved`), and the number of dynamic reservations
(`MemoryMap::dynamic`). -/
structure MemoryMap where
  ram : List Span
  reserved : List ReservedRegion
  dynamic : UInt64
  deriving DecidableEq, Repr, Inhabited

/-- Whether two spans touch: both are nonempty and they share an address,
compared at their exact ends. For the nonempty spans that the entries compare,
this is `Span.overlaps`. -/
def Span.touches (a b : Span) : Bool :=
  a.size != 0 && b.size != 0 && a.overlaps b

/-- Whether one span of `ranges` holds `s`, as address sets of the exact ends:
the contract's "inside one RAM range". -/
def inOneRange (ranges : List Span) (s : Span) : Bool :=
  ranges.any (·.holds s)

/-! ## Node bindings -/

/-- A flag of a node: false when absent, true for an empty value, and
`BadProperty` for a value. -/
def Node.flag (n : Node) (name : String) : Except Error Bool :=
  match n.property name with
  | none => .ok false
  | some value => if value.size = 0 then .ok true else .error .badProperty

/-- A memory name: `memory`, or a name that starts with `memory@`. -/
def isMemoryName (name : String) : Bool :=
  name == "memory" || name.startsWith "memory@"

/-! ## RAM -/

/-- One RAM range added after the ranges `ram`: of size 0, `EmptyRegion`;
sharing an address with an earlier range, `Overlap`; beyond
`MAX_MEMORY_REGIONS` ranges, `LimitExceeded`. -/
def addRam (ram : List Span) (s : Span) : Except Error (List Span) :=
  if s.size = 0 then .error .emptyRegion
  else if ram.any (·.touches s) then .error .overlap
  else if MAX_MEMORY_REGIONS.toNat < ram.length + 1 then .error .limitExceeded
  else .ok (ram ++ [s])

/-- One child of the root, after the RAM ranges `ram` of the children before
it. Its `device_type`, with the errors of `Node::string_property`; a child
that has neither a memory name nor the `device_type` `memory` is no memory
node and adds nothing. A memory node: its `status`, and a disabled one is
skipped before its binding is checked; then an enabled one without both the
memory name and the `device_type` `memory`, `BadProperty`; its `reg`, in the
cells of the root, with the errors of `Node::reg`; then each of its ranges in
order (`addRam`). -/
def ramOfChild (ram : List Span) (n : Node) : Except Error (List Span) := do
  let deviceType ← n.stringProperty "device_type"
  let byName := isMemoryName n.name
  let byType := deviceType == some "memory"
  if !(byName || byType) then return ram
  if !(← n.enabled) then return ram
  if !(byName && byType) then throw .badProperty
  let reg ← n.reg
  reg.entries.foldlM addRam ram

/-! ## Reserved regions -/

/-- One reserved region added after the regions `reserved`: beyond
`MAX_RESERVED_REGIONS` regions, `LimitExceeded`. -/
def pushReserved (reserved : List ReservedRegion) (r : ReservedRegion) :
    Except Error (List ReservedRegion) :=
  if MAX_RESERVED_REGIONS.toNat < reserved.length + 1 then .error .limitExceeded
  else .ok (reserved ++ [r])

/-- One span of the `reg` of a child of `/reserved-memory`, with the flags of
the child: of size 0, `EmptyRegion`; then the capacity (`pushReserved`). -/
def addReservedSpan (noMap reusable : Bool) (reserved : List ReservedRegion) (s : Span) :
    Except Error (List ReservedRegion) :=
  if s.size = 0 then .error .emptyRegion
  else pushReserved reserved ⟨s, noMap, reusable⟩

/-- The binding of `/reserved-memory`: its own `#address-cells` and
`#size-cells`, present and equal to those of the root, and an empty `ranges`;
any other, `BadProperty`. Every rule of the binding fails with the same error,
so their order decides nothing. -/
def reservedMemoryBinding (parent root : Node) : Except Error Unit := do
  if (parent.property "#address-cells").isNone || (parent.property "#size-cells").isNone then
    throw .badProperty
  if (← parent.addressCells) ≠ (← root.addressCells) then throw .badProperty
  if (← parent.sizeCells) ≠ (← root.sizeCells) then throw .badProperty
  match parent.property "ranges" with
  | some value => if value.size ≠ 0 then throw .badProperty
  | none => throw .badProperty

/-- One child of an enabled `/reserved-memory`, after the reserved regions and
the number of dynamic reservations of the children before it. Its `status`,
and a disabled child is skipped; its flags `no-map` and `reusable`, each
without a value, and not both, `BadProperty`; neither `reg` nor `size`,
`MissingProperty`; `size` without `reg`, a dynamic reservation, which is
counted and whose `size` is not read; otherwise its `reg`, in the cells of
`/reserved-memory`, with the errors of `Node::reg`, and each of its spans in
order (`addReservedSpan`). -/
def reservedOfChild (acc : List ReservedRegion × Nat) (n : Node) :
    Except Error (List ReservedRegion × Nat) := do
  if !(← n.enabled) then return acc
  let noMap ← n.flag "no-map"
  let reusable ← n.flag "reusable"
  if noMap && reusable then throw .badProperty
  match n.property "reg", n.property "size" with
  | none, none => throw .missingProperty
  | none, some _ => return (acc.1, acc.2 + 1)
  | some _, _ =>
    let reg ← n.reg
    let reserved ← reg.entries.foldlM (addReservedSpan noMap reusable) acc.1
    return (reserved, acc.2)

/-- The reserved regions of `/reserved-memory` after those of the reservation
map, `mapped`, with the number of dynamic reservations: none when the tree has
no `/reserved-memory`; otherwise its binding, then its `status`, and a
disabled one holds no reservation; then its children in tree order. -/
def Fdt.reservedMemory (t : Fdt) (root : Node) (mapped : List ReservedRegion) :
    Except Error (List ReservedRegion × Nat) := do
  match ← t.findNode "/reserved-memory" with
  | none => pure (mapped, 0)
  | some parent =>
    reservedMemoryBinding parent root
    if !(← parent.enabled) then return (mapped, 0)
    (t.nodes.filter (·.isChildOf parent)).foldlM reservedOfChild (mapped, 0)

/-! ## The discovery -/

/-- `Fdt::discover_memory`: the memory map of the tree, or the error of the
first broken rule of step 4 of the error order. The entries of the
reservation map in order, as reserved regions with `no-map` set and
`reusable` clear, `LimitExceeded` beyond `MAX_RESERVED_REGIONS`; the root, and
a tree without one, which the parse never builds, `BadTree`; the children of
the root in tree order (`ramOfChild`); no RAM range, `NoMemory`; the lookup
of `/reserved-memory` with its binding, its `status` and its children
(`Fdt.reservedMemory`). The number of dynamic reservations is at most the
number of nodes, at most `MAX_TOKENS` in a tree that the parse accepted, so it
fits its width. -/
def Fdt.discoverMemory (t : Fdt) : Except Error MemoryMap := do
  let mapped ← t.reservations.foldlM (fun rs s => pushReserved rs ⟨s, true, false⟩) []
  let some root ← t.findNode "/" | throw .badTree
  let ram ← (t.nodes.filter (·.isChildOf root)).foldlM ramOfChild []
  if ram.isEmpty then throw .noMemory
  let (reserved, dynamic) ← t.reservedMemory root mapped
  pure { ram, reserved, dynamic := UInt64.ofNat dynamic }

end Krepi.Spec.Fdt
