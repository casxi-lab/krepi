module

public import Krepi.Spec.Fdt.Parse

/-!
# Device tree: the node access

The entries of `Format and bounds` that read a tree that the parse accepted:
the nodes in the order of the structure block, the lookup of an absolute
path, and of a node its name, parent, properties, string properties, status
and cell counts. None of them reads the bytes again: they read the tree that
the parse built, so none fails with an error of the format.

The error orders of these entries follow from the contract's rules for each,
`Fdt::find_node` in step 8 of the error order of the entries on a tree, and,
where an entry reads a property through `Node::string_property`, the errors
of that entry: a value without a NUL or whose string is not UTF-8,
`BadString`, before a byte after the NUL, `BadProperty`.
-/

@[expose] public section

namespace Krepi.Spec.Fdt

/-! ## Nodes -/

/-- `Node`: a node of a tree, by its index in the order of the structure
block. -/
structure Node where
  fdt : Fdt
  index : Fin fdt.records.size

/-- The record of a node. -/
def Node.record (n : Node) : NodeRecord := n.fdt.records[n.index]

/-- `Fdt::nodes`: every node of the tree, in the order of the structure block.
-/
def Fdt.nodes (t : Fdt) : List Node :=
  (List.finRange t.records.size).map fun i => ⟨t, i⟩

/-- The root: the first node of the structure block. -/
def Fdt.root (t : Fdt) : Option Node :=
  if h : 0 < t.records.size then some ⟨t, ⟨0, h⟩⟩ else none

/-- `Node::name`: the name of the node, without its NUL; empty for the root.
-/
def Node.name (n : Node) : String := n.record.name

/-- `Node::parent`: the parent of the node, none for the root. -/
def Node.parent (n : Node) : Option Node :=
  match n.record.parent with
  | none => none
  | some p => if h : p < n.fdt.records.size then some ⟨n.fdt, ⟨p, h⟩⟩ else none

/-- Whether `c` is a child of `p`. -/
def Node.isChildOf (c p : Node) : Bool := c.record.parent == some p.index.val

/-! ## Paths -/

/-- Whether a path holds `//`. -/
def hasDoubleSlash : List Char → Bool
  | '/' :: '/' :: _ => true
  | _ :: rest => hasDoubleSlash rest
  | [] => false

/-- The form of a path that `Fdt::find_node` takes: it starts with `/`, ends
in `/` only when it is the root, and holds no `//`. -/
def pathValid (p : List Char) : Bool :=
  p.head? == some '/' && !(1 < p.length && p.getLast? == some '/') && !hasDoubleSlash p

/-- The components of a path without its first `/`, split at each `/`. -/
def splitSlash : List Char → List (List Char)
  | [] => [[]]
  | '/' :: rest => [] :: splitSlash rest
  | c :: rest =>
    match splitSlash rest with
    | [] => [[c]]
    | w :: ws => (c :: w) :: ws

/-- The node that the components `cs` name below `current`: for each
component, the children of the node so far with that name, of which two
fail with `AmbiguousMapping` and none give none. -/
def Fdt.descend (t : Fdt) : List (List Char) → Option Node → Except Error (Option Node)
  | [], current => .ok current
  | _ :: _, none => .ok none
  | c :: rest, some p =>
    match t.nodes.filter (fun n => n.isChildOf p && n.name.toList == c) with
    | [] => t.descend rest none
    | [n] => t.descend rest (some n)
    | _ :: _ :: _ => .error .ambiguousMapping

/-- `Fdt::find_node(path)`: the node of an absolute path with exact unit
addresses, `/` for the root. A path that does not start with `/`, ends in `/`
other than the root or holds `//`, `BadPath`; then each component in order,
a component that matches two sibling nodes, `AmbiguousMapping`; a path that
matches nothing gives none. -/
def Fdt.findNode (t : Fdt) (path : String) : Except Error (Option Node) :=
  let p := path.toList
  if !pathValid p then .error .badPath
  else if p == ['/'] then .ok t.root
  else t.descend (splitSlash p.tail) t.root

/-! ## Properties -/

/-- `Node::property(name)`: the value of the property of the node with that
name, or none. -/
def Node.property (n : Node) (name : String) : Option ByteArray :=
  (n.record.properties.find? (·.1 == name)).map (·.2)

/-- `Node::string_property(name)`: the string of a value that holds one
NUL-terminated UTF-8 string, or none without the property. A value without a
NUL, or whose bytes before the NUL are not UTF-8, `BadString`; then a byte
after the NUL, `BadProperty`. -/
def Node.stringProperty (n : Node) (name : String) : Except Error (Option String) :=
  match n.property name with
  | none => .ok none
  | some value => do
    let (s, e) ← cString value 0
    if e ≠ value.size then throw .badProperty
    pure (some s)

/-- `Node::enabled`: true when `status` is absent, `okay` or `ok`, false for
any other string, with the errors of `Node::string_property`. -/
def Node.enabled (n : Node) : Except Error Bool := do
  match ← n.stringProperty "status" with
  | none => pure true
  | some s => pure (s == "okay" || s == "ok")

/-- A cell count of the node's own: the default when the property is absent,
the value of 4 bytes, or `BadProperty` for a value of another length. -/
def Node.cellCount (n : Node) (name : String) (default : UInt32) : Except Error UInt32 :=
  match n.property name with
  | none => .ok default
  | some value => if value.size = 4 then u32At value 0 else .error .badProperty

/-- `Node::address_cells`: the node's own `#address-cells`, 2 when absent. -/
def Node.addressCells (n : Node) : Except Error UInt32 := n.cellCount "#address-cells" 2

/-- `Node::size_cells`: the node's own `#size-cells`, 1 when absent. -/
def Node.sizeCells (n : Node) : Except Error UInt32 := n.cellCount "#size-cells" 1

end Krepi.Spec.Fdt
