module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.Fdt.PathLemmas

/-!
# Device tree: lemmas about the values that the discoveries read

Lemmas for `UnreadValuesIgnored`: two trees `t` and `t'` that differ only in
the values that `unreadByDiscoveries t` names give the same results of the
discoveries. The nodes of `t'` are those of `t` at the same indices
(`moveTo`), and every entry that a discovery calls on a node of `t` gives on
that node of `t'` what it gives on `t`, as long as it reads only values that
are not free.

- String values: a `string_property` that gives a string is that string and
  its NUL (`findNulFrom_some`, `stringProperty_some`).
- Two records whose property names agree: the values that a lookup finds
  agree where the name is not free, and both find one or neither
  (`find_value_eq`, `find_isSome_eq`).
- The nodes of the second tree (`moveTo`, `mem_nodes`, `moveTo_mk`,
  `nodes_move`, `root_move`) keep the name, the parent, the children and the
  values that are not free (`record_move` to `parent_mem`), so the lookup of
  a path finds the same node (`descend_move`, `findNode_move`).
- Entries that read only some values: `stringProperty_congr`,
  `enabled_congr`, `flag_congr`, `addressCells_congr`, `sizeCells_congr`,
  `cpuOfChild_congr`, `ramOfChild_unnamed`, and `foldlM_congr` for the loops.
- Which values are free (`Clean`, `unread_true`): none of the root, of a
  child of the root other than `/chosen`, or of a node below a child of the
  root other than `/reserved-memory` (`clean_root`, `clean_child_root`,
  `clean_grandchild`); of `/chosen` not its `device_type`, nor its `status`
  when that is `memory` (`chosen_unread`); of a child of `/reserved-memory`
  only values of a dynamic reservation other than its `status` and flags
  (`reserved_unread`).
- The discoveries: `ramOfChild_move`, `reservedOfChild_move`,
  `reservedMemory_move`, `discoverMemory_move`, `discoverBootMemory_move`
  and `discoverCpus_move`.
-/

@[expose] public section

namespace Krepi.Proofs.Fdt

open Krepi.Spec.Fdt

/-! ## String values -/

/-- The NUL that `findNulFrom` finds is a NUL of the bytes. -/
theorem findNulFrom_some {b : ByteArray} : ∀ {fuel i j : Nat}, findNulFrom b fuel i = some j →
    b[j]? = some 0
  | 0, _, _, h => by simp [findNulFrom] at h
  | fuel + 1, i, j, h => by
    unfold findNulFrom at h
    split at h
    · cases h
      assumption
    · exact findNulFrom_some h

/-- A value that `Node::string_property` reads as a string is that string and
its NUL. -/
theorem stringProperty_some {n : Node} {name s : String}
    (h : n.stringProperty name = .ok (some s)) :
    n.property name = some (s.toByteArray.push 0) := by
  unfold Node.stringProperty at h
  split at h
  · cases h
  · rename_i value hv
    rw [hv]
    obtain ⟨⟨s', e⟩, hc, h⟩ := except_bind_ok.1 h
    obtain ⟨he, h⟩ := except_jp_ok h
    cases except_pure_ok.1 h
    unfold cString at hc
    split at hc
    · cases hc
    · rename_i nul hnul
      split at hc
      · cases hc
      · rename_i str hs
        cases hc
        obtain ⟨hlt, h0⟩ := getElem?_eq_some_iff.1 (findNulFrom_some hnul)
        have hsz : nul + 1 = value.size := by simpa using he
        have hstr : s.toByteArray = value.extract 0 nul := by
          unfold String.fromUTF8? at hs
          split at hs
          · cases hs
            rfl
          · cases hs
        congr 1
        rw [hstr, ← ByteArray.append_toByteArray_singleton, ← h0,
          ← ByteArray.extract_add_one (by omega),
          ← ByteArray.extract_eq_extract_append_extract nul (Nat.zero_le _)
            (Nat.le_add_right nul 1), hsz,
          ByteArray.extract_zero_size]

/-! ## Properties of two records -/

/-- Two property lists with the same names, whose values agree where `free`
is false: the value of a name that is not free agrees. -/
theorem find_value_eq {free : String → Bool} : ∀ (l l' : List (String × ByteArray)),
    l.map (·.1) = l'.map (·.1) → (∀ q ∈ l.zip l', free q.1.1 = false → q.1.2 = q.2.2) →
    ∀ name, free name = false →
      (l.find? (·.1 == name)).map (·.2) = (l'.find? (·.1 == name)).map (·.2)
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h
  | a :: l, b :: l', h, hz, name, hn => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [List.find?_cons, List.find?_cons]
    by_cases ha : a.1 = name
    · have hb : b.1 = name := h.1 ▸ ha
      simp only [ha, hb, beq_self_eq_true, Option.map_some]
      congr 1
      exact hz (a, b) (by simp) (ha ▸ hn)
    · have hb : b.1 ≠ name := h.1 ▸ ha
      have ha' : (a.1 == name) = false := by simpa using ha
      have hb' : (b.1 == name) = false := by simpa using hb
      simp only [ha', hb']
      exact find_value_eq l l' h.2 (fun q hq => hz q (by simp [hq])) name hn

/-- Two property lists with the same names hold the same names. -/
theorem find_isSome_eq : ∀ (l l' : List (String × ByteArray)),
    l.map (·.1) = l'.map (·.1) → ∀ name,
      ((l.find? (·.1 == name)).map (·.2)).isSome = ((l'.find? (·.1 == name)).map (·.2)).isSome
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | a :: l, b :: l', h, name => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [List.find?_cons, List.find?_cons, h.1]
    split
    · rfl
    · exact find_isSome_eq l l' h.2 name

/-! ## The nodes of a second tree -/

/-- The node of `t'` at the index of `n`, when `t'` has one. -/
def moveTo (t' : Fdt) (n : Node) : Node :=
  if h : n.index.val < t'.records.size then ⟨t', ⟨n.index.val, h⟩⟩ else n

/-- The nodes of a tree are the nodes at its indices. -/
theorem mem_nodes {t : Fdt} {n : Node} : n ∈ t.nodes ↔ ∃ i, n = ⟨t, i⟩ := by
  simp only [Fdt.nodes, List.mem_map, List.mem_finRange, true_and]
  exact ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩

section Move

variable {t t' : Fdt}

/-- `moveTo` of a node of a tree of as many records. -/
theorem moveTo_mk (hsz : t.records.size = t'.records.size) (i : Fin t.records.size) :
    moveTo t' ⟨t, i⟩ = ⟨t', ⟨i.val, hsz ▸ i.isLt⟩⟩ := by
  unfold moveTo
  split
  · rfl
  · rename_i h
    exact absurd (hsz ▸ i.isLt) h

/-- The nodes of a tree of as many records are those of `moveTo`. -/
theorem nodes_move (hsz : t.records.size = t'.records.size) :
    t'.nodes = t.nodes.map (moveTo t') := by
  apply List.ext_getElem
  · simp [Fdt.nodes, hsz]
  · intro i h1 h2
    simp [Fdt.nodes, moveTo_mk hsz]

/-- The root of a tree of as many records is that of `moveTo`. -/
theorem root_move (hsz : t.records.size = t'.records.size) :
    t'.root = t.root.map (moveTo t') := by
  unfold Fdt.root
  by_cases h : 0 < t.records.size
  · simp only [h, hsz ▸ h, ↓reduceDIte, Option.map_some, moveTo_mk hsz]
  · simp only [h, hsz ▸ h, ↓reduceDIte, Option.map_none]

end Move

section Same

variable {t t' : Fdt} (hs : t.SameExceptValues (unreadByDiscoveries t) t')
include hs

/-- The record of a node of `t'` agrees with that of `t`: name, parent,
property names, and the values that are not free. -/
theorem record_move {n : Node} (hn : n ∈ t.nodes) :
    (moveTo t' n).record.name = n.record.name ∧
    (moveTo t' n).record.parent = n.record.parent ∧
    n.record.properties.map (·.1) = (moveTo t' n).record.properties.map (·.1) ∧
    ∀ q ∈ n.record.properties.zip (moveTo t' n).record.properties,
      unreadByDiscoveries t n.index.val q.1.1 = false → q.1.2 = q.2.2 := by
  obtain ⟨i, rfl⟩ := mem_nodes.1 hn
  rw [moveTo_mk hs.2.2.1]
  obtain ⟨h1, h2, h3, h4⟩ := hs.2.2.2 i.val t.records[i]
    (t'.records[i.val]'(hs.2.2.1 ▸ i.isLt))
    (by simp) (by simp)
  exact ⟨h1.symm, h2.symm, h3, h4⟩

/-- `moveTo` keeps the index. -/
theorem index_move {n : Node} (hn : n ∈ t.nodes) : (moveTo t' n).index.val = n.index.val := by
  obtain ⟨i, rfl⟩ := mem_nodes.1 hn
  rw [moveTo_mk hs.2.2.1]

/-- `moveTo` keeps the name. -/
theorem name_move {n : Node} (hn : n ∈ t.nodes) : (moveTo t' n).name = n.name :=
  (record_move hs hn).1

/-- `moveTo` keeps a value that is not free. -/
theorem property_move {n : Node} (hn : n ∈ t.nodes) {name : String}
    (h : unreadByDiscoveries t n.index.val name = false) :
    (moveTo t' n).property name = n.property name := by
  obtain ⟨-, -, h3, h4⟩ := record_move hs hn
  exact (find_value_eq _ _ h3 h4 name h).symm

/-- `moveTo` keeps whether a property is present. -/
theorem isSome_move {n : Node} (hn : n ∈ t.nodes) (name : String) :
    ((moveTo t' n).property name).isSome = (n.property name).isSome :=
  (find_isSome_eq _ _ (record_move hs hn).2.2.1 name).symm

/-- `moveTo` keeps whether a node is a child of another. -/
theorem isChildOf_move {c p : Node} (hc : c ∈ t.nodes) (hp : p ∈ t.nodes) :
    (moveTo t' c).isChildOf (moveTo t' p) = c.isChildOf p := by
  unfold Node.isChildOf
  rw [(record_move hs hc).2.1, index_move hs hp]

/-- `moveTo` keeps the parent. -/
theorem parent_move {n : Node} (hn : n ∈ t.nodes) :
    (moveTo t' n).parent = n.parent.map (moveTo t') := by
  have hpar := (record_move hs hn).2.1
  obtain ⟨i, rfl⟩ := mem_nodes.1 hn
  rw [moveTo_mk hs.2.2.1] at hpar ⊢
  unfold Node.parent
  rw [hpar]
  split
  · rfl
  · rename_i p _
    by_cases hp : p < t.records.size
    · simp only [hp, hs.2.2.1 ▸ hp, ↓reduceDIte, Option.map_some, moveTo_mk hs.2.2.1]
    · simp only [hp, hs.2.2.1 ▸ hp, ↓reduceDIte, Option.map_none]

omit hs in
/-- The parent of a node is a node of the tree, at the index of its record.
-/
theorem parent_mem {n p : Node} (hn : n ∈ t.nodes) (h : n.parent = some p) :
    p ∈ t.nodes ∧ n.record.parent = some p.index.val := by
  obtain ⟨i, rfl⟩ := mem_nodes.1 hn
  unfold Node.parent at h
  split at h
  · cases h
  · rename_i q hq
    split at h
    · cases h
      exact ⟨node_mem t _, hq⟩
    · cases h

/-- `moveTo` keeps the children of a node, in order. -/
theorem children_move {p : Node} (hp : p ∈ t.nodes) :
    t'.nodes.filter (·.isChildOf (moveTo t' p)) =
      (t.nodes.filter (·.isChildOf p)).map (moveTo t') := by
  rw [nodes_move hs.2.2.1, List.filter_map]
  congr 1
  apply List.filter_congr
  intro x hx
  exact isChildOf_move hs hx hp

/-- `moveTo` keeps the children of a node with a given name, in order. -/
theorem named_move {p : Node} (hp : p ∈ t.nodes) (c : List Char) :
    t'.nodes.filter (fun n => n.isChildOf (moveTo t' p) && n.name.toList == c) =
      (t.nodes.filter (fun n => n.isChildOf p && n.name.toList == c)).map (moveTo t') := by
  rw [nodes_move hs.2.2.1, List.filter_map]
  congr 1
  apply List.filter_congr
  intro x hx
  simp only [Function.comp, isChildOf_move hs hx hp, name_move hs hx]

/-- The walk of a path through `t'` finds the node that it finds in `t`. -/
theorem descend_move : ∀ (cs : List (List Char)) (o : Option Node),
    (∀ x, o = some x → x ∈ t.nodes) →
    t'.descend cs (o.map (moveTo t')) = (t.descend cs o).map (Option.map (moveTo t')) ∧
      ∀ x, t.descend cs o = .ok (some x) → x ∈ t.nodes
  | [], o, ho => by
    simp only [Fdt.descend]
    exact ⟨rfl, fun x h => ho x (by cases h; rfl)⟩
  | c :: cs, none, _ => by
    simp only [Option.map_none, Fdt.descend]
    exact ⟨rfl, fun x h => by cases h⟩
  | c :: cs, some p, ho => by
    have hp := ho p rfl
    simp only [Option.map_some, Fdt.descend]
    rw [named_move hs hp]
    generalize hF : t.nodes.filter (fun n => n.isChildOf p && n.name.toList == c) = F
    match F with
    | [] => exact descend_move cs none (fun x h => by cases h)
    | [w] =>
      have hw : w ∈ t.nodes := by
        have : w ∈ t.nodes.filter (fun n => n.isChildOf p && n.name.toList == c) := by
          rw [hF]
          exact List.mem_singleton_self w
        exact (List.mem_filter.1 this).1
      exact descend_move cs (some w) (fun x h => by cases h; exact hw)
    | _ :: _ :: _ => exact ⟨rfl, fun x h => by cases h⟩

/-- The lookup of a path in `t'` finds the node that it finds in `t`, a node
of `t`. -/
theorem findNode_move (path : String) :
    t'.findNode path = (t.findNode path).map (Option.map (moveTo t')) ∧
      ∀ x, t.findNode path = .ok (some x) → x ∈ t.nodes := by
  have hroot : ∀ x, t.root = some x → x ∈ t.nodes := by
    intro x h
    unfold Fdt.root at h
    split at h
    · cases h
      exact node_mem t _
    · cases h
  unfold Fdt.findNode
  dsimp only
  by_cases h1 : (!pathValid path.toList) = true
  · simp only [h1, ↓reduceIte]
    exact ⟨rfl, fun x h => by cases h⟩
  · simp only [h1]
    by_cases h2 : (path.toList == ['/']) = true
    · simp only [h2, root_move hs.2.2.1]
      exact ⟨rfl, fun x h => hroot x (Except.ok.inj h)⟩
    · simp only [h2, root_move hs.2.2.1]
      exact descend_move hs _ _ hroot

end Same

/-! ## Entries that read only some values -/

section Congr

variable {a b : Node}

/-- `Node::string_property` reads only the value of its name. -/
theorem stringProperty_congr {name : String} (h : a.property name = b.property name) :
    a.stringProperty name = b.stringProperty name := by
  unfold Node.stringProperty
  rw [h]

/-- `Node::enabled` reads only `status`. -/
theorem enabled_congr (h : a.property "status" = b.property "status") : a.enabled = b.enabled := by
  unfold Node.enabled
  rw [stringProperty_congr h]

/-- A flag reads only the value of its name. -/
theorem flag_congr {name : String} (h : a.property name = b.property name) :
    a.flag name = b.flag name := by
  unfold Node.flag
  rw [h]

/-- `Node::address_cells` reads only `#address-cells`. -/
theorem addressCells_congr (h : a.property "#address-cells" = b.property "#address-cells") :
    a.addressCells = b.addressCells := by
  unfold Node.addressCells Node.cellCount
  rw [h]

/-- `Node::size_cells` reads only `#size-cells`. -/
theorem sizeCells_congr (h : a.property "#size-cells" = b.property "#size-cells") :
    a.sizeCells = b.sizeCells := by
  unfold Node.sizeCells Node.cellCount
  rw [h]

end Congr

/-- A byte string compares equal to itself. -/
theorem bne_some_self (b : ByteArray) : (some b != some b) = false := by
  show (!(b.data == b.data)) = false
  simp

/-- A block that throws first is that throw. -/
theorem except_throw_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (throw e >>= f : Except ε β) = throw e := rfl

/-- A block whose first step fails is that failure. -/
theorem except_error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f : Except ε β) = .error e := rfl

/-- A loop whose two steps agree on every entry gives the same result. -/
theorem foldlM_congr {α β : Type} {f g : β → α → Except Error β} :
    ∀ (l : List α) (init : β), (∀ x ∈ l, ∀ a, f a x = g a x) →
      l.foldlM f init = l.foldlM g init
  | [], _, _ => rfl
  | x :: l, init, h => by
    rw [List.foldlM_cons, List.foldlM_cons, h x List.mem_cons_self init]
    congr 1
    funext b
    exact foldlM_congr l b (fun y hy a => h y (List.mem_cons_of_mem _ hy) a)

/-! ## Values that the discoveries read -/

/-- A node none of whose values the discoveries leave unread. -/
def Clean (t : Fdt) (n : Node) : Prop := ∀ name, unreadByDiscoveries t n.index.val name = false

/-- The values that `unreadByDiscoveries` frees: those of `/chosen` but its
`device_type` and, when that is `memory`, its `status`, and those of a
dynamic reservation but its `status` and flags. -/
theorem unread_true {t : Fdt} {i : Nat} {name : String} (h : unreadByDiscoveries t i name = true) :
    ∃ r, t.records[i]? = some r ∧
      ((r.parent = some 0 ∧ r.name = "chosen" ∧ name ≠ "device_type" ∧
          ((r.value "device_type" != some ("memory".toByteArray.push 0)) = true ∨
            name ≠ "status")) ∨
       ∃ p q, r.parent = some p ∧ t.records[p]? = some q ∧ q.name = "reserved-memory" ∧
         q.parent = some 0 ∧ (r.value "size").isSome ∧ (r.value "reg").isNone ∧
         name ≠ "status" ∧ name ≠ "no-map" ∧ name ≠ "reusable") := by
  unfold unreadByDiscoveries at h
  split at h
  · cases h
  · rename_i r hr
    refine ⟨r, hr, ?_⟩
    rcases Bool.or_eq_true_iff.1 h with h | h
    · left
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
      exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩
    · right
      split at h
      · rename_i q hq
        obtain ⟨p, hp1, hp2⟩ := Option.bind_eq_some_iff.1 hq
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        have hc : ["status", "no-map", "reusable"].contains name = false := by simpa using h.2
        refine ⟨p, q, hp1, hp2, h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, ?_, ?_, ?_⟩ <;>
          · intro e
            subst e
            simp at hc
      · cases h

/-- The record of a node of a tree is the record at its index. -/
theorem record_get {t : Fdt} {n : Node} (hn : n ∈ t.nodes) :
    t.records[n.index.val]? = some n.record := by
  obtain ⟨i, rfl⟩ := mem_nodes.1 hn
  simp [Node.record]

/-- The root of a well-formed tree has no parent and the empty name. -/
theorem root_record {t : Fdt} (hwf : t.WellFormed) :
    ∃ r, t.records[0]? = some r ∧ r.parent = none ∧ r.name = "" := by
  have h0 : 0 < t.records.size := hwf.2.2.2.2.2.1
  have := (hwf.2.2.2.2.2.2.2 0 h0).1
  simp only [↓reduceIte] at this
  exact ⟨_, by simp [h0], this⟩

/-- No value of a node without a parent is free. -/
theorem clean_root {t : Fdt} {n : Node} (hn : n ∈ t.nodes) (hp : n.record.parent = none) :
    Clean t n := by
  intro name
  cases h : unreadByDiscoveries t n.index.val name
  · rfl
  · obtain ⟨r, hr, h⟩ := unread_true h
    rw [record_get hn] at hr
    cases hr
    rcases h with ⟨h, -⟩ | ⟨_, _, h, -⟩ <;> rw [hp] at h <;> cases h

/-- No value of a child of the root other than `/chosen` is free. -/
theorem clean_child_root {t : Fdt} (hwf : t.WellFormed) {n : Node} (hn : n ∈ t.nodes)
    (hp : n.record.parent = some 0) (hc : n.name ≠ "chosen") : Clean t n := by
  intro name
  cases h : unreadByDiscoveries t n.index.val name
  · rfl
  · obtain ⟨r, hr, h⟩ := unread_true h
    rw [record_get hn] at hr
    cases hr
    obtain ⟨r0, hr0, hr0p, hr0n⟩ := root_record hwf
    rcases h with ⟨-, h, -⟩ | ⟨p, q, h1, h2, h3, -⟩
    · exact absurd h hc
    · rw [hp] at h1
      cases h1
      rw [hr0] at h2
      cases h2
      rw [hr0n] at h3
      exact absurd h3 (by decide)

/-- A child of the root is not the root. -/
theorem index_ne_zero {t : Fdt} (hwf : t.WellFormed) {n : Node} (hn : n ∈ t.nodes)
    (hp : n.record.parent = some 0) : n.index.val ≠ 0 := by
  intro h
  obtain ⟨r0, hr0, hr0p, -⟩ := root_record hwf
  have := record_get hn
  rw [h, hr0] at this
  cases this
  rw [hr0p] at hp
  cases hp

/-- No value of a node below a child of the root other than
`/reserved-memory` is free. -/
theorem clean_grandchild {t : Fdt} (hwf : t.WellFormed) {n p : Node} (hn : n ∈ t.nodes)
    (hpn : p ∈ t.nodes) (hp : n.record.parent = some p.index.val) (hpp : p.record.parent = some 0)
    (hpname : p.name ≠ "reserved-memory") : Clean t n := by
  intro name
  cases h : unreadByDiscoveries t n.index.val name
  · rfl
  · obtain ⟨r, hr, h⟩ := unread_true h
    rw [record_get hn] at hr
    cases hr
    rcases h with ⟨h, -⟩ | ⟨p', q, h1, h2, h3, -⟩
    · rw [hp] at h
      exact absurd (Option.some.inj h) (index_ne_zero hwf hpn hpp)
    · rw [hp] at h1
      cases h1
      rw [record_get hpn] at h2
      cases h2
      exact absurd h3 hpname

/-- A free value of a child of the root is not its `device_type`, nor its
`status` when the `device_type` is `memory`. -/
theorem chosen_unread {t : Fdt} (hwf : t.WellFormed) {n : Node} (hn : n ∈ t.nodes)
    (hp : n.record.parent = some 0) {name : String}
    (h : unreadByDiscoveries t n.index.val name = true) :
    name ≠ "device_type" ∧
      ((n.property "device_type" != some ("memory".toByteArray.push 0)) = true ∨
        name ≠ "status") := by
  obtain ⟨r, hr, h⟩ := unread_true h
  rw [record_get hn] at hr
  cases hr
  obtain ⟨r0, hr0, -, hr0n⟩ := root_record hwf
  rcases h with ⟨-, -, h1, h2⟩ | ⟨p, q, h1, h2, h3, -⟩
  · exact ⟨h1, h2⟩
  · rw [hp] at h1
    cases h1
    rw [hr0] at h2
    cases h2
    rw [hr0n] at h3
    exact absurd h3 (by decide)

/-- A free value of a node below a child of the root is a value of a dynamic
reservation other than its `status` and flags. -/
theorem reserved_unread {t : Fdt} (hwf : t.WellFormed) {n p : Node} (hn : n ∈ t.nodes)
    (hpn : p ∈ t.nodes) (hp : n.record.parent = some p.index.val) (hpp : p.record.parent = some 0)
    {name : String} (h : unreadByDiscoveries t n.index.val name = true) :
    (n.property "size").isSome ∧ (n.property "reg").isNone ∧
      name ≠ "status" ∧ name ≠ "no-map" ∧ name ≠ "reusable" := by
  obtain ⟨r, hr, h⟩ := unread_true h
  rw [record_get hn] at hr
  cases hr
  rcases h with ⟨h, -⟩ | ⟨p', q, -, -, -, -, h⟩
  · rw [hp] at h
    exact absurd (Option.some.inj h) (index_ne_zero hwf hpn hpp)
  · exact h

/-- A child of the root without a memory name reads only its `device_type`,
and its `status` when that is `memory`. -/
theorem ramOfChild_unnamed {ram : List Span} {x x' : Node} (hx : isMemoryName x.name = false)
    (hx' : isMemoryName x'.name = false)
    (hdt : x'.stringProperty "device_type" = x.stringProperty "device_type")
    (hen : x.stringProperty "device_type" = .ok (some "memory") → x'.enabled = x.enabled) :
    ramOfChild ram x' = ramOfChild ram x := by
  unfold ramOfChild
  rw [hdt]
  cases hd : x.stringProperty "device_type" with
  | error e => rfl
  | ok dt =>
    simp only [except_ok_bind, hx, hx', Bool.false_or]
    by_cases hm : dt = some "memory"
    · subst hm
      rw [hen hd]
      simp only [beq_self_eq_true, Bool.false_and, Bool.not_false, ↓reduceIte, except_throw_bind]
    · have hm' : (dt == some "memory") = false := by simpa using hm
      simp only [hm', Bool.not_false, ↓reduceIte]

/-- A child of `/cpus` is read only through its values. -/
theorem cpuOfChild_congr {profile : CpuProfile} {cells : UInt32} {ids : List UInt64} {a a' : Node}
    (h : ∀ name, a'.property name = a.property name) :
    cpuOfChild profile cells ids a' = cpuOfChild profile cells ids a := by
  unfold cpuOfChild
  simp only [stringProperty_congr (h _), enabled_congr (h _), h]

section Move2

variable {t t' : Fdt} (hs : t.SameExceptValues (unreadByDiscoveries t) t')
include hs

/-- `moveTo` keeps every value of a node none of whose values is free. -/
theorem property_move_clean {n : Node} (hn : n ∈ t.nodes) (hc : Clean t n) (name : String) :
    (moveTo t' n).property name = n.property name :=
  property_move hs hn (hc name)

/-- `moveTo` keeps the `reg` of a node when no value of it or of its parent is
free. -/
theorem reg_move {n : Node} (hn : n ∈ t.nodes) (hc : Clean t n)
    (hpc : ∀ p, n.parent = some p → Clean t p) : (moveTo t' n).reg = n.reg := by
  unfold Node.reg
  rw [parent_move hs hn, property_move hs hn (hc "reg")]
  cases hp : n.parent with
  | none => rfl
  | some p =>
    have hpn := (parent_mem hn hp).1
    have hcp := hpc p hp
    simp only [Option.map_some, addressCells_congr (property_move_clean hs hpn hcp _),
      sizeCells_congr (property_move_clean hs hpn hcp _)]

/-- `moveTo` keeps what a child of the root adds to the RAM ranges. -/
theorem ramOfChild_move (hwf : t.WellFormed) {n : Node} (hn : n ∈ t.nodes)
    (hp : n.record.parent = some 0) (ram : List Span) :
    ramOfChild ram (moveTo t' n) = ramOfChild ram n := by
  by_cases hc : n.name = "chosen"
  · have hmn : isMemoryName n.name = false := by
      rw [hc]
      decide +kernel
    have hdt : unreadByDiscoveries t n.index.val "device_type" = false := by
      cases h : unreadByDiscoveries t n.index.val "device_type"
      · rfl
      · exact absurd rfl (chosen_unread hwf hn hp h).1
    refine ramOfChild_unnamed hmn (by rw [name_move hs hn]; exact hmn)
      (stringProperty_congr (property_move hs hn hdt))
      (fun hd => enabled_congr (property_move hs hn ?_))
    cases h : unreadByDiscoveries t n.index.val "status"
    · rfl
    · rcases (chosen_unread hwf hn hp h).2 with h1 | h1
      · rw [stringProperty_some hd, bne_some_self] at h1
        cases h1
      · exact absurd rfl h1
  · have hcl := clean_child_root hwf hn hp hc
    have hreg : (moveTo t' n).reg = n.reg := by
      refine reg_move hs hn hcl (fun p hpp => ?_)
      obtain ⟨hpn, hpi⟩ := parent_mem hn hpp
      rw [hp] at hpi
      refine clean_root hpn ?_
      obtain ⟨r0, hr0, hr0p, -⟩ := root_record hwf
      have := record_get hpn
      rw [← Option.some.inj hpi, hr0] at this
      rw [← Option.some.inj this, hr0p]
    unfold ramOfChild
    rw [name_move hs hn, stringProperty_congr (property_move_clean hs hn hcl _),
      enabled_congr (property_move_clean hs hn hcl _), hreg]

/-- `moveTo` keeps what a child of `/reserved-memory` adds to the reserved
regions. -/
theorem reservedOfChild_move (hwf : t.WellFormed) {n rm : Node} (hn : n ∈ t.nodes)
    (hrm : rm ∈ t.nodes) (hp : n.record.parent = some rm.index.val)
    (hrmp : rm.record.parent = some 0) (hrmc : Clean t rm) (acc : List ReservedRegion × Nat) :
    reservedOfChild acc (moveTo t' n) = reservedOfChild acc n := by
  have hkeep : ∀ name, (name = "status" ∨ name = "no-map" ∨ name = "reusable") →
      (moveTo t' n).property name = n.property name := by
    intro name hname
    apply property_move hs hn
    cases h : unreadByDiscoveries t n.index.val name
    · rfl
    · obtain ⟨-, -, h1, h2, h3⟩ := reserved_unread hwf hn hrm hp hrmp h
      rcases hname with e | e | e
      · exact absurd e h1
      · exact absurd e h2
      · exact absurd e h3
  unfold reservedOfChild
  rw [enabled_congr (hkeep _ (Or.inl rfl)), flag_congr (hkeep _ (Or.inr (Or.inl rfl))),
    flag_congr (hkeep _ (Or.inr (Or.inr rfl)))]
  by_cases hd : (n.property "size").isSome = true ∧ (n.property "reg").isNone = true
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hd.1
    have hreg : n.property "reg" = none := Option.isNone_iff_eq_none.1 hd.2
    have hsz' : ((moveTo t' n).property "size").isSome = true := by
      rw [isSome_move hs hn]
      exact hd.1
    obtain ⟨v', hv'⟩ := Option.isSome_iff_exists.1 hsz'
    have hreg' : (moveTo t' n).property "reg" = none := by
      have := isSome_move hs hn "reg"
      rw [hreg] at this
      cases h : (moveTo t' n).property "reg"
      · rfl
      · rw [h] at this
        cases this
    simp only [hv, hv', hreg, hreg']
  · have hcl : Clean t n := by
      intro name
      cases h : unreadByDiscoveries t n.index.val name
      · rfl
      · obtain ⟨h1, h2, -⟩ := reserved_unread hwf hn hrm hp hrmp h
        exact absurd ⟨h1, h2⟩ hd
    have hreg : (moveTo t' n).reg = n.reg := by
      refine reg_move hs hn hcl (fun p hpp => ?_)
      obtain ⟨-, hpi⟩ := parent_mem hn hpp
      rw [hp] at hpi
      intro name
      rw [← Option.some.inj hpi]
      exact hrmc name
    rw [property_move_clean hs hn hcl "reg", property_move_clean hs hn hcl "size", hreg]

omit hs in
/-- `moveTo` keeps the binding of `/reserved-memory` when no value of it or of
the root is free. -/
theorem binding_move {a b : Node} (ha : ∀ name, (moveTo t' a).property name = a.property name)
    (hb : ∀ name, (moveTo t' b).property name = b.property name) :
    reservedMemoryBinding (moveTo t' a) (moveTo t' b) = reservedMemoryBinding a b := by
  unfold reservedMemoryBinding
  simp only [ha, addressCells_congr (ha _), sizeCells_congr (ha _), addressCells_congr (hb _),
    sizeCells_congr (hb _)]

/-- `moveTo` keeps the reserved regions of `/reserved-memory`. -/
theorem reservedMemory_move (hwf : t.WellFormed) {root : Node} (hroot : root ∈ t.nodes)
    (hrp : root.record.parent = none) (mapped : List ReservedRegion) :
    t'.reservedMemory (moveTo t' root) mapped = t.reservedMemory root mapped := by
  have hrc := clean_root hroot hrp
  unfold Fdt.reservedMemory
  rw [(findNode_move hs "/reserved-memory").1]
  cases hf : t.findNode "/reserved-memory" with
  | error e => rfl
  | ok o =>
    cases o with
    | none => rfl
    | some rm =>
      obtain ⟨hrm, hrmp, hrmn⟩ := findNode_single hwf (c := "reserved-memory".toList)
        (by decide) (by decide) (by decide) hf
      have hrmc : Clean t rm := clean_child_root hwf hrm hrmp (by
        intro h
        rw [h] at hrmn
        exact absurd hrmn (by decide))
      have hfold : ∀ init, (t'.nodes.filter (·.isChildOf (moveTo t' rm))).foldlM
          reservedOfChild init =
          (t.nodes.filter (·.isChildOf rm)).foldlM reservedOfChild init := by
        intro init
        rw [children_move hs hrm, List.foldlM_map]
        apply foldlM_congr
        intro x hx acc
        have hx' := List.mem_filter.1 hx
        exact reservedOfChild_move hs hwf hx'.1 hrm (by simpa [Node.isChildOf] using hx'.2) hrmp
          hrmc acc
      simp only [Except.map, Option.map_some, except_ok_bind, hfold,
        enabled_congr (property_move_clean hs hrm hrmc _),
        binding_move (property_move_clean hs hrm hrmc) (property_move_clean hs hroot hrc)]

omit hs in
/-- The root of a well-formed tree: the node of index 0, without a parent,
that the lookup of `/` finds. -/
theorem root_facts (hwf : t.WellFormed) :
    ∃ root, root ∈ t.nodes ∧ root.record.parent = none ∧
      t.findNode "/" = .ok (some root) ∧ root.index.val = 0 := by
  have h0 : 0 < t.records.size := hwf.2.2.2.2.2.1
  refine ⟨⟨t, ⟨0, h0⟩⟩, node_mem t _, ?_, ?_, rfl⟩
  · obtain ⟨r0, hr0, hr0p, -⟩ := root_record hwf
    have := record_get (node_mem t ⟨0, h0⟩)
    rw [show (⟨t, ⟨0, h0⟩⟩ : Node).index.val = 0 from rfl, hr0] at this
    rw [← Option.some.inj this, hr0p]
  · rw [findNode_slash (by decide)]
    simp [Fdt.root, h0]

/-- The two trees give the same memory map. -/
theorem discoverMemory_move (hwf : t.WellFormed) : t'.discoverMemory = t.discoverMemory := by
  obtain ⟨root, hroot, hrp, hr, hr0⟩ := root_facts hwf
  have hr' : t'.findNode "/" = .ok (some (moveTo t' root)) := by
    rw [(findNode_move hs "/").1, hr]
    rfl
  have hfold : ∀ init, (t'.nodes.filter (·.isChildOf (moveTo t' root))).foldlM ramOfChild init =
      (t.nodes.filter (·.isChildOf root)).foldlM ramOfChild init := by
    intro init
    rw [children_move hs hroot, List.foldlM_map]
    apply foldlM_congr
    intro x hx acc
    have hx' := List.mem_filter.1 hx
    refine ramOfChild_move hs hwf hx'.1 ?_ acc
    have := hx'.2
    simp only [Node.isChildOf, beq_iff_eq] at this
    rw [this, hr0]
  unfold Fdt.discoverMemory
  simp only [← hs.2.1, hr, hr', except_ok_bind, hfold, reservedMemory_move hs hwf hroot hrp]

/-- The two trees give the same boot memory, with every hand-over profile. -/
theorem discoverBootMemory_move (hwf : t.WellFormed) (handOver : HandOverProfile) (a : UInt64)
    (image : Span) :
    t'.discoverBootMemory handOver a image = t.discoverBootMemory handOver a image := by
  obtain ⟨root, hroot, hrp, hr, -⟩ := root_facts hwf
  have hr' : t'.findNode "/" = .ok (some (moveTo t' root)) := by
    rw [(findNode_move hs "/").1, hr]
    rfl
  have hP := property_move_clean hs hroot (clean_root hroot hrp)
  unfold Fdt.discoverBootMemory
  simp only [← hs.1, hr, hr', except_ok_bind, addressCells_congr (hP _), sizeCells_congr (hP _),
    hP, discoverMemory_move hs hwf]

/-- The two trees give the same CPU topology. -/
theorem discoverCpus_move (hwf : t.WellFormed) (profile : CpuProfile) :
    t'.discoverCpus profile = t.discoverCpus profile := by
  unfold Fdt.discoverCpus
  rw [(findNode_move hs "/cpus").1, (findNode_move hs "/psci").1]
  cases hc : t.findNode "/cpus" with
  | error e => rfl
  | ok o =>
    cases o with
    | none => rfl
    | some cpus =>
      obtain ⟨hcm, hcp, hcn⟩ := findNode_single hwf (c := "cpus".toList) (by decide) (by decide)
        (by decide) hc
      have hcc : Clean t cpus := clean_child_root hwf hcm hcp (fun h => by
        rw [h] at hcn
        exact absurd hcn (by decide))
      have hC := property_move_clean hs hcm hcc
      have hfold : ∀ cells init, (t'.nodes.filter (·.isChildOf (moveTo t' cpus))).foldlM
          (cpuOfChild profile cells) init =
          (t.nodes.filter (·.isChildOf cpus)).foldlM (cpuOfChild profile cells) init := by
        intro cells init
        rw [children_move hs hcm, List.foldlM_map]
        apply foldlM_congr
        intro x hx acc
        have hx' := List.mem_filter.1 hx
        have hxp : x.record.parent = some cpus.index.val := by simpa [Node.isChildOf] using hx'.2
        have hxc : Clean t x := clean_grandchild hwf hx'.1 hcm hxp hcp (fun h => by
          rw [h] at hcn
          exact absurd hcn (by decide))
        exact cpuOfChild_congr (property_move_clean hs hx'.1 hxc)
      simp only [Except.map, Option.map_some, except_ok_bind, enabled_congr (hC _),
        sizeCells_congr (hC _), addressCells_congr (hC _), hfold]
      cases hp : t.findNode "/psci" with
      | error e => simp only [except_error_bind]
      | ok o =>
        cases o with
        | none => simp only [Option.map_none]
        | some psci =>
          obtain ⟨hpm, hpp, hpn⟩ := findNode_single hwf (c := "psci".toList) (by decide)
            (by decide) (by decide) hp
          have hQ := property_move_clean hs hpm (clean_child_root hwf hpm hpp (fun h => by
            rw [h] at hpn
            exact absurd hpn (by decide)))
          simp only [Option.map_some, except_ok_bind, enabled_congr (hQ _),
            stringProperty_congr (hQ _), hQ]

end Move2

end Krepi.Proofs.Fdt
