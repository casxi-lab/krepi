module

public import Krepi.Proofs.Fdt.Refinement.FormatLemmas
public import Krepi.Proofs.Fdt.Refinement.TreeSpecLemmas

/-!
# Device tree: refinement of the node walk

The triples of the generated functions of `fdt::nodes` that walk the nodes of
a tree, stated against the walk `nodesFrom` of
`Krepi.Proofs.Fdt.Refinement.TreeSpecLemmas`, so that the proof of a caller
steps over the call with the triple of the callee and a mutant of a callee
fails the proof of the callee alone. The lemmas that need no generated code
are in that module.

- The walker: `WalkerRepr` (a walker stands for the offsets of the open nodes),
  `AtRepr` (a node of the code stands for a begin-node token),
  `ancestors_length`, `start_repr` (`START`), `innermost_spec`,
  `walkerRepr_push`, `walkerRepr_pop`, and `PieceTok` with `piece_of_token`,
  the piece that `piece_at` reads at a token that `decodeToken` reads.
- One step: `StepPost`, what a call of `node_step` gives, with
  `node_step_loop_spec`, `node_step_spec` (from a walker whose walk of
  `nodesFrom` succeeds, the node of the next begin-node token and a walker for
  the rest, or none and a walker at the end token) and `node_step_end` (at the
  end token the walker stays); `node_of_spec`.
- The nodes of a tree: `TreeNodes`, the begin-node tokens of a tree of the
  code that stands for a tree of the specification, with
  `treeNodes_of_repr`, `TreeNodes.unique`, `TreeNodes.offsets`
  (`offsetsOf`), `TreeNodes.length` and `TreeNodes.nodeRepr_iff` (a node of
  the code stands for the node of index `k` exactly when it stands for the
  `k`-th token); `nodeRepr_begin`, what a node that stands for a node tells.
- The iterator: `NodesAt`, `nodes_next_sim` and `fdt_nodes_spec` (`Fdt.nodes`).
- The name and the parent: `bytesOf_of_slice`, `node_name_spec`
  (`Node.name`), `node_at_offset_loop_spec`, `node_at_offset_spec`,
  `parent_at_spec` and `node_parent_spec` (`Node.parent`).
- Paths: `map_byte_getElem!`, `drop_map_byte_getElem!`, `slash_beq`,
  `component_end_spec`, `double_slash_spec` (`doubleSlashB`) and
  `path_valid_spec` (`pathValidB`).
- The lookup: `is_child_spec`, `TreeNodes.child_iff` and `TreeNodes.name_eq`
  (the tests of `child_named` as `childPred`), `first_node_spec` (`Fdt.root`),
  `child_named_loop_spec` and `child_named_spec` (`scanChild`),
  `fdtRepr_unique`, `TreeNodes.of_nodeRepr`, `descend_loop_spec`
  (`descendB`), `find_path_spec`, and `fdt_find_node_spec_of_lt`, the triple
  of `Fdt::find_node` against `Fdt.findNode` for a path of fewer than
  `Usize.max` bytes. Without that premise the triple fails: for a path of
  `Usize.max` bytes whose last component is reached at a node, `descend`
  computes the index after the end of the path, which leaves `usize`; a
  slice of bytes of Rust has at most `isize::MAX` bytes.
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.Fdt Krepi.Spec.Fdt Krepi.Statements Krepi.Statements.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## The walker -/

/-- A walker of the code stands for the offsets `st` of the begin-node tokens of
the open nodes, innermost first: its depth is their number, at most
`MAX_DEPTH`, and its ancestors hold them from the outermost on. -/
def WalkerRepr (w : fdt.Walker) (st : List Nat) : Prop :=
  w.depth.val = st.length ∧ st.length ≤ MAX_DEPTH.toNat ∧
    (w.ancestors.val.take st.length).map (·.val) = st.reverse

/-- A node of the code stands for a begin-node token: at its offset, with the
offset of its parent, its name after the tag and its properties at the next
multiple of 4 after the NUL of its name. -/
def AtRepr (a : fdt.NodeAt) (b : Begin) : Prop :=
  a.offset.val = b.offset ∧ a.parent.map (·.val) = b.parent ∧ a.name_start.val = b.offset + 4 ∧
    a.name_end.val = b.offset + 4 + b.name.utf8ByteSize ∧
    a.properties.val = align4 (b.offset + 4 + b.name.utf8ByteSize + 1)

theorem ancestors_length (w : fdt.Walker) : w.ancestors.val.length = 32 := by
  simp

/-- `START`: the walker before the first token, with no open node. -/
theorem start_repr : WalkerRepr fdt.nodes.START [] ∧ fdt.nodes.START.cursor.val = 0 := by
  unfold fdt.nodes.START
  simp [WalkerRepr]

/-- `innermost(walker)`: the offset of the innermost open node. -/
@[step] theorem innermost_spec (w : fdt.Walker) (st : List Nat) (hw : WalkerRepr w st) :
    fdt.nodes.innermost w ⦃ o => o.map (·.val) = st.head? ⦄ := by
  obtain ⟨hd, hle, ha⟩ := hw
  unfold fdt.nodes.innermost
  have hl := ancestors_length w
  simp only [MAX_DEPTH, UInt64.reduceToNat] at hle
  step*
  · have : st.length = 0 := by scalar_tac
    rw [List.length_eq_zero_iff.1 this]; rfl
  · exfalso
    rw [show MAX_DEPTH.toNat = 32 from rfl] at i_post
    scalar_tac
  · cases st with
    | nil => simp at hd; scalar_tac
    | cons s st =>
      have hi : i1.val = st.length := by simp at hd; scalar_tac
      have e := congrArg (fun l => l[st.length]?) ha
      simp only [List.getElem?_map, List.getElem?_take, List.length_cons,
        Nat.lt_succ_self, ↓reduceIte, List.reverse_cons] at e
      rw [List.getElem?_append_right (by simp), List.length_reverse, Nat.sub_self,
        List.getElem?_cons_zero, List.getElem?_eq_getElem (by simp at hle; omega),
        Option.map_some, Option.some.injEq] at e
      rw [i2_post]
      simp only [List.head?_cons, Option.map_some, ← e, hi]

/-- A begin node opens a node: the walker with the cursor pushed on its
ancestors stands for one more open node. -/
theorem walkerRepr_push {w : fdt.Walker} {st : List Nat} (hw : WalkerRepr w st)
    (hlt : st.length < MAX_DEPTH.toNat) (next d : Usize) (hd : d.val = w.depth.val + 1) :
    WalkerRepr { cursor := next, depth := d, ancestors := w.ancestors.set w.depth w.cursor }
      (w.cursor.val :: st) := by
  obtain ⟨h1, -, h3⟩ := hw
  have hl := ancestors_length w
  simp only [MAX_DEPTH, UInt64.reduceToNat] at hlt
  refine ⟨by simp [hd, h1], by simp [MAX_DEPTH]; omega, ?_⟩
  simp only [List.length_cons, List.reverse_cons, ← h3, Array.set_val_eq, List.take_add_one,
    List.take_set, List.map_append, h1]
  rw [List.set_eq_of_length_le (by simp), List.getElem?_set_self (by omega)]
  rfl

/-- An end node closes the innermost open node. -/
theorem walkerRepr_pop {w : fdt.Walker} {st : List Nat} (hw : WalkerRepr w st) (c d : Usize)
    (hd : d.val = w.depth.val - 1) : WalkerRepr { w with cursor := c, depth := d } st.tail := by
  obtain ⟨h1, h2, h3⟩ := hw
  refine ⟨by simp [hd, h1], by simp; omega, ?_⟩
  cases st with
  | nil => simp
  | cons s t =>
    simp only [List.tail_cons]
    have e := congrArg (List.take t.length) h3
    rw [← List.map_take, List.take_take, List.length_cons, Nat.min_eq_left (by omega),
      List.reverse_cons, List.take_left' (by simp)] at e
    exact e

/-- The piece that the code reads at a token that `decodeToken` reads: the
same kind, with the NUL after the name of a begin node. -/
def PieceTok (c : Nat) : fdt.nodes.Piece → Token → Prop
  | .Begin e, .beginNode nm => e.val = c + 4 + nm.utf8ByteSize
  | .EndNode, .endNode => True
  | .Property _ _ _, .property _ _ => True
  | .Nop, .nop => True
  | .End, .endStructure => True
  | _, _ => False

/-- The piece of the code at a token that `decodeToken` reads. -/
theorem piece_of_token {o : Option (fdt.nodes.Piece × Usize)} {str strs : ByteArray}
    {c next : Nat} {tok : Token} (ho : o.map (fun p => (pieceOf p.1, p.2.val)) = pieceAt str c)
    (hd : decodeToken str strs c = .ok (tok, next)) :
    ∃ p n, o = some (p, n) ∧ n.val = next ∧ PieceTok c p tok := by
  have ht := pieceAt_of_decodeToken hd
  cases tok
  case property nm v =>
    obtain ⟨off, e, -, -, ht⟩ := ht
    rw [ht] at ho
    obtain ⟨⟨p, n⟩, rfl, hp⟩ := Option.map_eq_some_iff.1 ho
    simp only [Prod.mk.injEq] at hp
    obtain ⟨hp, rfl⟩ := hp
    refine ⟨p, n, rfl, rfl, ?_⟩
    cases p <;> simp_all [pieceOf, PieceTok]
  all_goals
    simp only [TokenPiece] at ht
    rw [ht] at ho
    obtain ⟨⟨p, n⟩, rfl, hp⟩ := Option.map_eq_some_iff.1 ho
    simp only [Prod.mk.injEq] at hp
    obtain ⟨hp, rfl⟩ := hp
    refine ⟨p, n, rfl, rfl, ?_⟩
    cases p <;> simp_all [pieceOf, PieceTok]

/-! ## One step of the walk -/

/-- What a call of `node_step` gives from a walker whose walk of `nodesFrom`
gives the begin-node tokens `L`: a walker whose walk gives the rest of `L`,
and the node of the first of `L`; at the end of `L`, none and a walker at the
end token. -/
def StepPost (str strs : ByteArray) (L : List Begin) (r : fdt.Walker × Option fdt.NodeAt) : Prop :=
  (∃ f st, f ≤ MAX_TOKENS.toNat ∧ WalkerRepr r.1 st ∧
    nodesFrom str strs f r.1.cursor.val st = some L.tail) ∧
  match L with
  | [] => r.2 = none ∧ ∃ e, decodeToken str strs r.1.cursor.val = .ok (.endStructure, e)
  | b :: _ => ∃ a, r.2 = some a ∧ AtRepr a b

/-- The loop of `node_step`: from a walker whose walk of `nodesFrom` succeeds,
with the tokens read so far and the fuel within `MAX_TOKENS`, the next
begin-node token or the end. -/
theorem node_step_loop_spec («structure» : Slice U8) (strs : ByteArray) (w : fdt.Walker)
    (read : Usize) (f : Nat) (st : List Nat) (L : List Begin)
    (hsz : «structure».length + 2 ^ 32 ≤ Usize.max) (hw : WalkerRepr w st)
    (hf : read.val + f ≤ MAX_TOKENS.toNat)
    (hL : nodesFrom (bytesOf «structure») strs f w.cursor.val st = some L) :
    fdt.nodes.node_step_loop «structure» w read ⦃ r => StepPost (bytesOf «structure») strs L r ⦄ := by
  unfold fdt.nodes.node_step_loop
  apply loop.spec_decr_nat
    (measure := fun (x : fdt.Walker × Usize) => MAX_TOKENS.toNat - x.2.val)
    (inv := fun (x : fdt.Walker × Usize) => ∃ f st, WalkerRepr x.1 st ∧
      x.2.val + f ≤ MAX_TOKENS.toNat ∧ nodesFrom (bytesOf «structure») strs f x.1.cursor.val st = some L)
  · rintro ⟨w, read⟩ ⟨f, st, hw, hf, hL⟩
    simp only at hw hf hL
    obtain ⟨f, tok, next, rfl, hd⟩ := nodesFrom_decode hL
    have hc := u32At_ok_le (decodeToken_tag_ok hd).choose_spec
    rw [bytesOf_size] at hc
    unfold fdt.nodes.node_step_loop.body
    step
    refine ite_spec_pos (by scalar_tac) ?_
    step with piece_at_spec
    obtain ⟨p, n, rfl, hn, hpt⟩ := piece_of_token o_post hd
    cases tok <;> cases p <;> simp only [PieceTok] at hpt
    · -- a begin node
      rename_i nm e
      obtain ⟨hlt, L', rfl, hL'⟩ := nodesFrom_begin_some hd hL
      have hdl : w.depth.val < 32 := by
        have := hw.1; simp only [MAX_DEPTH, UInt64.reduceToNat] at hlt; omega
      obtain ⟨hnext, -, -⟩ := decodeToken_begin hd
      simp only [MAX_DEPTH, UInt64.reduceToNat] at hlt
      simp only
      step*
      rw [show MAX_DEPTH.toNat = 32 from rfl] at i2_post
      simp only [show w.depth < i2 by scalar_tac, ↓reduceIte]
      step*
      refine ⟨⟨f, w.cursor.val :: st, by omega, ?_, by simpa [hn] using hL'⟩, _, rfl,
        rfl, o1_post, i1_post, by rw [hpt], by rw [hn, hnext]⟩
      rw [a_post]
      exact walkerRepr_push hw (by simpa [MAX_DEPTH] using hlt) n i3 (by scalar_tac)
    · -- an end node
      rw [nodesFrom_endNode hd] at hL
      simp only
      split
      · step*
        exact ⟨⟨f, st.tail, walkerRepr_pop hw n i1 (by scalar_tac), by scalar_tac,
          by simpa [hn] using hL⟩, by scalar_tac⟩
      · step*
        exact ⟨⟨f, st.tail, walkerRepr_pop hw n w.depth (by scalar_tac), by scalar_tac,
          by simpa [hn] using hL⟩, by scalar_tac⟩
    · -- a property
      rw [nodesFrom_property hd] at hL
      simp only
      step*
      exact ⟨⟨f, st, hw, by scalar_tac, by simpa [hn] using hL⟩, by scalar_tac⟩
    · -- a no-operation
      rw [nodesFrom_nop hd] at hL
      simp only
      step*
      exact ⟨⟨f, st, hw, by scalar_tac, by simpa [hn] using hL⟩, by scalar_tac⟩
    · -- the end token
      cases nodesFrom_end_some hd hL
      simp only
      step*
      exact ⟨⟨f + 1, st, by omega, hw, by rw [nodesFrom_end hd]; rfl⟩, rfl, _, hd⟩
  · exact ⟨f, st, hw, hf, hL⟩

/-- `node_step(structure, walker)`: from a walker whose walk of `nodesFrom`
gives `L` within `MAX_TOKENS` tokens, the node of the first of `L` and a walker
whose walk gives the rest, or none at the end. -/
theorem node_step_spec («structure» : Slice U8) (strs : ByteArray) (w : fdt.Walker)
    (f : Nat) (st : List Nat) (L : List Begin)
    (hsz : «structure».length + 2 ^ 32 ≤ Usize.max) (hw : WalkerRepr w st)
    (hf : f ≤ MAX_TOKENS.toNat)
    (hL : nodesFrom (bytesOf «structure») strs f w.cursor.val st = some L) :
    fdt.nodes.node_step «structure» w ⦃ r => StepPost (bytesOf «structure») strs L r ⦄ :=
  node_step_loop_spec «structure» strs w 0#usize f st L hsz hw (by simpa using hf) hL

/-- `node_step(structure, walker)` at the end token: none, and the walker
stays. -/
theorem node_step_end («structure» : Slice U8) (strs : ByteArray) (w : fdt.Walker) {e : Nat}
    (hsz : «structure».length + 2 ^ 32 ≤ Usize.max)
    (hd : decodeToken (bytesOf «structure») strs w.cursor.val = .ok (.endStructure, e)) :
    fdt.nodes.node_step «structure» w = .ok (w, none) := by
  have hc := u32At_ok_le (decodeToken_tag_ok hd).choose_spec
  rw [bytesOf_size] at hc
  have h : fdt.nodes.node_step «structure» w ⦃ r => r = (w, none) ⦄ := by
    unfold fdt.nodes.node_step fdt.nodes.node_step_loop
    apply loop.spec_decr_nat (measure := fun (_ : fdt.Walker × Usize) => 0)
      (inv := fun (x : fdt.Walker × Usize) => x = (w, 0#usize))
    · rintro x rfl
      unfold fdt.nodes.node_step_loop.body
      step
      rw [show MAX_TOKENS.toNat = 65536 from rfl] at r_post
      refine ite_spec_pos (by scalar_tac) ?_
      step with piece_at_spec
      obtain ⟨p, n, rfl, -, hpt⟩ := piece_of_token o_post hd
      cases p <;> simp only [PieceTok] at hpt
      simp only
      step*
    · rfl
  obtain ⟨r, hr, rfl⟩ := spec_iff.1 h
  exact hr

/-- `node_of(tree, found)`: the node of the tree at the node found. -/
@[step] theorem node_of_spec (tree : fdt.Fdt) (found : Option fdt.NodeAt) :
    fdt.nodes.node_of tree found ⦃ o => o = found.map (fun a => ⟨tree, a⟩) ⦄ := by
  unfold fdt.nodes.node_of
  cases found <;> simp

/-! ## The nodes of a tree -/

/-- The begin-node tokens `L` of a tree of the code that stands for `T`: the
walk of `nodesFrom` from the first token of its structure block gives them,
they stand for the records of `T`, and the block leaves room for the sums of
the code. -/
structure TreeNodes (t : fdt.Fdt) (T : Fdt) (L : List Begin) : Prop where
  repr : FdtRepr t T
  walk : nodesFrom (bytesOf t.structure) (bytesOf t.strings) MAX_TOKENS.toNat 0 [] = some L
  begins : BeginsOf T.records L
  size : t.structure.length + 2 ^ 32 ≤ Usize.max

/-- A tree of the code that stands for a tree of the specification has its
begin-node tokens. -/
theorem treeNodes_of_repr (hu : Usize64) {t : fdt.Fdt} {T : Fdt} (h : FdtRepr t T) :
    ∃ L, TreeNodes t T L := by
  obtain ⟨hp, hd, hh, hb, hs, hst, hres⟩ := h
  obtain ⟨L, hL, hbL⟩ := parse_nodesFrom hp hh
  obtain ⟨h1, h2, -⟩ := header_sizes hh
  refine ⟨L, ⟨⟨hp, hd, hh, hb, hs, hst, hres⟩, by rw [hs, hst]; exact hL, hbL, ?_⟩⟩
  have : t.structure.length = hd.structure_.size := by rw [← hs, bytesOf_size]
  rw [usize_max hu, this]
  simp only [MAX_BLOB_SIZE, UInt64.reduceToNat] at h1
  omega

/-- The begin-node tokens of a tree are determined by it. -/
theorem TreeNodes.unique {t : fdt.Fdt} {T : Fdt} {L L' : List Begin} (h : TreeNodes t T L)
    (h' : TreeNodes t T L') : L = L' := by
  have := h.walk.symm.trans h'.walk
  cases this; rfl

/-- The offsets of the begin-node tokens of a tree. -/
theorem TreeNodes.offsets {t : fdt.Fdt} {T : Fdt} {L : List Begin} (h : TreeNodes t T L) :
    offsetsOf t = L.map (·.offset) :=
  offsets_of_nodesFrom (beginOffsets (bytesOf t.structure) (bytesOf t.strings))
    (fun _ => rfl) (fun _ _ => rfl) h.walk

/-- A tree has as many begin-node tokens as records. -/
theorem TreeNodes.length {t : fdt.Fdt} {T : Fdt} {L : List Begin} (h : TreeNodes t T L) :
    L.length = T.records.size := h.begins.1

/-- A node of the code of a tree stands for the node of index `k` exactly when
it stands for the `k`-th begin-node token of the tree. -/
theorem TreeNodes.nodeRepr_iff {t : fdt.Fdt} {T : Fdt} {L : List Begin} (h : TreeNodes t T L)
    (a : fdt.NodeAt) (k : Nat) (hk : k < T.records.size) :
    NodeRepr ⟨t, a⟩ ⟨T, ⟨k, hk⟩⟩ ↔ AtRepr a (L[k]'(h.length ▸ hk)) := by
  have hkL : k < L.length := h.length ▸ hk
  obtain ⟨hn, hp⟩ := h.begins.2 k hkL hk
  simp only [NodeRepr, AtRepr, h.offsets, List.getElem?_map, List.getElem?_eq_getElem hkL,
    Option.map_some, Option.some.injEq, Node.name, Node.record, hn, hp, Fin.getElem_fin]
  constructor
  · rintro ⟨-, h1, h2, h3, h4, h5⟩
    exact ⟨h1.symm, h5, by omega, by omega, by rw [h4, h3, h2, h1]⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨h.repr, h1.symm, by omega, by omega, by rw [h5, h4], h2⟩

/-! ## The iterator of the nodes -/

/-- An iterator of the nodes of a tree stands for the nodes from index `k` on:
its walker stands for open nodes whose walk of `nodesFrom` gives the
begin-node tokens from index `k` on. -/
def NodesAt (t : fdt.Fdt) (T : Fdt) (L : List Begin) (s : fdt.Nodes) (l : List Node) : Prop :=
  s.tree = t ∧ ∃ k f st, l = T.nodes.drop k ∧ f ≤ MAX_TOKENS.toNat ∧ WalkerRepr s.walker st ∧
    nodesFrom (bytesOf t.structure) (bytesOf t.strings) f s.walker.cursor.val st = some (L.drop k)

/-- `Nodes::next()` from an iterator that stands for the nodes from index `k`
on, as `stands_of_sim` takes it. -/
theorem nodes_next_sim {t : fdt.Fdt} {T : Fdt} {L : List Begin} (ht : TreeNodes t T L) :
    (∀ s, NodesAt t T L s [] → fdt.nodes.Nodes.next s ⦃ o s' =>
      o = none ∧ fdt.nodes.Nodes.next s' = .ok (none, s') ⦄) ∧
    (∀ s b l, NodesAt t T L s (b :: l) → fdt.nodes.Nodes.next s ⦃ o s' =>
      ∃ a, o = some a ∧ NodeRepr a b ∧ NodesAt t T L s' l ⦄) := by
  constructor
  · rintro s ⟨rfl, k, f, st, hl, hf, hw, hL⟩
    have hk := nodes_drop_nil hl
    rw [List.drop_of_length_le (by rw [ht.length]; exact hk)] at hL
    unfold fdt.nodes.Nodes.next
    step with node_step_spec s.tree.structure (bytesOf s.tree.strings) s.walker f st [] ht.size hw hf hL
    obtain ⟨-, hnone, e, hend⟩ := walker_post
    dsimp only at hnone hend
    subst hnone
    step*
    refine ⟨by simpa using o_post, ?_⟩
    rw [node_step_end s.tree.structure _ walker ht.size hend]
    simp [fdt.nodes.node_of]
  · rintro s b l ⟨rfl, k, f, st, hl, hf, hw, hL⟩
    obtain ⟨hk, rfl, rfl⟩ := nodes_drop_cons hl
    have hkL : k < L.length := ht.length ▸ hk
    rw [List.drop_eq_getElem_cons hkL] at hL
    unfold fdt.nodes.Nodes.next
    step with node_step_spec s.tree.structure (bytesOf s.tree.strings) s.walker f st _ ht.size hw hf hL
    obtain ⟨⟨f', st', hf', hw', hL'⟩, a, ha, hat⟩ := walker_post
    dsimp only at ha hL' hw'
    subst ha
    step*
    exact ⟨_, by simpa using o_post, (ht.nodeRepr_iff a k hk).2 hat, rfl, k + 1, f', st', rfl, hf',
      hw', hL'⟩

/-- `Fdt::nodes()`: an iterator that stands for the nodes of the tree in the
order of the structure block. -/
theorem fdt_nodes_spec (hu : Usize64) (t : fdt.Fdt) (T : Fdt) (h : FdtRepr t T) :
    fdt.nodes.Fdt.nodes t ⦃ it => Stands fdt.nodes.Nodes.next NodeRepr it T.nodes ⦄ := by
  obtain ⟨L, ht⟩ := treeNodes_of_repr hu h
  obtain ⟨hnil, hcons⟩ := nodes_next_sim ht
  unfold fdt.nodes.Fdt.nodes
  simp only [spec_ok]
  refine stands_of_sim (NodesAt t T L) hnil hcons _ _
    ⟨rfl, 0, MAX_TOKENS.toNat, [], by simp, Nat.le_refl _, start_repr.1, ?_⟩
  rw [start_repr.2]; exact ht.walk

/-! ## The name and the parent of a node -/

/-- The bytes of a range of a slice. -/
theorem bytesOf_of_slice {s s1 : Slice U8} {a b : Nat} (h : s1.val = s.val.slice a b) :
    bytesOf s1 = (bytesOf s).extract a b := by
  rw [byteArray_eq_iff, bytesOf_toList, bytesOf_extract, h]
  rfl

/-- What a node of the code that stands for a node of the specification
tells: its tree has the begin-node tokens `L`, the node stands for the token of
its index, which `decodeToken` reads with the name of the node. -/
theorem nodeRepr_begin (hu : Usize64) {n : fdt.Node} {N : Node} (h : NodeRepr n N) :
    ∃ L, TreeNodes n.tree N.fdt L ∧ ∃ hk : N.index.val < L.length,
      AtRepr n.at L[N.index.val] ∧ L[N.index.val].name = N.name ∧
      ∃ next, decodeToken (bytesOf n.tree.structure) (bytesOf n.tree.strings) L[N.index.val].offset =
        .ok (.beginNode N.name, next) := by
  obtain ⟨L, ht⟩ := treeNodes_of_repr hu h.1
  obtain ⟨tree, a⟩ := n
  obtain ⟨T, ⟨k, hk⟩⟩ := N
  have hkL : k < L.length := ht.length ▸ hk
  have hat := (ht.nodeRepr_iff a k hk).1 h
  have hn : L[k].name = (⟨T, ⟨k, hk⟩⟩ : Node).name := (ht.begins.2 k hkL hk).1
  obtain ⟨next, hd⟩ := nodesFrom_mem ht.walk L[k] (List.getElem_mem hkL)
  exact ⟨L, ht, hkL, hat, hn, next, hn ▸ hd⟩

/-- `Node::name()`: the bytes of the name of the node. -/
theorem node_name_spec (hu : Usize64) (n : fdt.Node) (N : Node) (h : NodeRepr n N) :
    fdt.nodes.Node.name n ⦃ b => bytesOf b = N.name.toUTF8 ⦄ := by
  obtain ⟨L, ht, hk, ⟨-, -, h3, h4, -⟩, hn, next, hd⟩ := nodeRepr_begin hu h
  obtain ⟨hnext, hex, hle⟩ := decodeToken_begin hd
  have := le_align4 (L[N.index.val].offset + 4 + N.name.utf8ByteSize + 1)
  rw [bytesOf_size] at hle
  rw [hn] at h4
  unfold fdt.nodes.Node.name
  step*
  rw [bytesOf_of_slice b_post, h3, h4, hex, String.toUTF8_eq_toByteArray]

/-- The loop of `node_at_offset`: the first node from the walker on whose
begin-node token lies at `offset`. -/
theorem node_at_offset_loop_spec («structure» : Slice U8) (strs : ByteArray) (offset : Usize)
    (L : List Begin) (hsz : «structure».length + 2 ^ 32 ≤ Usize.max)
    (hlen : L.length < MAX_TOKENS.toNat) (w : fdt.Walker) (count : Usize) (f : Nat)
    (st : List Nat) (hw : WalkerRepr w st) (hf : f ≤ MAX_TOKENS.toNat)
    (hc : count.val ≤ L.length) (hne : ∀ b ∈ L.take count.val, b.offset ≠ offset.val)
    (hL : nodesFrom (bytesOf «structure») strs f w.cursor.val st = some (L.drop count.val)) :
    fdt.nodes.node_at_offset_loop «structure» offset w count ⦃ o =>
      OptionRel AtRepr o (L.find? (·.offset = offset.val)) ⦄ := by
  have hfind : ∀ c, (∀ b ∈ L.take c, b.offset ≠ offset.val) →
      L.find? (·.offset = offset.val) = (L.drop c).find? (·.offset = offset.val) := by
    intro c hc
    conv => lhs; rw [← List.take_append_drop c L]
    rw [List.find?_append, List.find?_eq_none.2 (by simpa using hc)]
    rfl
  unfold fdt.nodes.node_at_offset_loop
  apply loop.spec_decr_nat
    (measure := fun (x : fdt.Walker × Usize) => L.length - x.2.val)
    (inv := fun (x : fdt.Walker × Usize) => ∃ f st, WalkerRepr x.1 st ∧ f ≤ MAX_TOKENS.toNat ∧
      x.2.val ≤ L.length ∧ (∀ b ∈ L.take x.2.val, b.offset ≠ offset.val) ∧
      nodesFrom (bytesOf «structure») strs f x.1.cursor.val st = some (L.drop x.2.val))
  · rintro ⟨w, count⟩ ⟨f, st, hw, hf, hc, hne, hL⟩
    simp only at hw hc hne hL
    unfold fdt.nodes.node_at_offset_loop.body
    step
    rw [show MAX_TOKENS.toNat = 65536 from rfl] at r_post hlen
    refine ite_spec_pos (by scalar_tac) ?_
    rcases Nat.lt_or_ge count.val L.length with hlt | hge
    · rw [List.drop_eq_getElem_cons hlt] at hL
      step with node_step_spec «structure» strs w f st _ hsz hw hf hL
      obtain ⟨⟨f', st', hf', hw', hL'⟩, a, ha, hat⟩ := next_post
      dsimp only at ha hL' hw'
      subst ha
      simp only
      split
      · rename_i heq
        simp only [spec_ok]
        rw [hfind count.val hne, List.drop_eq_getElem_cons hlt, List.find?_cons,
          show decide (L[count.val].offset = offset.val) = true by
            simp only [decide_eq_true_eq, ← hat.1, heq]]
        exact hat
      · rename_i hne'
        step*
        refine ⟨⟨f', st', hw', hf', by scalar_tac, ?_, by simpa [count1_post] using hL'⟩, by scalar_tac⟩
        rw [count1_post, List.take_add_one, List.getElem?_eq_getElem hlt]
        intro b hb
        rcases List.mem_append.1 hb with hb | hb
        · exact hne b hb
        · simp only [Option.toList_some, List.mem_singleton] at hb
          subst hb
          rw [← hat.1]
          exact fun h => hne' (UScalar.eq_of_val_eq h)
    · rw [List.drop_of_length_le hge] at hL
      step with node_step_spec «structure» strs w f st [] hsz hw hf hL
      obtain ⟨-, hnone, -⟩ := next_post
      dsimp only at hnone
      subst hnone
      simp only [spec_ok]
      rw [hfind count.val hne, List.drop_of_length_le hge]
      trivial
  · exact ⟨f, st, hw, hf, hc, hne, hL⟩

/-- `node_at_offset(structure, offset)`: the node whose begin-node token lies
at `offset`, the first such of the walk from the first token. -/
theorem node_at_offset_spec («structure» : Slice U8) (strs : ByteArray) (offset : Usize)
    (L : List Begin) (hsz : «structure».length + 2 ^ 32 ≤ Usize.max)
    (hL : nodesFrom (bytesOf «structure») strs MAX_TOKENS.toNat 0 [] = some L) :
    fdt.nodes.node_at_offset «structure» offset ⦃ o =>
      OptionRel AtRepr o (L.find? (·.offset = offset.val)) ⦄ :=
  node_at_offset_loop_spec «structure» strs offset L hsz (nodesFrom_sorted hL).2.2 _ 0#usize
    MAX_TOKENS.toNat [] start_repr.1 (Nat.le_refl _) (by simp) (by simp)
    (by rw [start_repr.2]; simpa using hL)

/-- `parent_at(structure, node)`: the node whose begin-node token lies at the
offset of the parent of `node`, none without a parent. -/
theorem parent_at_spec («structure» : Slice U8) (strs : ByteArray) (node : fdt.NodeAt)
    (L : List Begin) (hsz : «structure».length + 2 ^ 32 ≤ Usize.max)
    (hL : nodesFrom (bytesOf «structure») strs MAX_TOKENS.toNat 0 [] = some L) :
    fdt.nodes.parent_at «structure» node ⦃ o =>
      OptionRel AtRepr o (node.parent.bind fun p => L.find? (·.offset = p.val)) ⦄ := by
  unfold fdt.nodes.parent_at
  cases node.parent with
  | none => simp
  | some p => exact node_at_offset_spec «structure» strs p L hsz hL

/-- `Node::parent()`: the parent of the node, none for the root. -/
theorem node_parent_spec (hu : Usize64) (n : fdt.Node) (N : Node) (h : NodeRepr n N) :
    fdt.nodes.Node.parent n ⦃ o => OptionRel NodeRepr o N.parent ⦄ := by
  obtain ⟨L, ht, hkL, hat, -, -⟩ := nodeRepr_begin hu h
  obtain ⟨tree, a⟩ := n
  obtain ⟨T, ⟨k, hk⟩⟩ := N
  dsimp only at ht hkL hat ⊢
  have hpar := hat.2.1
  rw [(ht.begins.2 k hkL hk).2] at hpar
  unfold fdt.nodes.Node.parent
  step with parent_at_spec tree.structure (bytesOf tree.strings) a L ht.size ht.walk as ⟨op, hop⟩
  step*
  subst o_post
  simp only [Node.parent, Node.record, Fin.getElem_fin]
  cases hp : T.records[k].parent with
  | none =>
    rw [hp] at hpar
    have ha : a.parent = none := by simpa using hpar
    rw [ha] at hop
    cases op with
    | none => trivial
    | some x => exact hop.elim
  | some p =>
    rw [hp] at hpar
    by_cases hps : p < T.records.size
    · have hpL : p < L.length := ht.length ▸ hps
      rw [Option.bind_some, List.getElem?_eq_getElem hpL, Option.map_some] at hpar
      obtain ⟨q, hq, hqv⟩ := Option.map_eq_some_iff.1 hpar
      rw [hq, Option.bind_some, hqv, find?_offset (nodesFrom_sorted ht.walk).2.1 hpL] at hop
      cases op with
      | none => exact hop.elim
      | some x =>
        simp only [hps, ↓reduceDIte, Option.map_some, optionRel_some_some]
        exact (ht.nodeRepr_iff x p hps).2 hop
    · have hlen := ht.length
      rw [Option.bind_some, List.getElem?_eq_none (by omega), Option.map_none] at hpar
      have ha : a.parent = none := by simpa using hpar
      rw [ha] at hop
      cases op with
      | none => simp [hps]
      | some x => exact hop.elim

/-! ## Paths -/

/-- The byte at an index of the bytes of a slice. -/
theorem map_byte_getElem! (s : Slice U8) (j : Nat) (hj : j < s.length) :
    (s.val.map byte)[j]! = byte s.val[j]! := by
  rw [getElem!_pos _ j (by simpa using hj), List.getElem_map, getElem!_pos s.val j hj]

/-- `component_end(path, start)`: the index of the first `/` from `start` on,
or the end of the path. -/
@[step] theorem component_end_spec (path : Slice U8) (start : Usize) (h : start.val ≤ path.length) :
    fdt.nodes.component_end path start ⦃ e => start.val ≤ e.val ∧ e.val ≤ path.length ∧
      (∀ j, start.val ≤ j → j < e.val → (path.val[j]!).val ≠ 47) ∧
      (e.val = path.length ∨ (path.val[e.val]!).val = 47) ⦄ := by
  unfold fdt.nodes.component_end fdt.nodes.component_end_loop
  apply loop.spec_decr_nat
    (measure := fun (i : Usize) => path.length - i.val)
    (inv := fun (i : Usize) => start.val ≤ i.val ∧ i.val ≤ path.length ∧
      ∀ j, start.val ≤ j → j < i.val → (path.val[j]!).val ≠ 47)
  · rintro i ⟨h1, h2, h3⟩
    unfold fdt.nodes.component_end_loop.body
    step*
    · refine ⟨h1, h2, h3, Or.inr ?_⟩
      rw [← getElem_eq_getElem! rfl (by scalar_tac), ← i1_post, ‹i1 = 47#u8›]; rfl
    · refine ⟨by omega, by scalar_tac, fun j hj1 hj2 => ?_, by scalar_tac⟩
      rcases Nat.lt_or_ge j i.val with hj | hj
      · exact h3 j hj1 hj
      · have : j = i.val := by scalar_tac
        subst this
        rw [← getElem_eq_getElem! rfl (by scalar_tac), ← i1_post]
        exact fun h => ‹¬i1 = 47#u8› (UScalar.eq_of_val_eq h)
  · exact ⟨Nat.le_refl _, h, fun j h1 h2 => absurd h2 (by omega)⟩

/-- A byte of the code is `/` exactly when it is 47. -/
theorem slash_beq (x : U8) : (byte x == 47) = decide (x = 47#u8) := by
  have : byte x = 47 ↔ x = 47#u8 := by
    rw [byte_eq_iff]
    exact ⟨fun h => UScalar.eq_of_val_eq h, fun h => by rw [h]; rfl⟩
  by_cases h : x = 47#u8
  · rw [decide_eq_true h]; exact beq_iff_eq.2 (this.2 h)
  · rw [decide_eq_false h]; exact beq_false_of_ne fun e => h (this.1 e)

/-- `double_slash(path)`: whether the path holds `//`. -/
@[step] theorem double_slash_spec (path : Slice U8) :
    fdt.nodes.double_slash path ⦃ b => b = doubleSlashB (path.val.map byte) ⦄ := by
  unfold fdt.nodes.double_slash fdt.nodes.double_slash_loop
  have hl : (path.val.map byte).length = path.length := List.length_map _
  apply loop.spec_decr_nat
    (measure := fun (i : Usize) => path.length - i.val)
    (inv := fun (i : Usize) => 1 ≤ i.val ∧
      doubleSlashB ((path.val.map byte).drop (i.val - 1)) = doubleSlashB (path.val.map byte))
  · rintro i ⟨h1, h2⟩
    unfold fdt.nodes.double_slash_loop.body
    step*
    · rw [← h2, ← i1_post, doubleSlashB_drop' (P := path.val.map byte)
        (show i1.val + 1 = i.val by scalar_tac) (by scalar_tac)]
      simp only [List.getElem_map, ← i2_post, ← i3_post, slash_beq, ‹i2 = 47#u8›, ‹i3 = 47#u8›]
      rfl
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [← h2, ← i1_post, doubleSlashB_drop' (P := path.val.map byte)
        (show i1.val + 1 = i.val by scalar_tac) (by scalar_tac), index1_post, Nat.add_sub_cancel]
      simp only [List.getElem_map, ← i2_post, ← i3_post, slash_beq, ‹¬i3 = 47#u8›]
      simp
    · refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [← h2, ← i1_post, doubleSlashB_drop' (P := path.val.map byte)
        (show i1.val + 1 = i.val by scalar_tac) (by scalar_tac), index1_post, Nat.add_sub_cancel]
      simp only [List.getElem_map, ← i2_post, slash_beq, ‹¬i2 = 47#u8›]
      simp
    · rw [← h2, doubleSlashB_short (by simp; scalar_tac)]
  · exact ⟨by simp, by simp⟩

/-- `path_valid(path)`: whether the path has the form that `Fdt::find_node`
takes, on its bytes. -/
@[step] theorem path_valid_spec (path : Slice U8) :
    fdt.nodes.path_valid path ⦃ b => b = pathValidB (path.val.map byte) ⦄ := by
  unfold fdt.nodes.path_valid
  have hl : (path.val.map byte).length = path.length := List.length_map _
  step*
  · rw [pathValidB]
    have : path.val = [] := List.length_eq_zero_iff.1 (by scalar_tac)
    simp [this]
  · have hpos : 0 < path.length := by scalar_tac
    rw [pathValidB, List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega), List.getElem_map,
      ← i_post]
    simp only [Option.some_beq_some, slash_beq]
    rw [decide_eq_false fun h => (bne_iff_ne.1 ‹(i != 47#u8) = true›) h]; rfl
  all_goals
    have hpos : 0 < path.length := by scalar_tac
    have hi : i = 47#u8 := by
      have := ‹¬(i != 47#u8) = true›
      rwa [bne_iff_ne, ne_eq, Decidable.not_not] at this
    have hh : (path.val.map byte).head? = some 47 := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega), List.getElem_map, ← i_post,
        hi]; rfl
    simp only [pathValidB, hh, beq_self_eq_true, Bool.true_and]
  · have e : (path.val.map byte).getLast? = some (byte i4) := by
      rw [List.getLast?_eq_getElem?, List.getElem?_map, i4_post, List.length_map,
        show path.val.length - 1 = i3.val by scalar_tac, List.getElem?_eq_getElem (by scalar_tac)]
      rfl
    have hlen : 1 < (path.val.map byte).length := by rw [hl]; scalar_tac
    simp only [e, Option.some_beq_some, slash_beq, ‹i4 = 47#u8›, decide_true, hlen,
      Bool.and_self, Bool.not_true, Bool.false_and]
  · have e : (path.val.map byte).getLast? = some (byte i4) := by
      rw [List.getLast?_eq_getElem?, List.getElem?_map, i4_post, List.length_map,
        show path.val.length - 1 = i3.val by scalar_tac, List.getElem?_eq_getElem (by scalar_tac)]
      rfl
    simp only [e, Option.some_beq_some, slash_beq, ‹¬i4 = 47#u8›, decide_false, Bool.and_false,
      Bool.not_false, Bool.true_and, b1_post]
    simp
  · have hlen : ¬ 1 < (path.val.map byte).length := by rw [hl]; scalar_tac
    simp only [hlen, decide_false, Bool.false_and, Bool.not_false, Bool.true_and, b1_post]
    simp

/-! ## The lookup -/

/-- `is_child(node, parent)`: whether the parent of `node` is at `parent`. -/
@[step] theorem is_child_spec (node : fdt.NodeAt) (parent : Usize) :
    fdt.nodes.is_child node parent ⦃ b => b = decide (node.parent = some parent) ⦄ := by
  unfold fdt.nodes.is_child
  cases node.parent <;> simp

/-- The test of `is_child` on two nodes of a tree is `Node.isChildOf`. -/
theorem TreeNodes.child_iff {t : fdt.Fdt} {T : Fdt} {L : List Begin} (ht : TreeNodes t T L)
    {k p : Nat} (hk : k < T.records.size) (hp : p < T.records.size) {a pa : fdt.NodeAt}
    (ha : AtRepr a (L[k]'(ht.length ▸ hk))) (hpa : AtRepr pa (L[p]'(ht.length ▸ hp))) :
    decide (a.parent = some pa.offset) = (⟨T, ⟨k, hk⟩⟩ : Node).isChildOf ⟨T, ⟨p, hp⟩⟩ := by
  have hkL : k < L.length := ht.length ▸ hk
  have hpL : p < L.length := ht.length ▸ hp
  have hiff := parent_offset_iff ht.begins (nodesFrom_sorted ht.walk).2.1 hkL hpL
  have e : a.parent = some pa.offset ↔ L[k].parent = some L[p].offset := by
    rw [← ha.2.1, ← hpa.1]
    cases a.parent with
    | none => simp
    | some q => simp only [Option.map_some, Option.some.injEq]; exact ⟨fun h => h ▸ rfl, UScalar.eq_of_val_eq⟩
  simp only [Node.isChildOf, Node.record, Fin.getElem_fin]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, e, hiff, beq_iff_eq]

/-- The test of `same_bytes` of the name of a node of a tree with a slice is the
comparison of the bytes of its name. -/
theorem TreeNodes.name_eq {t : fdt.Fdt} {T : Fdt} {L : List Begin} (ht : TreeNodes t T L)
    {k : Nat} (hk : k < T.records.size) {a : fdt.NodeAt} (ha : AtRepr a (L[k]'(ht.length ▸ hk)))
    («name» : Slice U8) :
    decide (a.name_start.val ≤ a.name_end.val ∧ a.name_end.val ≤ t.structure.length ∧
      (bytesOf t.structure).extract a.name_start.val a.name_end.val = bytesOf «name») =
      ((⟨T, ⟨k, hk⟩⟩ : Node).name.toUTF8.toList == «name».val.map byte) := by
  have hkL : k < L.length := ht.length ▸ hk
  obtain ⟨next, hd⟩ := nodesFrom_mem ht.walk L[k] (List.getElem_mem hkL)
  obtain ⟨hnext, hex, hle⟩ := decodeToken_begin hd
  have := le_align4 (L[k].offset + 4 + L[k].name.utf8ByteSize + 1)
  rw [bytesOf_size] at hle
  have hn : L[k].name = (⟨T, ⟨k, hk⟩⟩ : Node).name := (ht.begins.2 k hkL hk).1
  rw [hn] at hex hnext this
  rw [ha.2.2.1, ha.2.2.2.1, hn, hex]
  by_cases h : (⟨T, ⟨k, hk⟩⟩ : Node).name.toByteArray = bytesOf «name»
  · rw [decide_eq_true ⟨by omega, by omega, h⟩]
    rw [String.toUTF8_eq_toByteArray, h, bytesOf_toList]; simp
  · rw [decide_eq_false fun h' => h h'.2.2]
    refine (beq_false_of_ne fun e => h ?_).symm
    rw [byteArray_eq_iff, bytesOf_toList, ← e, String.toUTF8_eq_toByteArray]

/-- `first_node(structure)`: the root of the tree. -/
theorem first_node_spec {t : fdt.Fdt} {T : Fdt} {L : List Begin} (ht : TreeNodes t T L) :
    fdt.nodes.first_node t.structure ⦃ o => OptionRel (fun a N => NodeRepr ⟨t, a⟩ N) o T.root ⦄ := by
  unfold fdt.nodes.first_node
  step with node_step_spec t.structure (bytesOf t.strings) _ MAX_TOKENS.toNat [] L ht.size
    start_repr.1 (Nat.le_refl _) (by rw [start_repr.2]; exact ht.walk)
  have hpost := ‹StepPost _ _ _ _›
  have hlen := ht.length
  cases L with
  | nil =>
    obtain ⟨-, hnone, -⟩ := hpost
    dsimp only at hnone
    subst hnone
    have : ¬ 0 < T.records.size := by rw [← hlen]; exact Nat.lt_irrefl 0
    simp [Fdt.root, this]
  | cons b L =>
    obtain ⟨-, a, ha, hat⟩ := hpost
    dsimp only at ha
    subst ha
    have h0 : 0 < T.records.size := by rw [← hlen]; exact Nat.succ_pos _
    simp only [Fdt.root, h0, ↓reduceDIte, optionRel_some_some]
    exact (ht.nodeRepr_iff a 0 h0).2 hat

/-- The loop of `child_named`: the child of the node at `parent` whose name
has the bytes of `name`, among the nodes from the walker on, after `found`. -/
theorem child_named_loop_spec {t : fdt.Fdt} {T : Fdt} {L : List Begin} (ht : TreeNodes t T L)
    {p : Nat} (hp : p < T.records.size) {pa : fdt.NodeAt} (hpa : AtRepr pa (L[p]'(ht.length ▸ hp)))
    («name» : Slice U8) (w : fdt.Walker) (found : Option fdt.NodeAt) (seen : Bool) (count : Usize)
    (f : Nat) (st : List Nat) (fN : Option Node) (hw : WalkerRepr w st) (hf : f ≤ MAX_TOKENS.toNat)
    (hc : count.val ≤ L.length)
    (hL : nodesFrom (bytesOf t.structure) (bytesOf t.strings) f w.cursor.val st =
      some (L.drop count.val))
    (hfound : OptionRel (fun a N => NodeRepr ⟨t, a⟩ N) found fN) (hseen : seen = fN.isSome) :
    fdt.nodes.child_named_loop t.structure pa.offset «name» w found seen count ⦃ r =>
      Agrees (OptionRel (fun a N => NodeRepr ⟨t, a⟩ N)) errorOf r
        (scanChild (childPred ⟨T, ⟨p, hp⟩⟩ («name».val.map byte)) (T.nodes.drop count.val) fN) ⦄ := by
  have hlen := ht.length
  have hmax : L.length < MAX_TOKENS.toNat := (nodesFrom_sorted ht.walk).2.2
  rw [show MAX_TOKENS.toNat = 65536 from rfl] at hmax
  unfold fdt.nodes.child_named_loop
  apply loop.spec_decr_nat
    (measure := fun (x : fdt.Walker × Option fdt.NodeAt × Bool × Usize) => L.length - x.2.2.2.val)
    (inv := fun (x : fdt.Walker × Option fdt.NodeAt × Bool × Usize) => ∃ f st fN',
      WalkerRepr x.1 st ∧ f ≤ MAX_TOKENS.toNat ∧ x.2.2.2.val ≤ L.length ∧
      nodesFrom (bytesOf t.structure) (bytesOf t.strings) f x.1.cursor.val st =
        some (L.drop x.2.2.2.val) ∧
      OptionRel (fun a N => NodeRepr ⟨t, a⟩ N) x.2.1 fN' ∧ x.2.2.1 = fN'.isSome ∧
      scanChild (childPred ⟨T, ⟨p, hp⟩⟩ («name».val.map byte)) (T.nodes.drop x.2.2.2.val) fN' =
        scanChild (childPred ⟨T, ⟨p, hp⟩⟩ («name».val.map byte)) (T.nodes.drop count.val) fN)
  · rintro ⟨w, found, seen, count⟩ ⟨f, st, fN', hw, hf, hc, hL, hfound, hseen, hans⟩
    simp only at hw hc hL hfound hseen hans
    unfold fdt.nodes.child_named_loop.body
    step
    rw [show MAX_TOKENS.toNat = 65536 from rfl] at r_post
    refine ite_spec_pos (by scalar_tac) ?_
    rcases Nat.lt_or_ge count.val L.length with hlt | hge
    · have hk : count.val < T.records.size := by omega
      rw [List.drop_eq_getElem_cons hlt] at hL
      have hdrop : T.nodes.drop count.val = ⟨T, ⟨count.val, hk⟩⟩ :: T.nodes.drop (count.val + 1) := by
        rw [List.drop_eq_getElem_cons (by rw [nodes_length]; exact hk), nodes_getElem]
      rw [hdrop] at hans
      simp only [scanChild] at hans
      step with node_step_spec t.structure (bytesOf t.strings) w f st _ ht.size hw hf hL
      obtain ⟨⟨f', st', hf', hw', hL'⟩, a, ha, hat⟩ := next_post
      dsimp only at ha hL' hw'
      subst ha
      simp only
      step
      have hchild := ht.child_iff hk hp hat hpa
      have hnm := ht.name_eq hk hat «name»
      simp only [childPred] at hans
      by_cases hb : b = true
      · refine ite_spec_pos hb ?_
        have hc1 : (⟨T, ⟨count.val, hk⟩⟩ : Node).isChildOf ⟨T, ⟨p, hp⟩⟩ = true := by
          rw [← hchild, ← b_post]; exact hb
        simp only [hc1, Bool.true_and] at hans
        step
        rw [hnm] at b1_post
        by_cases hb1 : b1 = true
        · refine ite_spec_pos hb1 ?_
          simp only [← b1_post, hb1, ↓reduceIte] at hans
          by_cases hs : seen = true
          · refine ite_spec_pos hs ?_
            cases fN' with
            | none => simp [hs] at hseen
            | some m =>
              simp only [spec_ok]
              rw [← hans]; rfl
          · refine ite_spec_neg hs ?_
            cases fN' with
            | some m => simp [hs] at hseen
            | none =>
              simp only at hans
              step
              refine ⟨⟨f', st', some ⟨T, ⟨count.val, hk⟩⟩, hw', hf', by scalar_tac,
                by simpa [count1_post] using hL', (ht.nodeRepr_iff a count.val hk).2 hat, rfl,
                by rw [count1_post]; exact hans⟩, by scalar_tac⟩
        · refine ite_spec_neg hb1 ?_
          simp only [← b1_post, hb1, Bool.false_eq_true, ↓reduceIte] at hans
          step
          refine ⟨⟨f', st', fN', hw', hf', by scalar_tac, by simpa [count1_post] using hL', hfound,
            hseen, by rw [count1_post]; exact hans⟩, by scalar_tac⟩
      · refine ite_spec_neg hb ?_
        have hc1 : (⟨T, ⟨count.val, hk⟩⟩ : Node).isChildOf ⟨T, ⟨p, hp⟩⟩ = false := by
          rw [← hchild, ← b_post]; simpa using hb
        simp only [hc1, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hans
        step
        refine ⟨⟨f', st', fN', hw', hf', by scalar_tac, by simpa [count1_post] using hL', hfound,
          hseen, by rw [count1_post]; exact hans⟩, by scalar_tac⟩
    · rw [List.drop_of_length_le hge] at hL
      step with node_step_spec t.structure (bytesOf t.strings) w f st [] ht.size hw hf hL
      obtain ⟨-, hnone, -⟩ := next_post
      dsimp only at hnone
      subst hnone
      simp only [spec_ok]
      rw [List.drop_of_length_le (by rw [nodes_length]; omega), scanChild] at hans
      rw [← hans]
      exact hfound
  · exact ⟨f, st, fN, hw, hf, hc, hL, hfound, hseen, rfl⟩

/-- `child_named(structure, parent, path, start, end)`: the child of the node at
`parent` whose name has the bytes `[start, end)` of the path. -/
theorem child_named_spec {t : fdt.Fdt} {T : Fdt} {L : List Begin} (ht : TreeNodes t T L)
    {p : Nat} (hp : p < T.records.size) {pa : fdt.NodeAt} (hpa : AtRepr pa (L[p]'(ht.length ▸ hp)))
    (path : Slice U8) (start «end» : Usize) (h0 : start.val ≤ «end».val)
    (h1 : «end».val ≤ path.length) :
    fdt.nodes.child_named t.structure pa.offset path start «end» ⦃ r =>
      Agrees (OptionRel (fun a N => NodeRepr ⟨t, a⟩ N)) errorOf r
        (scanChild (childPred ⟨T, ⟨p, hp⟩⟩ (((path.val.map byte).drop start.val).take
          («end».val - start.val))) T.nodes none) ⦄ := by
  unfold fdt.nodes.child_named
  step*
  have e : «name».val.map byte = ((path.val.map byte).drop start.val).take («end».val - start.val) := by
    rw [name_post, List.slice, List.map_take, List.map_drop]
  rw [← e]
  exact child_named_loop_spec ht hp hpa «name» _ none false 0#usize MAX_TOKENS.toNat [] none
    start_repr.1 (Nat.le_refl _) (Nat.zero_le _) (by rw [start_repr.2]; simpa using ht.walk) trivial rfl

/-- Two trees of the specification that a tree of the code stands for are one. -/
theorem fdtRepr_unique {t : fdt.Fdt} {T T' : Fdt} (h : FdtRepr t T) (h' : FdtRepr t T') : T = T' := by
  have := h.1.symm.trans h'.1
  cases this; rfl

/-- A node of the code of a tree that stands for a node stands for one of the
tree, of the token of its index. -/
theorem TreeNodes.of_nodeRepr {t : fdt.Fdt} {T : Fdt} {L : List Begin} (ht : TreeNodes t T L)
    {a : fdt.NodeAt} {N : Node} (h : NodeRepr ⟨t, a⟩ N) :
    ∃ k, ∃ hk : k < T.records.size, N = ⟨T, ⟨k, hk⟩⟩ ∧ AtRepr a (L[k]'(ht.length ▸ hk)) := by
  obtain ⟨T', ⟨k, hk⟩⟩ := N
  obtain rfl := fdtRepr_unique ht.repr h.1
  exact ⟨k, hk, rfl, (ht.nodeRepr_iff a k hk).1 h⟩

/-- The byte at an index of the bytes from `i` on of a slice. -/
theorem drop_map_byte_getElem! (s : Slice U8) (i j : Nat) :
    ((s.val.map byte).drop i)[j]! = byte s.val[i + j]! := by
  rcases Nat.lt_or_ge (i + j) s.val.length with h | h
  · rw [getElem!_pos _ j (by simp; omega), List.getElem_drop, List.getElem_map,
      getElem!_pos s.val (i + j) h]
  · rw [getElem!_neg _ j (by simp; omega), getElem!_neg s.val (i + j) (by omega)]; rfl

/-- The loop of `descend`: from the component at `start`, the node that the
components of the path lead to from `current`. -/
theorem descend_loop_spec {t : fdt.Fdt} {T : Fdt} {L : List Begin} (ht : TreeNodes t T L)
    (path : Slice U8) (hpl : path.length < Usize.max) (start : Usize)
    (current : Option fdt.NodeAt) (curN : Option Node)
    (hcur : OptionRel (fun a N => NodeRepr ⟨t, a⟩ N) current curN)
    (hs : start.val ≤ path.length + 1) :
    fdt.nodes.descend_loop t.structure path start current ⦃ r =>
      Agrees (OptionRel (fun a N => NodeRepr ⟨t, a⟩ N)) errorOf r
        (if start.val ≤ path.length then descendB T (splitB ((path.val.map byte).drop start.val)) curN
         else .ok curN) ⦄ := by
  unfold fdt.nodes.descend_loop
  apply loop.spec_decr_nat
    (measure := fun (x : Usize × Option fdt.NodeAt) => path.length + 1 - x.1.val)
    (inv := fun (x : Usize × Option fdt.NodeAt) => ∃ cN,
      OptionRel (fun a N => NodeRepr ⟨t, a⟩ N) x.2 cN ∧ x.1.val ≤ path.length + 1 ∧
      (if x.1.val ≤ path.length then descendB T (splitB ((path.val.map byte).drop x.1.val)) cN
         else .ok cN) =
      (if start.val ≤ path.length then descendB T (splitB ((path.val.map byte).drop start.val)) curN
         else .ok curN))
  · rintro ⟨start, current⟩ ⟨cN, hcur, hs, hans⟩
    simp only at hcur hs hans
    unfold fdt.nodes.descend_loop.body
    step*
    · -- no node so far
      cases cN with
      | some _ => rw [‹current = none›] at hcur; exact hcur.elim
      | none =>
        rw [← hans]
        simp only [show start.val ≤ path.length by scalar_tac, ↓reduceIte]
        obtain ⟨c, cs, hc⟩ := List.exists_cons_of_ne_nil (splitB_ne_nil ((path.val.map byte).drop start.val))
        rw [hc, descendB]; trivial
    · -- a node so far
      rename_i node hnode
      rw [hnode] at hcur
      cases cN with
      | none => exact hcur.elim
      | some N =>
        obtain ⟨p, hp, rfl, hat⟩ := ht.of_nodeRepr hcur
        step with child_named_spec ht hp hat path start «end» end_post end_post1
        have e1 : «end».val ≤ path.val.length := end_post1
        have hk : «end».val - start.val ≤ ((path.val.map byte).drop start.val).length := by
          simp only [List.length_drop, List.length_map]; omega
        have hsplit := splitB_at hk (fun j hj => by
            rw [drop_map_byte_getElem!, ne_eq, byte_eq_iff]
            exact end_post2 (start.val + j) (by omega) (by omega))
          (by
            rcases end_post3 with h | h
            · left; simp only [List.length_drop, List.length_map]; rw [h]
            · right; rw [drop_map_byte_getElem!, byte_eq_iff, show start.val + («end».val - start.val) = «end».val by omega]
              exact h)
        simp only [show start.val ≤ path.length by scalar_tac, ↓reduceIte, hsplit, descendB] at hans
        step*
        · -- the child found
          obtain ⟨vN, hvN, hrel⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf_post ‹_› r_post)
          rw [hvN] at hans
          simp only at hans
          refine ⟨⟨vN, hrel, by scalar_tac, ?_⟩, by scalar_tac⟩
          rw [← hans, start1_post]
          rcases end_post3 with h | h
          · have h' : «end».val - start.val = ((path.val.map byte).drop start.val).length := by
              simp only [List.length_drop, List.length_map]; rw [h]
            have h'' : ¬ «end».val + 1 ≤ path.length := by scalar_tac
            simp only [h', h'', ↓reduceIte, descendB]
          · have hlt : «end».val < path.val.length := by
              rcases Nat.lt_or_ge «end».val path.val.length with h2 | h2
              · exact h2
              · rw [getElem!_neg path.val _ (by omega)] at h; cases h
            have h' : ¬ «end».val - start.val = ((path.val.map byte).drop start.val).length := by
              simp only [List.length_drop, List.length_map]; omega
            have h'' : «end».val + 1 ≤ path.length := hlt
            simp only [h', h'', ↓reduceIte, List.drop_drop]
            rw [show start.val + («end».val - start.val + 1) = «end».val + 1 by omega]
        · -- an error
          have hE := agrees_err_of_branch cf_post ‹_› residual_post r_post
          rw [hE] at hans
          simp only at hans
          rw [r1_post, ← hans, ← e_post]
          rfl
    · -- past the last component
      simp only [show ¬ start.val ≤ path.length by scalar_tac, ↓reduceIte] at hans
      rw [← hans]; exact hcur
  · exact ⟨curN, hcur, hs, rfl⟩

/-- `find_path(structure, path)`: the node of a path that is not empty, the root
for `/`, under the premise that the path leaves room for the index after its
last byte. -/
theorem find_path_spec {t : fdt.Fdt} {T : Fdt} {L : List Begin} (ht : TreeNodes t T L)
    (path : Slice U8) (hpl : path.length < Usize.max) (hne : 1 ≤ path.length) :
    fdt.nodes.find_path t.structure path ⦃ r =>
      Agrees (OptionRel (fun a N => NodeRepr ⟨t, a⟩ N)) errorOf r
        (if path.length = 1 then .ok T.root
         else descendB T (splitB ((path.val.map byte).drop 1)) T.root) ⦄ := by
  unfold fdt.nodes.find_path
  step with first_node_spec ht as ⟨root, hroot⟩
  by_cases h1 : path.length = 1
  · have : Slice.len path = 1#usize := by scalar_tac
    simp only [this, ↓reduceIte, spec_ok, h1, agrees_ok_ok]
    exact hroot
  · have : ¬ Slice.len path = 1#usize := by scalar_tac
    simp only [this, ↓reduceIte, h1]
    have := descend_loop_spec ht path hpl 1#usize root T.root hroot (by scalar_tac)
    simp only [show (1#usize : Usize).val = 1 from rfl, hne, ↓reduceIte] at this
    exact this

/-- `Fdt::find_node(path)` under the premise that the bytes of the path leave
room for the index after the last of them, which holds for every slice of
bytes of Rust (at most `isize::MAX` bytes): the node of `Fdt.findNode`. -/
theorem fdt_find_node_spec_of_lt (hu : Usize64) (t : fdt.Fdt) (T : Fdt) (path : Str) (p : String)
    (h : FdtRepr t T) (hs : StrRepr path p) (hp : p.utf8ByteSize < Usize.max) :
    fdt.nodes.Fdt.find_node t path ⦃ r => Agrees (OptionRel NodeRepr) errorOf r (T.findNode p) ⦄ := by
  obtain ⟨L, ht⟩ := treeNodes_of_repr hu h
  unfold fdt.nodes.Fdt.find_node
  have hs' : core.str.Str.as_bytes path ⦃ b => bytesOf b = p.toUTF8 ⦄ := hs
  step with hs' as ⟨path1, hb⟩
  have hP : path1.val.map byte = utf8Bytes p.toList := by
    rw [← bytesOf_toList, hb, toUTF8_toList]
  have hlen : path1.length = p.utf8ByteSize := by
    rw [← bytesOf_size, hb, String.toUTF8_eq_toByteArray, String.size_toByteArray]
  have hPl : (utf8Bytes p.toList).length = path1.length := by rw [← hP, List.length_map]
  rw [findNode_eq, ← hP]
  step*
  · have hv : pathValidB (path1.val.map byte) = true := by rwa [← b_post]
    have hne : 1 ≤ path1.length := by
      have h0 := hv
      simp only [pathValidB, Bool.and_eq_true, beq_iff_eq] at h0
      show 1 ≤ path1.val.length
      cases hq : path1.val with
      | nil => rw [hq] at h0; simp at h0
      | cons x xs => simp
    have hl1 : ((path1.val.map byte).length = 1) = (path1.length = 1) := by
      rw [List.length_map]
    simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hl1]
    step with find_path_spec ht path1 (by rw [hlen]; exact hp) hne
    step*
    · obtain ⟨vN, hvN, hrel⟩ := agrees_ok_iff.1 (agrees_of_branch_ok cf_post ‹_› r_post)
      rw [hvN, o_post, agrees_ok_ok]
      cases val <;> cases vN <;> simp_all
    · have hE := agrees_err_of_branch cf_post ‹_› residual_post ‹_›
      rw [hE, r_post, agrees_err_error, e_post]
  · have hv : pathValidB (path1.val.map byte) = false := by
      rw [← b_post]; simpa using ‹¬b = true›
    simp only [hv, Bool.not_false, ↓reduceIte, agrees_err_error]
    rfl

end Krepi.Proofs.Fdt.Refinement
