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

end Krepi.Proofs.Fdt.Refinement
