module

public import Krepi.Proofs.Fdt.Refinement.NodeWalkLemmas
public import Krepi.Proofs.Fdt.Refinement.TranslateLemmas
public import Krepi.Proofs.Fdt.Refinement.NodePropertySpecLemmas

/-!
# Device tree: refinement of the node properties

The triples of the generated functions of `fdt::nodes` that read the
properties of a node, its cell counts, its `reg`, its address maps and the
translation of a region through the buses above it, stated against the
specification of `Krepi.Spec.Fdt.Nodes` and `Krepi.Spec.Fdt.Translate`, so
that the proof of a caller steps over the call with the triple of the callee
and a mutant of a callee fails the proof of the callee alone. The lemmas that
need no generated code are in `Krepi.Proofs.Fdt.Refinement.NodePropertySpecLemmas`.
Each triple of a function that takes a `NodeAt` of a tree `t` takes a node of
the specification that `⟨t, a⟩` stands for (`NodeRepr`), so that the callers
use it for a node and for its parent alike.

- The value of a property: `piece_of_property_value` (the piece of the code at a
  property token), `property_range_loop_spec` (the loop of `property_range`
  against the properties that `propsFrom` reads), `value_at_spec` (the range
  of the value of `Node.property`, `RangeRepr`), `nodeRepr_offset_le`, and
  `node_property_spec` (`Node::property`).
- The parent: `parent_at_node_spec`, the node of the code that stands for
  `Node.parent`.
- Strings and the status: `string_at_spec` (the range of the string of
  `Node.stringProperty`), `node_string_property_spec`, `enabled_at_spec` and
  `node_enabled_spec`.
- Cells: `cells_at_spec` (`Node.cellCount`), `address_cells_at_spec`,
  `size_cells_at_spec`, `node_address_cells_spec` and `node_size_cells_spec`.
- Regions: `RegAtRepr`, `reg_at_spec` and `node_reg_spec` (`Node.reg`, with
  `reg_stands` of `Krepi.Proofs.Fdt.Refinement.TranslateLemmas`).
- Address maps: `MapAtRepr`, `map_at_spec` (`mapOf`, the map of a node with
  its parent), `node_address_map_spec` (`Node.addressMap`),
  `node_ranges_spec` and `node_dma_ranges_spec`.
- The translation of a region: `climb_loop_spec`, `climb_spec`
  (`climbRanges`) and `node_translate_reg_spec` (`Node.translateReg`).

The key of `Node::property` and `Node::string_property` is read by `name_at`
only, which compares it after `fits` has bounded it by the strings block, so
no sum of the code leaves `usize` for a key of any length.
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.Fdt Krepi.Spec.Fdt Krepi.Statements Krepi.Statements.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## The value of a property -/

/-- The piece of the code at a property token that `decodeToken` reads: the
range of its value within the block, and the offset of its name. -/
theorem piece_of_property_value {o : Option (fdt.nodes.Piece × Usize)} {str strs : ByteArray}
    {c next : Nat} {nm : String} {v : ByteArray}
    (ho : o.map (fun p => (pieceOf p.1, p.2.val)) = pieceAt str c)
    (hd : decodeToken str strs c = .ok (.property nm v, next)) :
    ∃ off vs ve n, o = some (.Property off vs ve, n) ∧ n.val = next ∧ vs.val ≤ ve.val ∧
      ve.val ≤ str.size ∧ str.extract vs.val ve.val = v ∧
      ∃ e, cString strs off.val = .ok (nm, e) := by
  obtain ⟨off, e, hcs, hv, hp⟩ := pieceAt_of_decodeToken hd
  rw [hp] at ho
  obtain ⟨⟨p, n⟩, rfl, hpn⟩ := Option.map_eq_some_iff.1 ho
  simp only [Prod.mk.injEq] at hpn
  obtain ⟨hpp, rfl⟩ := hpn
  have hle := pieceAt_property_le hp
  cases p with
  | Property off' vs ve =>
    simp only [pieceOf, Piece.property.injEq] at hpp
    obtain ⟨h1, h2, h3⟩ := hpp
    refine ⟨off', vs, ve, n, rfl, rfl, by omega, by omega, ?_, e, by rw [h1]; exact hcs⟩
    rw [h2, h3]; exact hv.symm
  | _ => simp [pieceOf] at hpp

/-- The loop of `property_range`: from a cursor whose walk of `propsFrom`
gives the properties `ps` within the tokens left, the range of the value of the
first property named as the bytes of `s`, none without one. -/
theorem property_range_loop_spec («structure» strings «name» : Slice U8) (s : String)
    (hk : bytesOf «name» = s.toUTF8) (cursor read : Usize) (f : Nat)
    (ps : List (String × ByteArray)) (hsz : «structure».length + 2 ^ 32 ≤ Usize.max)
    (hf : read.val + f ≤ MAX_TOKENS.toNat)
    (hps : propsFrom (bytesOf «structure») (bytesOf strings) f cursor.val = some ps) :
    fdt.nodes.property_range_loop «structure» strings «name» cursor read ⦃ o =>
      OptionRel (RangeRepr «structure») o (propValue ps s) ⦄ := by
  unfold fdt.nodes.property_range_loop
  apply loop.spec_decr_nat
    (measure := fun (x : Usize × Usize) => MAX_TOKENS.toNat - x.2.val)
    (inv := fun (x : Usize × Usize) => ∃ f ps', x.2.val + f ≤ MAX_TOKENS.toNat ∧
      propsFrom (bytesOf «structure») (bytesOf strings) f x.1.val = some ps' ∧
      propValue ps' s = propValue ps s)
  · rintro ⟨cursor, read⟩ ⟨f, ps', hf, hps', hval⟩
    simp only at hf hps' hval
    obtain ⟨f, tok, next, rfl, hd⟩ := propsFrom_decode hps'
    rw [show MAX_TOKENS.toNat = 65536 from rfl] at hf ⊢
    unfold fdt.nodes.property_range_loop.body
    step
    rw [show MAX_TOKENS.toNat = 65536 from rfl] at r_post
    refine ite_spec_pos (by scalar_tac) ?_
    step with piece_at_spec
    cases tok with
    | property nm v =>
      obtain ⟨ps'', rfl, hps''⟩ := propsFrom_property_some hd hps'
      obtain ⟨off, vs, ve, n, rfl, hn, hle, hve, hext, e, hcs⟩ := piece_of_property_value o_post hd
      simp only
      step as ⟨b, b_post⟩
      have hb : b = decide (nm = s) := by
        rw [b_post, decide_eq_decide, ← bytesOf_size «name», nameAt_iff hcs, hk,
          toByteArray_eq_toUTF8]
      rw [propValue_cons] at hval
      by_cases hns : nm = s
      · simp only [hb, hns, decide_true, ↓reduceIte] at hval ⊢
        simp only [spec_ok]
        rw [← hval]
        exact ⟨hle, by rwa [bytesOf_size] at hve, hext⟩
      · simp only [hb, hns, decide_false, Bool.false_eq_true, ↓reduceIte] at hval ⊢
        step*
        exact ⟨⟨f, ps'', by scalar_tac, by rwa [hn], hval⟩, by scalar_tac⟩
    | nop =>
      obtain ⟨p, n, rfl, hn, hpt⟩ := piece_of_token o_post hd
      cases p <;> simp only [PieceTok] at hpt
      simp only
      step*
      exact ⟨⟨f, ps', by scalar_tac, by rw [hn]; exact propsFrom_nop_some hd hps', hval⟩,
        by scalar_tac⟩
    | beginNode nm =>
      obtain ⟨p, n, rfl, hn, hpt⟩ := piece_of_token o_post hd
      cases p <;> simp only [PieceTok] at hpt
      step*
      rw [← hval, propsFrom_end_some hd (Or.inr (Or.inr ⟨nm, rfl⟩)) hps', propValue_nil]
      exact trivial
    | endNode =>
      obtain ⟨p, n, rfl, hn, hpt⟩ := piece_of_token o_post hd
      cases p <;> simp only [PieceTok] at hpt
      step*
      rw [← hval, propsFrom_end_some hd (Or.inr (Or.inl rfl)) hps', propValue_nil]
      exact trivial
    | endStructure =>
      obtain ⟨p, n, rfl, hn, hpt⟩ := piece_of_token o_post hd
      cases p <;> simp only [PieceTok] at hpt
      step*
      rw [← hval, propsFrom_end_some hd (Or.inl rfl) hps', propValue_nil]
      exact trivial
  · exact ⟨f, ps, hf, hps, rfl⟩

/-- `value_at(structure, strings, node, name)`: the range of the value of the
property of the node named as the bytes of `s`, none without one. -/
theorem value_at_spec (hu : Usize64) {t : fdt.Fdt} {a : fdt.NodeAt} {N : Node}
    (h : NodeRepr ⟨t, a⟩ N) («name» : Slice U8) (s : String)
    (hk : bytesOf «name» = s.toUTF8) :
    fdt.nodes.value_at t.structure t.strings a «name» ⦃ o =>
      OptionRel (RangeRepr t.structure) o (N.property s) ⦄ := by
  obtain ⟨-, f, hf, hps⟩ := nodeRepr_tokens hu h
  obtain ⟨L, ht⟩ := treeNodes_of_repr hu h.1
  unfold fdt.nodes.value_at fdt.nodes.property_range
  exact property_range_loop_spec _ _ _ s hk _ 0#usize f _ ht.size (by simpa using hf) hps

/-- The begin-node token of a node lies within the structure block. -/
theorem nodeRepr_offset_le (hu : Usize64) {t : fdt.Fdt} {a : fdt.NodeAt} {N : Node}
    (h : NodeRepr ⟨t, a⟩ N) : a.offset.val + 4 ≤ t.structure.length := by
  obtain ⟨hd, -⟩ := nodeRepr_tokens hu h
  have hc := u32At_ok_le (decodeToken_tag_ok hd).choose_spec
  rwa [bytesOf_size] at hc

/-- `parent_at(structure, node)` of a node of a tree: the node of the code that
stands for the parent, none for the root. -/
theorem parent_at_node_spec (hu : Usize64) {t : fdt.Fdt} {a : fdt.NodeAt} {N : Node}
    (h : NodeRepr ⟨t, a⟩ N) :
    fdt.nodes.parent_at t.structure a ⦃ o =>
      OptionRel (fun b P => NodeRepr ⟨t, b⟩ P) o N.parent ⦄ := by
  obtain ⟨L, ht⟩ := treeNodes_of_repr hu h.1
  obtain ⟨o, ho, -⟩ :=
    spec_iff.1 (parent_at_spec t.structure (bytesOf t.strings) a L ht.size ht.walk)
  have hp := node_parent_spec hu ⟨t, a⟩ N h
  unfold fdt.nodes.Node.parent at hp
  dsimp only at hp
  rw [ho, bind_ok] at hp
  obtain ⟨x, hx, rfl⟩ := spec_iff.1 (node_of_spec t o)
  rw [hx] at hp
  refine spec_of_eq ho ?_
  have hrel := eq_of_spec rfl hp
  rcases o with _ | b <;> rcases hq : N.parent with _ | P <;> rw [hq] at hrel
  · trivial
  · exact hrel.elim
  · exact hrel.elim
  · exact hrel

/-- `Node::property(name)`: the bytes of the value of the property of that
name, none without it. -/
theorem node_property_spec (hu : Usize64) (n : fdt.Node) (N : Node) (key : Str) (s : String)
    (h : NodeRepr n N) (hs : StrRepr key s) :
    fdt.nodes.Node.property n key ⦃ o => o.map bytesOf = N.property s ⦄ := by
  unfold fdt.nodes.Node.property
  have hs' : core.str.Str.as_bytes key ⦃ b => bytesOf b = s.toUTF8 ⦄ := hs
  step with hs' as ⟨b, hb⟩
  step with value_at_spec hu h b s hb as ⟨o, ho⟩
  rcases o with _ | ⟨st, en⟩ <;> rcases hv : N.property s with _ | v <;> rw [hv] at ho
  · simp only [spec_ok, Option.map_none]
  · exact ho.elim
  · exact ho.elim
  · obtain ⟨h1, h2, h3⟩ := ho
    dsimp only at h1 h2 h3
    simp only
    step*
    rw [Option.map_some, bytesOf_of_slice s1_post, h3]

/-- `string_at(structure, strings, node, name)`: the range of the string of the
property of the node named as the bytes of `s`, without its NUL, none without
the property, or the error of `Node.stringProperty`. -/
theorem string_at_spec (hu : Usize64) {t : fdt.Fdt} {a : fdt.NodeAt} {N : Node}
    (h : NodeRepr ⟨t, a⟩ N) («name» : Slice U8) (s : String)
    (hk : bytesOf «name» = s.toUTF8) :
    fdt.nodes.string_at t.structure t.strings a «name» ⦃ r =>
      Agrees (OptionRel fun p str => RangeRepr t.structure p str.toUTF8) errorOf r
        (N.stringProperty s) ⦄ := by
  unfold fdt.nodes.string_at
  step with value_at_spec hu h «name» s hk as ⟨o, ho⟩
  rcases o with _ | ⟨st, en⟩ <;> rcases hv : N.property s with _ | v <;> rw [hv] at ho
  · simp only [spec_ok]
    rw [stringProperty_none hv]
    trivial
  · exact ho.elim
  · exact ho.elim
  · obtain ⟨h1, h2, h3⟩ := ho
    dsimp only at h1 h2 h3
    rw [stringProperty_some hv]
    simp only
    step as ⟨value, hvalue⟩
    have hbv : bytesOf value = v := by rw [bytesOf_of_slice hvalue, h3]
    have hlv : value.length = en.val - st.val := by
      rw [← bytesOf_size, hbv, ← h3, ByteArray.size_extract, bytesOf_size, Nat.min_eq_left h2]
    step as ⟨o1, ho1⟩
    rcases o1 with _ | nul
    · rw [hbv] at ho1
      rw [stringOf_none ho1.symm]
      simp only [spec_ok]
      rfl
    · simp only [Option.map_some] at ho1
      rw [hbv] at ho1
      obtain ⟨-, hnl, -, -⟩ := findNul_some ho1.symm
      have hnl' : nul.val < value.length := by rw [← bytesOf_size, hbv]; exact hnl
      simp only
      step as ⟨b, hb⟩
      rw [hbv] at hb
      rcases hu8 : String.fromUTF8? (v.extract 0 nul.val) with _ | str
      · have hnv : ¬ (v.extract 0 nul.val).IsValidUTF8 := by
          rw [← fromUTF8?_isSome, hu8]; simp
        simp only [hb, hnv, decide_false, Bool.false_eq_true, ↓reduceIte]
        rw [stringOf_invalid ho1.symm hu8]
        simp only [spec_ok]
        rfl
      · have hvv : (v.extract 0 nul.val).IsValidUTF8 := by
          rw [← fromUTF8?_isSome, hu8]; rfl
        simp only [hb, hvv, decide_true, ↓reduceIte]
        rw [stringOf_valid ho1.symm hu8]
        step*
        · have : ¬ nul.val + 1 = v.size := by
            rw [← bytesOf_size value, hbv] at *; scalar_tac
          simp only [ne_eq, this, not_false_eq_true, ↓reduceIte]
          rfl
        · have : nul.val + 1 = v.size := by
            rw [← bytesOf_size value, hbv] at *; scalar_tac
          simp only [ne_eq, this, not_true_eq_false, ↓reduceIte, agrees_ok_ok,
            optionRel_some_some, RangeRepr]
          rw [← h3] at hu8
          refine ⟨by scalar_tac, by scalar_tac, ?_⟩
          rw [i2_post]
          exact stringOf_extract h1 (by omega) hu8

/-- `Node::string_property(name)`: the bytes of the string of the property, none
without it, or the error of `Node.stringProperty`. -/
theorem node_string_property_spec (hu : Usize64) (n : fdt.Node) (N : Node) (key : Str)
    (s : String) (h : NodeRepr n N) (hs : StrRepr key s) :
    fdt.nodes.Node.string_property n key ⦃ r =>
      Agrees (fun o v => o.map bytesOf = v.map String.toUTF8) errorOf r
        (N.stringProperty s) ⦄ := by
  unfold fdt.nodes.Node.string_property
  have hs' : core.str.Str.as_bytes key ⦃ b => bytesOf b = s.toUTF8 ⦄ := hs
  step with hs' as ⟨b, hb⟩
  step with string_at_spec hu h b s hb as ⟨r, r_post⟩
  rw [← bind_pure (N.stringProperty s)]
  refine try_spec r_post (fun e => from_residual_spec e) fun o v hov _ => ?_
  rcases o with _ | ⟨st, en⟩ <;> rcases v with _ | str
  · exact spec_of_eq rfl rfl
  · exact hov.elim
  · exact hov.elim
  · obtain ⟨h1, h2, h3⟩ := hov
    dsimp only at h1 h2 h3
    simp only
    step*
    show some (bytesOf s1) = some str.toUTF8
    rw [bytesOf_of_slice s1_post, h3]

/-! ## The status -/

/-- `enabled_at(structure, strings, node)`: whether the node is enabled, or the
error of `Node.enabled`. -/
theorem enabled_at_spec (hu : Usize64) {t : fdt.Fdt} {a : fdt.NodeAt} {N : Node}
    (h : NodeRepr ⟨t, a⟩ N) :
    fdt.nodes.enabled_at t.structure t.strings a ⦃ r =>
      Agrees (· = ·) errorOf r N.enabled ⦄ := by
  unfold fdt.nodes.enabled_at
  simp only [lift, bind_ok]
  step with string_at_spec hu h _ "status" bytes_status as ⟨r, r_post⟩
  rw [enabled_eq]
  refine try_spec r_post (fun e => from_residual_spec e) fun o v hov _ => ?_
  rcases o with _ | ⟨st, en⟩ <;> rcases v with _ | str
  · exact spec_of_eq rfl rfl
  · exact hov.elim
  · exact hov.elim
  · obtain ⟨h1, h2, h3⟩ := hov
    dsimp only at h1 h2 h3
    simp only
    step as ⟨b, b_post⟩
    have hb : b = decide (str = "okay") := by
      rw [b_post, h3, bytes_okay, decide_eq_decide, ← toByteArray_eq_toUTF8,
        ← String.toUTF8_eq_toByteArray]
      exact ⟨fun h => h.2.2, fun h => ⟨h1, h2, h⟩⟩
    by_cases hok : str = "okay"
    · simp only [hb, hok, decide_true, ↓reduceIte]
      refine spec_of_eq rfl ?_
      show true = ("okay" == "okay" || "okay" == "ok")
      simp
    · simp only [hb, hok, decide_false, Bool.false_eq_true, ↓reduceIte]
      step as ⟨b1, b1_post⟩
      show b1 = (str == "okay" || str == "ok")
      rw [b1_post, h3, bytes_ok]
      have e1 : (str == "okay") = false := by simpa using hok
      rw [e1, Bool.false_or]
      by_cases h' : str = "ok"
      · simp only [h', beq_self_eq_true, decide_eq_true_eq]
        exact ⟨h1, h2, trivial⟩
      · have e2 : (str == "ok") = false := by simpa using h'
        rw [e2, decide_eq_false_iff_not]
        rintro ⟨-, -, he⟩
        exact h' (toByteArray_eq_toUTF8.1 (by rw [← String.toUTF8_eq_toByteArray]; exact he))

/-- `Node::enabled()`: whether the node is enabled, or the error of
`Node.enabled`. -/
theorem node_enabled_spec (hu : Usize64) (n : fdt.Node) (N : Node) (h : NodeRepr n N) :
    fdt.nodes.Node.enabled n ⦃ r => Agrees (· = ·) errorOf r N.enabled ⦄ := by
  unfold fdt.nodes.Node.enabled
  exact enabled_at_spec hu h

/-! ## The cell counts -/

/-- `cells_at(structure, strings, node, name, default)`: the cell count of the
property of the node named as the bytes of `s`, or the error of
`Node.cellCount`. -/
theorem cells_at_spec (hu : Usize64) {t : fdt.Fdt} {a : fdt.NodeAt} {N : Node}
    (h : NodeRepr ⟨t, a⟩ N) («name» : Slice U8) (s : String)
    (hk : bytesOf «name» = s.toUTF8)
    (default : U32) :
    fdt.nodes.cells_at t.structure t.strings a «name» default ⦃ r =>
      Agrees (fun c C => word32 c = C) errorOf r (N.cellCount s (word32 default)) ⦄ := by
  unfold fdt.nodes.cells_at
  step with value_at_spec hu h «name» s hk as ⟨o, ho⟩
  rcases o with _ | ⟨st, en⟩ <;> rcases hv : N.property s with _ | v <;> rw [hv] at ho
  · rw [cellCount_none _ hv]
    exact spec_of_eq rfl rfl
  · exact ho.elim
  · exact ho.elim
  · obtain ⟨h1, h2, h3⟩ := ho
    dsimp only at h1 h2 h3
    have hsz : v.size = en.val - st.val := by
      rw [← h3, ByteArray.size_extract, bytesOf_size, Nat.min_eq_left h2]
    rw [cellCount_some _ hv]
    simp only
    step*
    · have : ¬ v.size = 4 := by
        simp only [usize_bne_iff] at *; scalar_tac
      simp only [this, ↓reduceIte]
      rfl
    · have : v.size = 4 := by
        simp only [usize_bne_iff, ne_eq, Decidable.not_not] at *; scalar_tac
      simp only [this, ↓reduceIte]
      rw [← h3, u32At_extract_zero (by omega) (by rwa [bytesOf_size])]
      exact r_post

/-- `address_cells_at(structure, strings, node)`: the node's own
`#address-cells`, or the error of `Node.addressCells`. -/
theorem address_cells_at_spec (hu : Usize64) {t : fdt.Fdt} {a : fdt.NodeAt} {N : Node}
    (h : NodeRepr ⟨t, a⟩ N) :
    fdt.nodes.address_cells_at t.structure t.strings a ⦃ r =>
      Agrees (fun c C => word32 c = C) errorOf r N.addressCells ⦄ := by
  unfold fdt.nodes.address_cells_at
  simp only [lift, bind_ok]
  exact cells_at_spec hu h _ "#address-cells" bytes_address_cells 2#u32

/-- `size_cells_at(structure, strings, node)`: the node's own `#size-cells`, or
the error of `Node.sizeCells`. -/
theorem size_cells_at_spec (hu : Usize64) {t : fdt.Fdt} {a : fdt.NodeAt} {N : Node}
    (h : NodeRepr ⟨t, a⟩ N) :
    fdt.nodes.size_cells_at t.structure t.strings a ⦃ r =>
      Agrees (fun c C => word32 c = C) errorOf r N.sizeCells ⦄ := by
  unfold fdt.nodes.size_cells_at
  simp only [lift, bind_ok]
  exact cells_at_spec hu h _ "#size-cells" bytes_size_cells 1#u32

/-- `Node::address_cells()`: the statement `NodeAddressCells`. -/
theorem node_address_cells_spec (hu : Usize64) (n : fdt.Node) (N : Node) (h : NodeRepr n N) :
    fdt.nodes.Node.address_cells n ⦃ r =>
      Agrees (fun c C => word32 c = C) errorOf r N.addressCells ⦄ := by
  unfold fdt.nodes.Node.address_cells
  exact address_cells_at_spec hu h

/-- `Node::size_cells()`: the statement `NodeSizeCells`. -/
theorem node_size_cells_spec (hu : Usize64) (n : fdt.Node) (N : Node) (h : NodeRepr n N) :
    fdt.nodes.Node.size_cells n ⦃ r =>
      Agrees (fun c C => word32 c = C) errorOf r N.sizeCells ⦄ := by
  unfold fdt.nodes.Node.size_cells
  exact size_cells_at_spec hu h

/-! ## The regions -/

/-- A `RegAt` of the code stands for the `Reg` of the specification: its range
lies in the block, and `Reg.new` of the bytes of the range with its cells
gives that `Reg`. -/
def RegAtRepr (b : Slice U8) (g : fdt.nodes.RegAt) (R : Reg) : Prop :=
  g.start.val ≤ g.end.val ∧ g.end.val ≤ b.length ∧
    Reg.new ((bytesOf b).extract g.start.val g.end.val) (word32 g.address_cells)
      (word32 g.size_cells) = .ok R

/-- `reg_at(structure, strings, node)`: the range of the `reg` of the node with
the cells of its parent, checked as `Node.reg` checks it, or its error. -/
theorem reg_at_spec (hu : Usize64) {t : fdt.Fdt} {a : fdt.NodeAt} {N : Node}
    (h : NodeRepr ⟨t, a⟩ N) :
    fdt.nodes.reg_at t.structure t.strings a ⦃ r =>
      Agrees (RegAtRepr t.structure) errorOf r N.reg ⦄ := by
  unfold fdt.nodes.reg_at
  step with parent_at_node_spec hu h as ⟨o, ho⟩
  rcases o with _ | b <;> rcases hp : N.parent with _ | P <;> rw [hp] at ho
  · rw [node_reg_none hp]
    exact spec_of_eq rfl rfl
  · exact ho.elim
  · exact ho.elim
  · simp only [lift, bind_ok]
    step with value_at_spec hu h _ "reg" bytes_reg as ⟨o1, ho1⟩
    rcases o1 with _ | ⟨st, en⟩ <;> rcases hv : N.property "reg" with _ | v <;> rw [hv] at ho1
    · rw [node_reg_absent hp hv]
      exact spec_of_eq rfl rfl
    · exact ho1.elim
    · exact ho1.elim
    · obtain ⟨h1, h2, h3⟩ := ho1
      dsimp only at h1 h2 h3
      rw [node_reg_present hp hv]
      simp only
      step with address_cells_at_spec hu ho as ⟨r, r_post⟩
      refine try_spec r_post (fun e => from_residual_spec e) fun ac AC hac _ => ?_
      simp only
      step with size_cells_at_spec hu ho as ⟨r1, r1_post⟩
      refine try_spec r1_post (fun e => from_residual_spec e) fun sc SC hsc _ => ?_
      simp only
      step as ⟨s1, s1_post⟩
      step as ⟨r2, r2_post⟩
      rw [bytesOf_of_slice s1_post, h3, hac, hsc] at r2_post
      rw [← bind_pure (Reg.new v AC SC)]
      refine try_spec r2_post (fun e => from_residual_spec e) fun _ R _ hR => ?_
      refine spec_of_eq rfl ⟨h1, h2, ?_⟩
      show Reg.new ((bytesOf t.structure).extract st.val en.val) (word32 ac) (word32 sc) = .ok R
      rw [h3, hac, hsc]
      exact hR

/-- `Node::reg()`: the statement `NodeReg`. -/
theorem node_reg_spec (hu : Usize64) (n : fdt.Node) (N : Node) (h : NodeRepr n N) :
    fdt.nodes.Node.reg n ⦃ r => Agrees (fun g R => RegRepr g R.entries) errorOf r N.reg ⦄ := by
  unfold fdt.nodes.Node.reg
  step with reg_at_spec hu h as ⟨r, r_post⟩
  rw [← bind_pure N.reg]
  refine try_spec r_post (fun e => from_residual_spec e) fun g R hg _ => ?_
  obtain ⟨h1, h2, hR⟩ := hg
  simp only
  step as ⟨s, s_post⟩
  rw [← bytesOf_of_slice s_post] at hR
  obtain ⟨hac, hsc, -, -, hm⟩ := regNew_ok hR
  rw [bytesOf_size] at hm
  exact reg_stands _ _ (show 0 < g.address_cells.val by omega)
    (show g.address_cells.val + g.size_cells.val ≤ 4 by omega) hm

/-! ## The address maps -/

/-- A `MapAt` of the code stands for the address map of the specification: its
range lies in the block, and `AddressMap.new` of the bytes of the range, none
when the property is absent, with its cells gives that map. -/
def MapAtRepr (b : Slice U8) (m : fdt.nodes.MapAt) (M : AddressMap) : Prop :=
  m.start.val ≤ m.end.val ∧ m.end.val ≤ b.length ∧
    AddressMap.new (if m.present then some ((bytesOf b).extract m.start.val m.end.val) else none)
      (word32 m.child_cells) (word32 m.parent_cells) (word32 m.size_cells) = .ok M

/-- `map_at(structure, strings, node, parent, name)`: the range of the property
of the node named as the bytes of `s` with the cells of the node and of its
parent `parent`, checked as `Node.addressMap` checks it, or its error. -/
theorem map_at_spec (hu : Usize64) {t : fdt.Fdt} {a b : fdt.NodeAt} {N P : Node}
    (h : NodeRepr ⟨t, a⟩ N) (hp : NodeRepr ⟨t, b⟩ P) («name» : Slice U8) (s : String)
    (hk : bytesOf «name» = s.toUTF8) :
    fdt.nodes.map_at t.structure t.strings a b «name» ⦃ r =>
      Agrees (MapAtRepr t.structure) errorOf r (mapOf N P s) ⦄ := by
  unfold fdt.nodes.map_at
  step with value_at_spec hu h «name» s hk as ⟨o, ho⟩
  apply WP.spec_bind (Pₘ := fun x : fdt.NodeAt × Usize × Usize × Bool => x.1 = a ∧
    x.2.1.val ≤ x.2.2.1.val ∧ x.2.2.1.val ≤ t.structure.length ∧
    (if x.2.2.2 then some ((bytesOf t.structure).extract x.2.1.val x.2.2.1.val) else none) =
      N.property s)
  · rcases o with _ | ⟨st, en⟩ <;> rcases hv : N.property s with _ | v <;> rw [hv] at ho
    · have := nodeRepr_offset_le hu h
      exact spec_of_eq rfl ⟨rfl, Nat.le_refl _, show a.offset.val ≤ _ by omega, rfl⟩
    · exact ho.elim
    · exact ho.elim
    · obtain ⟨h1, h2, h3⟩ := ho
      exact spec_of_eq rfl ⟨rfl, h1, h2, by rw [← h3]; rfl⟩
  · rintro ⟨node1, st, en, present⟩ ⟨rfl, h1, h2, hpv⟩
    dsimp only at h1 h2 hpv
    unfold mapOf
    step with address_cells_at_spec hu h as ⟨r, r_post⟩
    refine try_spec r_post (fun e => from_residual_spec e) fun cc CC hcc _ => ?_
    simp only
    step with address_cells_at_spec hu hp as ⟨r1, r1_post⟩
    refine try_spec r1_post (fun e => from_residual_spec e) fun pc PC hpc _ => ?_
    simp only
    step with size_cells_at_spec hu h as ⟨r2, r2_post⟩
    refine try_spec r2_post (fun e => from_residual_spec e) fun sc SC hsc _ => ?_
    simp only
    step as ⟨s1, s1_post⟩
    step as ⟨r3, r3_post⟩
    rw [bytesOf_of_slice s1_post, hpv, hcc, hpc, hsc] at r3_post
    rw [← bind_pure (AddressMap.new (N.property s) CC PC SC)]
    refine try_spec r3_post (fun e => from_residual_spec e) fun _ M _ hM => ?_
    refine spec_of_eq rfl ⟨h1, h2, ?_⟩
    show AddressMap.new
      (if present then some ((bytesOf t.structure).extract st.val en.val) else none)
      (word32 cc) (word32 pc) (word32 sc) = .ok M
    rw [hpv, hcc, hpc, hsc]
    exact hM

/-- `Node::address_map(name)`: the address map of the property named as the
bytes of `s`, `Node.addressMap`, or its error. -/
theorem node_address_map_spec (hu : Usize64) (n : fdt.Node) (N : Node) (h : NodeRepr n N)
    («name» : Slice U8) (s : String) (hk : bytesOf «name» = s.toUTF8) :
    fdt.nodes.Node.address_map n «name» ⦃ r =>
      Agrees AddressMapRepr errorOf r (N.addressMap s) ⦄ := by
  unfold fdt.nodes.Node.address_map
  step with parent_at_node_spec hu h as ⟨o, ho⟩
  rcases o with _ | b <;> rcases hp : N.parent with _ | P <;> rw [hp] at ho
  · rw [node_addressMap_none hp]
    exact spec_of_eq rfl rfl
  · exact ho.elim
  · exact ho.elim
  · rw [node_addressMap_some hp]
    simp only
    step with map_at_spec hu h ho «name» s hk as ⟨r, r_post⟩
    rw [← bind_pure (mapOf N P s)]
    refine try_spec r_post (fun e => from_residual_spec e) fun m M hm _ => ?_
    obtain ⟨h1, h2, hM⟩ := hm
    simp only
    step as ⟨s1, s1_post⟩
    show AddressMap.new (if m.present then some (bytesOf s1) else none) _ _ _ = .ok M
    rw [bytesOf_of_slice s1_post]
    exact hM

/-- `Node::ranges()`: the statement `NodeRanges`. -/
theorem node_ranges_spec (hu : Usize64) (n : fdt.Node) (N : Node) (h : NodeRepr n N) :
    fdt.nodes.Node.ranges n ⦃ r => Agrees AddressMapRepr errorOf r N.ranges ⦄ := by
  unfold fdt.nodes.Node.ranges
  simp only [lift, bind_ok]
  exact node_address_map_spec hu n N h _ "ranges" bytes_ranges

/-- `Node::dma_ranges()`: the statement `NodeDmaRanges`. -/
theorem node_dma_ranges_spec (hu : Usize64) (n : fdt.Node) (N : Node) (h : NodeRepr n N) :
    fdt.nodes.Node.dma_ranges n ⦃ r => Agrees AddressMapRepr errorOf r N.dmaRanges ⦄ := by
  unfold fdt.nodes.Node.dma_ranges
  simp only [lift, bind_ok]
  exact node_address_map_spec hu n N h _ "dma-ranges" bytes_dma_ranges

/-! ## The translation of a region -/

/-- The loop of `climb`: from a bus that stands for `B` after `steps` steps, the
translation of the span through the `ranges` of each bus up to the root, as
`climbRanges` with the steps left reads it. -/
theorem climb_loop_spec (hu : Usize64) {t : fdt.Fdt} (E : Except Krepi.Spec.Fdt.Error Span)
    (bus : fdt.NodeAt) (B : Node) (h : NodeRepr ⟨t, bus⟩ B) (span : fdt.Span) (steps : Usize)
    (hs : steps.val ≤ MAX_DEPTH.toNat)
    (hc : climbRanges (MAX_DEPTH.toNat - steps.val) B (spanOf span) = E) :
    fdt.nodes.climb_loop t.structure t.strings bus span steps ⦃ r =>
      Agrees SpanRepr errorOf r E ⦄ := by
  unfold fdt.nodes.climb_loop
  apply loop.spec_decr_nat
    (measure := fun (x : fdt.NodeAt × fdt.Span × Usize) => MAX_DEPTH.toNat - x.2.2.val)
    (inv := fun (x : fdt.NodeAt × fdt.Span × Usize) => ∃ B, NodeRepr ⟨t, x.1⟩ B ∧
      x.2.2.val ≤ MAX_DEPTH.toNat ∧
        climbRanges (MAX_DEPTH.toNat - x.2.2.val) B (spanOf x.2.1) = E)
  · rintro ⟨bus, span, steps⟩ ⟨B, h, hs, hc⟩
    dsimp only at h hs hc
    rw [show MAX_DEPTH.toNat = 32 from rfl] at hs hc ⊢
    unfold fdt.nodes.climb_loop.body
    step
    rw [show MAX_DEPTH.toNat = 32 from rfl] at r_post
    by_cases hlt : steps.val < 32
    · refine ite_spec_pos (by scalar_tac) ?_
      obtain ⟨k, hk⟩ : ∃ k, 32 - steps.val = k + 1 := ⟨31 - steps.val, by omega⟩
      rw [hk] at hc
      step with parent_at_node_spec hu h as ⟨o, ho⟩
      rcases o with _ | up <;> rcases hp : B.parent with _ | U <;> rw [hp] at ho
      · rw [climbRanges_none hp] at hc
        refine spec_of_eq rfl ?_
        show Agrees SpanRepr errorOf (.Ok span) E
        rw [← hc]
        rfl
      · exact ho.elim
      · exact ho.elim
      · rw [climbRanges_some hp] at hc
        simp only [lift, bind_ok]
        step with map_at_spec hu h ho _ "ranges" bytes_ranges as ⟨r1, r1_post⟩
        rcases r1 with m | e
        · obtain ⟨M, hM, h1, h2, hMn⟩ := agrees_ok_iff.1 r1_post
          rw [hM, except_ok_bind] at hc
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step as ⟨s1, s1_post⟩
          rw [← bytesOf_of_slice s1_post] at hMn
          step with translate_map_spec _ _ _ _ _ span false hMn as ⟨r2, r2_post⟩
          rcases r2 with sp | e'
          · obtain ⟨T, hT, hsp⟩ := agrees_ok_iff.1 r2_post
            rw [AddressMap.toParent, hT, except_ok_bind] at hc
            simp only [bind_ok]
            step*
            refine ⟨⟨U, ho, by scalar_tac, ?_⟩, by scalar_tac⟩
            have hsp' : spanOf sp = T := hsp
            have hk' : 32 - steps1.val = k := by scalar_tac
            rw [hk', hsp']
            exact hc
          · have hE := agrees_err_iff.1 r2_post
            rw [AddressMap.toParent, hE, except_error_bind] at hc
            simp only [bind_ok]
            step with from_residual_spec as ⟨r3, r3_post⟩
            subst r3_post
            show Agrees SpanRepr errorOf (.Err e') E
            rw [← hc]
            rfl
        · have hE := agrees_err_iff.1 r1_post
          rw [hE, except_error_bind] at hc
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          step with from_residual_spec as ⟨r3, r3_post⟩
          subst r3_post
          show Agrees SpanRepr errorOf (.Err e) E
          rw [← hc]
          rfl
    · refine ite_spec_neg (by scalar_tac) ?_
      rw [show 32 - steps.val = 0 by omega, climbRanges_zero] at hc
      refine spec_of_eq rfl ?_
      show Agrees SpanRepr errorOf (.Err .LimitExceeded) E
      rw [← hc]
      rfl
  · exact ⟨B, h, hs, hc⟩

/-- `climb(structure, strings, bus, span)`: the translation of the span through
the `ranges` of the bus `B` and of each bus above it, `climbRanges`. -/
theorem climb_spec (hu : Usize64) {t : fdt.Fdt} {bus : fdt.NodeAt} {B : Node}
    (h : NodeRepr ⟨t, bus⟩ B) (span : fdt.Span) :
    fdt.nodes.climb t.structure t.strings bus span ⦃ r =>
      Agrees SpanRepr errorOf r (climbRanges MAX_DEPTH.toNat B (spanOf span)) ⦄ := by
  unfold fdt.nodes.climb
  exact climb_loop_spec hu _ bus B h span 0#usize (by simp) (by simp)

/-- `Node::translate_reg(span)`: the statement `NodeTranslateReg`. -/
theorem node_translate_reg_spec (hu : Usize64) (n : fdt.Node) (N : Node) (span : fdt.Span)
    (h : NodeRepr n N) :
    fdt.nodes.Node.translate_reg n span ⦃ r =>
      Agrees SpanRepr errorOf r (N.translateReg (spanOf span)) ⦄ := by
  unfold fdt.nodes.Node.translate_reg
  step with parent_at_node_spec hu h as ⟨o, ho⟩
  rcases o with _ | b <;> rcases hp : N.parent with _ | B <;> rw [hp] at ho
  · rw [node_translateReg_none hp]
    exact spec_of_eq rfl rfl
  · exact ho.elim
  · exact ho.elim
  · rw [node_translateReg_some hp]
    simp only
    step with climb_spec hu ho span as ⟨r, r_post⟩
    refine try_spec r_post (fun e => from_residual_spec e) fun v T hv _ => ?_
    have hv' : spanOf v = T := hv
    simp only
    step as ⟨r1, r1_post⟩
    rw [hv'] at r1_post
    refine try_spec r1_post (fun e => from_residual_spec e) fun _ _ _ _ => ?_
    exact spec_of_eq rfl hv

end Krepi.Proofs.Fdt.Refinement
