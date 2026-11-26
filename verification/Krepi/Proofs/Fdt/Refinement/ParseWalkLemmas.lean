module

public import Krepi.Proofs.Fdt.Refinement.ParseHeaderLemmas
public import Krepi.Proofs.Fdt.Refinement.FormatLemmas
public import Krepi.Proofs.Fdt.Refinement.ParseWalkSpecLemmas

/-!
# Device tree: refinement of the walk over the tokens and of the parse

The triples of the generated functions of `fdt::parser` that decode the
tokens of the structure block and place them in the tree, of the walk over
the tokens, and of `Fdt::parse`, each a `@[step]` lemma where a caller steps
over it, so that a mutant of a callee fails the proof of the callee alone:

- the walk of the code as numbers: `frameOf` and `walkOf` (a frame and a walk
  of the code as `MFrame` and `MWalk` of
  `Krepi.Proofs.Fdt.Refinement.ParseWalkSpecLemmas`), `walkOf_open_eq_zero`,
  `walkOf_start`, `frameOf_getElem!`, and `Mirrors` (a step of the code
  returns what the step of `MWalk` gives);
- the steps of the walk against `MWalk`: `end_node_spec` (`end_node`),
  `end_structure_spec` (`end_structure`), `push_spec` (the opening of a node
  that `begin_node` writes twice), `begin_node_spec` (`begin_node`) and
  `property_spec` (`property`, with the answer of `repeats_name`), with
  `max_props_val`;
- the names of the properties so far: `piece_of_nop`, `piece_of_property`,
  `repeats_name_loop_spec` and `repeats_name_spec` (`repeats_name`: whether a
  name is among the names that `NamesFrom` reads);
- the tokens: `TokRel` (a token of the code stands for the token that
  `decodeToken` reads), `tokRel_next`, `decode_begin_spec`,
  `decode_property_spec` (with `max_name_val`), `u32_eq_iff` and
  `decode_token_spec` (`decode_token`: the token of `decodeToken`, or its
  error);
- the place of a token: `place_spec` (`place`: what `stepOf` gives for the
  token, through `MRel`);
- the walk: `walk_tokens_loop_spec` and `walk_tokens_spec` (`walk_tokens`
  succeeds exactly when `walkTokens` does, with the same error);
- the parse: `fdt_parse_spec`, the statement `FdtParse`.

`walk_tokens_loop_spec` is proved with `loop.spec_decr_nat`: the invariant is
`MRel` between the walk of the code and a walk of the specification at the
cursor, and the walk of the specification from there gives the result of the
walk from the start up to its records, which the code does not build.
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.Fdt Krepi.Spec.Fdt Krepi.Statements Krepi.Statements.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-- A frame of the walk of the code as numbers. -/
def frameOf (f : fdt.parser.Frame) : MFrame := ⟨f.properties.val, f.count.val, f.children⟩

/-- The walk of the code as numbers: its table of frames, the number of open
nodes and whether the root has begun. -/
def walkOf (w : fdt.parser.Walk) : MWalk := ⟨w.frames.val.map frameOf, w.open.val, w.seen_root⟩

/-- What a step of the code that changes the walk returns, against a step of `MWalk`. -/
def Mirrors (p : core.result.Result Bool fdt.Error × fdt.parser.Walk)
    (M : Except Krepi.Spec.Fdt.Error MWalk) : Prop :=
  Agrees (fun b m => b = false ∧ walkOf p.2 = m) errorOf p.1 M

/-- `end_node(walk)`: `MWalk.endNode`. -/
@[step] theorem end_node_spec (walk : fdt.parser.Walk) :
    fdt.parser.end_node walk ⦃ p => Mirrors p (walkOf walk).endNode ⦄ := by
  unfold fdt.parser.end_node MWalk.endNode
  by_cases h : walk.open = 0#usize
  · have h' : (walkOf walk).open_ = 0 := by simp [walkOf, h]
    simp only [h, ↓reduceIte, h', spec_ok, Mirrors, agrees_err_error]
    rfl
  · have h' : ¬ (walkOf walk).open_ = 0 := by
      simp only [walkOf]; intro h0; exact h (UScalar.eq_of_val_eq (by simpa using h0))
    simp only [h, ↓reduceIte, h']
    step*
    simp only [Mirrors, agrees_ok_ok, walkOf, true_and]
    simp [i_post]

/-- `end_structure(walk, next, length)`: `MWalk.endStructure`. -/
@[step] theorem end_structure_spec (walk : fdt.parser.Walk) (next length : Usize) :
    fdt.parser.end_structure walk next length ⦃ r =>
      Agrees (· = ·) errorOf r ((walkOf walk).endStructure next.val length.val) ⦄ := by
  unfold fdt.parser.end_structure MWalk.endStructure
  simp only [walkOf]
  by_cases h1 : walk.seen_root
  · by_cases h2 : walk.open = 0#usize
    · by_cases h3 : next = length
      · simp [h1, h2, h3]
      · have h3' : next.val ≠ length.val := fun e => h3 (UScalar.eq_of_val_eq e)
        simp [h1, h2, h3, h3']; rfl
    · have h2' : walk.open.val ≠ 0 := fun e => h2 (UScalar.eq_of_val_eq (by simpa using e))
      simp [h1, h2, h2']; rfl
  · simp [h1]; rfl

/-- A frame of the table of the code as numbers. -/
theorem frameOf_getElem! (l : List fdt.parser.Frame) (i : Nat) (h : i < l.length) :
    (l.map frameOf)[i]! = frameOf l[i] := by
  simp [h]

/-- The opening of a node that `begin_node` writes in both of its branches:
`MWalk.push`. -/
theorem push_spec (walk : fdt.parser.Walk) (next : Usize) :
    (do
      let i ← fdt.DEPTH
      if walk.open >= i
      then ok (core.result.Result.Err fdt.Error.LimitExceeded, walk)
      else
        let a ←
          if walk.open > 0#usize
          then
            do
            let i1 ← walk.open - 1#usize
            let (f, index_mut_back) ← Array.index_mut_usize walk.frames i1
            ok (index_mut_back { f with children := true })
          else ok walk.frames
        let a1 ←
          Array.update a walk.open
            ({ properties := next, count := 0#u64, children := false } :
            fdt.parser.Frame)
        let i1 ← walk.open + 1#usize
        ok (core.result.Result.Ok false,
          ({ frames := a1, «open» := i1, seen_root := true } : fdt.parser.Walk)) :
      Result ((core.result.Result Bool fdt.Error) × fdt.parser.Walk)) ⦃ p =>
      Mirrors p ((walkOf walk).push next.val) ⦄ := by
  unfold MWalk.push markChild
  step as ⟨i, i_post⟩
  have ho : (walkOf walk).open_ = walk.open.val := rfl
  rw [ho]
  have h32 : MAX_DEPTH.toNat = 32 := rfl
  by_cases hd : walk.open ≥ i
  · have : MAX_DEPTH.toNat ≤ walk.open.val := by rw [← i_post]; scalar_tac
    simp only [hd, ↓reduceIte, this, spec_ok, Mirrors, agrees_err_error]
    rfl
  · have hd' : ¬ MAX_DEPTH.toNat ≤ walk.open.val := by rw [← i_post]; scalar_tac
    simp only [hd, ↓reduceIte, hd']
    have hlt : walk.open.val < walk.frames.length := by scalar_tac
    by_cases hpos : walk.open > 0#usize
    · have hpos' : 0 < walk.open.val := by scalar_tac
      simp only [hpos, ↓reduceIte, hpos']
      step as ⟨j, j_post⟩
      step as ⟨x, x_post, x_post1⟩
      obtain ⟨f, back⟩ := x
      simp only at x_post x_post1
      subst x_post x_post1
      step*
      have hj : j.val < walk.frames.val.length := by scalar_tac
      have hf : frameOf { (walk.frames.val)[j.val] with children := true } =
          ((walk.frames.val.map frameOf)[j.val]!).mark := by
        rw [frameOf_getElem! _ _ hj]; rfl
      simp only [Mirrors, agrees_ok_ok, true_and, walkOf, a1_post, Array.set_val_eq, List.map_set,
        i1_post, hf, MWalk.mk.injEq, and_true]
      rw [j_post]
      rfl
    · have hpos' : ¬ 0 < walk.open.val := by scalar_tac
      simp only [hpos, ↓reduceIte, hpos']
      step*
      simp only [Mirrors, agrees_ok_ok, true_and, walkOf, a1_post, Array.set_val_eq, List.map_set,
        i1_post, MWalk.mk.injEq, and_true]
      rfl

/-- No open node, as numbers and in the code. -/
theorem walkOf_open_eq_zero {walk : fdt.parser.Walk} :
    (walkOf walk).open_ = 0 ↔ walk.open = 0#usize := by
  simp only [walkOf]
  constructor
  · intro h; exact UScalar.eq_of_val_eq (by simpa using h)
  · intro h; simp [h]

/-- `begin_node(walk, empty, next)`: `MWalk.beginNode`. -/
@[step] theorem begin_node_spec (walk : fdt.parser.Walk) (empty : Bool) (next : Usize) :
    fdt.parser.begin_node walk empty next ⦃ p =>
      Mirrors p ((walkOf walk).beginNode empty next.val) ⦄ := by
  unfold fdt.parser.begin_node
  have hs : (walkOf walk).seenRoot = walk.seen_root := rfl
  by_cases h0 : walk.open = 0#usize
  · have h0' := walkOf_open_eq_zero.mpr h0
    refine ite_spec_pos h0 ?_
    by_cases h1 : walk.seen_root = true
    · refine ite_spec_pos h1 ?_
      simp only [MWalk.beginNode, h0', hs, h1, ↓reduceIte, spec_ok, Mirrors, agrees_err_error]
      rfl
    · refine ite_spec_neg h1 ?_
      by_cases h2 : empty = true
      · refine ite_spec_pos h2 ?_
        have : (walkOf walk).beginNode empty next.val = (walkOf walk).push next.val := by
          simp only [MWalk.beginNode, h0', hs, h1, h2, ↓reduceIte, Bool.false_eq_true]
        rw [this]
        exact push_spec walk next
      · refine ite_spec_neg h2 ?_
        simp only [MWalk.beginNode, h0', hs, h1, h2, ↓reduceIte, Bool.false_eq_true, spec_ok,
          Mirrors, agrees_err_error]
        rfl
  · have h0' : ¬ (walkOf walk).open_ = 0 := fun h => h0 (walkOf_open_eq_zero.mp h)
    refine ite_spec_neg h0 ?_
    by_cases h2 : empty = true
    · refine ite_spec_pos h2 ?_
      simp only [MWalk.beginNode, h0', h2, ↓reduceIte, spec_ok, Mirrors, agrees_err_error]
      rfl
    · refine ite_spec_neg h2 ?_
      have : (walkOf walk).beginNode empty next.val = (walkOf walk).push next.val := by
        simp only [MWalk.beginNode, h0', h2, ↓reduceIte, Bool.false_eq_true]
      rw [this]
      exact push_spec walk next

/-- `MAX_PROPERTIES` of the code. -/
theorem max_props_val : fdt.MAX_PROPERTIES.val = 512 := by
  rw [fdt.MAX_PROPERTIES]; rfl

/-- `property(walk, structure, strings, cursor, name, name_end)`:
`MWalk.property`, for a walk within its table whose counts stay within
`MAX_PROPERTIES`, with `dup` the answer of `repeats_name` for the innermost open
node while it has no child. -/
theorem property_spec (walk : fdt.parser.Walk) («structure» strings : Slice U8)
    (cursor «name» name_end : Usize) (dup : Bool)
    (hle : (walkOf walk).open_ ≤ MAX_DEPTH.toNat)
    (hc : ∀ f ∈ (walkOf walk).frames, f.count ≤ MAX_PROPERTIES.toNat)
    (hdup : ∀ f : fdt.parser.Frame, (walkOf walk).open_ ≠ 0 →
      frameOf f = (walkOf walk).frames[(walkOf walk).open_ - 1]! → f.children = false →
      fdt.parser.repeats_name «structure» strings f.properties cursor «name» name_end ⦃ b =>
        b = dup ⦄) :
    fdt.parser.property walk «structure» strings cursor «name» name_end ⦃ p =>
      Mirrors p ((walkOf walk).property dup) ⦄ := by
  unfold fdt.parser.property MWalk.property
  by_cases h0 : walk.open = 0#usize
  · have h0' := walkOf_open_eq_zero.mpr h0
    refine ite_spec_pos h0 ?_
    simp only [h0', ↓reduceIte, spec_ok, Mirrors, agrees_err_error]
    rfl
  · have h0' : ¬ (walkOf walk).open_ = 0 := fun h => h0 (walkOf_open_eq_zero.mp h)
    refine ite_spec_neg h0 ?_
    simp only [h0', ↓reduceIte]
    have hle' : walk.open.val ≤ 32 := hle
    step as ⟨i, i_post⟩
    have hi : i.val < walk.frames.val.length := by scalar_tac
    step as ⟨frame, frame_post⟩
    have hfr : (walkOf walk).frames[(walkOf walk).open_ - 1]! = frameOf frame := by
      simp only [walkOf]; rw [← i_post, frameOf_getElem! _ _ hi, frame_post]
    have hmem : frameOf frame ∈ (walkOf walk).frames := by
      simp only [walkOf, frame_post]; exact List.mem_map_of_mem (List.getElem_mem hi)
    have hcnt : frame.count.val ≤ 512 := hc _ hmem
    rw [hfr]
    by_cases h1 : frame.children = true
    · refine ite_spec_pos h1 ?_
      simp only [frameOf, h1, ↓reduceIte, spec_ok, Mirrors, agrees_err_error]
      rfl
    · refine ite_spec_neg h1 ?_
      have h1' : frame.children = false := by simpa using h1
      simp only [frameOf, h1', Bool.false_eq_true, ↓reduceIte]
      step as ⟨i1, i1_post⟩
      by_cases h2 : i1 > fdt.MAX_PROPERTIES
      · refine ite_spec_pos h2 ?_
        have : MAX_PROPERTIES.toNat < frame.count.val + 1 := by
          have := max_props_val
          show 512 < _; scalar_tac
        simp only [this, ↓reduceIte, spec_ok, Mirrors, agrees_err_error]
        rfl
      · refine ite_spec_neg h2 ?_
        have : ¬ MAX_PROPERTIES.toNat < frame.count.val + 1 := by
          have := max_props_val
          show ¬ 512 < _; scalar_tac
        simp only [this, ↓reduceIte]
        step with hdup frame h0' hfr.symm h1' as ⟨b, b_post⟩
        subst b_post
        by_cases h3 : b = true
        · refine ite_spec_pos h3 ?_
          simp only [h3, ↓reduceIte, spec_ok, Mirrors, agrees_err_error]
          rfl
        · refine ite_spec_neg h3 ?_
          simp only [h3, Bool.false_eq_true, ↓reduceIte]
          step*
          rw [← frame_post] at f_post
          subst index_mut_back_post f_post
          simp only [Mirrors, agrees_ok_ok, true_and, walkOf, Array.set_val_eq, List.map_set,
            MWalk.mk.injEq, and_true]
          rw [i_post]
          simp only [frameOf, MFrame.bump, i1_post, h1']

/-- The piece of the code at a no-operation that `decodeToken` reads. -/
theorem piece_of_nop {o : Option (fdt.nodes.Piece × Usize)} {str strs : ByteArray} {c next : Nat}
    (ho : o.map (fun p => (pieceOf p.1, p.2.val)) = pieceAt str c)
    (hd : decodeToken str strs c = .ok (.nop, next)) :
    ∃ n : Usize, o = some (.Nop, n) ∧ n.val = next := by
  have ht : pieceAt str c = some (.nop, next) := pieceAt_of_decodeToken hd
  rw [ht] at ho
  obtain ⟨⟨p, n⟩, rfl, hp⟩ := Option.map_eq_some_iff.1 ho
  simp only [Prod.mk.injEq] at hp
  obtain ⟨hp, rfl⟩ := hp
  cases p <;> simp_all [pieceOf]

/-- The piece of the code at a property that `decodeToken` reads, with the
offset of its name. -/
theorem piece_of_property {o : Option (fdt.nodes.Piece × Usize)} {str strs : ByteArray}
    {c next : Nat} {nm : String} {v : ByteArray}
    (ho : o.map (fun p => (pieceOf p.1, p.2.val)) = pieceAt str c)
    (hd : decodeToken str strs c = .ok (.property nm v, next)) :
    ∃ (off vs ve n : Usize) (e : Nat), o = some (.Property off vs ve, n) ∧ n.val = next ∧
      cString strs off.val = .ok (nm, e) := by
  obtain ⟨off', e, hcs, -, ht⟩ := (pieceAt_of_decodeToken hd : TokenPiece _ _ _ _ _)
  rw [ht] at ho
  obtain ⟨⟨p, n⟩, rfl, hp⟩ := Option.map_eq_some_iff.1 ho
  simp only [Prod.mk.injEq] at hp
  obtain ⟨hp, rfl⟩ := hp
  cases p with
  | Property off vs ve =>
    simp only [pieceOf, Piece.property.injEq] at hp
    exact ⟨off, vs, ve, n, e, rfl, rfl, hp.1 ▸ hcs⟩
  | _ => simp [pieceOf] at hp

/-- The loop of `repeats_name`: from a token at `start` whose tokens up to
`cursor` are the properties `names` and no-operations, whether `nm`, the bytes
of `wanted`, is among the names. -/
theorem repeats_name_loop_spec («structure» strings : Slice U8) (cursor : Usize)
    (wanted : Slice U8) (start : Usize) (nm : String) (names : List String)
    (hsz : «structure».length + 2 ^ 32 ≤ Usize.max) (hw : bytesOf wanted = nm.toByteArray)
    (hn : NamesFrom (bytesOf «structure») (bytesOf strings) start.val cursor.val names) :
    fdt.parser.repeats_name_loop «structure» strings cursor wanted start ⦃ b =>
      b = names.contains nm ⦄ := by
  unfold fdt.parser.repeats_name_loop
  apply loop.spec_decr_nat
    (measure := fun (a : Usize) => cursor.val - a.val)
    (inv := fun (a : Usize) => ∃ rest, NamesFrom (bytesOf «structure») (bytesOf strings) a.val
      cursor.val rest ∧ rest.contains nm = names.contains nm)
  · rintro a ⟨rest, hr, hc⟩
    unfold fdt.parser.repeats_name_loop.body
    by_cases hlt : a < cursor
    · refine ite_spec_pos hlt ?_
      have hlt' : a.val < cursor.val := by scalar_tac
      step with piece_at_spec «structure» a hsz as ⟨o, o_post⟩
      rcases hr.cases_lt hlt' with ⟨next, hd, hr'⟩ | ⟨n, v, next, rest', rfl, hd, hr'⟩
      · obtain ⟨after, rfl, hn'⟩ := piece_of_nop o_post hd
        step*
        refine ⟨⟨rest, by rw [hn']; exact hr', hc⟩, ?_⟩
        have := decodeToken_next_ge hd; have := hr'.le; omega
      · obtain ⟨earlier, vs, ve, after, e, rfl, hn', hcs⟩ := piece_of_property o_post hd
        have hiff := (nameAt_iff hcs (bytesOf wanted)).trans
          (show n.toByteArray = bytesOf wanted ↔ n = nm by rw [hw, String.toByteArray_inj])
        rw [bytesOf_size] at hiff
        step*
        · have hnm : n = nm := hiff.mp (of_decide_post b_post ‹_›)
          rw [← hc, hnm]
          simp
        · have hnm : n ≠ nm := fun h =>
            ‹¬b = true› (by rw [b_post]; exact decide_eq_true (hiff.mpr h))
          refine ⟨⟨rest', by rw [hn']; exact hr', ?_⟩, ?_⟩
          · rw [← hc, List.contains_cons]
            simp [Ne.symm hnm]
          · have := decodeToken_next_ge hd; have := hr'.le; omega
    · refine ite_spec_neg hlt ?_
      rw [spec_ok]
      have hlt' : ¬ a.val < cursor.val := by scalar_tac
      rw [← hc, hr.eq_nil hlt']
      rfl
  · exact ⟨names, hn, rfl⟩

/-- `repeats_name(structure, strings, from, cursor, name, name_end)`: whether the
name that `cString` reads at `name`, with its NUL at `name_end`, is among the
names of the properties from `from` to `cursor`. -/
@[step] theorem repeats_name_spec («structure» strings : Slice U8)
    (start cursor «name» name_end : Usize) (nm : String) (names : List String)
    (hsz : «structure».length + 2 ^ 32 ≤ Usize.max)
    (hcs : cString (bytesOf strings) «name».val = .ok (nm, name_end.val + 1))
    (hn : NamesFrom (bytesOf «structure») (bytesOf strings) start.val cursor.val names) :
    fdt.parser.repeats_name «structure» strings start cursor «name» name_end ⦃ b =>
      b = names.contains nm ⦄ := by
  unfold fdt.parser.repeats_name
  obtain ⟨hnul, he⟩ := cString_nul hcs
  have hne : name_end.val = «name».val + nm.utf8ByteSize := by omega
  obtain ⟨-, hlt, -, -⟩ := findNul_some hnul
  rw [bytesOf_size] at hlt
  step as ⟨wanted, wanted_post, _⟩
  have hw : bytesOf wanted = nm.toByteArray := by
    rw [bytesOf_slice wanted_post, hne]; exact cString_extract hcs
  exact repeats_name_loop_spec «structure» strings cursor wanted start nm names hsz hw hn

/-- A token of the code as the token of the specification that `decodeToken`
reads, with the offset of the next: a begin node whose name is empty exactly
when the code says so, and a property whose name `cString` reads at the offset
of the code, its NUL at the end of the code. -/
def TokRel (strs : ByteArray) : fdt.parser.Token × Usize → Token × Nat → Prop
  | (.Begin empty, next), (.beginNode nm, N) => next.val = N ∧ empty = decide (nm = "")
  | (.EndNode, next), (.endNode, N) => next.val = N
  | (.Property off nameEnd, next), (.property nm _, N) =>
    next.val = N ∧ cString strs off.val = .ok (nm, nameEnd.val + 1)
  | (.Nop, next), (.nop, N) => next.val = N
  | (.End, next), (.endStructure, N) => next.val = N
  | _, _ => False

/-- `decode_begin(structure, start)`: `decodeBegin`. -/
@[step] theorem decode_begin_spec («structure» strings : Slice U8) (start : Usize)
    (hsz : «structure».length + 2 ^ 32 ≤ Usize.max) :
    fdt.parser.decode_begin «structure» start ⦃ r =>
      Agrees (TokRel (bytesOf strings)) errorOf r
        (decodeBegin (bytesOf «structure») start.val) ⦄ := by
  unfold fdt.parser.decode_begin decodeBegin
  step with c_string_spec «structure» start as ⟨r, r_post⟩
  refine try_spec r_post (fun e => from_residual_spec e) fun nul p hp hE => ?_
  obtain ⟨nm, nameEnd⟩ := p
  obtain ⟨hfn, hp2, hutf⟩ := hp
  simp only at hp2 hutf ⊢
  obtain ⟨hsn, hlt, -, -⟩ := findNul_some hfn
  rw [bytesOf_size] at hlt
  step as ⟨i, i_post⟩
  step with padded_end_spec «structure» i true (by scalar_tac) as ⟨r1, r1_post⟩
  rw [i_post, ← hp2] at r1_post
  refine try_spec r1_post (fun e => from_residual_spec e) fun a after ha hE1 => ?_
  step with name_bytes_spec «structure» start nul false (by omega) as ⟨b, b_post⟩
  rw [all_nameChar hutf, nameChar_false] at b_post
  refine check_else_spec (by rw [b_post]; simp) rfl fun _ _ => ?_
  rw [spec_ok]
  have hsize := utf8ByteSize_of_fromUTF8? hutf
  rw [ByteArray.size_extract, bytesOf_size] at hsize
  refine ⟨ha, ?_⟩
  have : (nul = start) ↔ nm = "" := by
    rw [← String.utf8ByteSize_eq_zero_iff, hsize]
    constructor
    · intro h; rw [h]; omega
    · intro h; exact UScalar.eq_of_val_eq (by omega)
  simp only [this]

/-- `MAX_PROPERTY_NAME` of the code. -/
theorem max_name_val : fdt.MAX_PROPERTY_NAME.val = 64 := by
  rw [fdt.MAX_PROPERTY_NAME]; rfl

/-- `decode_property(structure, strings, start)`: `decodeProperty`. -/
@[step] theorem decode_property_spec (hU : Usize64) («structure» strings : Slice U8) (start : Usize)
    (hsz : «structure».length + 2 ^ 32 ≤ Usize.max) :
    fdt.parser.decode_property «structure» strings start ⦃ r =>
      Agrees (TokRel (bytesOf strings)) errorOf r
        (decodeProperty (bytesOf «structure») (bytesOf strings) start.val) ⦄ := by
  unfold fdt.parser.decode_property decodeProperty
  have hm := usize_max hU
  step as ⟨r, r_post⟩
  refine try_spec r_post (fun e => from_residual_spec e) fun v len hv hE => ?_
  have hl := u32At_ok_le hE
  rw [bytesOf_size] at hl
  subst hv
  step as ⟨length, length_post⟩
  have hlen : length.val = v.val := by rw [length_post, U32.cast_Usize_val_eq]
  step as ⟨i, i_post⟩
  step as ⟨r1, r1_post⟩
  rw [i_post] at r1_post
  refine try_spec r1_post (fun e => from_residual_spec e) fun v1 off hv1 hE1 => ?_
  have hl1 := u32At_ok_le hE1
  rw [bytesOf_size] at hl1
  subst hv1
  step as ⟨nameU, name_post⟩
  have hname : nameU.val = v1.val := by rw [name_post, U32.cast_Usize_val_eq]
  step as ⟨i1, i1_post⟩
  step as ⟨o, o_post⟩
  rw [word32_toNat, ← hlen, word32_toNat, ← hname]
  cases o with
  | none =>
    rw [checkedAdd_of_not_lt (by scalar_tac), except_error_bind, spec_ok]
    rfl
  | some e =>
    obtain ⟨hle, he, -⟩ := o_post
    rw [checkedAdd_of_lt (by scalar_tac), except_ok_bind]
    simp only
    refine check_spec (by rw [UScalar.lt_equiv, Slice.len_val, bytesOf_size, he, i1_post]) rfl
      fun _ hnt => ?_
    step with c_string_spec strings nameU as ⟨r2, r2_post⟩
    refine try_spec r2_post (fun e => from_residual_spec e) fun nul p hp hE2 => ?_
    obtain ⟨nm, nmEnd⟩ := p
    obtain ⟨hfn, hp2, hutf⟩ := hp
    simp only at hp2 hutf hE2 ⊢
    obtain ⟨hsn, hlt, -, -⟩ := findNul_some hfn
    rw [bytesOf_size] at hlt
    have hsize := utf8ByteSize_of_fromUTF8? hutf
    rw [ByteArray.size_extract, bytesOf_size] at hsize
    rw [Bool.or_assoc]
    refine check_or_spec (by
      rw [String.isEmpty_iff, ← String.utf8ByteSize_eq_zero_iff, hsize]
      constructor
      · intro h; rw [h]; omega
      · intro h; exact UScalar.eq_of_val_eq (by omega)) rfl fun hne => ?_
    have hne' : nul.val ≠ nameU.val := fun h => hne (UScalar.eq_of_val_eq h)
    step as ⟨i3, i3_post⟩
    step as ⟨i4, i4_post⟩
    have hi4 : i4.val = nm.utf8ByteSize := by
      rw [i4_post, UScalar.cast_val_eq, Nat.mod_eq_of_lt (by scalar_tac), i3_post]; omega
    refine check_or_spec (by
      rw [gt_iff_lt, UScalar.lt_equiv, max_name_val, hi4, decide_eq_true_iff]; rfl) rfl
      fun _ => ?_
    step with name_bytes_spec strings nameU nul true (by omega) as ⟨b, b_post⟩
    rw [all_nameChar hutf, nameChar_true] at b_post
    refine check_else_spec (by rw [b_post]; simp) rfl fun _ _ => ?_
    step with padded_end_spec «structure» e false (by scalar_tac) as ⟨r3, r3_post⟩
    rw [he, i1_post] at r3_post
    refine try_spec r3_post (fun e => from_residual_spec e) fun a after ha hE3 => ?_
    rw [spec_ok]
    exact ⟨ha, by rw [hE2, hp2]⟩

/-- Two words are equal exactly when their values are. -/
theorem u32_eq_iff {v w : U32} : v = w ↔ v.val = w.val :=
  ⟨fun h => h ▸ rfl, UScalar.eq_of_val_eq⟩

/-- `decode_token(structure, strings, cursor)`: the token that `decodeToken`
reads and the offset of the next, or its error. -/
@[step] theorem decode_token_spec (hU : Usize64) («structure» strings : Slice U8) (cursor : Usize)
    (hsz : «structure».length + 2 ^ 32 ≤ Usize.max) :
    fdt.parser.decode_token «structure» strings cursor ⦃ r =>
      Agrees (TokRel (bytesOf strings)) errorOf r
        (decodeToken (bytesOf «structure») (bytesOf strings) cursor.val) ⦄ := by
  unfold fdt.parser.decode_token
  rw [decodeToken_eq]
  step as ⟨r, r_post⟩
  refine try_spec r_post (fun e => from_residual_spec e) fun tag t ht hE => ?_
  have hl := u32At_ok_le hE
  rw [bytesOf_size] at hl
  subst ht
  step as ⟨next, next_post⟩
  rw [word32_toNat]
  unfold decodeTag
  rw [← next_post]
  refine ite_agrees_spec (u32_eq_iff (w := 1#u32))
    (fun _ => decode_begin_spec «structure» strings next hsz) fun _ => ?_
  refine ite_agrees_spec (u32_eq_iff (w := 2#u32)) (fun _ => (spec_ok _).mpr rfl) fun _ => ?_
  refine ite_agrees_spec (u32_eq_iff (w := 3#u32))
    (fun _ => decode_property_spec hU «structure» strings next hsz) fun _ => ?_
  refine ite_agrees_spec (u32_eq_iff (w := 4#u32)) (fun _ => (spec_ok _).mpr rfl) fun _ => ?_
  refine ite_agrees_spec (u32_eq_iff (w := 9#u32)) (fun _ => (spec_ok _).mpr rfl) fun _ => ?_
  exact (spec_ok _).mpr rfl

/-- `place(walk, structure, strings, token, cursor, next)`: for a walk of the
code that stands for a walk of the specification at the cursor, and the token
that `decodeToken` reads there, what `stepOf` gives: the same error, the end
of the walk at the end token, or a walk that stands for the walk after the
token at the next cursor. -/
theorem place_spec (walk : fdt.parser.Walk) («structure» strings : Slice U8)
    (token : fdt.parser.Token) (cursor next : Usize) (W : Walk) (T : Token) (N : Nat)
    (hsz : «structure».length + 2 ^ 32 ≤ Usize.max)
    (hR : MRel (bytesOf «structure») (bytesOf strings) (walkOf walk) W cursor.val)
    (hd : decodeToken (bytesOf «structure») (bytesOf strings) cursor.val = .ok (T, N))
    (ht : TokRel (bytesOf strings) (token, next) (T, N)) :
    fdt.parser.place walk «structure» strings token cursor next ⦃ p =>
      Agrees (Placed (bytesOf «structure») (bytesOf strings) (walkOf p.2) N) errorOf p.1
        (stepOf W T N (bytesOf «structure»).size) ⦄ := by
  unfold fdt.parser.place
  cases token <;> cases T <;> simp only [TokRel] at ht
  · obtain ⟨hn, he⟩ := ht
    subst he hn
    exact spec_mono (begin_node_spec walk _ next) fun p hp => follows_place hp (mrel_begin hR)
  · subst ht
    exact spec_mono (end_node_spec walk) fun p hp => follows_place hp (mrel_endNode hR)
  · rename_i off nameEnd nm v
    obtain ⟨hn, hcs⟩ := ht
    subst hn
    let dup := match W.open_ with
      | f :: _ => f.names.contains nm
      | [] => false
    refine spec_mono (property_spec walk «structure» strings cursor off nameEnd dup hR.le hR.counts
      ?_) fun p hp => follows_place hp (mrel_property hR hd ?_)
    · intro f ho hf hc
      obtain ⟨g, rest, hW, hch, -⟩ := mrel_open_cons hR ho
      rw [← hf] at hch
      have hg : g.children = false := by rw [← hch]; exact hc
      obtain ⟨-, hnames⟩ := hR.inner g rest hW hg
      rw [← hf] at hnames
      refine spec_mono (repeats_name_spec «structure» strings f.properties cursor off nameEnd nm
        g.names hsz hcs hnames) fun b hb => ?_
      simp only [dup, hW, hb]
    · intro f rest hW _
      simp only [dup, hW]
  · subst ht
    rw [spec_ok]
    exact placed_nop hR hd
  · subst ht
    step with end_structure_spec walk next (Slice.len «structure») as ⟨r, r_post⟩
    rw [Slice.len_val, ← bytesOf_size] at r_post
    exact placed_end hR r_post

/-- The offset of the next token of a token that `TokRel` relates. -/
theorem tokRel_next {strs : ByteArray} {tok : fdt.parser.Token} {next : Usize} {T : Token} {N : Nat}
    (h : TokRel strs (tok, next) (T, N)) : next.val = N := by
  cases tok <;> cases T <;> simp only [TokRel] at h <;> first | exact h | exact h.1

/-- The loop of `walk_tokens`: from a walk that stands for the walk `W` of the
specification at `cursor`, after `read` tokens, the walk of `walkTokens` from
there, up to its records. -/
theorem walk_tokens_loop_spec (hU : Usize64) («structure» strings : Slice U8)
    (walk : fdt.parser.Walk) (cursor read : Usize) (W : Walk)
    (hsz : «structure».length + 2 ^ 32 ≤ Usize.max)
    (hR : MRel (bytesOf «structure») (bytesOf strings) (walkOf walk) W cursor.val)
    (hr : read.val ≤ MAX_TOKENS.toNat) :
    fdt.parser.walk_tokens_loop «structure» strings walk cursor read ⦃ r =>
      Agrees (fun _ _ => True) errorOf r (walkTokens (bytesOf «structure») (bytesOf strings)
        (MAX_TOKENS.toNat - read.val) cursor.val W) ⦄ := by
  unfold fdt.parser.walk_tokens_loop
  apply loop.spec_decr_nat
    (measure := fun (x : fdt.parser.Walk × Usize × Usize) => MAX_TOKENS.toNat - x.2.2.val)
    (inv := fun (x : fdt.parser.Walk × Usize × Usize) => ∃ W',
      MRel (bytesOf «structure») (bytesOf strings) (walkOf x.1) W' x.2.1.val ∧
      x.2.2.val ≤ MAX_TOKENS.toNat ∧
      (fun _ => ()) <$> walkTokens (bytesOf «structure») (bytesOf strings)
        (MAX_TOKENS.toNat - x.2.2.val) x.2.1.val W' =
      (fun _ => ()) <$> walkTokens (bytesOf «structure») (bytesOf strings)
        (MAX_TOKENS.toNat - read.val) cursor.val W)
  · rintro ⟨w, c, rd⟩ ⟨W', hR', hrd, hE⟩
    simp only at hR' hrd hE
    unfold fdt.parser.walk_tokens_loop.body
    step with tokens_spec as ⟨i, i_post⟩
    by_cases hlt : rd < i
    · refine ite_spec_pos hlt ?_
      have hlt' : rd.val < MAX_TOKENS.toNat := by rw [← i_post]; scalar_tac
      rw [show MAX_TOKENS.toNat - rd.val = (MAX_TOKENS.toNat - rd.val - 1) + 1 by omega,
        walkTokens_succ] at hE
      step with decode_token_spec hU «structure» strings c hsz as ⟨r, r_post⟩
      cases hdec : decodeToken (bytesOf «structure») (bytesOf strings) c.val with
      | error e =>
        rw [hdec] at r_post hE
        obtain ⟨x, rfl, hx⟩ := eq_err_of_agrees r_post
        refine branch_err_spec ?_
        step with from_residual_spec x as ⟨r1, r1_post⟩
        rw [r1_post]
        refine agrees_true_of_map_eq hE ?_
        rw [except_error_bind, agrees_err_error, hx]
      | ok p =>
        obtain ⟨T, N⟩ := p
        rw [hdec] at r_post hE
        obtain ⟨⟨token, next⟩, rfl, ht⟩ := eq_ok_of_agrees r_post
        refine branch_ok_spec ?_
        have hn := tokRel_next ht
        step with place_spec w «structure» strings token c next W' T N hsz hR' hdec ht
        rename_i w1
        rw [except_ok_bind] at hE
        cases hs : stepOf W' T N (bytesOf «structure»).size with
        | error e =>
          rw [hs] at r_post hE
          obtain ⟨x, rfl, hx⟩ := eq_err_of_agrees r_post
          refine branch_err_spec ?_
          step with from_residual_spec x as ⟨r2, r2_post⟩
          rw [r2_post]
          refine agrees_true_of_map_eq hE ?_
          rw [except_error_bind, agrees_err_error, hx]
        | ok o =>
          rw [hs] at r_post hE
          obtain ⟨b, rfl, hb⟩ := eq_ok_of_agrees r_post
          refine branch_ok_spec ?_
          rw [except_ok_bind] at hE
          cases o with
          | none =>
            simp only [Placed] at hb
            subst hb
            simp only [↓reduceIte, spec_ok]
            exact agrees_true_of_map_eq hE trivial
          | some W2 =>
            obtain ⟨rfl, hR2⟩ := hb
            simp only [Bool.false_eq_true, ↓reduceIte]
            step as ⟨read1, read1_post⟩
            refine ⟨⟨W2, by rw [hn]; exact hR2, by omega, ?_⟩, by omega⟩
            simp only at hE ⊢
            rw [read1_post, show MAX_TOKENS.toNat - (rd.val + 1) = MAX_TOKENS.toNat - rd.val - 1 by
              omega, hn]
            exact hE
    · refine ite_spec_neg hlt ?_
      rw [spec_ok]
      have h0 : MAX_TOKENS.toNat - rd.val = 0 := by rw [← i_post]; scalar_tac
      rw [h0] at hE
      exact agrees_true_of_map_eq hE rfl
  · exact ⟨W, hR, hr, rfl⟩

/-- The walk of the code before the first token, as numbers. -/
theorem walkOf_start :
    walkOf ({ frames := Array.repeat 32#usize fdt.parser.NO_FRAME, «open» := 0#usize,
              seen_root := false } : fdt.parser.Walk) =
      ⟨List.replicate 32 ⟨0, 0, false⟩, 0, false⟩ := by
  simp [walkOf, fdt.parser.NO_FRAME, frameOf]

/-- `walk_tokens(structure, strings)`: `walkTokens` over the structure block
from its start with the fuel `MAX_TOKENS`, up to its records, for a block
whose size leaves room for a value of 32 bits. -/
@[step] theorem walk_tokens_spec (hU : Usize64) («structure» strings : Slice U8)
    (hsz : «structure».length + 2 ^ 32 ≤ Usize.max) :
    fdt.parser.walk_tokens «structure» strings ⦃ r =>
      Agrees (fun _ _ => True) errorOf r (walkTokens (bytesOf «structure») (bytesOf strings)
        MAX_TOKENS.toNat 0 Walk.start) ⦄ := by
  unfold fdt.parser.walk_tokens
  have h := walk_tokens_loop_spec hU «structure» strings
    { frames := Array.repeat 32#usize fdt.parser.NO_FRAME, «open» := 0#usize, seen_root := false }
    0#usize 0#usize Walk.start hsz (by rw [walkOf_start]; exact mrel_start) (by simp)
  simpa using h

/-- `Fdt::parse(input)`: the statement `FdtParse`. -/
theorem fdt_parse_spec (hU : Usize64) (input : Slice U8) :
    fdt.parser.Fdt.parse input ⦃ r => Agrees FdtRepr errorOf r (Fdt.parse (bytesOf input)) ⦄ := by
  unfold fdt.parser.Fdt.parse Fdt.parse
  have hm := usize_max hU
  step with header_spec hU input as ⟨r, r_post⟩
  refine try_spec r_post (fun e => from_residual_spec e) fun l h hl hh => ?_
  have F := header_facts hh
  have htl := F.total_le
  rw [bytesOf_size] at htl
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hl
  step as ⟨blob, blob_post, _⟩
  have hb : bytesOf blob = h.blob := by rw [bytesOf_slice blob_post, h1, F.blob]
  have hbl : blob.length = h.layout.total := by rw [← bytesOf_size, hb, F.blob_size]
  step with reservation_map_spec hU blob l h ⟨h1, h2, h3, h4, h5, h6⟩ hb as ⟨r1, r1_post⟩
  refine try_spec r1_post (fun e => from_residual_spec e) fun e1 rs he1 hrs => ?_
  have hse := F.struct_end_le
  have hge := F.strings_end_le
  have hsl : h.layout.structStart ≤ h.layout.structEnd := by simp [Layout.structEnd]
  have hgl : h.layout.stringsStart ≤ h.layout.stringsEnd := by simp [Layout.stringsEnd]
  step as ⟨str, str_post, _⟩
  step as ⟨sg, sg_post, _⟩
  have hst : bytesOf str = h.structure_ := by
    rw [bytesOf_slice str_post, hb, h2, h3, F.structure_eq]
  have hsg : bytesOf sg = h.strings := by
    rw [bytesOf_slice sg_post, hb, h4, h5, F.strings_eq]
  have hsz : str.length + 2 ^ 32 ≤ Usize.max := by
    have := F.total_max
    have : str.length ≤ blob.length := by
      rw [← bytesOf_size, ← bytesOf_size, hst, hb]; exact (header_sizes hh).2.1
    simp only [MAX_BLOB_SIZE, UInt64.reduceToNat] at *
    omega
  step with walk_tokens_spec hU str sg hsz as ⟨r2, r2_post⟩
  rw [hst, hsg] at r2_post
  refine try_spec (E := structureNodes h) r2_post (fun e => from_residual_spec e)
    fun _ recs _ hrecs => ?_
  obtain ⟨-, hre⟩ := reservationMap_ok hrs
  step as ⟨s, s_post, _⟩
  refine fdtRepr_of_header _ hh ?_ hb hst hsg ?_
  · rw [Fdt.parse, hh, except_ok_bind, hrs, except_ok_bind, hrecs]
    rfl
  · rw [bytesOf_slice s_post, hb, h6, he1]

end Krepi.Proofs.Fdt.Refinement
