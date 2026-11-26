module

public import Krepi.Proofs.Fdt.Refinement.TreeSpecLemmas
public import Krepi.Proofs.Fdt.Refinement.ParseHeaderSpecLemmas
public import Krepi.Spec.Fdt.Translate
import Krepi.Proofs.Fdt.ExceptLemmas

/-!
# Device tree: lemmas about the specification of the node properties

Lemmas about the property entries of `Krepi.Spec.Fdt.Nodes` and the node
entries of `Krepi.Spec.Fdt.Translate`, for the refinement proofs of the
properties, cell counts, regions, address maps and the translation of a
`reg`. The module imports no generated definitions, so it is built once and
not again for every mutant of the code.

- The walk of the properties: `propsFrom_decode` (a walk of `propsFrom` that
  succeeds reads a token), `propsFrom_property_some`, `propsFrom_nop_some`
  and `propsFrom_end_some` (what it gives for each token),
  `propValue` (the value of the first property of a name, the lookup of
  `Node.property`) with `propValue_nil`, `propValue_cons` and
  `node_property_eq`, and `pieceAt_property_le` (a property that `pieceAt`
  reads lies within the block).
- Names: `toByteArray_eq_toUTF8` (two strings with the same bytes are
  equal), `RangeRepr` (a range of a block of the code holds a value), and
  the bytes of the names that the code writes as arrays: `bytes_status`,
  `bytes_okay`, `bytes_ok`, `bytes_reg`, `bytes_ranges`, `bytes_dma_ranges`,
  `bytes_address_cells`, `bytes_size_cells`.
- Strings: `except_throw_eq`, `stringOf` (the string of a value as
  `Node.stringProperty` reads it) with `stringProperty_none`,
  `stringProperty_some`, `stringOf_none`, `stringOf_invalid`,
  `stringOf_valid` and `stringOf_extract`; `enabled_eq`.
- Cells: `cellCount_none`, `cellCount_some` and `u32At_extract_zero`.
- The node entries with a parent: `node_reg_none`, `node_reg_absent`,
  `node_reg_present`, `mapOf` (the map of `Node.addressMap` of a node with its
  parent) with `node_addressMap_none` and `node_addressMap_some`,
  `climbRanges_zero`, `climbRanges_none`, `climbRanges_some`,
  `node_translateReg_none` and `node_translateReg_some`.
-/

@[expose] public section

open Aeneas Aeneas.Std
open Krepi.Statements Krepi.Spec.Fdt Krepi.Proofs.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## The walk of the properties -/

section Props

variable {str strs : ByteArray}

/-- A walk of `propsFrom` that succeeds reads a token at its cursor. -/
theorem propsFrom_decode {f c : Nat} {ps : List (String × ByteArray)}
    (h : propsFrom str strs f c = some ps) :
    ∃ f' tok next, f = f' + 1 ∧ decodeToken str strs c = .ok (tok, next) := by
  cases f with
  | zero => cases h
  | succ f =>
    rcases hd : decodeToken str strs c with e | ⟨tok, next⟩
    · rw [propsFrom, hd] at h; cases h
    · exact ⟨f, tok, next, rfl, rfl⟩

/-- A property heads the list of a walk of `propsFrom` that succeeds. -/
theorem propsFrom_property_some {f c next : Nat} {nm : String} {v : ByteArray}
    {ps : List (String × ByteArray)} (hd : decodeToken str strs c = .ok (.property nm v, next))
    (h : propsFrom str strs (f + 1) c = some ps) :
    ∃ ps', ps = (nm, v) :: ps' ∧ propsFrom str strs f next = some ps' := by
  rw [propsFrom_property hd] at h
  obtain ⟨ps', h1, h2⟩ := Option.map_eq_some_iff.1 h
  exact ⟨ps', h2.symm, h1⟩

/-- A no-operation is skipped by a walk of `propsFrom`. -/
theorem propsFrom_nop_some {f c next : Nat} {ps : List (String × ByteArray)}
    (hd : decodeToken str strs c = .ok (.nop, next)) (h : propsFrom str strs (f + 1) c = some ps) :
    propsFrom str strs f next = some ps := by
  rwa [propsFrom_nop hd] at h

/-- A begin node, an end node or the end token ends a walk of `propsFrom`. -/
theorem propsFrom_end_some {f c next : Nat} {tok : Token} {ps : List (String × ByteArray)}
    (hd : decodeToken str strs c = .ok (tok, next))
    (ht : tok = .endStructure ∨ tok = .endNode ∨ ∃ nm, tok = .beginNode nm)
    (h : propsFrom str strs (f + 1) c = some ps) : ps = [] := by
  rw [propsFrom_end hd ht] at h
  exact (Option.some.inj h).symm

end Props

/-- The value of the first property named `s` among `ps`: the lookup of
`Node.property`. -/
def propValue (ps : List (String × ByteArray)) (s : String) : Option ByteArray :=
  (ps.find? (·.1 == s)).map (·.2)

theorem propValue_nil (s : String) : propValue [] s = none := rfl

theorem propValue_cons (nm : String) (v : ByteArray) (ps : List (String × ByteArray))
    (s : String) : propValue ((nm, v) :: ps) s = if nm = s then some v else propValue ps s := by
  by_cases h : nm = s
  · simp [propValue, h]
  · simp [propValue, h]

theorem node_property_eq (N : Node) (s : String) :
    N.property s = propValue N.record.properties s := rfl

/-- A property that `pieceAt` reads lies within the block. -/
theorem pieceAt_property_le {b : ByteArray} {c off vs ve n : Nat}
    (h : pieceAt b c = some (.property off vs ve, n)) : vs ≤ ve ∧ ve ≤ b.size := by
  unfold pieceAt at h
  split at h
  · cases h
  · split at h
    · obtain ⟨_, -, h⟩ := Option.map_eq_some_iff.1 h
      cases h
    · split at h
      · split at h
        · split at h
          · cases h
          · cases h; omega
        · cases h
      · split at h
        · cases h
        · split at h <;> cases h

/-! ## Names -/

/-- Two strings with the same bytes are equal. -/
theorem toByteArray_eq_toUTF8 {a s : String} : a.toByteArray = s.toUTF8 ↔ a = s := by
  rw [String.toUTF8_eq_toByteArray]
  exact String.toByteArray_inj

/-- The range `[r.1, r.2)` of the block `b` of the code holds the value `v`. -/
def RangeRepr (b : Slice U8) (r : Usize × Usize) (v : ByteArray) : Prop :=
  r.1.val ≤ r.2.val ∧ r.2.val ≤ b.length ∧ (bytesOf b).extract r.1.val r.2.val = v

theorem bytes_status :
    bytesOf (Array.to_slice (Array.make 6#usize [115#u8, 116#u8, 97#u8, 116#u8, 117#u8, 115#u8])) =
      "status".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

theorem bytes_okay :
    bytesOf (Array.to_slice (Array.make 4#usize [111#u8, 107#u8, 97#u8, 121#u8])) =
      "okay".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

theorem bytes_ok :
    bytesOf (Array.to_slice (Array.make 2#usize [111#u8, 107#u8])) = "ok".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

theorem bytes_reg :
    bytesOf (Array.to_slice (Array.make 3#usize [114#u8, 101#u8, 103#u8])) = "reg".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

theorem bytes_ranges :
    bytesOf (Array.to_slice (Array.make 6#usize [114#u8, 97#u8, 110#u8, 103#u8, 101#u8, 115#u8])) =
      "ranges".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

theorem bytes_dma_ranges :
    bytesOf (Array.to_slice (Array.make 10#usize [100#u8, 109#u8, 97#u8, 45#u8, 114#u8, 97#u8,
      110#u8, 103#u8, 101#u8, 115#u8])) = "dma-ranges".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

theorem bytes_address_cells :
    bytesOf (Array.to_slice (Array.make 14#usize [35#u8, 97#u8, 100#u8, 100#u8, 114#u8, 101#u8,
      115#u8, 115#u8, 45#u8, 99#u8, 101#u8, 108#u8, 108#u8, 115#u8])) =
      "#address-cells".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

theorem bytes_size_cells :
    bytesOf (Array.to_slice (Array.make 11#usize [35#u8, 115#u8, 105#u8, 122#u8, 101#u8, 45#u8,
      99#u8, 101#u8, 108#u8, 108#u8, 115#u8])) = "#size-cells".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

/-! ## Strings -/

theorem except_throw_eq {ε α : Type} (e : ε) : (throw e : Except ε α) = .error e := by
  simp [throw, throwThe, MonadExceptOf.throw]

/-- The string of a value as `Node.stringProperty` reads it. -/
def stringOf (value : ByteArray) : Except Krepi.Spec.Fdt.Error (Option String) := do
  let (s, e) ← cString value 0
  if e ≠ value.size then throw .badProperty
  pure (some s)

theorem stringProperty_none {N : Node} {key : String} (h : N.property key = none) :
    N.stringProperty key = .ok none := by
  simp only [Node.stringProperty, h]

theorem stringProperty_some {N : Node} {key : String} {v : ByteArray}
    (h : N.property key = some v) : N.stringProperty key = stringOf v := by
  simp only [Node.stringProperty, h]
  rfl

/-- A value without a NUL. -/
theorem stringOf_none {v : ByteArray} (h : findNul v 0 = none) :
    stringOf v = .error .badString := by
  simp only [stringOf, cString, h]
  rfl

/-- A value whose bytes before the NUL are not UTF-8. -/
theorem stringOf_invalid {v : ByteArray} {nul : Nat} (h : findNul v 0 = some nul)
    (hu : String.fromUTF8? (v.extract 0 nul) = none) : stringOf v = .error .badString := by
  simp only [stringOf, cString, h, hu]
  rfl

/-- A value whose bytes before the NUL are the string `s`. -/
theorem stringOf_valid {v : ByteArray} {nul : Nat} {s : String} (h : findNul v 0 = some nul)
    (hu : String.fromUTF8? (v.extract 0 nul) = some s) :
    stringOf v = if nul + 1 ≠ v.size then .error .badProperty else .ok (some s) := by
  simp only [stringOf, cString, h, hu, except_ok_bind]
  by_cases he : nul + 1 = v.size
  · simp only [he, ne_eq, not_true_eq_false, ↓reduceIte]
    rfl
  · simp only [he, ne_eq, not_false_eq_true, ↓reduceIte, except_throw_eq]
    rfl

/-- The bytes of the string that a range of a block holds before its NUL. -/
theorem stringOf_extract {b : ByteArray} {i j nul : Nat} {s : String} (hij : i ≤ j)
    (hn : nul ≤ j - i) (hu : String.fromUTF8? ((b.extract i j).extract 0 nul) = some s) :
    b.extract i (i + nul) = s.toUTF8 := by
  rw [String.toUTF8_eq_toByteArray, toByteArray_of_fromUTF8? hu, ByteArray.extract_extract,
    Nat.add_zero, Nat.min_eq_left (by omega)]

theorem enabled_eq (N : Node) : N.enabled = N.stringProperty "status" >>= fun o =>
    match o with
    | none => pure true
    | some s => pure (s == "okay" || s == "ok") := rfl

/-! ## Cells -/

theorem cellCount_none {N : Node} {key : String} (d : UInt32) (h : N.property key = none) :
    N.cellCount key d = .ok d := by
  simp only [Node.cellCount, h]

theorem cellCount_some {N : Node} {key : String} {v : ByteArray} (d : UInt32)
    (h : N.property key = some v) :
    N.cellCount key d = if v.size = 4 then u32At v 0 else .error .badProperty := by
  simp only [Node.cellCount, h]

/-- The word at the start of a range of 4 bytes is the word of the block. -/
theorem u32At_extract_zero {b : ByteArray} {s e : Nat} (h : e - s = 4) (he : e ≤ b.size) :
    u32At (b.extract s e) 0 = u32At b s := by
  rw [u32At_extract (by omega) he, Nat.add_zero]

/-! ## The node entries with a parent -/

theorem node_reg_none {N : Node} (h : N.parent = none) : N.reg = .error .badTree := by
  simp only [Node.reg, h, except_throw_eq]

theorem node_reg_absent {N P : Node} (h : N.parent = some P) (hv : N.property "reg" = none) :
    N.reg = .error .missingProperty := by
  simp only [Node.reg, h, hv, except_throw_eq]

theorem node_reg_present {N P : Node} {v : ByteArray} (h : N.parent = some P)
    (hv : N.property "reg" = some v) :
    N.reg = (P.addressCells >>= fun ac => P.sizeCells >>= fun sc => Reg.new v ac sc) := by
  simp only [Node.reg, h, hv]

/-- `Node.addressMap` of a node with the parent `p`. -/
def mapOf (n p : Node) (key : String) : Except Krepi.Spec.Fdt.Error AddressMap := do
  let childCells ← n.addressCells
  let parentCells ← p.addressCells
  let sizeCells ← n.sizeCells
  AddressMap.new (n.property key) childCells parentCells sizeCells

theorem node_addressMap_none {N : Node} (h : N.parent = none) (key : String) :
    N.addressMap key = .error .badTree := by
  simp only [Node.addressMap, h, except_throw_eq]

theorem node_addressMap_some {N P : Node} (h : N.parent = some P) (key : String) :
    N.addressMap key = mapOf N P key := by
  simp only [Node.addressMap, h]
  rfl

theorem climbRanges_zero (B : Node) (s : Span) : climbRanges 0 B s = .error .limitExceeded := rfl

theorem climbRanges_none {k : Nat} {B : Node} (h : B.parent = none) (s : Span) :
    climbRanges (k + 1) B s = .ok s := by
  simp only [climbRanges, h]

theorem climbRanges_some {k : Nat} {B U : Node} (h : B.parent = some U) (s : Span) :
    climbRanges (k + 1) B s = mapOf B U "ranges" >>= fun m =>
      m.toParent s >>= fun t => climbRanges k U t := by
  simp only [climbRanges, h, Node.ranges, node_addressMap_some h]

theorem node_translateReg_none {N : Node} (h : N.parent = none) (s : Span) :
    N.translateReg s = .error .badTree := by
  simp only [Node.translateReg, h, except_throw_eq]

theorem node_translateReg_some {N B : Node} (h : N.parent = some B) (s : Span) :
    N.translateReg s =
      (climbRanges MAX_DEPTH.toNat B s >>= fun t => t.endAddr >>= fun _ => pure t) := by
  simp only [Node.translateReg, h]

end Krepi.Proofs.Fdt.Refinement
