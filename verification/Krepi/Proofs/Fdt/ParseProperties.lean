module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
public import Krepi.Proofs.Fdt.ExceptLemmas
public import Krepi.Proofs.Fdt.ParseBytes
public import Krepi.Proofs.Fdt.ParseSteps
public import Krepi.Proofs.Fdt.ParseBuilt

/-!
# Device tree: the parse at the limit of the properties of a node

The parse of `treeOfProperties n`, the root with the `n` properties `p0`,
`p1`, ...: their names are distinct, at most 4 bytes of a letter and digits
without a NUL byte (`propName_inj`, `propName_size`, `propName_bytes`,
`propName_chars`), each property token decodes to its name from the strings
block (`prop_decode`), and each is placed in the root (`place_prop`) up to
`MAX_PROPERTIES`, beyond which the place fails with `LimitExceeded`
(`place_prop_over`).
-/

@[expose] public section

namespace Krepi.Proofs.Fdt

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

/-! ## Names -/

/-- A character of the property names of the tree: `p` or a decimal digit. -/
def PropChar (c : Char) : Prop := (c = 'p' ∨ c.isDigit = true)

/-- Such a character is one byte from 48 to 127. -/
theorem propChar_val {c : Char} (h : PropChar c) : 48 ≤ c.val.toNat ∧ c.val.toNat ≤ 127 := by
  rcases h with rfl | h
  · decide
  · simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    simp only [UInt32.le_iff_toNat_le] at h1 h2
    constructor
    · exact Nat.le_trans (by decide) h1
    · exact Nat.le_trans h2 (by decide)

/-- Such a character encodes as its one byte. -/
theorem encode_propChar {c : Char} (h : PropChar c) :
    String.utf8EncodeChar c = [c.val.toUInt8] := by
  apply String.utf8EncodeChar_eq_singleton
  rw [Char.utf8Size_eq_one_iff, UInt32.le_iff_toNat_le]
  exact (propChar_val h).2

/-- The bytes of a string of such characters. -/
theorem bytes_ofList {l : List Char} (h : ∀ c ∈ l, PropChar c) :
    (String.ofList l).toByteArray.toList = l.map fun c => c.val.toUInt8 := by
  rw [String.toByteArray_ofList, byteArray_toList, List.utf8Encode, List.toList_data_toByteArray]
  induction l with
  | nil => rfl
  | cons c l ih =>
    rw [List.flatMap_cons, encode_propChar (h c List.mem_cons_self),
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

/-- The name `p` and the digits of `i`. -/
theorem propName_eq (i : Nat) : "p" ++ toString i = String.ofList ('p' :: Nat.toDigits 10 i) := by
  apply String.toList_injective
  rw [String.toList_append, String.toList_ofList]
  simp [Nat.toString_eq_repr, Nat.toList_repr]

/-- The characters of a name are such characters. -/
theorem propChars (i : Nat) : ∀ c ∈ 'p' :: Nat.toDigits 10 i, PropChar c := by
  intro c hc
  rcases List.mem_cons.1 hc with rfl | hc
  · exact Or.inl rfl
  · exact Or.inr (Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)

/-- Distinct indices give distinct names. -/
theorem propName_inj {i j : Nat} (h : "p" ++ toString i = "p" ++ toString j) : i = j := by
  rw [propName_eq, propName_eq] at h
  have := congrArg String.toList h
  simp only [String.toList_ofList, List.cons.injEq, true_and] at this
  rw [← Nat.ofDigitChars_ten_toDigits (n := i), this, Nat.ofDigitChars_ten_toDigits]

/-- The bytes of a name hold no NUL. -/
theorem propName_bytes (i : Nat) : 0 ∉ ("p" ++ toString i).toByteArray.toList := by
  rw [propName_eq, bytes_ofList (propChars i)]
  intro h
  obtain ⟨c, hc, h0⟩ := List.mem_map.1 h
  have := propChar_val (propChars i c hc)
  have h1 := congrArg UInt8.toNat h0
  rw [UInt32.toNat_toUInt8] at h1
  have h2 : (0 : UInt8).toNat = 0 := rfl
  omega

/-- A name of an index below 1000 is nonempty and of at most 4 bytes. -/
theorem propName_size (i : Nat) (hi : i < 1000) : ("p" ++ toString i).utf8ByteSize ≤ 4 ∧
    ("p" ++ toString i) ≠ "" := by
  have hl : ("p" ++ toString i).utf8ByteSize = 1 + (Nat.toDigits 10 i).length := by
    have : ("p" ++ toString i).utf8ByteSize = ("p" ++ toString i).toByteArray.toList.length := by
      rw [byteArray_toList, Array.length_toList]; rfl
    rw [this, propName_eq, bytes_ofList (propChars i)]
    simp; omega
  have h3 := (Nat.length_toDigits_le_iff (b := 10) (n := i) (k := 3) (by decide) (by decide)).2
    (by simpa using hi)
  refine ⟨by omega, ?_⟩
  intro h
  rw [h] at hl
  simp at hl
  omega

/-- The characters of a name are property name characters. -/
theorem propName_chars (i : Nat) : ("p" ++ toString i).toList.all isPropertyNameChar = true := by
  rw [propName_eq, String.toList_ofList, List.all_eq_true]
  intro c hc
  rcases propChars i c hc with rfl | h
  · decide
  · simp [isPropertyNameChar, Char.isAlphanum, h]

/-! ## The tree -/

/-- The names of `treeOfProperties n`. -/
def propNames (n : Nat) : List String := (List.range n).map fun i => "p" ++ toString i

/-- The built tree of `treeOfProperties n`. -/
def propTree (n : Nat) : BuiltTree :=
  ⟨[], propNames n, Item.beginNode "" :: (List.range n).map (fun i => Item.property i []) ++
    [.endNode]⟩

/-- The bytes of a name in the strings block, its NUL included. -/
def nameBytes (s : String) : List UInt8 := s.toByteArray.toList ++ [0]

/-- A name in the strings block takes its bytes and its NUL. -/
theorem length_nameBytes (s : String) : (nameBytes s).length = s.utf8ByteSize + 1 := by
  simp [nameBytes, length_toByteArray_toList]

/-- The offset of the name of index `k` is the length of the names before it. -/
theorem nameOffsets_getD : ∀ (names : List String) (off k : Nat), k < names.length →
    (nameOffsets off names).getD k 0 = off + ((names.take k).flatMap nameBytes).length
  | [], _, _, h => absurd h (by simp)
  | name :: rest, off, 0, _ => by simp [nameOffsets]
  | name :: rest, off, k + 1, h => by
    simp only [nameOffsets, List.getD_cons_succ, List.take_succ_cons, List.flatMap_cons,
      List.length_append, length_nameBytes]
    rw [nameOffsets_getD rest _ k (by simpa using h)]
    omega

/-- The structure block of `propTree n`. -/
theorem prop_struct (n : Nat) : structBytes (propTree n) = [0, 0, 0, 1, 0, 0, 0, 0] ++
    (((List.range n).map fun i => Item.property i []).flatMap
      (Item.bytes (nameOffsets 0 (propNames n))) ++ (be32 2 ++ be32 9)) := by
  have hroot : Item.bytes (nameOffsets 0 (propNames n)) (.beginNode "") =
      [0, 0, 0, 1, 0, 0, 0, 0] := by
    simp only [Item.bytes]; decide +kernel
  simp only [structBytes, propTree, List.cons_append, List.flatMap_cons, List.flatMap_append,
    List.flatMap_nil, List.append_nil, List.append_assoc, hroot]
  rfl

/-- The name of index `k`. -/
theorem propNames_getElem {n k : Nat} (hk : k < (propNames n).length) :
    (propNames n)[k] = "p" ++ toString k := by
  simp [propNames]

/-- `propTree n` has `n` names. -/
theorem length_propNames (n : Nat) : (propNames n).length = n := by simp [propNames]

/-- Names of at most 4 bytes take at most 5 bytes each in the strings block. -/
theorem length_names_le : ∀ (names : List String), (∀ s ∈ names, s.utf8ByteSize ≤ 4) →
    (names.flatMap nameBytes).length ≤ 5 * names.length
  | [], _ => by simp
  | s :: rest, h => by
    simp only [List.flatMap_cons, List.length_append, length_nameBytes, List.length_cons]
    have := h s List.mem_cons_self
    have := length_names_le rest fun x hx => h x (List.mem_cons_of_mem _ hx)
    omega

/-- The names of `propTree n`, `n` at most 1000, take at most 4 bytes. -/
theorem propNames_small (n : Nat) (hn : n ≤ 1000) :
    ∀ s ∈ propNames n, s.utf8ByteSize ≤ 4 := by
  intro s hs
  simp only [propNames, List.mem_map, List.mem_range] at hs
  obtain ⟨i, hi, rfl⟩ := hs
  exact (propName_size i (by omega)).1

/-- Property tokens with empty values take 12 bytes each. -/
theorem length_propItems (n : Nat) (offs : List Nat) :
    (((List.range n).map fun i => Item.property i []).flatMap (Item.bytes offs)).length =
      12 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.flatMap_append, List.length_append, ih]
    simp [Item.bytes, length_be32, padTo4]; omega

/-- The property token of index `k` decodes to its name with an empty value. -/
theorem prop_decode (n k : Nat) (hn : n ≤ 1000) (hk : k < n) :
    decodeToken (ByteArray.mk (structBytes (propTree n)).toArray)
        (ByteArray.mk (stringBytes (propTree n)).toArray) (8 + 12 * k) =
      .ok (.property ("p" ++ toString k) ByteArray.empty, 8 + 12 * (k + 1)) := by
  have hkl : k < (propNames n).length := by rw [length_propNames]; exact hk
  have hoff := nameOffsets_getD (propNames n) 0 k hkl
  have hStr : stringBytes (propTree n) = (propNames n).flatMap nameBytes := rfl
  have hsmall := length_names_le _ (propNames_small n hn)
  have htk : ((propNames n).take k).flatMap nameBytes ++ (nameBytes (propNames n)[k] ++
      ((propNames n).drop (k + 1)).flatMap nameBytes) = (propNames n).flatMap nameBytes :=
    (flatMap_split _ _ k hkl).symm
  have hoffle : (((propNames n).take k).flatMap nameBytes).length ≤
      ((propNames n).flatMap nameBytes).length := by
    rw [← htk]; simp
  rw [prop_struct]
  have hlen := length_propItems n (nameOffsets 0 (propNames n))
  have hd := decode_property (l := [0, 0, 0, 1, 0, 0, 0, 0] ++
      (((List.range n).map fun i => Item.property i []).flatMap
      (Item.bytes (nameOffsets 0 (propNames n))) ++ (be32 2 ++ be32 9)))
    (strs := ByteArray.mk (stringBytes (propTree n)).toArray) (c := 8 + 12 * k) (len := 0)
    (off := (nameOffsets 0 (propNames n)).getD k 0) (name := (propNames n)[k])
    (e := (((propNames n).take k).flatMap nameBytes).length + (propNames n)[k].utf8ByteSize + 1)
    ?_ (by decide)
    (by rw [hoff, length_propNames] at *; omega) ?_ (by omega) ?_ ?_
  · rw [Nat.add_zero, ByteArray.extract_same, propNames_getElem] at hd
    rw [hd]
    congr 2
    unfold align4; omega
  · rw [show 8 + 12 * k = ([0, 0, 0, 1, 0, 0, 0, 0] : List UInt8).length + 12 * k by rfl,
      List.drop_length_add_append, drop_flatMap_const _ 12 _ _ _ ?_ (by simp; omega)]
    · rw [List.drop_eq_getElem_cons (by simp; omega), List.flatMap_cons, List.getElem_map,
        List.getElem_range, List.append_assoc,
        List.take_left' (l₁ := Item.bytes (nameOffsets 0 (propNames n)) (Item.property k []))
          (by simp [Item.bytes, length_be32, padTo4])]
      rfl
    · intro a ha
      simp only [List.mem_map, List.mem_range] at ha
      obtain ⟨i, -, rfl⟩ := ha
      simp [Item.bytes, length_be32, padTo4]
  · simp only [List.length_append, hlen, length_be32, List.length_cons, List.length_nil]
    unfold align4; omega
  · rw [hoff, Nat.zero_add, hStr, ← htk, nameBytes, List.append_assoc]
    exact cString_mk _ _ _ (by rw [propNames_getElem]; exact propName_bytes k)
  · rw [propNames_getElem]
    obtain ⟨h1, h2⟩ := propName_size k (by omega)
    exact ⟨h2, Nat.le_trans h1 (by decide), propName_chars k⟩

/-! ## The walk -/

/-- The walk after the root and its first `k` properties. -/
def propWalk (names : List String) (k : Nat) : Walk :=
  ⟨[⟨0, names.take k, false⟩], true,
    #[⟨"", none, (names.take k).map fun s => (s, ByteArray.empty)⟩]⟩

/-- A property of a new name below `MAX_PROPERTIES` is placed in the root. -/
theorem place_prop (names : List String) (k : Nat) (hk : k < names.length)
    (hlim : k + 1 ≤ MAX_PROPERTIES.toNat) (hnd : names[k] ∉ names.take k) :
    (propWalk names k).place (.property names[k] ByteArray.empty) =
      .ok (propWalk names (k + 1)) := by
  unfold Walk.place propWalk
  refine jp_eq_of_not (fun h => Bool.false_ne_true h) ?_
  refine jp_eq_of_not (by simp only [List.length_take]; omega) ?_
  refine jp_eq_of_not (by simpa using hnd) ?_
  show Except.ok _ = _
  rw [← take_succ_map _ _ _ hk, List.take_add_one, List.getElem?_eq_getElem hk]
  rfl

/-- A property beyond `MAX_PROPERTIES` fails with `LimitExceeded`. -/
theorem place_prop_over (names : List String) (k : Nat) (hk : k ≤ names.length)
    (hlim : MAX_PROPERTIES.toNat < k + 1) (name : String) (v : ByteArray) :
    (propWalk names k).place (.property name v) = .error .limitExceeded := by
  unfold Walk.place propWalk
  refine jp_eq_of_not (fun h => Bool.false_ne_true h) ?_
  exact jp_eq_of (by simp only [List.length_take]; omega)

/-- No name of the tree is one of the names before it. -/
theorem propNames_nodup (n k : Nat) (hk : k < (propNames n).length) :
    (propNames n)[k] ∉ (propNames n).take k := by
  intro h
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem h
  simp only [List.length_take] at hi
  rw [List.getElem_take, propNames_getElem, propNames_getElem] at he
  have := propName_inj he
  omega

/-- The walk of the root and the first `m` properties. -/
theorem prop_walk (n m f F : Nat) (hn : n ≤ 1000) (hm : m ≤ n)
    (hlim : m ≤ MAX_PROPERTIES.toNat)
    (hF : F = f + m + 1) :
    walkTokens (ByteArray.mk (structBytes (propTree n)).toArray)
        (ByteArray.mk (stringBytes (propTree n)).toArray) F 0 Walk.start =
      walkTokens (ByteArray.mk (structBytes (propTree n)).toArray)
        (ByteArray.mk (stringBytes (propTree n)).toArray) f (8 + 12 * m)
        (propWalk (propNames n) m) := by
  subst hF
  have hroot := decode_root (l := structBytes (propTree n)) (c := 0)
    (ByteArray.mk (stringBytes (propTree n)).toArray) (by rw [prop_struct]; rfl) rfl
  rw [walkTokens_step hroot (by simp) (rfl : Walk.start.place _ = .ok (propWalk (propNames n) 0))]
  have hit := walkTokens_iter (str := ByteArray.mk (structBytes (propTree n)).toArray)
    (strs := ByteArray.mk (stringBytes (propTree n)).toArray) (fun k => 8 + 12 * k)
    (fun k => propWalk (propNames n) k) (fun k => .property ("p" ++ toString k) ByteArray.empty) m
    ?_ f
  · simpa using hit
  · intro k hk
    have hkl : k < (propNames n).length := by rw [length_propNames]; omega
    refine ⟨prop_decode n k hn (by omega), by simp, ?_⟩
    have := place_prop (propNames n) k hkl (by omega) (propNames_nodup n k hkl)
    rw [propNames_getElem] at this
    exact this

/-- The length of the structure block of `propTree n`. -/
theorem length_prop_struct (n : Nat) : (structBytes (propTree n)).length = 12 * n + 16 := by
  have h := congrArg List.length (prop_struct n)
  simp only [List.length_append, length_propItems, length_be32, List.length_cons,
    List.length_nil] at h
  omega

/-- The length of `propTree n` without padding. -/
theorem natural_prop (n : Nat) (hn : n ≤ 1000) : natural (propTree n) ≤ 72 + 17 * n := by
  have h1 := length_prop_struct n
  have h2 := length_names_le _ (propNames_small n hn)
  rw [length_propNames] at h2
  have h3 : stringBytes (propTree n) = (propNames n).flatMap nameBytes := rfl
  simp only [natural, length_mapBytes, h1, h3]
  simp only [propTree, List.length_nil]
  omega

/-- The end node and the end token after the properties. -/
theorem prop_drop_end (n : Nat) :
    (structBytes (propTree n)).drop (8 + 12 * n) = be32 2 ++ be32 9 := by
  rw [prop_struct, show 8 + 12 * n = ([0, 0, 0, 1, 0, 0, 0, 0] : List UInt8).length + 12 * n by rfl,
    List.drop_length_add_append, drop_flatMap_const _ 12 _ _ _ ?_ (by simp),
    List.drop_eq_nil_of_le (by simp)]
  · rfl
  · intro a ha
    simp only [List.mem_map, List.mem_range] at ha
    obtain ⟨i, -, rfl⟩ := ha
    simp [Item.bytes, length_be32, padTo4]

/-- A node of `MAX_PROPERTIES` properties is accepted. -/
theorem parse_properties_limit :
    ∃ t, Fdt.parse (treeOfProperties MAX_PROPERTIES.toNat) = .ok t := by
  have hn : MAX_PROPERTIES.toNat ≤ 1000 := by decide
  have hmax : max (natural (propTree MAX_PROPERTIES.toNat)) 0 ≤ MAX_BLOB_SIZE.toNat := by
    have := natural_prop _ hn
    have h : MAX_PROPERTIES.toNat = 512 := rfl
    have h' : MAX_BLOB_SIZE.toNat = 2097152 := rfl
    omega
  have h12 : 12 ≤ (structBytes (propTree MAX_PROPERTIES.toNat)).length := by
    rw [length_prop_struct]; omega
  have hd := prop_drop_end MAX_PROPERTIES.toNat
  have hl := length_prop_struct MAX_PROPERTIES.toNat
  generalize hS : structBytes (propTree MAX_PROPERTIES.toNat) = S at hd hl
  have hw : walkTokens (ByteArray.mk (structBytes (propTree MAX_PROPERTIES.toNat)).toArray)
      (ByteArray.mk (stringBytes (propTree MAX_PROPERTIES.toNat)).toArray) MAX_TOKENS.toNat 0
        Walk.start = .ok #[⟨"", none,
          ((propNames MAX_PROPERTIES.toNat).take MAX_PROPERTIES.toNat).map
          fun s => (s, ByteArray.empty)⟩] := by
    rw [prop_walk _ _ (65021 + 1 + 1) _ hn (Nat.le_refl _) (Nat.le_refl _) (by decide)]
    rw [hS]
    refine (walkTokens_step ((decode_tag (u32At_of_take ?_ (by decide) ?_)).1 rfl) (by simp)
      rfl).trans ?_
    · rw [hd]; rfl
    · omega
    · refine walkTokens_end ?_ rfl rfl
      have := (decode_tag (strs :=
          ByteArray.mk (stringBytes (propTree MAX_PROPERTIES.toNat)).toArray)
        (u32At_of_take (l := S) (i := 8 + 12 * MAX_PROPERTIES.toNat + 4) (v := 9) ?_ (by decide)
          (by omega))).2.2 rfl
      · rw [this, size_mk, hl,
          show 8 + 12 * MAX_PROPERTIES.toNat + 4 + 4 = 12 * MAX_PROPERTIES.toNat + 16 by omega]
      · rw [← List.drop_drop, hd]; rfl
  exact ⟨_, (parse_built (propTree MAX_PROPERTIES.toNat) 0 hmax h12
    (reservationMap_none _ _ hmax rfl)).trans (by rw [structureNodes_built, hw]; rfl)⟩

/-- A node of `MAX_PROPERTIES + 1` properties fails with `LimitExceeded`. -/
theorem parse_properties_over :
    Fdt.parse (treeOfProperties (MAX_PROPERTIES.toNat + 1)) = .error .limitExceeded := by
  have hn : MAX_PROPERTIES.toNat + 1 ≤ 1000 := by decide
  have hmax : max (natural (propTree (MAX_PROPERTIES.toNat + 1))) 0 ≤ MAX_BLOB_SIZE.toNat := by
    have := natural_prop _ hn
    have h : MAX_PROPERTIES.toNat = 512 := rfl
    have h' : MAX_BLOB_SIZE.toNat = 2097152 := rfl
    omega
  have h12 : 12 ≤ (structBytes (propTree (MAX_PROPERTIES.toNat + 1))).length := by
    rw [length_prop_struct]; omega
  have hw : walkTokens (ByteArray.mk (structBytes (propTree (MAX_PROPERTIES.toNat + 1))).toArray)
      (ByteArray.mk (stringBytes (propTree (MAX_PROPERTIES.toNat + 1))).toArray) MAX_TOKENS.toNat 0
        Walk.start = .error .limitExceeded := by
    rw [prop_walk _ MAX_PROPERTIES.toNat (65022 + 1) _ hn (by omega) (Nat.le_refl _) (by decide)]
    have hkl : MAX_PROPERTIES.toNat ≤ (propNames (MAX_PROPERTIES.toNat + 1)).length := by
      rw [length_propNames]; omega
    exact walkTokens_step_error (prop_decode _ _ hn (by omega)) (by simp)
      (place_prop_over _ _ hkl (by omega) _ _)
  exact (parse_built (propTree (MAX_PROPERTIES.toNat + 1)) 0 hmax h12
    (reservationMap_none _ _ hmax rfl)).trans (by rw [structureNodes_built, hw]; rfl)

end Krepi.Proofs.Fdt
