module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
public import Krepi.Proofs.Fdt.ExceptLemmas
public import Krepi.Proofs.Fdt.SpanLemmas
public import Krepi.Proofs.Fdt.ParseBytes
public import Krepi.Proofs.Fdt.ParseSteps

/-!
# Device tree: the parse of a built tree

Lemmas that evaluate the parse of a tree that the encoder
`BuiltTree.bytes` of `Krepi.SpecProperties.Fdt` writes, without evaluating
its bytes, so that trees of any size can be read:

- the parts of a built tree: `mapBytes`, `structBytes`, `stringBytes`,
  `natural` (the length without padding) and `headerWords`, with `bytes_eq`;
- `header_built`: a built tree whose `totalsize` is at most `MAX_BLOB_SIZE`
  and whose structure block holds at least 12 bytes passes the header, with
  its blocks the byte arrays of `structBytes` and `stringBytes`;
  `header_built_over`: one whose `totalsize` is larger fails with
  `LimitExceeded`;
- `reservationMap_built`: entries each nonempty and within 64 bits, no two
  overlapping and at most `MAX_RESERVATIONS`, give their spans
  (`entrySpan`); `reservationMap_built_over`: more than `MAX_RESERVATIONS`
  such entries fail with `LimitExceeded`; `reservationMap_none`;
- `parse_built`: the parse is then the walk of the structure block, which
  `structureNodes_built` states on the byte arrays of the lists, so that a
  small block can be walked by a kernel decision.
-/

@[expose] public section

namespace Krepi.Proofs.Fdt

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

/-! ## The parts of a built tree -/

/-- The reservation map of a built tree, its terminator included. -/
def mapBytes (b : BuiltTree) : List UInt8 :=
  b.reservations.flatMap (fun e => be64 e.1 ++ be64 e.2) ++ List.replicate 16 0

/-- The structure block of a built tree. -/
def structBytes (b : BuiltTree) : List UInt8 :=
  b.items.flatMap (Item.bytes (nameOffsets 0 b.names)) ++ be32 9

/-- The strings block of a built tree. -/
def stringBytes (b : BuiltTree) : List UInt8 :=
  b.names.flatMap fun name => name.toByteArray.toList ++ [0]

/-- The length of a built tree without padding. -/
def natural (b : BuiltTree) : Nat :=
  40 + (mapBytes b).length + (structBytes b).length + (stringBytes b).length

/-- The words of the header of a built tree of `totalsize` `total`. -/
def headerWords (b : BuiltTree) (total : Nat) : List Nat :=
  [0xd00d_feed, total, 40 + (mapBytes b).length, 40 + (mapBytes b).length + (structBytes b).length,
    40, 17, 16, 0, (stringBytes b).length, (structBytes b).length]

/-- The layout that the header of a built tree gives. -/
def builtLayout (b : BuiltTree) (size : Nat) : Layout :=
  { total := max (natural b) size, structStart := 40 + (mapBytes b).length,
    structSize := (structBytes b).length,
    stringsStart := 40 + (mapBytes b).length + (structBytes b).length,
    stringsSize := (stringBytes b).length, reserveStart := 40 }

/-- The bytes of a built tree as its header words and its parts. -/
theorem bytes_eq (b : BuiltTree) (size : Nat) :
    b.bytes size = ByteArray.mk ((headerWords b (max (natural b) size)).flatMap be32 ++
      (mapBytes b ++ (structBytes b ++ (stringBytes b ++
        List.replicate (max (natural b) size - natural b) 0)))).toArray := by
  simp only [BuiltTree.bytes, headerWords, mapBytes, structBytes, stringBytes, natural,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-- `padTo4` writes a multiple of 4 bytes. -/
theorem length_padTo4 (l : List UInt8) : (padTo4 l).length % 4 = 0 := by
  simp only [padTo4, List.length_append, List.length_replicate]
  omega

/-- Each item writes a multiple of 4 bytes. -/
theorem length_item (offs : List Nat) (it : Item) : (it.bytes offs).length % 4 = 0 := by
  cases it with
  | beginNode name =>
    simp only [Item.bytes, List.length_append, length_be32]
    have := length_padTo4 (name.toByteArray.toList ++ [0]); omega
  | property name value =>
    simp only [Item.bytes, List.length_append, length_be32]
    have := length_padTo4 value; omega
  | endNode => simp [Item.bytes, length_be32]
  | nop => simp [Item.bytes, length_be32]

/-- Items write a multiple of 4 bytes. -/
theorem length_flatMap_items (offs : List Nat) :
    ∀ items : List Item, (items.flatMap (Item.bytes offs)).length % 4 = 0
  | [] => rfl
  | it :: items => by
    simp only [List.flatMap_cons, List.length_append]
    have := length_item offs it
    have := length_flatMap_items offs items
    omega

/-- The reservation map takes 16 bytes for each entry and the terminator. -/
theorem length_mapBytes (b : BuiltTree) :
    (mapBytes b).length = 16 * (b.reservations.length + 1) := by
  simp only [mapBytes, List.length_append, List.length_replicate]
  suffices ∀ l : List (Nat × Nat),
    (l.flatMap fun e => be64 e.1 ++ be64 e.2).length = 16 * l.length by
    rw [this]; omega
  intro l
  induction l with
  | nil => rfl
  | cons e l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [ih]
    simp only [be64, List.length_append, length_be32]
    omega

/-! ## The header -/

/-- A built tree has its `totalsize` bytes. -/
theorem size_built (b : BuiltTree) (size : Nat) : (b.bytes size).size = max (natural b) size := by
  have hnat : natural b ≤ max (natural b) size := Nat.le_max_left _ _
  rw [bytes_eq, size_mk]
  simp only [List.length_append, length_words, headerWords, List.length_cons, List.length_nil,
    List.length_replicate]
  simp only [natural] at hnat ⊢
  omega

/-- The words of the header of a built tree. -/
theorem u32At_built (b : BuiltTree) (size k : Nat)
    (h : k < (headerWords b (max (natural b) size)).length) :
    u32At (b.bytes size) (4 * k) =
      .ok (UInt32.ofNat (headerWords b (max (natural b) size))[k]) := by
  rw [bytes_eq]; exact u32At_words _ _ k h

/-- A built tree within `MAX_BLOB_SIZE` with a structure block of at least 12 bytes passes the
header. -/
theorem header_built (b : BuiltTree) (size : Nat)
    (hmax : max (natural b) size ≤ MAX_BLOB_SIZE.toNat)
    (h12 : 12 ≤ (structBytes b).length) :
    header (b.bytes size) = .ok ⟨b.bytes size, builtLayout b size,
      ByteArray.mk (structBytes b).toArray, ByteArray.mk (stringBytes b).toArray⟩ := by
  have hX := bytes_eq b size
  have hmaxv : MAX_BLOB_SIZE.toNat = 2097152 := rfl
  have hnat : natural b ≤ max (natural b) size := Nat.le_max_left _ _
  have hsz := size_built b size
  have rd := u32At_built b size
  have r0 : u32At (b.bytes size) 0 = .ok (UInt32.ofNat 0xd00d_feed) := by
    exact rd 0 (by simp [headerWords])
  have r1 : u32At (b.bytes size) 4 = .ok (UInt32.ofNat (max (natural b) size)) := by
    exact rd 1 (by simp [headerWords])
  have r2 : u32At (b.bytes size) 8 = .ok (UInt32.ofNat (40 + (mapBytes b).length)) := by
    exact rd 2 (by simp [headerWords])
  have r3 : u32At (b.bytes size) 12 =
      .ok (UInt32.ofNat (40 + (mapBytes b).length + (structBytes b).length)) := by
    exact rd 3 (by simp [headerWords])
  have r4 : u32At (b.bytes size) 16 = .ok (UInt32.ofNat 40) := by
    exact rd 4 (by simp [headerWords])
  have r5 : u32At (b.bytes size) 20 = .ok (UInt32.ofNat 17) := by
    exact rd 5 (by simp [headerWords])
  have r6 : u32At (b.bytes size) 24 = .ok (UInt32.ofNat 16) := by
    exact rd 6 (by simp [headerWords])
  have r8 : u32At (b.bytes size) 32 = .ok (UInt32.ofNat (stringBytes b).length) := by
    exact rd 8 (by simp [headerWords])
  have r9 : u32At (b.bytes size) 36 = .ok (UInt32.ofNat (structBytes b).length) := by
    exact rd 9 (by simp [headerWords])
  have hext : (b.bytes size).extract 0 (max (natural b) size) = b.bytes size := by
    rw [← hsz, ByteArray.extract_zero_size]
  have hlt : ∀ n, n ≤ max (natural b) size → (UInt32.ofNat n).toNat = n := by
    intro n hn
    apply UInt32.toNat_ofNat_of_lt'
    simp [UInt32.size]; omega
  have hm4 := length_mapBytes b
  have hs4 : (structBytes b).length % 4 = 0 := by
    simp only [structBytes, List.length_append, length_be32]
    have := length_flatMap_items (nameOffsets 0 b.names) b.items
    omega
  have hnd : natural b = 40 + (mapBytes b).length + (structBytes b).length +
      (stringBytes b).length := rfl
  have hA : ((headerWords b (max (natural b) size)).flatMap be32).length = 40 := by
    rw [length_words]; rfl
  have blk1 : block (b.bytes size) (40 + (mapBytes b).length) (structBytes b).length =
      .ok (ByteArray.mk (structBytes b).toArray) := by
    have := block_mk ((headerWords b (max (natural b) size)).flatMap be32 ++ mapBytes b)
      (structBytes b) (stringBytes b ++ List.replicate (max (natural b) size - natural b) 0)
      (by simp only [List.length_append, hA, HEADER_SIZE]; omega)
      (by simp only [List.length_append, hA]; omega)
    simp only [List.length_append, hA, List.append_assoc] at this
    rw [hX]; exact this
  have blk2 : block (b.bytes size) (40 + (mapBytes b).length + (structBytes b).length)
      (stringBytes b).length = .ok (ByteArray.mk (stringBytes b).toArray) := by
    have := block_mk ((headerWords b (max (natural b) size)).flatMap be32 ++ mapBytes b ++
      structBytes b) (stringBytes b) (List.replicate (max (natural b) size - natural b) 0)
      (by simp only [List.length_append, hA, HEADER_SIZE]; omega)
      (by simp only [List.length_append, hA]; omega)
    simp only [List.length_append, hA, List.append_assoc] at this
    rw [hX, Nat.add_assoc]; exact this
  have hT : (UInt32.ofNat (max (natural b) size)).toNat = max (natural b) size :=
      hlt _ (Nat.le_refl _)
  have hext' :
      (b.bytes size).extract 0 (UInt32.ofNat (max (natural b) size)).toNat = b.bytes size := by
    rw [hT, hext]
  unfold header
  refine jp_eq_of_not (by rw [hsz]; simp only [HEADER_SIZE]; omega) ?_
  refine bind_eq_of_ok r0 ?_
  refine jp_eq_of_not (by decide) ?_
  refine bind_eq_of_ok r1 ?_
  refine jp_eq_of_not (by rw [hT]; simp only [HEADER_SIZE]; omega) ?_
  refine jp_eq_of_not (by rw [hT]; omega) ?_
  refine jp_eq_of_not (by rw [hT, hsz]; omega) ?_
  refine bind_eq_of_ok (by rw [hext']; exact r5) ?_
  refine bind_eq_of_ok (by rw [hext']; exact r6) ?_
  refine jp_eq_of_not (by decide) ?_
  refine bind_eq_of_ok (by rw [hext']; exact r2) ?_
  refine bind_eq_of_ok (by rw [hext']; exact r3) ?_
  refine bind_eq_of_ok (by rw [hext']; exact r4) ?_
  refine bind_eq_of_ok (by rw [hext']; exact r8) ?_
  refine bind_eq_of_ok (by rw [hext']; exact r9) ?_
  have hS : (UInt32.ofNat (structBytes b).length).toNat = (structBytes b).length := hlt _ (by omega)
  have hS0 : (UInt32.ofNat (40 + (mapBytes b).length)).toNat = 40 + (mapBytes b).length :=
    hlt _ (by omega)
  have hS1 : (UInt32.ofNat (40 + (mapBytes b).length + (structBytes b).length)).toNat =
      40 + (mapBytes b).length + (structBytes b).length := hlt _ (by omega)
  have hS2 : (UInt32.ofNat (stringBytes b).length).toNat = (stringBytes b).length :=
      hlt _ (by omega)
  have h40 : (UInt32.ofNat 40).toNat = 40 := rfl
  refine jp_eq_of_not ?_ ?_
  · rw [hS0, hS, h40, hm4]
    simp only [hs4, Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not, and_true]
    omega
  refine bind_eq_of_ok (by rw [hS, hS0, hext']; exact blk1) ?_
  refine bind_eq_of_ok (by rw [hS1, hS2, hext']; exact blk2) ?_
  refine jp_eq_of_not ?_ ?_
  · rw [hS, h40]
    simp [HEADER_SIZE]; omega
  refine jp_eq_of_not ?_ ?_
  · rw [hS0, hS, hS1, hS2]
    simp [intersects, Layout.structEnd, Layout.stringsEnd]
  simp only [hT, hS0, hS, hS1, hS2, h40, hext]
  rfl

/-- A built tree whose `totalsize` is above `MAX_BLOB_SIZE` fails with `LimitExceeded`. -/
theorem header_built_over (b : BuiltTree) (size : Nat)
    (hover : MAX_BLOB_SIZE.toNat < max (natural b) size) (h32 : max (natural b) size < 2 ^ 32) :
    header (b.bytes size) = .error .limitExceeded := by
  have hsz := size_built b size
  have hT : (UInt32.ofNat (max (natural b) size)).toNat = max (natural b) size :=
    UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
  have hmaxv : MAX_BLOB_SIZE.toNat = 2097152 := rfl
  unfold header
  refine jp_eq_of_not (by rw [hsz]; simp only [HEADER_SIZE]; omega) ?_
  have r0 : u32At (b.bytes size) 0 = .ok (UInt32.ofNat 0xd00d_feed) :=
    u32At_built b size 0 (by simp [headerWords])
  have r1 : u32At (b.bytes size) 4 = .ok (UInt32.ofNat (max (natural b) size)) :=
    u32At_built b size 1 (by simp [headerWords])
  refine bind_eq_of_ok r0 ?_
  refine jp_eq_of_not (by decide) ?_
  refine bind_eq_of_ok r1 ?_
  refine jp_eq_of_not (by rw [hT]; simp only [HEADER_SIZE]; omega) ?_
  exact jp_eq_of (by rw [hT]; omega)

/-! ## The reservation map -/

/-- The bytes of a reservation entry. -/
def entryBytes (e : Nat × Nat) : List UInt8 := be64 e.1 ++ be64 e.2

/-- A reservation entry takes 16 bytes. -/
theorem length_entryBytes (e : Nat × Nat) : (entryBytes e).length = 16 := by
  simp [entryBytes, be64, length_be32]

/-- The reservation map as its entries and its terminator. -/
theorem mapBytes_eq (b : BuiltTree) :
    mapBytes b = b.reservations.flatMap entryBytes ++ List.replicate 16 0 := rfl

/-- The bytes of a built tree from the reservation map on. -/
theorem bytes_eq_map (b : BuiltTree) (size : Nat) :
    ∃ A R : List UInt8, A.length = 40 ∧
      b.bytes size = ByteArray.mk (A ++ (b.reservations.flatMap entryBytes ++
        (List.replicate 16 0 ++ R))).toArray ∧
      (A ++ (b.reservations.flatMap entryBytes ++ (List.replicate 16 0 ++ R))).length =
        max (natural b) size := by
  refine ⟨(headerWords b (max (natural b) size)).flatMap be32, structBytes b ++ (stringBytes b ++
    List.replicate (max (natural b) size - natural b) 0), by rw [length_words]; rfl,
    by rw [bytes_eq, mapBytes_eq, List.append_assoc], ?_⟩
  have hnat : natural b ≤ max (natural b) size := Nat.le_max_left _ _
  have hnd : natural b = 40 + (mapBytes b).length + (structBytes b).length +
      (stringBytes b).length := rfl
  rw [mapBytes_eq] at hnd
  simp only [List.length_append, length_words, headerWords, List.length_cons, List.length_nil,
    List.length_replicate] at hnd ⊢
  omega

/-- The address and the size of the reservation entry of index `k`. -/
theorem u64At_entry (b : BuiltTree) (size k : Nat) (hk : k < b.reservations.length) :
    u64At (b.bytes size) (40 + 16 * k) = .ok (UInt64.ofNat b.reservations[k].1) ∧
      u64At (b.bytes size) (40 + 16 * k + 8) = .ok (UInt64.ofNat b.reservations[k].2) := by
  obtain ⟨A, R, hA, hX, hL⟩ := bytes_eq_map b size
  have hlen := length_mapBytes b
  rw [mapBytes_eq] at hlen
  have hnat : natural b ≤ max (natural b) size := Nat.le_max_left _ _
  have hnd : natural b = 40 + (mapBytes b).length + (structBytes b).length +
      (stringBytes b).length := rfl
  have hdrop : (A ++ (b.reservations.flatMap entryBytes ++ (List.replicate 16 0 ++ R))).drop
      (40 + 16 * k) = entryBytes b.reservations[k] ++
        ((b.reservations.drop (k + 1)).flatMap entryBytes ++ (List.replicate 16 0 ++ R)) := by
    rw [← hA, List.drop_length_add_append,
      drop_flatMap_const entryBytes 16 _ _ _ (fun e _ => length_entryBytes e) (Nat.le_of_lt hk),
      List.drop_eq_getElem_cons hk, List.flatMap_cons, List.append_assoc]
  rw [hX]
  constructor
  · rw [u64At_mk _ _ (by rw [hL]; rw [length_mapBytes] at hnd; omega), hdrop, entryBytes,
      List.append_assoc, List.take_left' (by simp [be64, length_be32]), ofNat_beOf_be64]
  · rw [u64At_mk _ _ (by rw [hL]; rw [length_mapBytes] at hnd; omega), ← List.drop_drop, hdrop,
      entryBytes, List.append_assoc, List.drop_left' (by simp [be64, length_be32]),
      List.take_left' (by simp [be64, length_be32]), ofNat_beOf_be64]

/-- The terminator of the reservation map reads two zeros. -/
theorem u64At_terminator (b : BuiltTree) (size : Nat) :
    u64At (b.bytes size) (40 + 16 * b.reservations.length) = .ok 0 ∧
      u64At (b.bytes size) (40 + 16 * b.reservations.length + 8) = .ok 0 := by
  obtain ⟨A, R, hA, hX, hL⟩ := bytes_eq_map b size
  have hnat : natural b ≤ max (natural b) size := Nat.le_max_left _ _
  have hnd : natural b = 40 + (mapBytes b).length + (structBytes b).length +
      (stringBytes b).length := rfl
  rw [length_mapBytes] at hnd
  have hdrop : (A ++ (b.reservations.flatMap entryBytes ++ (List.replicate 16 0 ++ R))).drop
      (40 + 16 * b.reservations.length) = List.replicate 16 0 ++ R := by
    rw [← hA, List.drop_length_add_append,
      drop_flatMap_const entryBytes 16 _ _ _ (fun e _ => length_entryBytes e) (Nat.le_refl _)]
    simp
  rw [hX]
  constructor
  · rw [u64At_mk _ _ (by rw [hL]; omega), hdrop]
    rfl
  · rw [u64At_mk _ _ (by rw [hL]; omega), ← List.drop_drop, hdrop]
    rfl

/-- The span of a reservation entry. -/
def entrySpan (e : Nat × Nat) : Span := ⟨UInt64.ofNat e.1, UInt64.ofNat e.2⟩

/-- The header that `header_built` gives. -/
def builtHeader (b : BuiltTree) (size : Nat) : Header :=
  ⟨b.bytes size, builtLayout b size, ByteArray.mk (structBytes b).toArray,
    ByteArray.mk (stringBytes b).toArray⟩

/-- The checks of an entry of the reservation map of a built tree before its words are read. -/
theorem head_facts (b : BuiltTree) (size k : Nat)
    (hmax : max (natural b) size ≤ MAX_BLOB_SIZE.toNat)
    (hk : k ≤ b.reservations.length) :
    checkedAdd (40 + 16 * k) 16 = .ok (40 + 16 * k + 16) ∧
    ¬ (builtLayout b size).total < 40 + 16 * k + 16 ∧
    ¬ (intersects (40 + 16 * k) (40 + 16 * k + 16) (builtLayout b size).structStart
          (builtLayout b size).structEnd ||
        intersects (40 + 16 * k) (40 + 16 * k + 16) (builtLayout b size).stringsStart
          (builtLayout b size).stringsEnd) = true := by
  have hmaxv : MAX_BLOB_SIZE.toNat = 2097152 := rfl
  have hnat : natural b ≤ max (natural b) size := Nat.le_max_left _ _
  have hnd : natural b = 40 + (mapBytes b).length + (structBytes b).length +
      (stringBytes b).length := rfl
  have hm := length_mapBytes b
  have hn2 : natural b ≤ 2097152 := Nat.le_trans hnat (hmaxv ▸ hmax)
  refine ⟨?_, ?_, ?_⟩
  · simp only [checkedAdd]; split
    · rfl
    · omega
  · simp only [builtLayout, Nat.not_lt]
    exact Nat.le_trans (by omega : 40 + 16 * k + 16 ≤ natural b) hnat
  · rw [intersects_false (Or.inl (by simp only [builtLayout]; omega)),
      intersects_false (Or.inl (by simp only [builtLayout]; omega))]
    decide

/-- An entry of the reservation map of a built tree, nonempty, within 64 bits and apart from the
entries before it. -/
theorem reservationsFrom_entry (b : BuiltTree) (size : Nat)
    (hmax : max (natural b) size ≤ MAX_BLOB_SIZE.toNat) (k fuel : Nat)
    (hk : k < b.reservations.length) (hlim : k + 1 ≤ MAX_RESERVATIONS.toNat)
    (hgood : 0 < b.reservations[k].2 ∧ b.reservations[k].1 + b.reservations[k].2 < 2 ^ 64)
    (hdisj : ∀ i (hi : i < k), (entrySpan (b.reservations[i]'(by omega))).overlaps
      (entrySpan b.reservations[k]) = false) :
    reservationsFrom (builtHeader b size) (fuel + 1) (40 + 16 * k)
        ((b.reservations.take k).map entrySpan) =
      reservationsFrom (builtHeader b size) fuel (40 + 16 * (k + 1))
        ((b.reservations.take (k + 1)).map entrySpan) := by
  obtain ⟨h1, h2, h3⟩ := head_facts b size k hmax (Nat.le_of_lt hk)
  obtain ⟨r1, r2⟩ := u64At_entry b size k hk
  have hs : (UInt64.ofNat b.reservations[k].2).toNat = b.reservations[k].2 :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have ha : (UInt64.ofNat b.reservations[k].1).toNat = b.reservations[k].1 :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  rw [reservationsFrom]
  refine bind_eq_of_ok h1 ?_
  refine jp_eq_of_not h2 ?_
  refine jp_eq_of_not h3 ?_
  refine bind_eq_of_ok r1 ?_
  refine bind_eq_of_ok r2 ?_
  refine ite_else_eq ?_ ?_
  · intro h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have := congrArg UInt64.toNat h.2
    rw [hs] at this
    simp at this
    omega
  refine jp_eq_of_not (by simp; omega) ?_
  refine bind_eq_of_ok (a := entrySpan b.reservations[k])
    (span_new_ok.2 ⟨by rw [ha, hs]; exact hgood.2, rfl⟩) ?_
  refine jp_eq_of_not ?_ ?_
  · intro h
    have := congrArg UInt64.toNat h
    rw [hs] at this
    simp at this
    omega
  refine jp_eq_of_not ?_ ?_
  · simp only [List.any_eq_true, List.mem_map, not_exists, not_and, Bool.not_eq_true]
    intro x ⟨e, he, hx⟩
    subst hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    simp only [List.length_take] at hi
    simp only [List.getElem_take]
    exact hdisj i (by omega)
  rw [show 40 + 16 * k + 16 = 40 + 16 * (k + 1) by omega, take_succ_map _ _ _ hk]

/-- An entry beyond `MAX_RESERVATIONS` fails with `LimitExceeded`. -/
theorem reservationsFrom_over (b : BuiltTree) (size : Nat)
    (hmax : max (natural b) size ≤ MAX_BLOB_SIZE.toNat) (k fuel : Nat)
    (hk : k < b.reservations.length) (hlim : MAX_RESERVATIONS.toNat < k + 1)
    (hgood : 0 < b.reservations[k].2 ∧ b.reservations[k].1 + b.reservations[k].2 < 2 ^ 64) :
    reservationsFrom (builtHeader b size) (fuel + 1) (40 + 16 * k)
        ((b.reservations.take k).map entrySpan) = .error .limitExceeded := by
  obtain ⟨h1, h2, h3⟩ := head_facts b size k hmax (Nat.le_of_lt hk)
  obtain ⟨r1, r2⟩ := u64At_entry b size k hk
  have hs : (UInt64.ofNat b.reservations[k].2).toNat = b.reservations[k].2 :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  rw [reservationsFrom]
  refine bind_eq_of_ok h1 ?_
  refine jp_eq_of_not h2 ?_
  refine jp_eq_of_not h3 ?_
  refine bind_eq_of_ok r1 ?_
  refine bind_eq_of_ok r2 ?_
  refine ite_else_eq ?_ ?_
  · intro h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have := congrArg UInt64.toNat h.2
    rw [hs] at this
    simp at this
    omega
  exact jp_eq_of (by simp; omega)

/-- The terminator ends the reservation map. -/
theorem reservationsFrom_end (b : BuiltTree) (size : Nat)
    (hmax : max (natural b) size ≤ MAX_BLOB_SIZE.toNat) (fuel : Nat) :
    reservationsFrom (builtHeader b size) (fuel + 1) (40 + 16 * b.reservations.length)
        (b.reservations.map entrySpan) = .ok (b.reservations.map entrySpan) := by
  obtain ⟨h1, h2, h3⟩ := head_facts b size _ hmax (Nat.le_refl _)
  obtain ⟨r1, r2⟩ := u64At_terminator b size
  rw [reservationsFrom]
  refine bind_eq_of_ok h1 ?_
  refine jp_eq_of_not h2 ?_
  refine jp_eq_of_not h3 ?_
  refine bind_eq_of_ok r1 ?_
  refine bind_eq_of_ok r2 ?_
  exact ite_then_eq rfl rfl

/-- Entries each nonempty and within 64 bits, no two overlapping and at most `MAX_RESERVATIONS`,
give their spans. -/
theorem reservationMap_built (b : BuiltTree) (size : Nat)
    (hmax : max (natural b) size ≤ MAX_BLOB_SIZE.toNat)
    (hlen : b.reservations.length ≤ MAX_RESERVATIONS.toNat)
    (hgood : ∀ e ∈ b.reservations, 0 < e.2 ∧ e.1 + e.2 < 2 ^ 64)
    (hdisj : (b.reservations.map entrySpan).Pairwise (fun x y => x.overlaps y = false)) :
    reservationMap (builtHeader b size) = .ok (b.reservations.map entrySpan) := by
  have step : ∀ j k fuel, k + j = b.reservations.length →
      reservationsFrom (builtHeader b size) (fuel + j + 1) (40 + 16 * k)
        ((b.reservations.take k).map entrySpan) = .ok (b.reservations.map entrySpan) := by
    intro j
    induction j with
    | zero =>
      intro k fuel hk
      simp only [Nat.add_zero] at hk
      subst hk
      rw [List.take_length]
      exact reservationsFrom_end b size hmax fuel
    | succ j ih =>
      intro k fuel hk
      have hk' : k < b.reservations.length := by omega
      rw [show fuel + (j + 1) + 1 = (fuel + j + 1) + 1 by omega,
        reservationsFrom_entry b size hmax k _ hk' (by omega)
          (hgood _ (List.getElem_mem hk'))]
      · exact ih (k + 1) fuel (by omega)
      · intro i hi
        have := List.pairwise_iff_getElem.1 hdisj i k (by simp; omega) (by simp; omega) hi
        simpa using this
  have := step b.reservations.length 0 (MAX_RESERVATIONS.toNat - b.reservations.length) (by omega)
  rw [show MAX_RESERVATIONS.toNat - b.reservations.length + b.reservations.length + 1 =
    MAX_RESERVATIONS.toNat + 1 by omega] at this
  simpa [reservationMap, builtHeader, builtLayout] using this

/-- More than `MAX_RESERVATIONS` entries, each nonempty and within 64 bits and no two overlapping,
fail with `LimitExceeded`. -/
theorem reservationMap_built_over (b : BuiltTree) (size : Nat)
    (hmax : max (natural b) size ≤ MAX_BLOB_SIZE.toNat)
    (hlen : MAX_RESERVATIONS.toNat < b.reservations.length)
    (hgood : ∀ e ∈ b.reservations, 0 < e.2 ∧ e.1 + e.2 < 2 ^ 64)
    (hdisj : (b.reservations.map entrySpan).Pairwise (fun x y => x.overlaps y = false)) :
    reservationMap (builtHeader b size) = .error .limitExceeded := by
  have step : ∀ j k, k + j = MAX_RESERVATIONS.toNat →
      reservationsFrom (builtHeader b size) (j + 1) (40 + 16 * k)
        ((b.reservations.take k).map entrySpan) = .error .limitExceeded := by
    intro j
    induction j with
    | zero =>
      intro k hk
      exact reservationsFrom_over b size hmax k 0 (by omega) (by omega)
        (hgood _ (List.getElem_mem (by omega)))
    | succ j ih =>
      intro k hk
      have hk' : k < b.reservations.length := by omega
      rw [reservationsFrom_entry b size hmax k _ hk' (by omega)
          (hgood _ (List.getElem_mem hk'))]
      · exact ih (k + 1) (by omega)
      · intro i hi
        have := List.pairwise_iff_getElem.1 hdisj i k (by simp; omega) (by simp; omega) hi
        simpa using this
  have := step MAX_RESERVATIONS.toNat 0 (by omega)
  simpa [reservationMap, builtHeader, builtLayout] using this

/-- A built tree without reservation entries has an empty reservation map. -/
theorem reservationMap_none (b : BuiltTree) (size : Nat)
    (hmax : max (natural b) size ≤ MAX_BLOB_SIZE.toNat) (h : b.reservations = []) :
    reservationMap (builtHeader b size) = .ok [] := by
  have := reservationMap_built b size hmax (by simp [h]) (by simp [h]) (by simp [h])
  simpa [h] using this

/-! ## The parse -/

/-- The walk of the structure block of a built tree on the byte arrays of its lists. -/
theorem structureNodes_built (b : BuiltTree) (size : Nat) :
    structureNodes (builtHeader b size) = walkTokens (ByteArray.mk (structBytes b).toArray)
      (ByteArray.mk (stringBytes b).toArray) MAX_TOKENS.toNat 0 Walk.start := rfl

/-- The parse of a built tree that passes the header and the reservation map is the walk of its
structure block. -/
theorem parse_built (b : BuiltTree) (size : Nat)
    (hmax : max (natural b) size ≤ MAX_BLOB_SIZE.toNat) (h12 : 12 ≤ (structBytes b).length)
    {rs : List Span} (hres : reservationMap (builtHeader b size) = .ok rs) :
    Fdt.parse (b.bytes size) = (structureNodes (builtHeader b size)).bind fun records =>
      .ok { totalSize := UInt64.ofNat (max (natural b) size), reservations := rs, records } := by
  unfold Fdt.parse
  refine bind_eq_of_ok (header_built b size hmax h12) ?_
  refine bind_eq_of_ok hres ?_
  rfl

end Krepi.Proofs.Fdt
