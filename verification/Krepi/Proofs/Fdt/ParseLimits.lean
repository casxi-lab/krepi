module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
public import Krepi.Proofs.Fdt.ExceptLemmas
public import Krepi.Proofs.Fdt.SpanLemmas
public import Krepi.Proofs.Fdt.ParseBytes
public import Krepi.Proofs.Fdt.ParseSteps
public import Krepi.Proofs.Fdt.ParseBuilt

/-!
# Device tree: the parse at five of its limits

The parse of the trees of `ParseLimitsExact` at the limits of `totalsize`, the
nodes on a path, the bytes of a property name, the reservation entries and
the tokens, and 1 above each. The header and the reservation map are
evaluated by the lemmas of `Krepi.Proofs.Fdt.ParseBuilt`; the walk of a small
structure block (the depth and the name) is a kernel decision on the byte
arrays of its lists, and the walk of the `MAX_TOKENS` tokens is
`walkTokens_iter` over the no-operations.
-/

@[expose] public section

namespace Krepi.Proofs.Fdt

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

/-! ## Depth -/

/-- The items of `treeOfDepth n`. -/
def depthItems (n : Nat) : List Item :=
  Item.beginNode "" :: List.replicate (n - 1) (.beginNode "a") ++ List.replicate n .endNode

/-- A path of `MAX_DEPTH` nodes is accepted. -/
theorem parse_depth_limit : ∃ t, Fdt.parse (treeOfDepth MAX_DEPTH.toNat) = .ok t := by
  have hmax : max (natural ⟨[], [], depthItems MAX_DEPTH.toNat⟩) 0 ≤ MAX_BLOB_SIZE.toNat := by
    decide +kernel
  have h12 : 12 ≤ (structBytes ⟨[], [], depthItems MAX_DEPTH.toNat⟩).length := by
    decide +kernel
  have hw :
      (structureNodes (builtHeader ⟨[], [], depthItems MAX_DEPTH.toNat⟩ 0)).toBool = true := by
    decide +kernel
  obtain ⟨recs, hr⟩ := exists_ok_of_toBool hw
  exact ⟨_, (parse_built _ 0 hmax h12 (reservationMap_none _ 0 hmax rfl)).trans
    (by rw [hr]; rfl)⟩

/-- A path of `MAX_DEPTH + 1` nodes fails with `LimitExceeded`. -/
theorem parse_depth_over :
    Fdt.parse (treeOfDepth (MAX_DEPTH.toNat + 1)) = .error .limitExceeded := by
  have hmax :
      max (natural ⟨[], [], depthItems (MAX_DEPTH.toNat + 1)⟩) 0 ≤ MAX_BLOB_SIZE.toNat := by
    decide +kernel
  have h12 : 12 ≤ (structBytes ⟨[], [], depthItems (MAX_DEPTH.toNat + 1)⟩).length := by
    decide +kernel
  have hw : errOf (structureNodes (builtHeader ⟨[], [], depthItems (MAX_DEPTH.toNat + 1)⟩ 0)) =
      some .limitExceeded := by
    decide +kernel
  exact (parse_built _ 0 hmax h12 (reservationMap_none _ 0 hmax rfl)).trans
    (by rw [eq_error_of_errOf hw]; rfl)

/-! ## Size -/

/-- A tree of `MAX_BLOB_SIZE` bytes is accepted. -/
theorem parse_size_limit : ∃ t, Fdt.parse (treeOfSize MAX_BLOB_SIZE.toNat) = .ok t := by
  have hmax : max (natural ⟨[], [], rootOnly⟩) MAX_BLOB_SIZE.toNat ≤ MAX_BLOB_SIZE.toNat := by
    decide +kernel
  have h12 : 12 ≤ (structBytes ⟨[], [], rootOnly⟩).length := by decide +kernel
  have hw : (walkTokens (ByteArray.mk (structBytes ⟨[], [], rootOnly⟩).toArray)
      (ByteArray.mk (stringBytes ⟨[], [], rootOnly⟩).toArray) MAX_TOKENS.toNat 0
        Walk.start).toBool = true := by
    decide +kernel
  obtain ⟨recs, hr⟩ := exists_ok_of_toBool hw
  exact ⟨_, (parse_built _ _ hmax h12 (reservationMap_none _ _ hmax rfl)).trans
    (by rw [structureNodes_built, hr]; rfl)⟩

/-- A tree of `MAX_BLOB_SIZE + 1` bytes fails with `LimitExceeded`. -/
theorem parse_size_over :
    Fdt.parse (treeOfSize (MAX_BLOB_SIZE.toNat + 1)) = .error .limitExceeded := by
  unfold Fdt.parse treeOfSize
  rw [header_built_over _ _ (by decide +kernel) (by decide +kernel)]
  rfl

/-! ## Property name -/

/-- The built tree of `treeOfNameBytes n`. -/
def nameTree (n : Nat) : BuiltTree :=
  BuiltTree.mk [] [String.ofList (List.replicate n 'a')] [.beginNode "", .property 0 [], .endNode]

/-- A property name of `MAX_PROPERTY_NAME` bytes is accepted. -/
theorem parse_name_limit : ∃ t, Fdt.parse (treeOfNameBytes MAX_PROPERTY_NAME.toNat) = .ok t := by
  have hmax : max (natural (nameTree MAX_PROPERTY_NAME.toNat)) 0 ≤ MAX_BLOB_SIZE.toNat := by
    decide +kernel
  have h12 : 12 ≤ (structBytes (nameTree MAX_PROPERTY_NAME.toNat)).length := by decide +kernel
  have hw : (walkTokens (ByteArray.mk (structBytes (nameTree MAX_PROPERTY_NAME.toNat)).toArray)
      (ByteArray.mk (stringBytes (nameTree MAX_PROPERTY_NAME.toNat)).toArray) MAX_TOKENS.toNat 0
        Walk.start).toBool = true := by
    decide +kernel
  obtain ⟨recs, hr⟩ := exists_ok_of_toBool hw
  exact ⟨_, (parse_built (nameTree _) 0 hmax h12 (reservationMap_none _ _ hmax rfl)).trans
    (by rw [structureNodes_built, hr]; rfl)⟩

/-- A property name of `MAX_PROPERTY_NAME + 1` bytes fails with `BadString`. -/
theorem parse_name_over :
    Fdt.parse (treeOfNameBytes (MAX_PROPERTY_NAME.toNat + 1)) = .error .badString := by
  have hmax : max (natural (nameTree (MAX_PROPERTY_NAME.toNat + 1))) 0 ≤ MAX_BLOB_SIZE.toNat := by
    decide +kernel
  have h12 : 12 ≤ (structBytes (nameTree (MAX_PROPERTY_NAME.toNat + 1))).length := by
    decide +kernel
  have hw : errOf (walkTokens
      (ByteArray.mk (structBytes (nameTree (MAX_PROPERTY_NAME.toNat + 1))).toArray)
      (ByteArray.mk (stringBytes (nameTree (MAX_PROPERTY_NAME.toNat + 1))).toArray)
        MAX_TOKENS.toNat 0 Walk.start) = some .badString := by
    decide +kernel
  exact (parse_built (nameTree _) 0 hmax h12 (reservationMap_none _ _ hmax rfl)).trans
    (by rw [structureNodes_built, eq_error_of_errOf hw]; rfl)

/-! ## Reservation entries -/

/-- The built tree of `treeOfReservations n`. -/
def resTree (n : Nat) : BuiltTree :=
  ⟨(List.range n).map fun i => ((i + 1) * 0x1000, 0x1000), [], rootOnly⟩

/-- The entries of `resTree n` are nonempty and within 64 bits. -/
theorem resTree_good (n : Nat) (hn : n ≤ 2 ^ 40) :
    ∀ e ∈ (resTree n).reservations, 0 < e.2 ∧ e.1 + e.2 < 2 ^ 64 := by
  intro e he
  simp only [resTree, List.mem_map, List.mem_range] at he
  obtain ⟨i, hi, rfl⟩ := he
  simp only
  omega

/-- No two entries of `resTree n` overlap. -/
theorem resTree_disj (n : Nat) (hn : n ≤ 2 ^ 40) :
    ((resTree n).reservations.map entrySpan).Pairwise (fun x y => x.overlaps y = false) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [resTree, List.length_map, List.length_range] at hi hj
  simp only [resTree, List.getElem_map, List.getElem_range, entrySpan, Span.overlaps,
    Span.endNat]
  have h1 : (UInt64.ofNat ((i + 1) * 4096)).toNat = (i + 1) * 4096 :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have h2 : (UInt64.ofNat ((j + 1) * 4096)).toNat = (j + 1) * 4096 :=
    UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have h3 : (UInt64.ofNat 4096).toNat = 4096 := rfl
  rw [h1, h2, h3]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt]
  omega

/-- `MAX_RESERVATIONS` reservation entries are accepted. -/
theorem parse_reservations_limit :
    ∃ t, Fdt.parse (treeOfReservations MAX_RESERVATIONS.toNat) = .ok t := by
  have hmax : max (natural (resTree MAX_RESERVATIONS.toNat)) 0 ≤ MAX_BLOB_SIZE.toNat := by
    decide +kernel
  have h12 : 12 ≤ (structBytes (resTree MAX_RESERVATIONS.toNat)).length := by decide +kernel
  have hw : (walkTokens (ByteArray.mk (structBytes (resTree MAX_RESERVATIONS.toNat)).toArray)
      (ByteArray.mk (stringBytes (resTree MAX_RESERVATIONS.toNat)).toArray) MAX_TOKENS.toNat 0
        Walk.start).toBool = true := by
    decide +kernel
  obtain ⟨recs, hr⟩ := exists_ok_of_toBool hw
  exact ⟨_, (parse_built (resTree _) 0 hmax h12 (reservationMap_built _ 0 hmax
    (by simp [resTree]) (resTree_good _ (by decide)) (resTree_disj _ (by decide)))).trans
    (by rw [structureNodes_built, hr]; rfl)⟩

/-- `MAX_RESERVATIONS + 1` reservation entries fail with `LimitExceeded`. -/
theorem parse_reservations_over :
    Fdt.parse (treeOfReservations (MAX_RESERVATIONS.toNat + 1)) = .error .limitExceeded := by
  have hmax : max (natural (resTree (MAX_RESERVATIONS.toNat + 1))) 0 ≤ MAX_BLOB_SIZE.toNat := by
    decide +kernel
  have h12 : 12 ≤ (structBytes (resTree (MAX_RESERVATIONS.toNat + 1))).length := by
    decide +kernel
  show Fdt.parse ((resTree _).bytes 0) = _
  unfold Fdt.parse
  refine bind_eq_of_ok (header_built (resTree _) 0 hmax h12) ?_
  exact bind_eq_of_error (reservationMap_built_over _ 0 hmax (by simp [resTree])
    (resTree_good _ (by decide)) (resTree_disj _ (by decide)))

/-! ## Tokens -/

/-- The built tree of `treeOfTokens n`. -/
def tokTree (n : Nat) : BuiltTree :=
  ⟨[], [], Item.beginNode "" :: List.replicate (n - 3) .nop ++ [.endNode]⟩

/-- The structure block of `tokTree n`: the root, `n - 3` no-operations, its end node and the end
token. -/
theorem tok_struct (n : Nat) : structBytes (tokTree n) = [0, 0, 0, 1, 0, 0, 0, 0] ++
    ((List.replicate (n - 3) Item.nop).flatMap (Item.bytes []) ++ (be32 2 ++ be32 9)) := by
  have hroot : Item.bytes [] (.beginNode "") = [0, 0, 0, 1, 0, 0, 0, 0] := by decide +kernel
  simp only [structBytes, tokTree, List.cons_append, List.flatMap_cons,
    List.flatMap_append, List.flatMap_nil, List.append_nil, List.append_assoc]
  rw [show nameOffsets 0 [] = [] from rfl, hroot]
  rfl

/-- No-operations take 4 bytes each. -/
theorem length_nops (m : Nat) :
    ((List.replicate m Item.nop).flatMap (Item.bytes [])).length = 4 * m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, List.flatMap_cons, List.length_append, ih]
    simp [Item.bytes, length_be32]; omega

/-- The walk of the root and the no-operations of `tokTree n` up to the end token. -/
theorem tok_walk (n f F : Nat) (hF : F = f + 1 + (n - 3) + 1) :
    walkTokens (ByteArray.mk (structBytes (tokTree n)).toArray)
        (ByteArray.mk (stringBytes (tokTree n)).toArray) F 0 Walk.start =
      walkTokens (ByteArray.mk (structBytes (tokTree n)).toArray)
        (ByteArray.mk (stringBytes (tokTree n)).toArray) f (8 + 4 * (n - 3) + 4)
        ⟨[], true, #[⟨"", none, []⟩]⟩ := by
  subst hF
  generalize hm : n - 3 = m
  have hS := tok_struct n
  rw [hm] at hS
  generalize ByteArray.mk (stringBytes (tokTree n)).toArray = strs
  rw [hS]
  have hnl := length_nops m
  have hnop : Item.bytes [] Item.nop = be32 4 := rfl
  have hread : ∀ k, k ≤ m → ([0, 0, 0, 1, 0, 0, 0, 0] ++ ((List.replicate m Item.nop).flatMap
      (Item.bytes []) ++ (be32 2 ++ be32 9))).drop (8 + 4 * k) =
      (List.replicate (m - k) Item.nop).flatMap (Item.bytes []) ++ (be32 2 ++ be32 9) := by
    intro k hk
    rw [show 8 + 4 * k = ([0, 0, 0, 1, 0, 0, 0, 0] : List UInt8).length + 4 * k from rfl,
      List.drop_length_add_append, drop_flatMap_const _ 4 _ _ _
        (fun a ha => by rw [List.eq_of_mem_replicate ha]; rfl) (by simpa using hk),
      List.drop_replicate]
  let Wr : Walk := ⟨[⟨0, [], false⟩], true, #[⟨"", none, []⟩]⟩
  have hroot := decode_root (l := [0, 0, 0, 1, 0, 0, 0, 0] ++ ((List.replicate m Item.nop).flatMap
      (Item.bytes []) ++ (be32 2 ++ be32 9))) (c := 0) strs rfl rfl
  rw [walkTokens_step hroot (by simp) (rfl : Walk.start.place _ = .ok Wr)]
  have hit := walkTokens_iter (str := ByteArray.mk ([0, 0, 0, 1, 0, 0, 0, 0] ++
      ((List.replicate m Item.nop).flatMap (Item.bytes []) ++ (be32 2 ++ be32 9))).toArray)
    (strs := strs) (fun k => 8 + 4 * k) (fun _ => Wr) (fun _ => .nop) m ?_ (f + 1)
  · simp only [Nat.mul_zero, Nat.add_zero] at hit
    rw [hit]
    refine walkTokens_step ((decode_tag (u32At_of_take ?_ (by decide) ?_)).1 rfl) (by simp) rfl
    · rw [hread m (Nat.le_refl _), Nat.sub_self, List.replicate_zero, List.flatMap_nil,
        List.nil_append]
      rfl
    · simp only [List.length_append, hnl, length_be32, List.length_cons, List.length_nil]; omega
  · intro k hk
    refine ⟨(decode_tag (u32At_of_take ?_ (by decide) ?_)).2.1 rfl, by simp, rfl⟩
    · rw [hread k (by omega), show m - k = (m - k - 1) + 1 by omega, List.replicate_succ,
        List.flatMap_cons, hnop, List.append_assoc]
      rfl
    · simp only [List.length_append, hnl, length_be32, List.length_cons, List.length_nil]; omega

/-- The length of the structure block of `tokTree n`. -/
theorem length_tok_struct (n : Nat) : (structBytes (tokTree n)).length = 4 * (n - 3) + 16 := by
  have h := congrArg List.length (tok_struct n)
  simp only [List.length_append, length_nops, length_be32, List.length_cons,
    List.length_nil] at h
  omega

/-- The length of `tokTree n` without padding. -/
theorem natural_tok (n : Nat) : natural (tokTree n) = 72 + 4 * (n - 3) := by
  have h := congrArg List.length (tok_struct n)
  simp only [List.length_append, length_nops, length_be32, List.length_cons,
    List.length_nil] at h
  simp only [natural, h, length_mapBytes]
  simp only [tokTree, stringBytes, List.flatMap_nil, List.length_nil]
  omega

/-- The end token of `tokTree n` ends its walk. -/
theorem tok_end (n f : Nat) :
    walkTokens (ByteArray.mk (structBytes (tokTree n)).toArray)
        (ByteArray.mk (stringBytes (tokTree n)).toArray) (f + 1) (8 + 4 * (n - 3) + 4)
        ⟨[], true, #[⟨"", none, []⟩]⟩ = .ok #[⟨"", none, []⟩] := by
  have hS := tok_struct n
  generalize n - 3 = m at hS ⊢
  have hnl := length_nops m
  generalize ByteArray.mk (stringBytes (tokTree n)).toArray = strs
  rw [hS]
  have hl : ([0, 0, 0, 1, 0, 0, 0, 0] ++ ((List.replicate m Item.nop).flatMap (Item.bytes []) ++
      (be32 2 ++ be32 9))).length = 8 + 4 * m + 4 + 4 := by
    simp only [List.length_append, hnl, length_be32, List.length_cons, List.length_nil]; omega
  have hd := (decode_tag (strs := strs) (u32At_of_take (v := 9) (l := [0, 0, 0, 1, 0, 0, 0, 0] ++
      ((List.replicate m Item.nop).flatMap (Item.bytes []) ++ (be32 2 ++ be32 9)))
      (i := 8 + 4 * m + 4) ?_ (by decide) (by omega))).2.2 rfl
  · rw [← hl, ← size_mk] at hd
    exact walkTokens_end hd rfl rfl
  · rw [show 8 + 4 * m + 4 = ([0, 0, 0, 1, 0, 0, 0, 0] : List UInt8).length +
        (((List.replicate m Item.nop).flatMap (Item.bytes [])).length + (be32 2).length) by
        rw [hnl, length_be32]; rfl,
      List.drop_length_add_append, List.drop_length_add_append, List.drop_left]
    rfl

/-- A structure block of `MAX_TOKENS` tokens is accepted. -/
theorem parse_tokens_limit : ∃ t, Fdt.parse (treeOfTokens MAX_TOKENS.toNat) = .ok t := by
  have hmax : max (natural (tokTree MAX_TOKENS.toNat)) 0 ≤ MAX_BLOB_SIZE.toNat := by
    rw [natural_tok]; decide
  have h12 : 12 ≤ (structBytes (tokTree MAX_TOKENS.toNat)).length := by
    rw [length_tok_struct]; omega
  have hw : walkTokens (ByteArray.mk (structBytes (tokTree MAX_TOKENS.toNat)).toArray)
      (ByteArray.mk (stringBytes (tokTree MAX_TOKENS.toNat)).toArray) MAX_TOKENS.toNat 0
        Walk.start = .ok #[⟨"", none, []⟩] := by
    rw [tok_walk MAX_TOKENS.toNat 1 MAX_TOKENS.toNat (by decide), tok_end]
  exact ⟨_, (parse_built (tokTree MAX_TOKENS.toNat) 0 hmax h12
    (reservationMap_none _ _ hmax rfl)).trans (by rw [structureNodes_built, hw]; rfl)⟩

/-- A structure block of `MAX_TOKENS + 1` tokens fails with `LimitExceeded`. -/
theorem parse_tokens_over :
    Fdt.parse (treeOfTokens (MAX_TOKENS.toNat + 1)) = .error .limitExceeded := by
  have hmax : max (natural (tokTree (MAX_TOKENS.toNat + 1))) 0 ≤ MAX_BLOB_SIZE.toNat := by
    rw [natural_tok]; decide
  have h12 : 12 ≤ (structBytes (tokTree (MAX_TOKENS.toNat + 1))).length := by
    rw [length_tok_struct]; omega
  have hw : walkTokens (ByteArray.mk (structBytes (tokTree (MAX_TOKENS.toNat + 1))).toArray)
      (ByteArray.mk (stringBytes (tokTree (MAX_TOKENS.toNat + 1))).toArray) MAX_TOKENS.toNat 0
        Walk.start = .error .limitExceeded := by
    rw [tok_walk (MAX_TOKENS.toNat + 1) 0 MAX_TOKENS.toNat (by decide)]
    rfl
  exact (parse_built (tokTree (MAX_TOKENS.toNat + 1)) 0 hmax h12
    (reservationMap_none _ _ hmax rfl)).trans (by rw [structureNodes_built, hw]; rfl)

end Krepi.Proofs.Fdt
