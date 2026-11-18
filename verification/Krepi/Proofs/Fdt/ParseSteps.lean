module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
public import Krepi.Proofs.Fdt.ExceptLemmas
public import Krepi.Proofs.Fdt.ParseBytes

/-!
# Device tree: the steps of the parse

Lemmas about the steps of `Fdt.parse` on any input:

- `header_ok`: what a successful header tells about the input: at least 40
  bytes, the magic, and a `totalsize` from 40 to `MAX_BLOB_SIZE` that the
  input holds;
- `block_mk`: a block of a byte array of a list;
- the decoding of the tokens of a structure block written as a list:
  `decode_root` (the begin token of the root), `decode_tag` (the end node, a
  no-operation and the end token) and `decode_property`;
- the walk over the tokens: `walkTokens_step`, `walkTokens_step_error`,
  `walkTokens_end` and `walkTokens_iter`, which consumes a sequence of
  decoded and placed tokens;
- `errOf`, `eq_error_of_errOf` and `exists_ok_of_toBool`, through which a
  kernel decision of a result gives an equation (Lean core has no decidable
  equality for `Except`).
-/

@[expose] public section

namespace Krepi.Proofs.Fdt

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

/-- What a successful header tells about the input: at least 40 bytes, the magic, and a `totalsize`
from 40 to `MAX_BLOB_SIZE` that the input holds. -/
theorem header_ok {input : ByteArray} {hd : Header} (h : header input = .ok hd) :
    HEADER_SIZE ≤ input.size ∧ u32At input 0 = .ok FDT_MAGIC ∧
      (∃ v, u32At input 4 = .ok v ∧ v.toNat = hd.layout.total) ∧
      HEADER_SIZE ≤ hd.layout.total ∧ hd.layout.total ≤ MAX_BLOB_SIZE.toNat ∧
      hd.layout.total ≤ input.size := by
  unfold header at h
  obtain ⟨h1, h⟩ := except_jp_ok h
  obtain ⟨m, hm, h⟩ := except_bind_ok.1 h
  obtain ⟨h2, h⟩ := except_jp_ok h
  obtain ⟨v, hv, h⟩ := except_bind_ok.1 h
  obtain ⟨h3, h⟩ := except_jp_ok h
  obtain ⟨h4, h⟩ := except_jp_ok h
  obtain ⟨h5, h⟩ := except_jp_ok h
  obtain ⟨a, -, h⟩ := except_bind_ok.1 h
  obtain ⟨a, -, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨a, -, h⟩ := except_bind_ok.1 h
  obtain ⟨a, -, h⟩ := except_bind_ok.1 h
  obtain ⟨a, -, h⟩ := except_bind_ok.1 h
  obtain ⟨a, -, h⟩ := except_bind_ok.1 h
  obtain ⟨a, -, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨a, -, h⟩ := except_bind_ok.1 h
  obtain ⟨a, -, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨-, h⟩ := except_jp_ok h
  have h := except_pure_ok.1 h
  subst h
  refine ⟨Nat.le_of_not_lt h1, ?_, ⟨v, hv, rfl⟩, Nat.le_of_not_lt h3, Nat.le_of_not_lt h4,
    Nat.le_of_not_lt h5⟩
  rw [hm, Decidable.not_not.1 h2]

/-- A block of a byte array of a list that lies after the header. -/
theorem block_mk (P C D : List UInt8) (h40 : HEADER_SIZE ≤ P.length)
    (hlt : P.length + C.length < 2 ^ 64) :
    block (ByteArray.mk (P ++ (C ++ D)).toArray) P.length C.length =
      .ok (ByteArray.mk C.toArray) := by
  unfold block
  refine jp_eq_of_not (by omega) ?_
  refine bind_eq_of_ok (x := checkedAdd _ _) (a := P.length + C.length) ?_ ?_
  · simp [checkedAdd, hlt]
  refine jp_eq_of_not (by simp only [size_mk, List.length_append]; omega) ?_
  rw [extract_mk_mid]
  rfl

/-! ## Tokens -/

/-- The begin token of the root, its empty name and its padding, at offset `c`. -/
theorem decode_root {l : List UInt8} {c : Nat} (strs : ByteArray)
    (h : (l.drop c).take 8 = [0, 0, 0, 1, 0, 0, 0, 0]) (hc : c % 4 = 0) :
    decodeToken (ByteArray.mk l.toArray) strs c = .ok (.beginNode "", c + 8) := by
  have hlen : c + 8 ≤ l.length := by
    have := congrArg List.length h; simp at this; omega
  unfold decodeToken
  have h0 := take_drop_of_take h 0 4 (by omega)
  simp only [Nat.add_zero] at h0
  refine bind_eq_of_ok (u32At_of_take (v := 1) (by rw [h0]; rfl) (by decide) (by omega)) ?_
  have h4 : l[c + 4]? = some 0 := by
    have := take_drop_of_take h 4 1 (by omega)
    have h' : ((l.drop (c + 4)).take 1)[0]? = some 0 := by rw [this]; rfl
    simpa using h'
  refine bind_eq_of_ok (a := ("", c + 5)) ?_ ?_
  · unfold cString findNul
    rw [findNulFrom_mk _ _ _ (c + 4) (Nat.le_refl _) (by rw [size_mk]; omega)
      (fun k h1 h2 => absurd h2 (by omega)) h4]
    simp only [ByteArray.extract_same]
    rfl
  refine bind_eq_of_ok (a := c + 8) ?_ ?_
  · have hal : align4 (c + 4 + 1) = c + 8 := by unfold align4; omega
    have := paddedEnd_mk (l := l) (e := c + 4 + 1) (by omega) ?_ true
    · rw [hal] at this; exact this
    · rw [hal, show c + 8 - (c + 4 + 1) = 3 by omega, take_drop_of_take h 5 3 (by omega)]
      decide
  exact jp_eq_of_not (by decide) rfl

/-- The tokens without operands: the end node, a no-operation and the end token. -/
theorem decode_tag {str strs : ByteArray} {c : Nat} {t : UInt32} (h : u32At str c = .ok t) :
    (t = 2 → decodeToken str strs c = .ok (.endNode, c + 4)) ∧
    (t = 4 → decodeToken str strs c = .ok (.nop, c + 4)) ∧
    (t = 9 → decodeToken str strs c = .ok (.endStructure, c + 4)) := by
  refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_⟩ <;> subst ht <;> unfold decodeToken <;>
    exact bind_eq_of_ok h rfl

/-- A property token whose name lies in the strings block and whose value fits the block. -/
theorem decode_property {l : List UInt8} {strs : ByteArray} {c len off e : Nat} {name : String}
    (hpre : (l.drop c).take 12 = [3, len, off].flatMap be32)
    (hlen : len < 2 ^ 32) (hoff : off < 2 ^ 32)
    (hsz : align4 (c + 4 + 8 + len) ≤ l.length) (h64 : c + 4 + 8 + len < 2 ^ 64)
    (hs : cString strs off = .ok (name, e))
    (hname : name ≠ "" ∧ name.utf8ByteSize ≤ MAX_PROPERTY_NAME.toNat ∧
      name.toList.all isPropertyNameChar = true) :
    decodeToken (ByteArray.mk l.toArray) strs c =
      .ok (.property name ((ByteArray.mk l.toArray).extract (c + 4 + 8) (c + 4 + 8 + len)),
        align4 (c + 4 + 8 + len)) := by
  have hal : c + 4 + 8 + len ≤ align4 (c + 4 + 8 + len) := by unfold align4; omega
  have r0 := read_word (ws := [3, len, off]) hpre 0 (by simp)
  have r1 := read_word (ws := [3, len, off]) hpre 1 (by simp)
  have r2 := read_word (ws := [3, len, off]) hpre 2 (by simp)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, List.getElem_cons_zero,
    List.getElem_cons_succ] at r0 r1 r2
  have hl : (UInt32.ofNat len).toNat = len := UInt32.toNat_ofNat_of_lt' (by simpa [UInt32.size])
  have ho : (UInt32.ofNat off).toNat = off := UInt32.toNat_ofNat_of_lt' (by simpa [UInt32.size])
  unfold decodeToken
  refine bind_eq_of_ok (u32At_of_take r0 (by decide) (by omega)) ?_
  refine bind_eq_of_ok (u32At_of_take r1 hlen (by omega)) ?_
  refine bind_eq_of_ok (u32At_of_take (by rw [Nat.add_assoc]; exact r2) hoff (by omega)) ?_
  refine bind_eq_of_ok (a := c + 4 + 8 + len) (by simp only [checkedAdd, hl]; simp [h64]) ?_
  refine jp_eq_of_not (by rw [size_mk]; omega) ?_
  refine bind_eq_of_ok (by rw [ho]; exact hs) ?_
  refine jp_eq_of_not ?_ ?_
  · obtain ⟨h1, h2, h3⟩ := hname
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true', not_or, Nat.not_lt]
    refine ⟨⟨?_, h2⟩, by simpa using h3⟩
    simpa [String.isEmpty_iff] using h1
  exact bind_eq_of_ok (paddedEnd_false hsz) rfl

/-- One token decoded and placed: the walk goes on from the next token. -/
theorem walkTokens_step {str strs : ByteArray} {c c' fuel : Nat} {w w' : Walk} {tok : Token}
    (hd : decodeToken str strs c = .ok (tok, c')) (hne : tok ≠ .endStructure)
    (hp : w.place tok = .ok w') :
    walkTokens str strs (fuel + 1) c w = walkTokens str strs fuel c' w' := by
  rw [walkTokens]
  refine bind_eq_of_ok hd ?_
  cases tok with
  | endStructure => exact absurd rfl hne
  | _ => exact bind_eq_of_ok hp rfl

/-- One token decoded whose place fails: the walk fails with that error. -/
theorem walkTokens_step_error {str strs : ByteArray} {c c' fuel : Nat} {w : Walk} {tok : Token}
    {e : Error} (hd : decodeToken str strs c = .ok (tok, c')) (hne : tok ≠ .endStructure)
    (hp : w.place tok = .error e) :
    walkTokens str strs (fuel + 1) c w = .error e := by
  rw [walkTokens]
  refine bind_eq_of_ok hd ?_
  cases tok with
  | endStructure => exact absurd rfl hne
  | _ => exact bind_eq_of_error hp

/-- The end token at the end of the block, after the root and with no open node. -/
theorem walkTokens_end {str strs : ByteArray} {c fuel : Nat} {w : Walk}
    (hd : decodeToken str strs c = .ok (.endStructure, str.size)) (hs : w.seenRoot = true)
    (ho : w.open_ = []) :
    walkTokens str strs (fuel + 1) c w = .ok w.records := by
  rw [walkTokens]
  refine bind_eq_of_ok hd ?_
  refine jp_eq_of_not ?_ rfl
  simp [hs, ho]

/-- A sequence of `m` tokens decoded and placed: the walk goes on after them with `m` tokens less of
fuel. -/
theorem walkTokens_iter {str strs : ByteArray} (cur : Nat → Nat) (W : Nat → Walk)
    (T : Nat → Token) :
    ∀ m, (∀ k < m, decodeToken str strs (cur k) = .ok (T k, cur (k + 1)) ∧
      T k ≠ .endStructure ∧ (W k).place (T k) = .ok (W (k + 1))) →
    ∀ fuel, walkTokens str strs (fuel + m) (cur 0) (W 0) = walkTokens str strs fuel (cur m) (W m)
  | 0, _, _ => rfl
  | m + 1, h, fuel => by
    rw [show fuel + (m + 1) = (fuel + 1) + m by omega,
      walkTokens_iter cur W T m (fun k hk => h k (by omega)) (fuel + 1)]
    obtain ⟨h1, h2, h3⟩ := h m (by omega)
    exact walkTokens_step h1 h2 h3

/-! ## Results -/

/-- The error of a result, if any. -/
def errOf {ε α : Type} : Except ε α → Option ε
  | .error e => some e
  | .ok _ => none

/-- A result whose error is `e` is `.error e`. -/
theorem eq_error_of_errOf {ε α : Type} {x : Except ε α} {e : ε} (h : errOf x = some e) :
    x = .error e := by
  cases x <;> simp_all [errOf]

/-- A result that `Except.toBool` accepts is a success. -/
theorem exists_ok_of_toBool {ε α : Type} {x : Except ε α} (h : x.toBool = true) :
    ∃ a, x = .ok a := by
  cases x <;> simp_all [Except.toBool]

end Krepi.Proofs.Fdt
