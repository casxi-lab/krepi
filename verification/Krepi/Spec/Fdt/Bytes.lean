module

public import Krepi.Spec.Fdt.Basic

/-!
# Device tree: reading bytes

The byte-level reads of the parse and of the node access: big-endian words,
NUL-terminated UTF-8 strings within a block, the padding up to a multiple of
4, and the character sets of node and property names. Every read is bounded
by the bytes it is given and fails with the error that the contract gives for
a read past the end of a block, so no read takes a value from outside them.

A string is UTF-8 as Lean core defines it (`String.fromUTF8?`, whose
`ByteArray.IsValidUTF8` is the encoding of a list of Unicode scalar values),
which refuses overlong encodings, surrogates and code points above
`U+10FFFF`. The character sets are those of Tables 2.1 and 2.2 of DTSpec v0.4,
whose letters and digits are the ASCII ones (`Char.isAlphanum`), with `@`
between a node name and its unit address.
-/

@[expose] public section

namespace Krepi.Spec.Fdt

/-! ## Words -/

/-- The number that the bytes `b[i]`, ..., `b[i + n - 1]` write in big-endian
order. The callers read only bytes inside `b`. -/
def beNat (b : ByteArray) (i n : Nat) : Nat :=
  (b.extract i (i + n)).toList.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- The big-endian 32-bit word at `i`, or `Truncated` when it runs past the end
of `b`. -/
def u32At (b : ByteArray) (i : Nat) : Except Error UInt32 :=
  if i + 4 ≤ b.size then .ok (UInt32.ofNat (beNat b i 4)) else .error .truncated

/-- The big-endian 64-bit word at `i`, or `Truncated` when it runs past the end
of `b`. -/
def u64At (b : ByteArray) (i : Nat) : Except Error UInt64 :=
  if i + 8 ≤ b.size then .ok (UInt64.ofNat (beNat b i 8)) else .error .truncated

/-! ## Strings -/

/-- The first index at or after `i` that holds a NUL byte, trying at most
`fuel` indices. -/
def findNulFrom (b : ByteArray) : (fuel i : Nat) → Option Nat
  | 0, _ => none
  | fuel + 1, i => if b[i]? = some 0 then some i else findNulFrom b fuel (i + 1)

/-- The first NUL byte of `b` at or after `start`: a string is read up to the
end of its block and no further. -/
def findNul (b : ByteArray) (start : Nat) : Option Nat :=
  findNulFrom b (b.size - start) start

/-- The NUL-terminated string at `start` of the block `b` and the index just
after its NUL; `BadString` when no NUL follows within the block, which holds
for a start at or past its end, or when the bytes before the NUL are not
UTF-8. -/
def cString (b : ByteArray) (start : Nat) : Except Error (String × Nat) :=
  match findNul b start with
  | none => .error .badString
  | some nul =>
    match String.fromUTF8? (b.extract start nul) with
    | none => .error .badString
    | some s => .ok (s, nul + 1)

/-! ## Padding -/

/-- The least multiple of 4 that is at least `n`. -/
def align4 (n : Nat) : Nat := (n + 3) / 4 * 4

/-- The end of the padding after `e`, up to the next multiple of 4:
`Truncated` when the padding runs past the end of the block, and, when
`requireZero`, `BadPadding` for a nonzero byte in it. -/
def paddedEnd (b : ByteArray) (e : Nat) (requireZero : Bool) : Except Error Nat :=
  let aligned := align4 e
  if b.size < aligned then .error .truncated
  else if requireZero && (b.extract e aligned).toList.any (· ≠ 0) then .error .badPadding
  else .ok aligned

/-! ## Names -/

/-- A character of a node name: an ASCII letter or digit, or one of
`,._+-@`. -/
def isNodeNameChar (c : Char) : Bool :=
  c.isAlphanum || [',', '.', '_', '+', '-', '@'].contains c

/-- A character of a property name: an ASCII letter or digit, or one of
`,._+?#-`. -/
def isPropertyNameChar (c : Char) : Bool :=
  c.isAlphanum || [',', '.', '_', '+', '?', '#', '-'].contains c

/-! ## Ranges of offsets -/

/-- Whether the offsets `[a, ae)` and `[b, be)` intersect: both are nonempty
and each starts before the other ends. -/
def intersects (a ae b be : Nat) : Bool :=
  a < ae && b < be && a < be && b < ae

end Krepi.Spec.Fdt
