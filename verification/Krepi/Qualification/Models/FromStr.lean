module

public import Aeneas

/-!
# `String::from(&str)`

A definition that the reviewed external declaration of the qualification
case `str_from` uses. It serves only the type checking of that case: it is
not a model, `verification/models.json` does not register it, and no proof
target uses it.

The Rust standard library documents `String` as a UTF-8 encoded, growable
string, and `From<&str> for String` as converting a `&str` into a `String`:
the result holds a copy of the bytes of the string slice. A `str` is valid
UTF-8: the standard library may assume so, and a string slice that is not
can lead to undefined behaviour. The Aeneas
library represents `&str` as `Str`, a slice of `u8`, and `String` as the
Lean string, so `fromStr` decodes the bytes of the slice as UTF-8 with
`String.fromUTF8?`. Bytes that are not UTF-8, which no Rust `&str` holds,
give the undefined-behaviour error. Allocation failure is outside this
definition.
-/

@[expose] public section

namespace Krepi.Qualification.Models.FromStr

open Aeneas.Std

/-- The bytes of `s`, in order. -/
def bytes (s : Str) : ByteArray :=
  ⟨(s.val.map fun byte => UInt8.ofNat byte.val).toArray⟩

/-- `String::from(&str)`: the string whose UTF-8 encoding is the bytes of
`s`. -/
def fromStr (s : Str) : Result String :=
  match String.fromUTF8? (bytes s) with
  | some string => .ok string
  | none => .fail .undef

end Krepi.Qualification.Models.FromStr

end
