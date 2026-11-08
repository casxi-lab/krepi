module

/-!
The replay of the vectors fixture of `cargo xtask formal vectors`, with
Lean core only: the sum of the two natural numbers of an input
`a=<m> b=<n>`.
-/

namespace Krepi.SpecTests.Fixture.Sum

/-- The sum of the numbers `a` and `b` of `input`, or `malformed` for any
other input. -/
public def replay (input : String) : String :=
  match (input.splitOn " ").map (·.splitOn "=") with
  | [["a", a], ["b", b]] =>
    match a.toNat?, b.toNat? with
    | some a, some b => toString (a + b)
    | _, _ => "malformed"
  | _ => "malformed"

#guard replay "a=1 b=2" == "3"
#guard replay "a=18446744073709551615 b=1" == "18446744073709551616"
#guard replay "a=1" == "malformed"

end Krepi.SpecTests.Fixture.Sum
