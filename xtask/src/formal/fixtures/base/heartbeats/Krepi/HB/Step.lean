module

public import Aeneas

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result

namespace Krepi.HB

def idU32 (x : U32) : Result U32 := ok x

#count_heartbeats in
/-- The identity, with a doc comment
of two lines. -/
@[step] theorem idU32_spec (x : U32) : idU32 x ⦃ y => y = x ⦄ := by
  unfold idU32
  simp

#count_heartbeats in
theorem after (x : Nat) : x + 0 = x := by
  simp

end Krepi.HB
