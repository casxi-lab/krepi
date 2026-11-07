module

public import Aeneas

namespace Krepi.HB

/-- The first of two counted theorems in one file. -/
public theorem pa (x : Nat) : (x + 1) * (x + 2) = x ^ 2 + 3 * x + 2 := by
  ring

public theorem pb (x : Nat) : (x + 1) * (x + 2) * (x + 3) * (x + 4) =
    x ^ 4 + 10 * x ^ 3 + 35 * x ^ 2 + 50 * x + 24 := by
  ring

end Krepi.HB
