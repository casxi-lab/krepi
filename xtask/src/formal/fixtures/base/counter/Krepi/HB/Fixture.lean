module

public import Aeneas

namespace Krepi.HB

public theorem fx (x : Nat) : (x + 1) * (x + 2) * (x + 3) = x ^ 3 + 6 * x ^ 2 + 11 * x + 6 := by
  ring

end Krepi.HB
