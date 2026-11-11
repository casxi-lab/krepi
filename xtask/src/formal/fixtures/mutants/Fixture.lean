module

/-!
# A fixture of the declaration ranges

Declarations of the shapes that a proof module may hold.
-/

namespace Krepi.Proofs.Fixture

/-- A documented theorem with an attribute. -/
@[simp] public theorem documented : 1 + 1 = 2 := rfl

public theorem plain (n : Nat) : n + 0 = n := by
  simp

private theorem hidden (n : Nat) : 0 + n = n := by
  simp

public def double (n : Nat) : Nat := n + n

public abbrev Pair := Nat × Nat

public structure Point where
  x : Nat
  y : Nat
  deriving Repr, BEq

public inductive Color where
  | red
  | green

deriving instance BEq for Color

public instance : Inhabited Point := ⟨⟨0, 0⟩⟩

public def withHelper (n : Nat) : Nat := helper n + 1
where
  helper (m : Nat) : Nat := m * 2

variable {α : Type} [Inhabited α]

public theorem uses_instance (_a : α) : (default : α) = default := rfl

omit [Inhabited α] in
public theorem after_omit (a : α) : a = a := rfl

example : double 1 = 2 := rfl

end Krepi.Proofs.Fixture
