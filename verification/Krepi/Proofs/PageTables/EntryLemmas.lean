module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: lemmas about the first checks of the entries

What a first check that passes tells: `checkEntry_ok`, `checkPhysical_ok`
and `checkPool_ok` (the pool that the contract admits, `PoolOk`).
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables

theorem checkEntry_ok {r : Region} {N : Nat} {v : UInt64} {align : Nat} {base : UInt64}
    {bits : UInt8} {u : Unit} :
    checkEntry r N v align base bits = .ok u ↔
      v.toNat % align = 0 ∧ base.toNat % PAGE_SIZE = 0 ∧ r.holds v = true ∧
        widthOk bits = true ∧ poolFits N base bits = true := by
  unfold checkEntry
  by_cases h1 : v.toNat % align = 0 <;> by_cases h2 : base.toNat % PAGE_SIZE = 0 <;>
    by_cases h3 : r.holds v = true <;> by_cases h4 : widthOk bits = true <;>
    by_cases h5 : poolFits N base bits = true <;>
    simp_all [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

theorem checkPhysical_ok {p : UInt64} {align : Nat} {bits : UInt8} {u : Unit} :
    checkPhysical p align bits = .ok u ↔ p.toNat % align = 0 ∧ p.toNat < 2 ^ bits.toNat := by
  unfold checkPhysical
  by_cases h1 : p.toNat % align = 0 <;> by_cases h2 : 2 ^ bits.toNat ≤ p.toNat <;>
    simp_all [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

theorem checkPool_ok {N : Nat} {base : UInt64} {bits : UInt8} {u : Unit} :
    checkPool N base bits = .ok u ↔ PoolOk N base bits := by
  unfold checkPool PoolOk
  by_cases h1 : base.toNat % PAGE_SIZE = 0 <;> by_cases h2 : widthOk bits = true <;>
    by_cases h3 : poolFits N base bits = true <;>
    simp_all [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]

end Krepi.Proofs.PageTables
