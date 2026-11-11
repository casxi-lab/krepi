module

public import KrepiGen.Calibration.Funs

/-!
# Statements about the calibration target

One proposition for each entry of the calibration target, over every input
that its preconditions allow. The theorems below `Krepi.Proofs.Calibration`
prove them, and each mutant that the registry of the target lists makes the
proof of one of them fail.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open KrepiGen.Calibration

namespace Krepi.Calibration

/-- The largest generation that a handle holds, `2 ^ 24 - 1`. -/
def generationMax : Nat := 16777215

/-- A handle packs an index of at most 255 and a generation that fits, the
generation above the eight bits of the index; anything else is refused. -/
def Encode : Prop :=
  ∀ index generation : Std.U32,
    handle.encode index generation ⦃ r =>
      match r with
      | some h =>
        index.val ≤ 255 ∧ generation.val ≤ generationMax ∧
          h.val = generation.val * 256 + index.val
      | none => 255 < index.val ∨ generationMax < generation.val ⦄

/-- The index of a handle is its eight low bits. -/
def Index : Prop :=
  ∀ h : Std.U32, handle.index h ⦃ r => r.val = h.val % 256 ⦄

/-- The generation of a handle is what lies above its index. -/
def Generation : Prop :=
  ∀ h : Std.U32, handle.generation h ⦃ r => r.val = h.val / 256 ⦄

/-- The next handle names the same slot at the next generation, unless the
generation is the largest. -/
def Next : Prop :=
  ∀ h : Std.U32,
    handle.next h ⦃ r =>
      match r with
      | some h' => h'.val % 256 = h.val % 256 ∧ h'.val / 256 = h.val / 256 + 1
      | none => h.val / 256 = generationMax ⦄

/-- A charge leaves the rest of the budget, unless it exceeds the budget. -/
def Charge : Prop :=
  ∀ left cost : Std.U32,
    arith.charge left cost ⦃ r =>
      match r with
      | some rest => cost.val ≤ left.val ∧ rest.val = left.val - cost.val
      | none => left.val < cost.val ⦄

/-- A split is the quotient, rounded down, unless there are no parts. -/
def Split : Prop :=
  ∀ total parts : Std.U32,
    arith.split total parts ⦃ r =>
      match r with
      | some share => 0 < parts.val ∧ share.val = total.val / parts.val
      | none => parts.val = 0 ⦄

/-- A range fits exactly when its end is at most the limit. -/
def Fits : Prop :=
  ∀ base length limit : Std.U32,
    arith.fits base length limit ⦃ b => (b = true ↔ base.val + length.val ≤ limit.val) ⦄

/-- A table is made for one to four slots, with none in use. -/
def New : Prop :=
  ∀ capacity : Std.U32,
    table.Table.new capacity ⦃ r =>
      match r with
      | some t => 0 < capacity.val ∧ capacity.val ≤ 4 ∧ t.capacity = capacity ∧ t.used.val = 0
      | none => capacity.val = 0 ∨ 4 < capacity.val ⦄

/-- The slot that is allocated is the first that is not in use, while one
of the capacity is left; the capacity and the generations do not change. -/
def Alloc : Prop :=
  ∀ t : table.Table, t.used.val ≤ t.capacity.val →
    t.alloc ⦃ r t' =>
      t'.capacity = t.capacity ∧ t'.generations = t.generations ∧
        match r with
        | some index =>
          index = t.used ∧ t.used.val < t.capacity.val ∧ t'.used.val = t.used.val + 1
        | none => t.capacity.val ≤ t.used.val ∧ t'.used = t.used ⦄

/-- Retiring a slot of the capacity moves it to its next generation, unless
that overflows, and changes nothing else; otherwise nothing changes. -/
def Retire : Prop :=
  ∀ (t : table.Table) (index : Std.U32), t.capacity.val ≤ 4 →
    t.retire index ⦃ b t' =>
      t'.capacity = t.capacity ∧ t'.used = t.used ∧
        if b then
          index.val < t.capacity.val ∧
            (t'.generations.val[index.val]!).val = (t.generations.val[index.val]!).val + 1 ∧
            ∀ j, j ≠ index.val → t'.generations.val[j]! = t.generations.val[j]!
        else
          t' = t ∧
            (t.capacity.val ≤ index.val ∨ (t.generations.val[index.val]!).val = 4294967295) ⦄

/-- A handle is current exactly when it names a slot of the capacity at the
generation of the slot. -/
def IsCurrent : Prop :=
  ∀ (t : table.Table) (h : Std.U32), t.capacity.val ≤ 4 →
    t.is_current h ⦃ b =>
      (b = true ↔ h.val % 256 < t.capacity.val ∧
        (t.generations.val[h.val % 256]!).val = h.val / 256) ⦄

/-- At most the capacity of slots are retired, and all of them when no slot
of the capacity has the generation 0. -/
def Retired : Prop :=
  ∀ t : table.Table, t.capacity.val ≤ 4 →
    t.retired ⦃ n =>
      n.val ≤ t.capacity.val ∧
        ((∀ j < t.capacity.val, (t.generations.val[j]!).val ≠ 0) → n.val = t.capacity.val) ⦄

end Krepi.Calibration
