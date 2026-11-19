module

public import Krepi.Spec.PageTables.Witnesses.PageOwnership
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.OwnerLemmas
import Krepi.Proofs.PageTables.WriteLemmas
import Krepi.Proofs.PageTables.ScanLemmas
import Krepi.Proofs.PageTables.Ownership

/-!
# Page tables: proofs of the unreachable error branches of the page ownership table

One theorem for each proposition of
`Krepi.Spec.PageTables.Witnesses.PageOwnership` that the module does not
prove itself, whose type is exactly that proposition: for each error branch
that no input of its entry reaches, that the entry never takes it.

`takeAcceptsChoice`: a table that the entries build is well-formed (the
private `built_wellFormed`, by `Ownership.newOwnershipWellFormed` and the
well-formedness of each write entry, `assign` on a choice of `choose`), so
its extents are in address order and apart. A choice of `choose` lies inside
a free extent with the room that taking it needs (`choose_extent` of
`Krepi.Proofs.PageTables.ScanLemmas`), and the counter that `choose` found
not exhausted is the counter of `take`; the first free extent that holds the
range, which `take` finds, holds a page of it, so it is that extent.

`highPlacementNoOverflow`: the scan of a high placement never fails with
`AddressOverflow` (`scan_error`, `fit_high_ne_overflow`), so that error of
`choose` is the one of its first check (`choose_error`).

Every theorem here is proved. Mathlib is imported so that the gate counts the
heartbeats of each theorem.
-/

namespace Krepi.Proofs.PageTables.Witnesses.PageOwnership

open Krepi.Spec.PageTables.Witnesses.PageOwnership
open Krepi.Spec.PageTables Krepi.SpecProperties.PageTables
open Krepi.Proofs.PageTables

/-- A table that the entries build is well-formed. -/
private theorem built_wellFormed {E X : Nat} {t : Ownership E X} (h : Built t) : t.WellFormed := by
  induction h with
  | new h => exact Ownership.newOwnershipWellFormed _ _ _ _ _ _ h
  | assign _ hc ha ih =>
    exact Ownership.assignWellFormed _ _ _ _ _ _ _ ih ⟨_, _, _, _, hc⟩ ha
  | reserve _ h ih => exact Ownership.reserveWellFormed _ _ _ _ _ _ _ _ _ ih h
  | publish _ h ih => exact Ownership.publishWellFormed _ _ _ _ _ _ _ ih h
  | cancel _ h ih => exact Ownership.cancelWellFormed _ _ _ _ _ _ ih h
  | release _ h ih => exact Ownership.releaseWellFormed _ _ _ _ _ _ ih h

/-! ## Unreachable error branches -/

public theorem takeAcceptsChoice : TakeAcceptsChoice := by
  intro E X t o m al p c s hb hc
  have hord : ExtentsInOrder t.extents := (built_wellFormed hb).2.2.2.2.2.2.1
  have hcnt := (choose_ok hc).2.2.2.2.1
  obtain ⟨e, he, hf, hcont, hroom⟩ := choose_extent hc
  obtain ⟨g, hg⟩ : ∃ g, t.counter = .next g := by
    cases h : t.counter with
    | next g => exact ⟨g, rfl⟩
    | exhausted => exact absurd h hcnt
  cases hsp : splitFirst (fun e => e.holding == .free && e.range.contains c.range) t.extents [] with
  | none => exact absurd (splitFirst_none hsp e he) (by simp [hf, hcont])
  | some v =>
    obtain ⟨before, e', after⟩ := v
    obtain ⟨hl, hp⟩ := splitFirst_some hsp
    simp only [List.reverse_nil, List.nil_append] at hl
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have he' : e' ∈ t.extents := by rw [hl]; simp
    have hee : e' = e := by
      have h1 := range_lt c.range
      simp only [PhysRange.contains, Bool.and_eq_true, decide_eq_true_eq] at hcont hp
      rcases pairwise_mem_cases hord he' he with h | h | h
      · exact h
      · omega
      · omega
    subst hee
    cases htk : t.take c s with
    | ok y => exact ⟨y, rfl⟩
    | error err =>
      exfalso
      unfold Ownership.take at htk
      simp only [hg, pure, Except.pure, bind, Except.bind, hsp] at htk
      split at htk
      · omega
      · cases htk

public theorem highPlacementNoOverflow : HighPlacementNoOverflow := by
  intro E X t o m al w h
  rcases choose_error h with ⟨-, h1⟩ | he | he | he | ⟨-, -, hs⟩
  · exact h1
  · cases he
  · cases he
  · cases he
  · rcases scan_error hs with ⟨-, e, -, -, hf⟩ | ⟨-, ⟨he, -⟩ | ⟨he, -⟩⟩
    · exact absurd hf (fit_high_ne_overflow _ _ _ _)
    · cases he
    · cases he

end Krepi.Proofs.PageTables.Witnesses.PageOwnership
