module

public import Krepi.Spec.Fdt.Witnesses
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.SpanLemmas
import Krepi.Proofs.Fdt.PlanLemmas
import Krepi.Proofs.Fdt.DiscoveryLemmas
import Krepi.Proofs.Fdt.ErrorSets
import Krepi.Proofs.Fdt.BoundLemmas

/-!
# Device tree: proofs of the unreachable error branches

One theorem for each proposition of `Krepi.Spec.Fdt.Witnesses` that the
module does not prove itself, whose type is exactly that proposition: for
each error branch that no input of its entry reaches, that the entry never
takes it.

Every theorem here is proved but `discoverBootMemoryNoBadTree`,
`cpuRegNoUnsupportedCells` and `findAvailableNoLimitExceeded`, which are
planned: each proof is `sorry` until a proof pull request proves it. The
proofs evaluate no entry: the errors that
an entry can give are followed through its steps
(`Krepi.Proofs.Fdt.ErrorSets`), and the bounds of fuel and of sums come from
`Krepi.Proofs.Fdt.BoundLemmas`. Mathlib is imported so that the gate counts
the heartbeats of each theorem.
-/

namespace Krepi.Proofs.Fdt.Witnesses

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt Krepi.Spec.Fdt.Witnesses

/-! ## Unreachable error branches -/

public theorem headerNoOverflow : HeaderNoOverflow := fun input =>
  ne_of_errsIn (header_errs input) (fun h => h rfl)

public theorem reservationEntriesFit : ReservationEntriesFit := by
  intro input h hh
  have := (header_bounds hh).1
  have h128 : MAX_RESERVATIONS.toNat = 128 := rfl
  rw [h128]
  omega

public theorem tokensNoOverflow : TokensNoOverflow := fun _ _ hh =>
  ne_of_errsIn (walkTokens_errs _ (header_bounds hh).2 _ _ _) (fun h => h rfl)

public theorem reservationFuelSuffices : ReservationFuelSuffices := by
  intro h n
  unfold reservationMap
  exact reservationsFrom_fuel h _ n _ [] (by simp) (by simp)

public theorem discoverMemoryNoBadTree : DiscoverMemoryNoBadTree := fun _ ht =>
  ne_of_errsIn (discoverMemory_errs ht) (fun h => h rfl)

public theorem discoverBootMemoryNoBadTree : DiscoverBootMemoryNoBadTree := by
  sorry

public theorem ramBytesFit : RamBytesFit := by
  intro t m h
  obtain ⟨-, -, -, ⟨-, hne, hpw⟩, -⟩ := discoverMemory_ok h
  exact disjoint_bytes hne hpw

public theorem climbRangesNoBadTree : ClimbRangesNoBadTree := fun fuel bus s =>
  ne_of_errsIn (climbRanges_errs fuel bus s) (fun h => h rfl)

public theorem translateRegFuelSuffices : TranslateRegFuelSuffices := by
  intro n s ht
  refine ne_of_errsIn (P := (· ≠ .limitExceeded)) ?_ (fun h => h rfl)
  obtain ⟨t, i⟩ := n
  unfold Node.translateReg
  split
  · rename_i bus hbus
    obtain ⟨j, rfl, -⟩ := parent_depth ht hbus
    refine errsIn_bind (climbRanges_fuel ht _ j s (ht.2.2.2.2.2.2.2 j j.isLt).2.2.1)
      fun r _ => ?_
    exact errsIn_bind (errsIn_sub (endAddr_errs _) (by decide)) fun _ _ => errsIn_pure _
  · exact errsIn_throw (by decide)

public theorem windowTranslationNoOverflow : WindowTranslationNoOverflow := by
  intro m s reverse w ws hm hws hw
  refine ne_of_errsIn (P := (· ≠ .overflow)) ?_ (fun h => h rfl)
  by_cases hs : s.size = 0
  · unfold AddressMap.translate
    exact errsIn_jp (fun _ => by decide) fun h => absurd hs h
  · rw [translate_windows hs hw hws]
    refine throughWindows_noov _ fun x hx => ?_
    obtain ⟨hsz, hwx⟩ := window_target (hm.2.2.2 _ hws x hx) reverse
    exact ⟨hsz, hwx.1⟩

public theorem cpuRegNoUnsupportedCells : CpuRegNoUnsupportedCells := by
  sorry

public theorem findAvailableNoLimitExceeded : FindAvailableNoLimitExceeded := by
  sorry

public theorem bankBytesFit : BankBytesFit := by
  intro ram banks h
  obtain ⟨hres, hpw, hne⟩ := addBank_fold ram [] banks h List.Pairwise.nil
  rw [hres, List.nil_append] at hpw ⊢
  have := sorted_bytes (sortByStart ram) 0 (by decide) (sortByStart_pairwise ram hne hpw)
    fun x hx => ⟨Nat.zero_le _, (hne x ((sortByStart_perm ram).mem_iff.1 hx)).2⟩
  omega

end Krepi.Proofs.Fdt.Witnesses
