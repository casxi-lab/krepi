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

Every theorem here is proved, without evaluating any entry: the errors that
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

public theorem discoverBootMemoryNoBadTree : DiscoverBootMemoryNoBadTree :=
  fun _ handOver a image ht => ne_of_errsIn (discoverBootMemory_errs ht handOver a image)
    (fun h => h rfl)

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
  intro profile cells ids n hc
  have h2 : cells.toNat ≤ 2 := by rcases hc with rfl | rfl <;> decide
  refine ne_of_errsIn (P := (· ≠ .unsupportedCells)) ?_ (fun h => h rfl)
  unfold cpuOfChild
  errs_auto
  all_goals exact errsIn_sub (cellsU64_small _ h2) (by decide)

public theorem findAvailableNoLimitExceeded : FindAvailableNoLimitExceeded := by
  intro m size alignment minimum limit
  refine ne_of_errsIn (P := (· ≠ .limitExceeded)) ?_ (fun h => h rfl)
  unfold BootMemory.findAvailable
  refine errsIn_jp (fun _ => by decide) fun _ => ?_
  refine errsIn_jp (fun _ => by decide) fun hpow => ?_
  have hal : 0 < alignment.toNat := by
    have h2 : isPowerOfTwo alignment = true := by simpa using hpow
    simp only [isPowerOfTwo, List.any_eq_true, beq_iff_eq] at h2
    obtain ⟨k, -, hk⟩ := h2
    rw [hk]
    exact Nat.two_pow_pos k
  generalize m.ram = l
  induction l with
  | nil => exact errsIn_ok _
  | cons r rest ih =>
    rw [BootMemory.searchRanges]
    refine errsIn_bind (errsIn_sub (alignUp_errs _ _) (by decide)) fun c _ => ?_
    refine errsIn_bind (searchRange_fuel hal _ _ ?_) fun o _ => ?_
    · have := List.countP_le_length (p := fun x => decide (c < x.endNat)) (l := m.exclusions)
      simp only [BootMemory.exclusions, List.length_cons, List.length_map] at this ⊢
      omega
    · split
      · exact errsIn_pure _
      · exact ih

public theorem bankBytesFit : BankBytesFit := by
  intro ram banks h
  obtain ⟨hres, hpw, hne⟩ := addBank_fold ram [] banks h List.Pairwise.nil
  rw [hres, List.nil_append] at hpw ⊢
  have := sorted_bytes (sortByStart ram) 0 (by decide) (sortByStart_pairwise ram hne hpw)
    fun x hx => ⟨Nat.zero_le _, (hne x ((sortByStart_perm ram).mem_iff.1 hx)).2⟩
  omega

end Krepi.Proofs.Fdt.Witnesses
