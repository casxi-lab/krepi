module

public import Krepi.SpecProperties.PageTables.Properties
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.PoolLemmas
import Krepi.Proofs.PageTables.EntryLemmas
import Krepi.Proofs.PageTables.WalkLemmas
import Krepi.Proofs.PageTables.WellFormedLemmas
import Krepi.Proofs.PageTables.OwnerLemmas
import Krepi.Proofs.PageTables.NewLemmas
import Krepi.Proofs.PageTables.WriteLemmas
import Krepi.Proofs.PageTables.ScanLemmas
import Krepi.Proofs.PageTables.DirectMapLemmas
import Krepi.Proofs.PageTables.Ownership

/-!
# Page tables: proofs about placement and the owners at boot

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about placement and the owners at boot,
whose type is exactly that statement: that `choose` takes the first fit of
its placement, and that the table of the kernel root matches the direct map.

`placementFirstFit` follows the scan of `choose` with
`Krepi.Proofs.PageTables.ScanLemmas`: a choice is the range that `fit` finds
in the extent where the scan stops (`scan_ok`), which is the range that the
extent gives (`fit_gives`), and every extent before it was passed over, so
each range that one gives needs more extents than the capacity has free
(`passed_gives`); a refusal comes from the end of the scan (`choose_error`,
`scan_error`), after every extent was passed over, with none that held a
range for `OutOfMemory` (`fit_none`) and one that gave a range for
`MetadataExhausted`. It needs no hypothesis on the table.

`bootOwnersMatchDirectMap` takes one owner for every managed page from
`Ownership.newOneOwner`. A page is free exactly when it is free or held,
since the table of `Ownership::new` has only free extents, so exactly when it
is a page of a usable range (`Ownership.newFreeOrHeldUsable`); and the pages
that `direct_map` of the boot maps are exactly those pages
(`Krepi.Proofs.PageTables.DirectMapLemmas`, through the private
`boot_pages`: the set of `Tables::new` on zero storage is well-formed and
maps nothing, `new_M` of `Krepi.Proofs.PageTables.WalkLemmas`).

Every theorem here is proved. Mathlib is imported so that the gate counts the
heartbeats of each theorem.
-/

namespace Krepi.Proofs.PageTables.Allocation

open Krepi.SpecProperties.PageTables
open Krepi.Spec.PageTables
open Krepi.Proofs.PageTables
open Krepi.Proofs.Fdt (except_bind_ok)

public theorem placementFirstFit : PlacementFirstFit := by
  intro E X t owner pages alignment p _
  refine ⟨fun c hc => ?_, fun h => ?_, fun h => ?_⟩
  · obtain ⟨-, -, hpg, hal, -, ho, hs⟩ := choose_ok hc
    obtain ⟨i, e, h1, h2, h3, h4, h5⟩ := scan_ok hs
    exact ⟨ho, i, e, h1, fit_gives h2 hpg hal h3, h4,
      fun e' he' r' hr' => passed_gives hpg hal (h5 e' he') hr'⟩
  · rcases choose_error h with ⟨he, -⟩ | he | he | he | ⟨hpg, hal, hs⟩
    · cases he
    · cases he
    · cases he
    · cases he
    · rcases scan_error hs with ⟨he, -⟩ | ⟨-, ⟨-, -, h4⟩ | ⟨he, -⟩⟩
      · cases he
      · intro e he r hr
        rcases h4 e (mem_scanOrder.2 he) with h5 | h5
        · exact h5 (extent_holds_iff.1 hr).1
        · exact fit_none hpg hal h5 r hr
      · cases he
  · rcases choose_error h with ⟨he, -⟩ | he | he | he | ⟨hpg, hal, hs⟩
    · cases he
    · cases he
    · cases he
    · cases he
    · rcases scan_error hs with ⟨he, -⟩ | ⟨h1, ⟨he, -⟩ | ⟨-, h3⟩⟩
      · cases he
      · cases he
      · refine ⟨?_, fun e he r hr => passed_gives hpg hal (h1 e (mem_scanOrder.2 he)) hr⟩
        rcases h3 with h3 | ⟨e, he, hf, r, hr⟩
        · cases h3
        · exact ⟨e, mem_scanOrder.1 he, r, fit_gives hf hpg hal hr⟩

/-- The pages that `direct_map` of the boot maps are the pages of the usable
ranges of its boot memory map. -/
private theorem boot_pages {N : Nat} {B : Krepi.Spec.Fdt.MemoryPlan} {base : UInt64} {bits : UInt8}
    {s : Tables .upper N} {plan : Plan}
    (h : (Tables.new (Pool.zero N) : Tables .upper N).directMap B base bits = .ok (s, plan))
    {q : Nat} (hq : q % PAGE_SIZE = 0) :
    (∃ v l, (s.apply plan).M base v l ∧ l.pa.toNat = q) ↔ usablePage B q = true := by
  have hp : PoolOk N base bits := by
    unfold Tables.directMap at h
    obtain ⟨_, hc, -⟩ := except_bind_ok.1 h
    exact checkPool_ok.1 hc
  have hs : (Tables.new (Pool.zero N) : Tables .upper N).WellFormed base bits :=
    wf_zero hp (fun t i => by simp [Tables.new, Pool.zero, Pool.get, Table.zero]) rfl
  unfold usablePage
  simp only [Bool.and_eq_true, beq_iff_eq, hq, true_and, List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨v, l, hm, rfl⟩
    rcases directMap_M_usable hs h hm with hold | ⟨u, hu, h1, h2⟩
    · exact absurd hold new_M
    · exact ⟨u, hu, h1, h2⟩
  · rintro ⟨u, hu, h1, h2⟩
    obtain ⟨hlt, hm⟩ := directMap_M_of_usable hs h hu hq h1 h2
    refine ⟨_, _, hm, ?_⟩
    rw [UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (by simp only [VA_LIMIT] at hlt; omega)

public theorem bootOwnersMatchDirectMap : BootOwnersMatchDirectMap := by
  intro E X N B arena banks exclusions t base bits s plan hB hR ht hd
  refine ⟨Ownership.newOneOwner _ _ _ _ _ _ ht, fun q hq => ?_⟩
  have hu := Ownership.newFreeOrHeldUsable E X B arena banks exclusions t
    hB hR ht q hq
  rw [boot_pages hd hq, ← hu]
  constructor
  · intro h; exact ⟨_, h, rfl⟩
  · rintro ⟨o, ho, hfo⟩
    obtain ⟨x, hx, -, rfl⟩ := ownerOf_freeOrHeld ho hfo
    rw [ho]
    obtain ⟨-, -, -, -, -, -, -, rfl⟩ := new_ok ht
    obtain ⟨j, b, -, hx⟩ := mem_initialExtents.1 hx
    rw [(mem_bankExtents hx).2.1]
    rfl

end Krepi.Proofs.PageTables.Allocation
