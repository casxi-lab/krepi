module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.PlanLemmas
import Krepi.Proofs.Fdt.Pi5Lemmas

/-!
# Device tree: proofs about the selection of the Pi 5 boot memory

One theorem for each registered statement of `Krepi.SpecProperties.Fdt`
about the selection of the Pi 5 boot memory, whose type is exactly that
statement: that `Pi5BootMemory::find_available` gives a well-formed span,
available and of the lowest aligned start in the first RAM range that has
one.

Every theorem here is proved, from the lemmas about the search of
`Krepi.Proofs.Fdt.Pi5Lemmas`: in each RAM range, every start below a
candidate that touches an exclusion and up to the end of the furthest such
exclusion touches it too, and the next candidate is that end aligned up, so
the search skips no start that fits. Mathlib is imported so that the gate
counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.Fdt.Pi5

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

public theorem findAvailableWellFormed : FindAvailableWellFormed := by
  intro m size alignment minimum limit s h
  obtain ⟨hsz, hal, h⟩ := findAvailable_ok h
  obtain ⟨i, r, c0, -, hc0, hs, -⟩ := searchRanges_some m.ram s h
  have hpos : 0 < size.toNat := by
    have : size.toNat ≠ 0 := fun h0 => hsz (UInt64.toNat_inj.1 (h0.trans rfl))
    omega
  obtain ⟨t, rfl, -, hg, -⟩ := searchRange_some hpos hal _ _ _ hs (alignUp_ok hal hc0).2.1
  obtain ⟨-, hlt, -, -⟩ := hg
  obtain ⟨-, -, hce⟩ := cand_toNat hlt
  exact ⟨UInt64.ofNat_toNat, by rw [UInt64.ofNat_toNat]; exact hsz,
    by unfold Span.Valid; rw [hce]; exact hlt⟩

public theorem findAvailableLowest : FindAvailableLowest := by
  intro m size alignment minimum limit
  refine ⟨fun s h => ?_, fun h => ?_⟩
  · obtain ⟨hsz, hal, h⟩ := findAvailable_ok h
    obtain ⟨i, r, c0, hi, hc0, hs, hb⟩ := searchRanges_some m.ram s h
    have hpos : 0 < size.toNat := by
      have : size.toNat ≠ 0 := fun h0 => hsz (UInt64.toNat_inj.1 (h0.trans rfl))
      omega
    obtain ⟨t, rfl, hct, hg, hlow⟩ :=
      searchRange_some hpos hal _ _ _ hs (alignUp_ok hal hc0).2.1
    have hfit := fits_of_accepts hal hc0 hct hg
    obtain ⟨-, hlt, -, hx⟩ := hg
    obtain ⟨hcs, -, hce⟩ := cand_toNat hlt
    refine ⟨?_, i, r, hi, hfit, ?_, ?_⟩
    · unfold Pi5BootMemory.isAvailable
      rw [ite_eq_right (by rw [UInt64.ofNat_toNat]; exact hsz),
        ite_eq_right (by unfold Span.Valid; rw [hce]; omega)]
      have hin : inOneRange m.ram ⟨UInt64.ofNat t, UInt64.ofNat size.toNat⟩ = true :=
        List.any_eq_true.2 ⟨r, List.mem_of_getElem? hi, hfit.2.2.2.2.2.1⟩
      have hex :
          m.exclusions.any (·.touches ⟨UInt64.ofNat t, UInt64.ofNat size.toNat⟩) = false :=
        List.any_eq_false.2 fun x hxm => by rw [hx x hxm]; decide
      rw [hin, hex]
      rfl
    · intro r' hr' s' hf
      obtain ⟨c1, hc1, hn⟩ := hb r' hr'
      obtain ⟨-, h1, h2⟩ := accepts_of_fits hal hc1 hf
      exact searchRange_none hpos hal _ _ hn _ h1 h2
    · intro s' hf
      obtain ⟨-, h1, h2⟩ := accepts_of_fits hal hc0 hf
      rw [hcs]
      by_cases hts : t ≤ s'.start.toNat
      · exact hts
      · exact absurd h2 (hlow _ h1 (by omega))
  · obtain ⟨hsz, hal, h⟩ := findAvailable_ok h
    have hpos : 0 < size.toNat := by
      have : size.toNat ≠ 0 := fun h0 => hsz (UInt64.toNat_inj.1 (h0.trans rfl))
      omega
    intro r hr s hf
    obtain ⟨c1, hc1, hn⟩ := searchRanges_none m.ram h r hr
    obtain ⟨-, h1, h2⟩ := accepts_of_fits hal hc1 hf
    exact searchRange_none hpos hal _ _ hn _ h1 h2

end Krepi.Proofs.Fdt.Pi5
