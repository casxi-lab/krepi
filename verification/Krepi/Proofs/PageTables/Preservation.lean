module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.OwnerLemmas
import Krepi.Proofs.PageTables.WriteLemmas
import Krepi.Proofs.PageTables.PreserveLemmas

/-!
# Page tables: proofs about the preservation of the invariants of the page ownership table

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about the preservation of the invariants
of the page ownership table, whose type is exactly that statement: that each
write entry of the page ownership table preserves each of its functional
invariants.

All twenty-five theorems are proved. `assign` and `reserve` write with
`take`, of a range on pages (a choice of `choose`, which `assign` takes as
its requirement): each invariant follows from the lemma of `take` in
`Krepi.Proofs.PageTables.PreserveLemmas`. `publish` relabels the extent
of the packet, reserved, as published with the same generation
(`publish_spec` and `publish_extents` of
`Krepi.Proofs.PageTables.WriteLemmas`): the pages that the extents hold
(the private `publish_holds_iff`, then `oneOwner_of_holds_iff` and
`freeOrHeldUsable_of_holds_iff`), the generation of every page and the free
extents stay as they are.

`cancel` and `release` find the extent of the value (`cancel_ok`,
`release_ok` and `findHeld_ok` of `Krepi.Proofs.PageTables.WriteLemmas`),
free it and merge it with its free neighbours (`mergeFreed`): each
invariant follows from the lemma of `mergeFreed` in
`Krepi.Proofs.PageTables.PreserveLemmas`.

Mathlib is imported so that the gate counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.PageTables.Preservation

open Krepi.SpecProperties.PageTables
open Krepi.Spec.PageTables
open Krepi.Proofs.PageTables

/-- `publish` keeps the pages that the extents hold: it gives the pages of an
extent of the table another holder. -/
private theorem publish_holds_iff {E X : Nat} {t t' : Ownership E X} {o : UInt64}
    {x : Initialized} {a : Allocation} (hwf : t.WellFormed) (h : t.publish o x = .ok (t', a))
    (q : Nat) :
    (∃ y ∈ t'.extents, y.range.holdsPage q = true) ↔
      ∃ y ∈ t.extents, y.range.holdsPage q = true := by
  obtain ⟨-, -, -, -, -, -, ⟨e, he, her, -⟩, hown, -⟩ := publish_spec hwf h
  exact holds_iff_of_ownerOf rfl (fun hq => ⟨e, he, by rw [her]; exact hq⟩) (hown q)

public theorem assignOneOwner : AssignOneOwner := by
  rintro E X t c z t' a hinv ⟨_, _, _, _, hch⟩ h
  exact take_oneOwner hinv (choose_onPages hch) (assign_ok h).2

public theorem reserveOneOwner : ReserveOneOwner := by
  intro E X t owner pages alignment p t' r hinv h
  obtain ⟨c, a, hch, ht, -⟩ := reserve_ok h
  exact take_oneOwner hinv (choose_onPages hch) ht

public theorem publishOneOwner : PublishOneOwner := by
  rintro E X t o x t' a ⟨hwf, hone, -⟩ h
  obtain ⟨-, hwf', -, hb, hx, -⟩ := publish_spec hwf h
  exact oneOwner_of_holds_iff hwf.2.2.2.2.2.2.1 hwf'.2.2.2.2.2.2.1 hb hx
    (fun q _ => publish_holds_iff hwf h q) hone

public theorem cancelOneOwner : CancelOneOwner := by
  intro E X t o r t' hinv h
  obtain ⟨-, before, e, after, hf, ht'⟩ := cancel_ok h
  exact free_oneOwner hinv (findHeld_ok hf).2.2.1 ht'

public theorem releaseOneOwner : ReleaseOneOwner := by
  intro E X t o x t' hinv h
  obtain ⟨before, e, after, hf, ht'⟩ := release_ok h
  exact free_oneOwner hinv (findHeld_ok hf).2.2.1 ht'

public theorem assignHolderRanges : AssignHolderRanges := by
  rintro E X t c z t' a hinv ⟨_, _, _, _, hch⟩ h
  exact take_holderRanges hinv (choose_onPages hch) (assign_ok h).2

public theorem reserveHolderRanges : ReserveHolderRanges := by
  intro E X t owner pages alignment p t' r hinv h
  obtain ⟨c, a, hch, ht, -⟩ := reserve_ok h
  exact take_holderRanges hinv (choose_onPages hch) ht

public theorem publishHolderRanges : PublishHolderRanges := by
  rintro E X t o x t' a ⟨hwf, -, hhold, -, -⟩ h
  obtain ⟨-, -, -, -, -, -, ⟨e, he, her, heh⟩, hown, -⟩ := publish_spec hwf h
  -- every page keeps the generation of its holder
  have key : ∀ q n, (∃ o' s', t'.ownerOf q = some (.held o' n s')) ↔
      ∃ o' s', t.ownerOf q = some (.held o' n s') := by
    intro q n
    rw [hown q]
    split
    · rename_i hq
      rw [ownerOf_of_mem hwf.2.2.2.2.2.2.1 he (by rw [her]; exact hq), heh]
      simp [Holding.owner]
    · exact Iff.rfl
  intro y hy o' n s hyh q hq
  rw [key]
  rcases publish_extents h y hy with hy' | ⟨hyr, hyh'⟩
  · exact hhold y hy' o' n s hyh q hq
  · rw [hyh'] at hyh
    cases hyh
    rw [hyr, ← her]
    exact hhold e he _ _ _ heh q hq

public theorem cancelHolderRanges : CancelHolderRanges := by
  intro E X t o r t' hinv h
  obtain ⟨-, before, e, after, hf, ht'⟩ := cancel_ok h
  exact free_holderRanges hinv (findHeld_ok hf).2.2.1 ht'

public theorem releaseHolderRanges : ReleaseHolderRanges := by
  intro E X t o x t' hinv h
  obtain ⟨before, e, after, hf, ht'⟩ := release_ok h
  exact free_holderRanges hinv (findHeld_ok hf).2.2.1 ht'

public theorem assignGenerationsBelowCounter : AssignGenerationsBelowCounter := by
  rintro E X t c z t' a hinv ⟨_, _, _, _, hch⟩ h
  exact take_generationsBelowCounter hinv (choose_onPages hch) (assign_ok h).2

public theorem reserveGenerationsBelowCounter : ReserveGenerationsBelowCounter := by
  intro E X t owner pages alignment p t' r hinv h
  obtain ⟨c, a, hch, ht, -⟩ := reserve_ok h
  exact take_generationsBelowCounter hinv (choose_onPages hch) ht

public theorem publishGenerationsBelowCounter : PublishGenerationsBelowCounter := by
  rintro E X t o x t' a ⟨hwf, -, -, hgen, -⟩ h
  obtain ⟨-, -, -, -, -, hc, ⟨e, he, her, heh⟩, hown, -⟩ := publish_spec hwf h
  intro q o' n s hq
  rw [hc]
  rw [hown q] at hq
  split at hq
  · rename_i hrq
    simp only [Option.some.injEq, Owner.held.injEq] at hq
    obtain ⟨rfl, rfl, -⟩ := hq
    exact hgen q _ _ _ ((ownerOf_of_mem hwf.2.2.2.2.2.2.1 he (by rw [her]; exact hrq)).trans
      (by rw [heh]; rfl))
  · exact hgen q o' n s hq

public theorem cancelGenerationsBelowCounter : CancelGenerationsBelowCounter := by
  intro E X t o r t' hinv h
  obtain ⟨-, before, e, after, hf, ht'⟩ := cancel_ok h
  exact free_generationsBelowCounter hinv (findHeld_ok hf).2.2.1 ht'

public theorem releaseGenerationsBelowCounter : ReleaseGenerationsBelowCounter := by
  intro E X t o x t' hinv h
  obtain ⟨before, e, after, hf, ht'⟩ := release_ok h
  exact free_generationsBelowCounter hinv (findHeld_ok hf).2.2.1 ht'

public theorem assignFreeExtentsMaximal : AssignFreeExtentsMaximal := by
  rintro E X t c z t' a hinv - h
  exact take_freeExtentsMaximal hinv (assign_ok h).2

public theorem reserveFreeExtentsMaximal : ReserveFreeExtentsMaximal := by
  intro E X t owner pages alignment p t' r hinv h
  obtain ⟨c, a, -, ht, -⟩ := reserve_ok h
  exact take_freeExtentsMaximal hinv ht

public theorem publishFreeExtentsMaximal : PublishFreeExtentsMaximal := by
  rintro E X t o x t' a ⟨-, -, -, -, hmax⟩ h
  -- every free extent after the write is one of the table
  have hfree : ∀ y ∈ t'.extents, y.holding = .free → y ∈ t.extents := fun y hy hf => by
    rcases publish_extents h y hy with hy' | ⟨-, hyh⟩
    · exact hy'
    · rw [hyh] at hf
      cases hf
  intro y hy z hz hyf hzf
  exact hmax y (hfree y hy hyf) z (hfree z hz hzf) hyf hzf

public theorem cancelFreeExtentsMaximal : CancelFreeExtentsMaximal := by
  intro E X t o r t' hinv h
  obtain ⟨-, before, e, after, hf, ht'⟩ := cancel_ok h
  exact free_freeExtentsMaximal hinv (findHeld_ok hf).2.2.1 ht'

public theorem releaseFreeExtentsMaximal : ReleaseFreeExtentsMaximal := by
  intro E X t o x t' hinv h
  obtain ⟨before, e, after, hf, ht'⟩ := release_ok h
  exact free_freeExtentsMaximal hinv (findHeld_ok hf).2.2.1 ht'

public theorem assignFreeOrHeldUsable : AssignFreeOrHeldUsable := by
  rintro E X B t c z t' a hinv hu ⟨_, _, _, _, hch⟩ h
  exact take_freeOrHeldUsable hinv (choose_onPages hch) (assign_ok h).2 hu

public theorem reserveFreeOrHeldUsable : ReserveFreeOrHeldUsable := by
  intro E X B t owner pages alignment p t' r hinv hu h
  obtain ⟨c, a, hch, ht, -⟩ := reserve_ok h
  exact take_freeOrHeldUsable hinv (choose_onPages hch) ht hu

public theorem publishFreeOrHeldUsable : PublishFreeOrHeldUsable := by
  rintro E X B t o x t' a ⟨hwf, -⟩ hu h
  exact freeOrHeldUsable_of_holds_iff (fun q _ => publish_holds_iff hwf h q) hu

public theorem cancelFreeOrHeldUsable : CancelFreeOrHeldUsable := by
  intro E X B t o r t' hinv hu h
  obtain ⟨-, before, e, after, hf, ht'⟩ := cancel_ok h
  exact free_freeOrHeldUsable hinv (findHeld_ok hf).2.2.1 ht' hu

public theorem releaseFreeOrHeldUsable : ReleaseFreeOrHeldUsable := by
  intro E X B t o x t' hinv hu h
  obtain ⟨before, e, after, hf, ht'⟩ := release_ok h
  exact free_freeOrHeldUsable hinv (findHeld_ok hf).2.2.1 ht' hu

end Krepi.Proofs.PageTables.Preservation
