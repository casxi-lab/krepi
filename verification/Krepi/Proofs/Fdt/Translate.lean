module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.Fdt.SpanLemmas

/-!
# Device tree: proofs about spans, cells and address translation

One theorem for each registered statement of `Krepi.SpecProperties.Fdt`
about spans, cells and address translation, whose type is exactly that
statement: the well-formedness of the spans, regions and address maps that
the entries of address translation give, and that a translation goes through
the one window that holds the request.

Every theorem here is proved; the lemmas about spans, widths and the
translation through windows that the proofs share are in
`Krepi.Proofs.Fdt.SpanLemmas`. Mathlib is imported so that the gate counts
the heartbeats of each theorem.
-/

namespace Krepi.Proofs.Fdt.Translate

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

public theorem spanNewWellFormed : SpanNewWellFormed := by
  intro start size s h
  obtain ⟨hlt, rfl⟩ := span_new_ok.1 h
  exact hlt

public theorem regNewWellFormed : RegNewWellFormed := by
  intro bytes ac sc r h
  unfold Reg.new at h
  simp only at h
  split at h
  · exact absurd h (except_throw_bind_ne _ _ _)
  · split at h
    · exact absurd h (except_throw_bind_ne _ _ _)
    · rename_i h2
      obtain ⟨entries, he, h⟩ := except_bind_ok.1 h
      rw [except_pure_ok] at h
      subst h
      obtain ⟨hl, hm⟩ := except_mapM_ok he
      refine ⟨fun hnil => ?_, fun s hs => ?_⟩
      · have hnil' : entries = [] := hnil
        rw [chunks_length, hnil', List.length_nil] at hl
        simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, not_or,
          Decidable.not_not] at h2
        have := Nat.div_add_mod bytes.size ((ac.toNat + sc.toNat) * 4)
        rw [← hl] at this
        omega
      · obtain ⟨e, _, he⟩ := hm s hs
        exact regEntry_withinWidth he

public theorem addressMapNewWellFormed : AddressMapNewWellFormed := by
  intro bytes cc pc sc m h
  unfold AddressMap.new at h
  simp only at h
  split at h
  · exact absurd h (except_throw_bind_ne _ _ _)
  · rename_i hcells
    simp at hcells
    obtain ⟨⟨hc, hp⟩, hs⟩ := hcells
    have key : ∀ wo : Option (List Window),
        (∀ ws, wo = some ws → ∀ w ∈ ws, w.WellFormed cc pc) →
        AddressMap.WellFormed ⟨wo, cc, pc, sc⟩ := fun wo hw =>
      ⟨Decidable.or_iff_not_imp_left.2 hc, Decidable.or_iff_not_imp_left.2 hp, hs, hw⟩
    split at h
    · rw [except_bind_ok] at h
      obtain ⟨_, h1, h⟩ := h
      rw [except_pure_ok] at h1 h
      subst h h1
      exact key none (fun _ h => by cases h)
    · split at h
      · rw [except_bind_ok] at h
        obtain ⟨_, h1, h⟩ := h
        rw [except_pure_ok] at h1 h
        subst h h1
        exact key _ (fun ws h w hw => by cases h; cases hw)
      · split at h
        · exact absurd h (except_throw_bind_ne _ _ _)
        · obtain ⟨ws, hws, h⟩ := except_bind_ok.1 h
          obtain ⟨_, h1, h⟩ := except_bind_ok.1 h
          rw [except_pure_ok] at h1 h
          subst h h1
          refine key _ (fun ws' h w hw => ?_)
          cases h
          obtain ⟨_, _, he⟩ := (except_mapM_ok hws).2 w hw
          exact window_wellFormed he

public theorem nodeRegWellFormed : NodeRegWellFormed := by
  intro n parent cells r hp hc h
  unfold Node.reg at h
  rw [hp] at h
  simp only at h
  split at h
  · obtain ⟨ac, hac, h⟩ := except_bind_ok.1 h
    obtain ⟨_, _, h⟩ := except_bind_ok.1 h
    rw [hc] at hac
    cases hac
    exact regNewWellFormed _ _ _ _ h
  · exact absurd h (except_throw_ne _ _)

/-- The map of a property of a node, read in the cells of the node and of its
parent, is well-formed. -/
theorem addressMap_wellFormed {n : Node} {name : String} {m : AddressMap}
    (h : n.addressMap name = .ok m) : m.WellFormed := by
  unfold Node.addressMap at h
  split at h
  · obtain ⟨_, _, h⟩ := except_bind_ok.1 h
    obtain ⟨_, _, h⟩ := except_bind_ok.1 h
    obtain ⟨_, _, h⟩ := except_bind_ok.1 h
    exact addressMapNewWellFormed _ _ _ _ _ h
  · exact absurd h (except_throw_ne _ _)

public theorem nodeRangesWellFormed : NodeRangesWellFormed :=
  fun _ _ h => addressMap_wellFormed h

public theorem nodeDmaRangesWellFormed : NodeDmaRangesWellFormed :=
  fun _ _ h => addressMap_wellFormed h

public theorem toParentWellFormed : ToParentWellFormed :=
  fun _ _ _ hm h => translate_wellFormed (reverse := false) hm h

public theorem toChildWellFormed : ToChildWellFormed :=
  fun _ _ _ hm h => translate_wellFormed (reverse := true) hm h

public theorem translateRegWellFormed : TranslateRegWellFormed := by
  intro n s r h
  unfold Node.translateReg at h
  split at h
  · obtain ⟨t, ht, h⟩ := except_bind_ok.1 h
    obtain ⟨_, he, h⟩ := except_bind_ok.1 h
    rw [except_pure_ok] at h
    subst h
    exact ⟨endAddr_ok he, climbRanges_size ht⟩
  · exact absurd h (except_throw_ne _ _)

public theorem translationThroughOneWindow : TranslationThroughOneWindow := by
  intro m s reverse hm hne hw
  refine ⟨fun hnone r h => ?_, fun hnil => ⟨fun r h => ?_, fun hw2 => ?_⟩,
    fun w₀ ws₀ hws => ?_⟩
  · obtain ⟨-, -, hcase⟩ := translate_ok h
    rcases hcase with ⟨h1, -⟩ | ⟨_, _, h1, -⟩ <;> rw [hnone] at h1 <;> cases h1
  · obtain ⟨-, -, hcase⟩ := translate_ok h
    rcases hcase with ⟨-, rfl, -⟩ | ⟨_, _, h1, -⟩
    · rfl
    · rw [hnil] at h1
      cases h1
  · exact translate_identity hne hw hnil hw2
  · dsimp only
    refine ⟨⟨fun ⟨r, h⟩ => ?_, fun ⟨w, hf, hh⟩ => ?_⟩, fun r w h hf => ?_⟩
    · obtain ⟨-, -, hcase⟩ := translate_ok h
      rcases hcase with ⟨h1, -⟩ | ⟨v₀, vs₀, h1, ht⟩
      · rw [hws] at h1
        cases h1
      · rw [hws] at h1
        cases h1
        obtain ⟨w, hf, hh, -⟩ := (throughWindows_ok hne ht).1 rfl
        exact ⟨w, hf, hh⟩
    · rw [translate_windows hne hw hws]
      refine throughWindows_single hne (fun v hv => ?_) hf hh
      obtain ⟨hsz, hvw⟩ := window_target (hm.2.2.2 _ hws v hv) reverse
      exact ⟨hsz, hvw.1⟩
    · rw [translate_windows hne hw hws] at h
      obtain ⟨w', hf', -, hrs, hrst⟩ := (throughWindows_ok hne h).1 rfl
      rw [hf] at hf'
      cases hf'
      exact ⟨hrs, hrst⟩

end Krepi.Proofs.Fdt.Translate
