module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.ExceptLemmas

/-!
# Device tree: lemmas about spans, widths and address maps

Lemmas about the spans of the specification of the `fdt` component, the
widths of addresses in cells and the translation through an address map,
for the proofs of the statements about them and of the statements that read
spans, regions and maps:

- the checks of spans against their propositions: `holds_iff`,
  `overlaps_iff`, `withinWidth_iff`, `nonempty_iff`, `onPages_iff`, and
  `allPairs_iff` for the pairwise checks of tables;
- the steps of the entries that build spans: `checkedAdd_ok`, `span_new_ok`,
  `checkWidth_ok`, `endAddr_ok`, `chunks_length`, `regEntry_withinWidth` and
  `window_wellFormed`;
- the translation through the windows of a map: `throughWindows_ok` (a
  success went through the one window that touches the request, which holds
  it), `throughWindows_single` and `throughWindows_untouched` (the converse),
  `window_target` and `target_withinWidth` (the result lies within the width
  of the target side);
- the translation of a map: `translate_ok` (the steps of a success),
  `translate_identity` and `translate_windows` (the result of a nonempty
  request within its width), `translate_size`, `translate_wellFormed` and
  `climbRanges_size`.
-/

namespace Krepi.Proofs.Fdt

open Krepi.Spec.Fdt

/-! ## Checks of spans -/

/-- `Span.holds` as inequalities of the exact ends. -/
public theorem holds_iff {outer inner : Span} :
    outer.holds inner = true ↔
      outer.start.toNat ≤ inner.start.toNat ∧ inner.endNat ≤ outer.endNat := by
  simp only [Span.holds, Bool.and_eq_true, decide_eq_true_eq]

/-- `Span.overlaps` as inequalities of the exact ends. -/
public theorem overlaps_iff {a b : Span} :
    a.overlaps b = true ↔ a.start.toNat < b.endNat ∧ b.start.toNat < a.endNat := by
  simp only [Span.overlaps, Bool.and_eq_true, decide_eq_true_eq]

/-- `Span.withinWidth` decides `Span.WithinWidth`. -/
public theorem withinWidth_iff {s : Span} {cells : UInt32} :
    s.withinWidth cells = true ↔ s.WithinWidth cells := by
  unfold Span.withinWidth Span.WithinWidth
  by_cases hc : cells = 1 <;> simp [hc]

/-- `Span.nonempty` decides `Span.Nonempty`. -/
public theorem nonempty_iff {s : Span} : s.nonempty = true ↔ s.Nonempty := by
  unfold Span.nonempty Span.Nonempty
  simp

/-- `Span.onPages` decides `Span.OnPages`. -/
public theorem onPages_iff {s : Span} : s.onPages = true ↔ s.OnPages := by
  unfold Span.onPages Span.OnPages
  simp

/-- `allPairs` decides `List.Pairwise`. -/
public theorem allPairs_iff {α : Type} {r : α → α → Bool} :
    ∀ {l : List α}, allPairs r l = true ↔ l.Pairwise (fun a b => r a b = true)
  | [] => by simp [allPairs]
  | a :: rest => by
    have ih := allPairs_iff (r := r) (l := rest)
    simp [allPairs, ih, List.pairwise_cons]

/-- A size that is not 0 has a natural value that is not 0. -/
public theorem size_toNat_ne_zero {s : Span} (h : s.size ≠ 0) : s.size.toNat ≠ 0 := by
  intro h0
  exact h (UInt64.toNat_inj.1 (h0.trans rfl))

/-- A span that holds a nonempty span shares an address with it. -/
public theorem overlaps_of_holds {outer r : Span} (hr : r.size ≠ 0)
    (h : outer.holds r = true) : outer.overlaps r = true := by
  have := size_toNat_ne_zero hr
  rw [holds_iff] at h
  rw [overlaps_iff]
  unfold Span.endNat at h ⊢
  omega

/-! ## Steps of the entries -/

/-- `checkedAdd` succeeds with the sum exactly when it fits in 64 bits. -/
public theorem checkedAdd_ok {a b c : Nat} :
    checkedAdd a b = .ok c ↔ a + b < 2 ^ 64 ∧ a + b = c := by
  unfold checkedAdd
  split
  · simp_all
  · simp only [reduceCtorEq, false_iff, not_and]
    omega

/-- `Span::new` succeeds with the span of its arguments exactly when its end
fits in 64 bits. -/
public theorem span_new_ok {start size : UInt64} {s : Span} :
    Span.new start size = .ok s ↔ start.toNat + size.toNat < 2 ^ 64 ∧ ⟨start, size⟩ = s := by
  unfold Span.new
  split
  · simp_all
  · simp only [reduceCtorEq, false_iff, not_and]
    omega

/-- `checkWidth` succeeds exactly on a span within the width. -/
public theorem checkWidth_ok {s : Span} {cells : UInt32} {u : Unit} :
    checkWidth s cells = .ok u ↔ s.WithinWidth cells := by
  unfold checkWidth Span.WithinWidth
  by_cases hv : s.Valid <;> by_cases hc : cells = 1 <;> simp [hv, hc]

/-- `Span::end` succeeds only on a span of the contract. -/
public theorem endAddr_ok {s : Span} {e : UInt64} : s.endAddr = .ok e → s.Valid := by
  unfold Span.endAddr
  split <;> simp_all

/-- `chunks` gives as many pieces as it is asked for. -/
public theorem chunks_length (bytes : ByteArray) (stride : Nat) :
    ∀ count from_, (chunks bytes stride count from_).length = count
  | 0, _ => rfl
  | c + 1, f => by simp [chunks, chunks_length bytes stride c]

/-- An entry of a `reg` lies within the width of its address cells. -/
public theorem regEntry_withinWidth {ac sc : UInt32} {e : ByteArray} {s : Span}
    (h : regEntry ac sc e = .ok s) : s.WithinWidth ac := by
  unfold regEntry at h
  obtain ⟨_, _, h⟩ := except_bind_ok.1 h
  obtain ⟨_, _, h⟩ := except_bind_ok.1 h
  obtain ⟨span, _, h⟩ := except_bind_ok.1 h
  obtain ⟨_, hw, h⟩ := except_bind_ok.1 h
  rw [except_pure_ok] at h
  subst h
  exact checkWidth_ok.1 hw

/-- A window of a map is well-formed in the cells of its two sides. -/
public theorem window_wellFormed {cc pc sc : UInt32} {e : ByteArray} {w : Window}
    (h : window cc pc sc e = .ok w) : w.WellFormed cc pc := by
  unfold window at h
  simp only at h
  obtain ⟨child, _, h⟩ := except_bind_ok.1 h
  obtain ⟨parent, _, h⟩ := except_bind_ok.1 h
  obtain ⟨size, _, h⟩ := except_bind_ok.1 h
  split at h
  · exact absurd h (except_throw_bind_ne _ _ _)
  · rename_i hsize
    obtain ⟨cs, hcs, h⟩ := except_bind_ok.1 h
    obtain ⟨ps, hps, h⟩ := except_bind_ok.1 h
    obtain ⟨_, hcw, h⟩ := except_bind_ok.1 h
    obtain ⟨_, hpw, h⟩ := except_bind_ok.1 h
    rw [except_pure_ok] at h
    subst h
    obtain ⟨_, rfl⟩ := span_new_ok.1 hcs
    obtain ⟨_, rfl⟩ := span_new_ok.1 hps
    exact ⟨hsize, rfl, checkWidth_ok.1 hcw, checkWidth_ok.1 hpw⟩

/-! ## Translation through windows -/

/-- A translation through windows that succeeds went through the one window
that touches the request, which holds it, and gave the span of the request's
size at the request's offset in that window; after a window that held it,
no later window touches it. -/
public theorem throughWindows_ok {request : Span} (hne : request.size ≠ 0)
    {src tgt : Window → Span} :
    ∀ {ws : List Window} {found : Option Span} {r : Span},
    throughWindows request src tgt ws found = .ok r →
    (found = none → ∃ w, ws.filter (fun w => (src w).overlaps request) = [w] ∧
        (src w).holds request = true ∧ r.size = request.size ∧
        r.start.toNat = (tgt w).start.toNat + (request.start.toNat - (src w).start.toNat)) ∧
    (∀ x, found = some x → ws.filter (fun w => (src w).overlaps request) = [] ∧ r = x)
  | [], found, r, h => by
    cases found with
    | none => simp [throughWindows] at h
    | some x =>
      simp only [throughWindows, Except.ok.injEq] at h
      subst h
      simp
  | w :: ws, found, r, h => by
    simp only [throughWindows] at h
    split at h
    · rename_i hholds
      cases found with
      | some x => exact absurd h (except_throw_bind_ne _ _ _)
      | none =>
        obtain ⟨start, hstart, h⟩ := except_bind_ok.1 h
        obtain ⟨s, hs, h⟩ := except_bind_ok.1 h
        obtain ⟨hnil, rfl⟩ := (throughWindows_ok hne h).2 s rfl
        obtain ⟨hlt, rfl⟩ := checkedAdd_ok.1 hstart
        obtain ⟨hlt', rfl⟩ := span_new_ok.1 hs
        refine ⟨fun _ => ⟨w, ?_, hholds, rfl, ?_⟩, fun _ h => by cases h⟩
        · simp only [List.filter_cons, overlaps_of_holds hne hholds, ↓reduceIte, hnil]
        · exact UInt64.toNat_ofNat_of_lt' hlt
    · split at h
      · simp at h
      · rename_i hholds hover
        have ih := throughWindows_ok hne h
        simp only [List.filter_cons, hover, Bool.false_eq_true, ↓reduceIte]
        exact ih

/-- After a window that held the request, windows that do not touch it keep
the result. -/
public theorem throughWindows_untouched {request : Span} (hne : request.size ≠ 0)
    {src tgt : Window → Span} :
    ∀ {ws : List Window} (x : Span), ws.filter (fun w => (src w).overlaps request) = [] →
      throughWindows request src tgt ws (some x) = .ok x
  | [], x, _ => by simp [throughWindows]
  | w :: ws, x, h => by
    rw [List.filter_cons] at h
    split at h
    · cases h
    · rename_i hov
      have hh : ¬ (src w).holds request = true := fun hh => hov (overlaps_of_holds hne hh)
      rw [throughWindows, ite_eq_right hh, ite_eq_right hov]
      exact throughWindows_untouched hne x h

/-- A translation through windows whose target sides have the size of their
source sides and lie within 64 bits succeeds when one window, and no other,
touches the request and that window holds it. -/
public theorem throughWindows_single {request : Span} (hne : request.size ≠ 0)
    {src tgt : Window → Span} :
    ∀ {ws : List Window} {w : Window},
      (∀ v ∈ ws, (tgt v).size = (src v).size ∧ (tgt v).Valid) →
      ws.filter (fun v => (src v).overlaps request) = [w] → (src w).holds request = true →
      ∃ r, throughWindows request src tgt ws none = .ok r
  | [], w, _, h, _ => by simp at h
  | v :: ws, w, hwf, h, hh => by
    rw [List.filter_cons] at h
    split at h
    · simp only [List.cons.injEq] at h
      obtain ⟨rfl, hnil⟩ := h
      obtain ⟨hsz, hval⟩ := hwf v List.mem_cons_self
      have hh' := holds_iff.1 hh
      unfold Span.Valid Span.endNat at hval
      unfold Span.endNat at hh'
      have := size_toNat_ne_zero hne
      have hsz' : (tgt v).size.toNat = (src v).size.toNat := by rw [hsz]
      have hlt : (tgt v).start.toNat + (request.start.toNat - (src v).start.toNat) < 2 ^ 64 := by
        omega
      have hlt' : (UInt64.ofNat ((tgt v).start.toNat +
          (request.start.toNat - (src v).start.toNat))).toNat + request.size.toNat < 2 ^ 64 := by
        rw [UInt64.toNat_ofNat_of_lt' hlt]
        omega
      rw [throughWindows, ite_eq_left hh]
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, checkedAdd, hlt, except_ok_bind,
        Span.new, hlt']
      exact ⟨_, throughWindows_untouched hne _ hnil⟩
    · rename_i hov
      have hh2 : ¬ (src v).holds request = true := fun hh => hov (overlaps_of_holds hne hh)
      rw [throughWindows, ite_eq_right hh2, ite_eq_right hov]
      exact throughWindows_single hne (fun u hu => hwf u (List.mem_cons_of_mem _ hu)) h hh

/-- The span that a window gives for a nonempty request that its source side
holds lies within the width of its target side, when the target side has the
size of the source side and lies within that width. -/
public theorem target_withinWidth {src tgt req r : Span} {cells : UInt32}
    (hne : req.size ≠ 0) (hsz : tgt.size = src.size) (hw : tgt.WithinWidth cells)
    (hh : src.holds req = true) (hrs : r.size = req.size)
    (hrst : r.start.toNat = tgt.start.toNat + (req.start.toNat - src.start.toNat)) :
    r.WithinWidth cells := by
  have := size_toNat_ne_zero hne
  have hsz' : tgt.size.toNat = src.size.toNat := by rw [hsz]
  have hrs' : r.size.toNat = req.size.toNat := by rw [hrs]
  rw [holds_iff] at hh
  obtain ⟨hv, h1⟩ := hw
  unfold Span.Valid Span.endNat at hv
  unfold Span.endNat at h1 hh
  unfold Span.WithinWidth Span.Valid Span.endNat
  refine ⟨by omega, fun hc => ?_⟩
  have := h1 hc
  omega

/-- The target side of a well-formed window has the size of its source side
and lies within the width of its cells, in both directions. -/
public theorem window_target {w : Window} {cc pc : UInt32} (hw : w.WellFormed cc pc)
    (reverse : Bool) :
    (w.target reverse).size = (w.source reverse).size ∧
      (w.target reverse).WithinWidth (if reverse then cc else pc) := by
  obtain ⟨-, hsz, hc, hp⟩ := hw
  cases reverse
  · exact ⟨hsz.symm, hp⟩
  · exact ⟨hsz, hc⟩

/-! ## Translation of a map -/

/-- The steps of a translation that succeeds: the request is nonempty and
within the width of its side, and either the map is empty and gives the
request, within the width of the other side, or the map has windows and the
translation through them gives the result. -/
public theorem translate_ok {m : AddressMap} {s r : Span} {reverse : Bool}
    (h : m.translate s reverse = .ok r) :
    s.size ≠ 0 ∧ s.WithinWidth (if reverse then m.parentCells else m.childCells) ∧
      ((m.windows = some [] ∧ r = s ∧
          s.WithinWidth (if reverse then m.childCells else m.parentCells)) ∨
        ∃ w₀ ws₀, m.windows = some (w₀ :: ws₀) ∧
          throughWindows s (Window.source · reverse) (Window.target · reverse) (w₀ :: ws₀) none =
            .ok r) := by
  unfold AddressMap.translate at h
  simp only at h
  split at h
  · exact absurd h (except_throw_bind_ne _ _ _)
  · rename_i hsize
    refine ⟨hsize, ?_⟩
    cases reverse
    all_goals
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨_, hw, h⟩ := except_bind_ok.1 h
      refine ⟨checkWidth_ok.1 hw, ?_⟩
      split at h
      · exact absurd h (except_throw_ne _ _)
      · obtain ⟨_, hw', h⟩ := except_bind_ok.1 h
        rw [except_pure_ok] at h
        exact Or.inl ⟨‹_›, h.symm, checkWidth_ok.1 hw'⟩
      · rename_i ws hne hws
        cases ws with
        | nil => exact absurd rfl hne
        | cons w₀ ws₀ => exact Or.inr ⟨w₀, ws₀, hws, h⟩

/-- An empty map gives a nonempty request within the widths of both sides. -/
public theorem translate_identity {m : AddressMap} {s : Span} {reverse : Bool}
    (hne : s.size ≠ 0) (hw : s.WithinWidth (if reverse then m.parentCells else m.childCells))
    (hnil : m.windows = some [])
    (hw2 : s.WithinWidth (if reverse then m.childCells else m.parentCells)) :
    m.translate s reverse = .ok s := by
  have hc := (checkWidth_ok (u := ())).2 hw
  have hc2 := (checkWidth_ok (u := ())).2 hw2
  unfold AddressMap.translate
  cases reverse
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hc hc2 ⊢
    simp only [hne, ↓reduceIte, hc, except_ok_bind, hnil, hc2]
    rfl

/-- A map with windows translates a nonempty request within the width of its
side through its windows. -/
public theorem translate_windows {m : AddressMap} {s : Span} {reverse : Bool}
    (hne : s.size ≠ 0) (hw : s.WithinWidth (if reverse then m.parentCells else m.childCells))
    {w₀ : Window} {ws₀ : List Window} (hws : m.windows = some (w₀ :: ws₀)) :
    m.translate s reverse =
      throughWindows s (Window.source · reverse) (Window.target · reverse) (w₀ :: ws₀) none := by
  have hc := (checkWidth_ok (u := ())).2 hw
  unfold AddressMap.translate
  cases reverse
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hc ⊢
    simp only [hne, ↓reduceIte, hc, except_ok_bind, hws]
    rfl

/-- A translation keeps the size of the request. -/
public theorem translate_size {m : AddressMap} {s r : Span} {reverse : Bool}
    (h : m.translate s reverse = .ok r) : r.size = s.size := by
  obtain ⟨hne, -, hcase⟩ := translate_ok h
  rcases hcase with ⟨-, rfl, -⟩ | ⟨w₀, ws₀, -, ht⟩
  · rfl
  · obtain ⟨_, -, -, hrs, -⟩ := (throughWindows_ok hne ht).1 rfl
    exact hrs

/-- A translation through a well-formed map gives a nonempty span of the size
of the request within the width of the target side. -/
public theorem translate_wellFormed {m : AddressMap} {s r : Span} {reverse : Bool}
    (hm : m.WellFormed) (h : m.translate s reverse = .ok r) :
    r.size = s.size ∧ r.size ≠ 0 ∧
      r.WithinWidth (if reverse then m.childCells else m.parentCells) := by
  obtain ⟨hne, -, hcase⟩ := translate_ok h
  rcases hcase with ⟨-, rfl, hw⟩ | ⟨w₀, ws₀, hws, ht⟩
  · exact ⟨rfl, hne, hw⟩
  · obtain ⟨w, hf, hh, hrs, hrst⟩ := (throughWindows_ok hne ht).1 rfl
    have hmem : w ∈ w₀ :: ws₀ :=
      (List.mem_filter.1 (by rw [hf]; exact List.mem_singleton_self w)).1
    obtain ⟨hsz, hw⟩ := window_target (hm.2.2.2 _ hws w hmem) reverse
    exact ⟨hrs, hrs ▸ hne, target_withinWidth hne hsz hw hh hrs hrst⟩

/-- The translation through the `ranges` of the buses up to the root keeps the
size of the span. -/
public theorem climbRanges_size :
    ∀ {fuel : Nat} {bus : Node} {s r : Span}, climbRanges fuel bus s = .ok r → r.size = s.size
  | 0, _, _, _, h => by simp [climbRanges] at h
  | fuel + 1, bus, s, r, h => by
    simp only [climbRanges] at h
    split at h
    · cases h
      rfl
    · obtain ⟨_, _, h⟩ := except_bind_ok.1 h
      obtain ⟨t, ht, h⟩ := except_bind_ok.1 h
      rw [climbRanges_size h, translate_size ht]

end Krepi.Proofs.Fdt
