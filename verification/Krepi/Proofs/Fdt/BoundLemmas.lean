module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
public import Krepi.Proofs.Fdt.ErrorSets
public import Krepi.Proofs.Fdt.ParseWalk
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.Fdt.SpanLemmas
import Krepi.Proofs.Fdt.PlanLemmas
import Krepi.Proofs.Fdt.BootMemoryLemmas

/-!
# Device tree: bounds of fuel and of sums

Lemmas for the branches that 64-bit arithmetic or enough fuel leave
unreached:

- sums of spans: `foldl_size_add`, `spansBytes_cons`, `spansBytes_perm`;
  spans in address order within 64 bits hold fewer than `2 ^ 64` bytes
  (`sorted_bytes`), and so do nonempty spans of which no two touch
  (`disjoint_bytes`);
- the reservation map: more fuel than `MAX_RESERVATIONS + 1` entries gives
  the same result (`reservationsFrom_fuel`);
- the depth of a well-formed tree: parents precede their children
  (`parentsBelow`), and the parent of a node lies one level higher
  (`parent_depth`), so a climb with more fuel than the depth of its bus never
  runs out (`climbRanges_fuel`);
- a translation through windows whose target sides have the sizes of their
  source sides and end within 64 bits never fails with `Overflow`
  (`throughWindows_noov`).
-/

@[expose] public section

namespace Krepi.Proofs.Fdt

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

/-! ## Sums of spans -/

/-- The fold of `spansBytes` from any initial sum. -/
theorem foldl_size_add : ∀ (l : List Span) (acc : Nat),
    l.foldl (fun sum s => sum + s.size.toNat) acc = acc + spansBytes l
  | [], acc => by simp [spansBytes]
  | s :: l, acc => by
    have h1 := foldl_size_add l (acc + s.size.toNat)
    have h2 := foldl_size_add l (0 + s.size.toNat)
    simp only [spansBytes, List.foldl_cons] at h1 h2 ⊢
    omega

theorem spansBytes_cons (s : Span) (l : List Span) :
    spansBytes (s :: l) = s.size.toNat + spansBytes l := by
  have := foldl_size_add l (0 + s.size.toNat)
  simp only [spansBytes, List.foldl_cons] at this ⊢
  omega

theorem spansBytes_perm {l1 l2 : List Span} (h : l1.Perm l2) :
    spansBytes l1 = spansBytes l2 := by
  induction h with
  | nil => rfl
  | cons x _ ih => rw [spansBytes_cons, spansBytes_cons, ih]
  | swap x y l => rw [spansBytes_cons, spansBytes_cons, spansBytes_cons, spansBytes_cons]; omega
  | trans _ _ ih1 ih2 => rw [ih1, ih2]

/-- Spans in address order, from `lo` on, that end within 64 bits hold fewer
than `2 ^ 64 - lo` bytes. -/
theorem sorted_bytes : ∀ (l : List Span) (lo : Nat), lo < 2 ^ 64 →
    l.Pairwise (fun a b => a.endNat ≤ b.start.toNat) →
    (∀ x ∈ l, lo ≤ x.start.toNat ∧ x.endNat < 2 ^ 64) → lo + spansBytes l < 2 ^ 64
  | [], lo, h, _, _ => by simpa [spansBytes] using h
  | s :: l, lo, h, hp, hx => by
    rw [spansBytes_cons]
    obtain ⟨hs1, hs2⟩ := hx s List.mem_cons_self
    have ih := sorted_bytes l s.endNat hs2 (List.pairwise_cons.1 hp).2 fun x hx' =>
      ⟨(List.pairwise_cons.1 hp).1 x hx', (hx x (List.mem_cons_of_mem _ hx')).2⟩
    unfold Span.endNat at ih hs2
    omega

/-- Nonempty spans of which no two touch hold fewer than `2 ^ 64` bytes. -/
theorem disjoint_bytes {l : List Span} (hne : ∀ s ∈ l, s.Nonempty)
    (hp : l.Pairwise (fun a b => a.touches b = false)) : spansBytes l < 2 ^ 64 := by
  rw [spansBytes_perm (sortByStart_perm l).symm]
  have := sorted_bytes (sortByStart l) 0 (by decide) (sortByStart_pairwise l hne hp)
    fun x hx => ⟨Nat.zero_le _, (hne x ((sortByStart_perm l).mem_iff.1 hx)).2⟩
  omega

/-! ## The reservation map -/

/-- With fuel for every entry up to the limit and one more, more fuel gives
the same result: the map ends, fails or reaches the limit first. -/
theorem reservationsFrom_fuel (h : Header) : ∀ (fuel k cursor : Nat) (earlier : List Span),
    MAX_RESERVATIONS.toNat + 1 ≤ earlier.length + fuel → 1 ≤ fuel →
    reservationsFrom h (fuel + k) cursor earlier = reservationsFrom h fuel cursor earlier
  | 0, _, _, _, _, h1 => absurd h1 (by decide)
  | fuel + 1, k, cursor, earlier, hf, _ => by
    rw [show fuel + 1 + k = (fuel + k) + 1 by omega]
    by_cases hl : MAX_RESERVATIONS.toNat < earlier.length + 1
    · simp only [reservationsFrom, hl, ↓reduceIte]
      rfl
    · have ih : ∀ c s, reservationsFrom h (fuel + k) c (earlier ++ [s]) =
          reservationsFrom h fuel c (earlier ++ [s]) := fun c s =>
        reservationsFrom_fuel h fuel k c (earlier ++ [s]) (by simp; omega) (by omega)
      simp only [reservationsFrom, ih]

/-! ## Depth -/

/-- In a well-formed tree every parent precedes its child. -/
theorem parentsBelow {t : Fdt} (ht : t.WellFormed) : ParentsBelow t.records := by
  intro j p h
  by_cases hj : j < t.records.size
  · have hw := (ht.2.2.2.2.2.2.2 j hj).1
    rw [Array.getElem?_eq_getElem hj] at h
    simp only [Option.bind_some] at h
    split at hw
    · rw [hw.1] at h; cases h
    · obtain ⟨⟨p', hp', hlt⟩, -⟩ := hw
      rw [hp'] at h
      cases h
      exact hlt
  · rw [Array.getElem?_eq_none (by omega)] at h
    cases h

/-- The parent of a node of a well-formed tree is a node of the tree one level
higher. -/
theorem parent_depth {t : Fdt} (ht : t.WellFormed) {i : Fin t.records.size} {up : Node}
    (h : (⟨t, i⟩ : Node).parent = some up) :
    ∃ j : Fin t.records.size, up = ⟨t, j⟩ ∧ t.depth j + 1 = t.depth i := by
  unfold Node.parent at h
  split at h
  · cases h
  · rename_i p hp
    split at h
    · rename_i hps
      cases h
      refine ⟨⟨p, hps⟩, rfl, ?_⟩
      have hq : (t.records[i.val]?).bind (·.parent) = some p := by
        rw [Array.getElem?_eq_getElem i.isLt]
        exact hp
      have hpi : p < i.val := parentsBelow ht i p hq
      show t.depth p + 1 = t.depth i.val
      unfold Fdt.depth
      rw [depthFrom_eq_recDepth, depthFrom_eq_recDepth]
      conv => rhs; rw [recDepth, hq]
      dsimp only
      rw [recDepth_fuel (parentsBelow ht) i.val (p + 1) p hpi (by omega)]
    · cases h

/-- A climb from a bus of a well-formed tree with more fuel than its depth
never runs out of fuel. -/
theorem climbRanges_fuel {t : Fdt} (ht : t.WellFormed) :
    ∀ fuel (i : Fin t.records.size) s, t.depth i < fuel →
      ErrsIn (· ≠ .limitExceeded) (climbRanges fuel ⟨t, i⟩ s)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | fuel + 1, i, s, h => by
    rw [climbRanges]
    split
    · exact errsIn_ok _
    · rename_i up hup
      obtain ⟨j, rfl, hd⟩ := parent_depth ht hup
      refine errsIn_bind (errsIn_sub (ranges_errs hup) (by decide)) fun m _ => ?_
      refine errsIn_bind (errsIn_sub (translate_errs _ _ _) (by decide)) fun s' _ => ?_
      exact climbRanges_fuel ht fuel j s' (by omega)

/-! ## Translation through windows -/

/-- A translation through windows whose target sides have the sizes of their
source sides and end within 64 bits never fails with `Overflow`: the result
lies inside the target side of the window that holds the request. -/
theorem throughWindows_noov {req : Span} {src tgt : Window → Span} :
    ∀ {ws : List Window} (found : Option Span),
    (∀ w ∈ ws, (tgt w).size = (src w).size ∧ (tgt w).Valid) →
    ErrsIn (· ≠ .overflow) (throughWindows req src tgt ws found)
  | [], none, _ => errsIn_error (by decide)
  | [], some _, _ => errsIn_ok _
  | w :: ws, found, hw => by
    rw [throughWindows]
    have ih := fun f => throughWindows_noov (req := req) (ws := ws) f
      (fun x hx => hw x (List.mem_cons_of_mem _ hx))
    refine errsIn_ite (fun hh => ?_) (fun _ => errsIn_ite (fun _ => errsIn_error (by decide))
      fun _ => ih _)
    refine errsIn_jp (fun _ => by decide) fun _ => ?_
    obtain ⟨hsz, hv⟩ := hw w List.mem_cons_self
    rw [holds_iff] at hh
    have hsz' : (tgt w).size.toNat = (src w).size.toNat := by rw [hsz]
    unfold Span.Valid Span.endNat at hv
    unfold Span.endNat at hh
    have hlt : (tgt w).start.toNat + (req.start.toNat - (src w).start.toNat) + req.size.toNat <
        2 ^ 64 := by omega
    refine errsIn_bind (errsIn_of_ok (checkedAdd_ok.2 ⟨by omega, rfl⟩)) fun st hst => ?_
    have hst' := (checkedAdd_ok.1 hst).2
    have hu : UInt64.size = 2 ^ 64 := rfl
    have hst2 : (UInt64.ofNat st).toNat = st := UInt64.toNat_ofNat_of_lt' (by omega)
    refine errsIn_bind (errsIn_of_ok (span_new_ok.2 ⟨?_, rfl⟩)) fun s' _ => ih _
    rw [hst2]
    omega

end Krepi.Proofs.Fdt
