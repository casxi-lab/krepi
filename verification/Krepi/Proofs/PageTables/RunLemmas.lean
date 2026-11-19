module

public import Krepi.SpecProperties.PageTables.Invariants
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: lemmas about runs of pages

The runs `[a, b)` of the specification of the page ownership table, lists
of pairs of numbers that `cutRuns` and `cutAll` cut: what the points of the
runs are, and the shape of the runs that the cuts keep.

- `cutAll_mem`: a point lies in a run of the result exactly when it lies in
  a run of the input and in no cut;
- `cutAll_sub`: every run of the result lies inside a run of the input;
- `cutAll_nonempty`: the cuts keep every run nonempty, `a < b`;
- `cutAll_pairwise`: the cuts keep runs that are in strict address order,
  apart from each other, in that order, for cuts that are nonempty;
- `cutAll_aligned`: the cuts keep the ends of the runs multiples of a number
  when the cuts have such ends;
- `runs_eq_nil_iff`: nonempty runs are none exactly when no point lies in
  one.

Each fact of `cutAll` follows from the same fact of `cutRuns`, the runs after
one cut, by private steps; the private `mem_pieces` names the two parts of a
run that a cut meets.
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables Krepi.SpecProperties.PageTables

private theorem mem_pieces {a b s t : Nat} {r : Nat × Nat}
    (h : r ∈ (if a < s then [(a, s)] else []) ++ (if t < b then [(t, b)] else [])) :
    (r = (a, s) ∧ a < s) ∨ (r = (t, b) ∧ t < b) := by
  split at h <;> split at h <;> simp_all

private theorem cutRuns_mem (s t p : Nat) : ∀ runs : List (Nat × Nat),
    (∃ r ∈ cutRuns s t runs, r.1 ≤ p ∧ p < r.2) ↔
      (∃ r ∈ runs, r.1 ≤ p ∧ p < r.2) ∧ ¬ (s ≤ p ∧ p < t)
  | [] => by simp [cutRuns]
  | (a, b) :: rest => by
    have ih := cutRuns_mem s t p rest
    unfold cutRuns
    split
    · rename_i h
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      constructor
      · rintro ⟨r, hr, h1, h2⟩
        rcases List.mem_cons.1 hr with rfl | hr
        · exact ⟨⟨_, List.mem_cons_self, h1, h2⟩, by omega⟩
        · obtain ⟨⟨r', hr', h3⟩, h4⟩ := ih.1 ⟨r, hr, h1, h2⟩
          exact ⟨⟨r', List.mem_cons_of_mem _ hr', h3⟩, h4⟩
      · rintro ⟨⟨r, hr, h1, h2⟩, hc⟩
        rcases List.mem_cons.1 hr with rfl | hr
        · exact ⟨_, List.mem_cons_self, h1, h2⟩
        · obtain ⟨r', hr', h3⟩ := ih.2 ⟨⟨r, hr, h1, h2⟩, hc⟩
          exact ⟨r', List.mem_cons_of_mem _ hr', h3⟩
    · rename_i h
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at h
      constructor
      · rintro ⟨r, hr, h1, h2⟩
        rcases List.mem_append.1 hr with hr | hr
        · refine ⟨⟨(a, b), List.mem_cons_self, ?_⟩, ?_⟩ <;>
            rcases mem_pieces hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
        · obtain ⟨⟨r', hr', h3⟩, h4⟩ := ih.1 ⟨r, hr, h1, h2⟩
          exact ⟨⟨r', List.mem_cons_of_mem _ hr', h3⟩, h4⟩
      · rintro ⟨⟨r, hr, h1, h2⟩, hc⟩
        rcases List.mem_cons.1 hr with rfl | hr
        · by_cases hp : p < s
          · exact ⟨(a, s), List.mem_append_left _ (List.mem_append_left _
              (by rw [ite_eq_left (by omega)]; exact List.mem_singleton_self _)), h1, hp⟩
          · exact ⟨(t, b), List.mem_append_left _ (List.mem_append_right _
              (by rw [ite_eq_left (by omega)]; exact List.mem_singleton_self _)), by omega, h2⟩
        · obtain ⟨r', hr', h3⟩ := ih.2 ⟨⟨r, hr, h1, h2⟩, hc⟩
          exact ⟨r', List.mem_append_right _ hr', h3⟩

theorem cutAll_mem (p : Nat) : ∀ (cuts runs : List (Nat × Nat)),
    (∃ r ∈ cutAll cuts runs, r.1 ≤ p ∧ p < r.2) ↔
      (∃ r ∈ runs, r.1 ≤ p ∧ p < r.2) ∧ ∀ c ∈ cuts, ¬ (c.1 ≤ p ∧ p < c.2)
  | [], runs => by simp [cutAll]
  | c :: cs, runs => by
    have ih := cutAll_mem p cs (cutRuns c.1 c.2 runs)
    simp only [cutAll, List.foldl_cons] at ih ⊢
    rw [ih, cutRuns_mem, List.forall_mem_cons, and_assoc]

private theorem cutRuns_sub (s t : Nat) : ∀ runs : List (Nat × Nat), ∀ r ∈ cutRuns s t runs,
    ∃ r' ∈ runs, r'.1 ≤ r.1 ∧ r.2 ≤ r'.2
  | [] => by simp [cutRuns]
  | (a, b) :: rest => by
    have ih := cutRuns_sub s t rest
    unfold cutRuns
    intro r hr
    split at hr
    · rcases List.mem_cons.1 hr with rfl | hr
      · exact ⟨(a, b), List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
      · obtain ⟨r', h1, h2⟩ := ih r hr
        exact ⟨r', List.mem_cons_of_mem _ h1, h2⟩
    · rename_i h
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at h
      rcases List.mem_append.1 hr with hr | hr
      · refine ⟨(a, b), List.mem_cons_self, ?_⟩
        rcases List.mem_append.1 hr with hr | hr <;> split at hr <;>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr <;> subst hr <;> simp <;>
          omega
      · obtain ⟨r', h1, h2⟩ := ih r hr
        exact ⟨r', List.mem_cons_of_mem _ h1, h2⟩

theorem cutAll_sub : ∀ (cuts runs : List (Nat × Nat)), ∀ r ∈ cutAll cuts runs,
    ∃ r' ∈ runs, r'.1 ≤ r.1 ∧ r.2 ≤ r'.2
  | [], runs => fun r hr => ⟨r, by simpa [cutAll] using hr, Nat.le_refl _, Nat.le_refl _⟩
  | c :: cs, runs => fun r hr => by
    simp only [cutAll, List.foldl_cons] at hr
    obtain ⟨r1, h1, h2⟩ := cutAll_sub cs (cutRuns c.1 c.2 runs) r hr
    obtain ⟨r2, h3, h4⟩ := cutRuns_sub c.1 c.2 runs r1 h1
    exact ⟨r2, h3, by omega, by omega⟩

private theorem cutRuns_nonempty (s t : Nat) : ∀ runs : List (Nat × Nat), (∀ r ∈ runs, r.1 < r.2) →
    ∀ r ∈ cutRuns s t runs, r.1 < r.2
  | [] => by simp [cutRuns]
  | (a, b) :: rest => by
    intro hr
    have ih := cutRuns_nonempty s t rest fun r h => hr r (List.mem_cons_of_mem _ h)
    unfold cutRuns
    intro r h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact hr _ List.mem_cons_self
      · exact ih r h
    · rcases List.mem_append.1 h with h | h
      · rcases List.mem_append.1 h with h | h <;> split at h <;>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;> subst h <;> simp <;>
          omega
      · exact ih r h

theorem cutAll_nonempty : ∀ (cuts runs : List (Nat × Nat)), (∀ r ∈ runs, r.1 < r.2) →
    ∀ r ∈ cutAll cuts runs, r.1 < r.2
  | [], runs => fun h => by simpa [cutAll] using h
  | c :: cs, runs => fun h => by
    simp only [cutAll, List.foldl_cons]
    exact cutAll_nonempty cs _ (cutRuns_nonempty c.1 c.2 runs h)

private theorem cutRuns_pairwise {s t : Nat} (hst : s < t) : ∀ runs : List (Nat × Nat),
    runs.Pairwise (fun x y => x.2 < y.1) → (cutRuns s t runs).Pairwise (fun x y => x.2 < y.1)
  | [] => by simp [cutRuns]
  | (a, b) :: rest => by
    intro hp
    rw [List.pairwise_cons] at hp
    have ih := cutRuns_pairwise hst rest hp.2
    have hsub := cutRuns_sub s t rest
    have hb : ∀ y ∈ cutRuns s t rest, b < y.1 := fun y hy => by
      obtain ⟨r', h1, h2⟩ := hsub y hy
      have := hp.1 r' h1
      omega
    unfold cutRuns
    split
    · exact List.pairwise_cons.2 ⟨hb, ih⟩
    · rename_i h
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at h
      refine List.pairwise_append.2 ⟨?_, ih, ?_⟩
      · split <;> split <;> simp [hst]
      · intro x hx y hy
        have := hb y hy
        rcases List.mem_append.1 hx with hx | hx <;> split at hx <;>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx <;> subst hx <;> simp <;>
          omega

theorem cutAll_pairwise : ∀ (cuts runs : List (Nat × Nat)), (∀ c ∈ cuts, c.1 < c.2) →
    runs.Pairwise (fun x y => x.2 < y.1) → (cutAll cuts runs).Pairwise (fun x y => x.2 < y.1)
  | [], runs => fun _ h => by simpa [cutAll] using h
  | c :: cs, runs => fun hc h => by
    simp only [cutAll, List.foldl_cons]
    exact cutAll_pairwise cs _ (fun c' h' => hc c' (List.mem_cons_of_mem _ h'))
      (cutRuns_pairwise (hc c List.mem_cons_self) runs h)

private theorem cutRuns_aligned {m s t : Nat} (hs : s % m = 0) (ht : t % m = 0) :
    ∀ runs : List (Nat × Nat), (∀ r ∈ runs, r.1 % m = 0 ∧ r.2 % m = 0) →
      ∀ r ∈ cutRuns s t runs, r.1 % m = 0 ∧ r.2 % m = 0
  | [] => by simp [cutRuns]
  | (a, b) :: rest => by
    intro hr
    have ih := cutRuns_aligned hs ht rest fun r h => hr r (List.mem_cons_of_mem _ h)
    have hab := hr _ List.mem_cons_self
    simp only at hab
    unfold cutRuns
    intro r h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact hab
      · exact ih r h
    · rcases List.mem_append.1 h with h | h
      · rcases List.mem_append.1 h with h | h <;> split at h <;>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;> subst h <;>
          exact ⟨by first | exact hab.1 | exact ht, by first | exact hs | exact hab.2⟩
      · exact ih r h

theorem cutAll_aligned {m : Nat} : ∀ (cuts runs : List (Nat × Nat)),
    (∀ c ∈ cuts, c.1 % m = 0 ∧ c.2 % m = 0) → (∀ r ∈ runs, r.1 % m = 0 ∧ r.2 % m = 0) →
      ∀ r ∈ cutAll cuts runs, r.1 % m = 0 ∧ r.2 % m = 0
  | [], runs => fun _ h => by simpa [cutAll] using h
  | c :: cs, runs => fun hc h => by
    simp only [cutAll, List.foldl_cons]
    have h0 := hc c List.mem_cons_self
    exact cutAll_aligned cs _ (fun c' h' => hc c' (List.mem_cons_of_mem _ h'))
      (cutRuns_aligned h0.1 h0.2 runs h)

theorem runs_eq_nil_iff {runs : List (Nat × Nat)} (h : ∀ r ∈ runs, r.1 < r.2) :
    runs = [] ↔ ∀ p, ¬ ∃ r ∈ runs, r.1 ≤ p ∧ p < r.2 := by
  constructor
  · rintro rfl p ⟨r, hr, _⟩
    simp at hr
  · intro hp
    cases runs with
    | nil => rfl
    | cons r rest =>
      exact absurd ⟨r, List.mem_cons_self, Nat.le_refl _, h r List.mem_cons_self⟩ (hp r.1)

end Krepi.Proofs.PageTables
