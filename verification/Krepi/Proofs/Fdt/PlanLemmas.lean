module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.Fdt.SpanLemmas

/-!
# Device tree: lemmas about the boot memory map

Lemmas about the entries of the boot memory map of the specification of the
`fdt` component and about its usable ranges, for the proofs of the
statements about them:

- folds and counts of lists: `foldl_max_spec`, `foldl_min_spec`, `countP_lt`
  and `length_le_of_nodup_subset`;
- spans: `touches_iff`, `touches_false`, `nonempty_lt`, `spanBetween_spec`,
  the pages of an address (`roundDown_spec`, `roundUp_spec`) and of a span
  (`checkPlanSpan_ok`, `pagesOf_ok`);
- the steps of `MemoryPlan::all_ram`: the banks in input order
  (`addBank_fold`) and in address order (`sortByStart_perm`,
  `sortByStart_pairwise`), their managed banks (`managedOf`,
  `managedOf_spec`, `admitBank_fold`), the boot storage (`addBoot_fold`) and
  the firmware reservations (`addFirmware_fold`); and the entries
  (`allRam_wellFormed`, `new_wellFormed`);
- the usable ranges: one step of `usableFrom` (`usableFrom_succ`, with
  `holdingOf`, `nextOf` and `maxEndOf`), what each range is
  (`usableFrom_mem`, `availableRanges_mem`), their order
  (`usableFrom_pairwise`) and that they cover every free address of a
  managed bank (`usableFrom_covers`).

Every `omega` here sees few facts: a context with two roundings to pages and
a bound of `2 ^ 64` exceeds its recursion depth, so the roundings are taken
apart by `roundDown_spec` and `roundUp_spec` instead.
-/

@[expose] public section

namespace Krepi.Proofs.Fdt

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

/-! ## Folds and counts -/

/-- The greatest of an initial value and the values of a list: at least each of
them, and one of them. -/
theorem foldl_max_spec {α : Type} (f : α → Nat) : ∀ (l : List α) (init : Nat),
    init ≤ l.foldl (fun e s => max e (f s)) init ∧
    (∀ x ∈ l, f x ≤ l.foldl (fun e s => max e (f s)) init) ∧
    (l.foldl (fun e s => max e (f s)) init = init ∨
      ∃ x ∈ l, l.foldl (fun e s => max e (f s)) init = f x)
  | [], init => by simp
  | a :: l, init => by
    obtain ⟨h1, h2, h3⟩ := foldl_max_spec f l (max init (f a))
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp, exists_eq_or_imp]
    refine ⟨by omega, ⟨by omega, h2⟩, ?_⟩
    rcases h3 with h3 | h3
    · rw [h3]
      by_cases hc : init ≤ f a
      · exact Or.inr (Or.inl (by omega))
      · exact Or.inl (by omega)
    · exact Or.inr (Or.inr h3)

/-- The least of an initial value and the starts of a list above `c`, the fold of
`usableFrom` for the end of a usable range: at most each of them, and one of
them. -/
theorem foldl_min_spec (c : Nat) : ∀ (l : List Span) (init : Nat),
    l.foldl (fun e r => if c < r.start.toNat then min e r.start.toNat else e) init ≤ init ∧
    (∀ x ∈ l, c < x.start.toNat →
      l.foldl (fun e r => if c < r.start.toNat then min e r.start.toNat else e) init ≤
        x.start.toNat) ∧
    (l.foldl (fun e r => if c < r.start.toNat then min e r.start.toNat else e) init = init ∨
      ∃ x ∈ l, c < x.start.toNat ∧
        l.foldl (fun e r => if c < r.start.toNat then min e r.start.toNat else e) init =
          x.start.toNat)
  | [], init => by simp
  | a :: l, init => by
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp, exists_eq_or_imp]
    by_cases ha : c < a.start.toNat
    · rw [ite_eq_left ha]
      obtain ⟨h1, h2, h3⟩ := foldl_min_spec c l (min init a.start.toNat)
      refine ⟨by omega, ⟨fun _ => by omega, h2⟩, ?_⟩
      rcases h3 with h3 | h3
      · rw [h3]
        by_cases hc : init ≤ a.start.toNat
        · exact Or.inl (by omega)
        · exact Or.inr (Or.inl ⟨ha, by omega⟩)
      · exact Or.inr (Or.inr h3)
    · rw [ite_eq_right ha]
      obtain ⟨h1, h2, h3⟩ := foldl_min_spec c l init
      refine ⟨h1, ⟨fun h => absurd h ha, h2⟩, ?_⟩
      rcases h3 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (Or.inr h3)

/-- A predicate that implies another and fails on an entry where the other holds
counts fewer entries. -/
theorem countP_lt {α : Type} {p q : α → Bool} : ∀ {l : List α},
    (∀ x ∈ l, p x = true → q x = true) → (∃ x ∈ l, q x = true ∧ p x = false) →
    l.countP p < l.countP q
  | [], _, ⟨_, hx, _⟩ => absurd hx List.not_mem_nil
  | a :: l, himp, ⟨x, hx, hqx, hpx⟩ => by
    simp only [List.countP_cons]
    have hmono := List.countP_mono_left (fun y hy => himp y (List.mem_cons_of_mem _ hy))
    have ha := himp a List.mem_cons_self
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [ite_eq_right (by rw [hpx]; exact Bool.false_ne_true), ite_eq_left hqx]
      omega
    · have := countP_lt (fun y hy => himp y (List.mem_cons_of_mem _ hy)) ⟨x, hx, hqx, hpx⟩
      by_cases hpa : p a = true
      · rw [ite_eq_left hpa, ite_eq_left (ha hpa)]
        omega
      · rw [ite_eq_right hpa]
        split <;> omega

/-- A list without duplicates whose entries all lie in `L` is at most as long as
`L`. -/
theorem length_le_of_nodup_subset : ∀ {l L : List Nat}, l.Nodup → (∀ x ∈ l, x ∈ L) →
    l.length ≤ L.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, L, hn, hs => by
    have ha : a ∈ L := hs a List.mem_cons_self
    have hn' := List.nodup_cons.1 hn
    have ih := length_le_of_nodup_subset (L := L.erase a) hn'.2 (fun x hx =>
      (List.mem_erase_of_ne (fun h => hn'.1 (by rw [← h]; exact hx))).2
        (hs x (List.mem_cons_of_mem _ hx)))
    rw [List.length_erase_of_mem ha] at ih
    have := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-! ## Spans of the boot memory map -/

/-- `Span.touches` as inequalities of the exact ends. -/
theorem touches_iff {a b : Span} :
    a.touches b = true ↔ a.size ≠ 0 ∧ b.size ≠ 0 ∧
      a.start.toNat < b.endNat ∧ b.start.toNat < a.endNat := by
  simp only [Span.touches, Span.overlaps, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq, and_assoc]

/-- Two nonempty spans that do not touch lie one after the other. -/
theorem touches_false {a b : Span} (ha : a.Nonempty) (hb : b.Nonempty)
    (h : a.touches b = false) : a.endNat ≤ b.start.toNat ∨ b.endNat ≤ a.start.toNat := by
  have h1 := size_toNat_ne_zero ha.1
  have h2 := size_toNat_ne_zero hb.1
  simp only [Span.touches, Span.overlaps, Bool.and_eq_false_iff, bne_eq_false_iff_eq,
    decide_eq_false_iff_not, Nat.not_lt] at h
  unfold Span.endNat at h ⊢
  rcases h with (h | h) | h | h
  · exact absurd h ha.1
  · exact absurd h hb.1
  · omega
  · omega

/-- A nonempty span starts below its end. -/
theorem nonempty_lt {x : Span} (h : x.Nonempty) : x.start.toNat < x.endNat := by
  have := size_toNat_ne_zero h.1
  unfold Span.endNat
  omega

/-- The span from `a` up to `b` below `2 ^ 64` starts at `a`, ends at `b` and is
nonempty. -/
theorem spanBetween_spec {a b : Nat} (hab : a < b) (hb : b < 2 ^ 64) :
    (spanBetween a b).start.toNat = a ∧ (spanBetween a b).endNat = b ∧
      (spanBetween a b).Nonempty := by
  have hu : UInt64.size = 2 ^ 64 := rfl
  have h1 : (UInt64.ofNat a).toNat = a := UInt64.toNat_ofNat_of_lt' (by omega)
  have h2 : (UInt64.ofNat (b - a)).toNat = b - a := UInt64.toNat_ofNat_of_lt' (by omega)
  have he : (spanBetween a b).endNat = b := by
    unfold Span.endNat spanBetween
    rw [h1, h2]
    omega
  refine ⟨h1, he, ?_, by unfold Span.Valid; rw [he]; exact hb⟩
  intro h0
  have : (spanBetween a b).size.toNat = 0 := by rw [h0]; rfl
  unfold spanBetween at this
  rw [h2] at this
  omega

/-- An address rounded down to a page. -/
theorem roundDown_spec (x : Nat) :
    x / 4096 * 4096 ≤ x ∧ x / 4096 * 4096 % 4096 = 0 := by
  omega

/-- An address rounded up to a page. -/
theorem roundUp_spec (x : Nat) :
    x ≤ (x + 4096 - 1) / 4096 * 4096 ∧ (x + 4096 - 1) / 4096 * 4096 % 4096 = 0 := by
  omega

/-- A span that `checkPlanSpan` accepts is nonempty. -/
theorem checkPlanSpan_ok {s : Span} {u : Unit} (h : checkPlanSpan s = .ok u) : s.Nonempty := by
  unfold checkPlanSpan at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact ⟨‹_›, Decidable.not_not.1 ‹_›⟩

/-- The pages of a span are nonempty and on pages. -/
theorem pagesOf_ok {s p : Span} (h : pagesOf s = .ok p) : p.Nonempty ∧ p.OnPages := by
  unfold pagesOf at h
  obtain ⟨u, hu, h⟩ := except_bind_ok.1 h
  have hs := checkPlanSpan_ok hu
  obtain ⟨hstop, h⟩ := except_jp_ok h
  rw [except_pure_ok] at h
  subst h
  unfold MemoryPlan.PAGE_SIZE at hstop ⊢
  obtain ⟨hd1, hd2⟩ := roundDown_spec s.start.toNat
  obtain ⟨hu1, hu2⟩ := roundUp_spec s.endNat
  obtain ⟨h1, h2, h3⟩ := spanBetween_spec
    (Nat.lt_of_le_of_lt hd1 (Nat.lt_of_lt_of_le (nonempty_lt hs) hu1)) (Nat.lt_of_not_le hstop)
  refine ⟨h3, ?_, ?_⟩
  · rw [h1]
    exact hd2
  · rw [h2]
    exact hu2

/-! ## The banks -/

/-- The banks of `MemoryPlan::all_ram` in input order: the banks given, each
nonempty, no two touching. -/
theorem addBank_fold : ∀ (l acc res : List Span), l.foldlM addBank acc = .ok res →
    acc.Pairwise (fun a b => a.touches b = false) →
    res = acc ++ l ∧ res.Pairwise (fun a b => a.touches b = false) ∧ ∀ s ∈ l, s.Nonempty
  | [], acc, res, h, hp => by
    simp only [List.foldlM_nil, except_pure_ok] at h
    subst h
    simp [hp]
  | s :: l, acc, res, h, hp => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc', h1, h⟩ := except_bind_ok.1 h
    unfold addBank at h1
    obtain ⟨u, hu, h1⟩ := except_bind_ok.1 h1
    obtain ⟨hany, h1⟩ := except_jp_ok h1
    rw [except_pure_ok] at h1
    subst h1
    have hp' : (acc ++ [s]).Pairwise (fun a b => a.touches b = false) := by
      rw [List.pairwise_append]
      refine ⟨hp, List.pairwise_singleton _ _, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      simp only [Bool.not_eq_true, List.any_eq_false] at hany
      simpa using hany a ha
    obtain ⟨h1, h2, h3⟩ := addBank_fold l _ res h hp'
    refine ⟨by rw [h1]; simp, h2, ?_⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact checkPlanSpan_ok hu
    · exact h3 x hx

/-- `insertByStart` puts the span among the others. -/
theorem insertByStart_perm (s : Span) : ∀ l : List Span, (insertByStart s l).Perm (s :: l)
  | [] => List.Perm.refl _
  | b :: rest => by
    unfold insertByStart
    split
    · exact List.Perm.refl _
    · exact ((insertByStart_perm s rest).cons b).trans (List.Perm.swap s b rest)

/-- `sortByStart` keeps the spans. -/
theorem sortByStart_perm : ∀ l : List Span, (sortByStart l).Perm l
  | [] => List.Perm.refl _
  | s :: rest => (insertByStart_perm s _).trans ((sortByStart_perm rest).cons s)

/-- A span put among spans in address order that it does not share an address
with keeps them in address order. -/
theorem insertByStart_pairwise {s : Span} (hs : s.start.toNat < s.endNat) :
    ∀ l : List Span, l.Pairwise (fun a b => a.endNat ≤ b.start.toNat) →
      (∀ b ∈ l, b.start.toNat < b.endNat ∧
        (s.endNat ≤ b.start.toNat ∨ b.endNat ≤ s.start.toNat)) →
      (insertByStart s l).Pairwise (fun a b => a.endNat ≤ b.start.toNat)
  | [], _, _ => List.pairwise_singleton _ _
  | b :: rest, hl, hb => by
    rw [List.pairwise_cons] at hl
    have hb0 := hb b List.mem_cons_self
    unfold insertByStart
    split
    · rename_i hsb
      refine List.pairwise_cons.2 ⟨?_, List.pairwise_cons.2 hl⟩
      have hsb' : s.endNat ≤ b.start.toNat := by omega
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hsb'
      · have := hl.1 y hy
        omega
    · rename_i hsb
      refine List.pairwise_cons.2 ⟨?_, insertByStart_pairwise hs rest hl.2
        (fun y hy => hb y (List.mem_cons_of_mem _ hy))⟩
      intro y hy
      rcases List.mem_cons.1 ((insertByStart_perm s rest).mem_iff.1 hy) with rfl | hy
      · omega
      · exact hl.1 y hy

/-- Nonempty spans no two of which touch, sorted by their start, are in address
order. -/
theorem sortByStart_pairwise : ∀ l : List Span, (∀ b ∈ l, b.Nonempty) →
    l.Pairwise (fun a b => a.touches b = false) →
    (sortByStart l).Pairwise (fun a b => a.endNat ≤ b.start.toNat)
  | [], _, _ => List.Pairwise.nil
  | s :: rest, hn, hp => by
    rw [List.pairwise_cons] at hp
    have hs := hn s List.mem_cons_self
    have hsz := size_toNat_ne_zero hs.1
    refine insertByStart_pairwise (by unfold Span.endNat; omega) _
      (sortByStart_pairwise rest (fun b hb => hn b (List.mem_cons_of_mem _ hb)) hp.2) ?_
    intro b hb
    have hb' := (sortByStart_perm rest).mem_iff.1 hb
    have hbn := hn b (List.mem_cons_of_mem _ hb')
    have := size_toNat_ne_zero hbn.1
    exact ⟨by unfold Span.endNat; omega, touches_false hs hbn (hp.1 b hb')⟩

/-- The managed bank of a bank, its complete pages, or none: what `admitBank`
adds for it. -/
def managedOf (b : Span) : Option Span :=
  if (b.start.toNat + MemoryPlan.PAGE_SIZE - 1) / MemoryPlan.PAGE_SIZE * MemoryPlan.PAGE_SIZE <
      b.endNat / MemoryPlan.PAGE_SIZE * MemoryPlan.PAGE_SIZE then
    some (spanBetween
      ((b.start.toNat + MemoryPlan.PAGE_SIZE - 1) / MemoryPlan.PAGE_SIZE * MemoryPlan.PAGE_SIZE)
      (b.endNat / MemoryPlan.PAGE_SIZE * MemoryPlan.PAGE_SIZE))
  else none

/-- The managed bank of a bank within 64 bits is nonempty, on pages and inside the
bank. -/
theorem managedOf_spec {b x : Span} (hb : b.Valid) (h : managedOf b = some x) :
    x.Nonempty ∧ x.OnPages ∧ b.start.toNat ≤ x.start.toNat ∧ x.endNat ≤ b.endNat := by
  unfold managedOf at h
  split at h
  · rename_i hlt
    injection h with h
    subst h
    unfold Span.Valid at hb
    unfold MemoryPlan.PAGE_SIZE at hlt ⊢
    obtain ⟨hd1, hd2⟩ := roundDown_spec b.endNat
    obtain ⟨hu1, hu2⟩ := roundUp_spec b.start.toNat
    obtain ⟨h1, h2, h3⟩ := spanBetween_spec hlt (Nat.lt_of_le_of_lt hd1 hb)
    refine ⟨h3, ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [h1]; exact hu2
    · rw [h2]; exact hd2
    · rw [h1]; exact hu1
    · rw [h2]; exact hd1
  · cases h

/-- The fold of `admitBank` over banks: the sum of their sizes, within 16 GiB, and
their managed banks after those before. -/
theorem admitBank_fold : ∀ (l : List Span) (acc res : Nat × List Span),
    l.foldlM admitBank acc = .ok res → acc.1 ≤ MemoryPlan.MAX_RAM_BYTES →
    res.1 = l.foldl (fun sum s => sum + s.size.toNat) acc.1 ∧
      res.1 ≤ MemoryPlan.MAX_RAM_BYTES ∧ res.2 = acc.2 ++ l.filterMap managedOf
  | [], acc, res, h, hacc => by
    simp only [List.foldlM_nil, except_pure_ok] at h
    subst h
    simp [hacc]
  | b :: l, acc, res, h, hacc => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc', h1, h⟩ := except_bind_ok.1 h
    unfold admitBank at h1
    obtain ⟨-, h1⟩ := except_jp_ok h1
    obtain ⟨hmax, h1⟩ := except_jp_ok h1
    obtain ⟨-, h1⟩ := except_jp_ok h1
    rw [except_pure_ok] at h1
    subst h1
    obtain ⟨h2, h3, h4⟩ := admitBank_fold l _ res h (by omega)
    refine ⟨by rw [h2]; rfl, h3, ?_⟩
    rw [h4, List.filterMap_cons]
    unfold managedOf
    split <;> simp

/-! ## Boot storage and firmware -/

/-- The fold of `addBoot`: one span of pages for each span of boot storage, each
nonempty, on pages and inside one bank, no two touching. -/
theorem addBoot_fold (banks : List Span) : ∀ (l acc res : List Span),
    l.foldlM (addBoot banks) acc = .ok res →
    (∀ s ∈ acc, s.Nonempty ∧ s.OnPages ∧ inOneRange banks s = true) →
    acc.Pairwise (fun a b => a.touches b = false) →
    res.length = acc.length + l.length ∧
      (∀ s ∈ res, s.Nonempty ∧ s.OnPages ∧ inOneRange banks s = true) ∧
      res.Pairwise (fun a b => a.touches b = false)
  | [], acc, res, h, h1, h2 => by
    simp only [List.foldlM_nil, except_pure_ok] at h
    subst h
    exact ⟨rfl, h1, h2⟩
  | s :: l, acc, res, h, h1, h2 => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc', ha, h⟩ := except_bind_ok.1 h
    unfold addBoot at ha
    obtain ⟨pages, hp, ha1⟩ := except_bind_ok.1 ha
    obtain ⟨hin, ha2⟩ := except_jp_ok ha1
    obtain ⟨hany, ha3⟩ := except_jp_ok ha2
    rw [except_pure_ok] at ha3
    subst ha3
    have hpg := pagesOf_ok hp
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hin
    simp only [Bool.not_eq_true, List.any_eq_false] at hany
    obtain ⟨r1, r2, r3⟩ := addBoot_fold banks l _ res h (by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h1 x hx
      · rw [List.mem_singleton] at hx
        subst hx
        exact ⟨hpg.1, hpg.2, by simpa using hin⟩) (by
      rw [List.pairwise_append]
      refine ⟨h2, List.pairwise_singleton _ _, ?_⟩
      intro a hma b hb
      rw [List.mem_singleton] at hb
      rw [hb]
      simpa using hany a hma)
    refine ⟨by rw [r1]; simp; omega, r2, r3⟩

/-- The fold of `addFirmware`: one span of pages for each reservation, each
nonempty, on pages and touching no boot storage. -/
theorem addFirmware_fold (boot : List Span) : ∀ (l : List ReservedRegion) (acc res : List Span),
    l.foldlM (addFirmware boot) acc = .ok res →
    (∀ f ∈ acc, f.Nonempty ∧ f.OnPages ∧ ∀ s ∈ boot, s.touches f = false) →
    res.length = acc.length + l.length ∧
      ∀ f ∈ res, f.Nonempty ∧ f.OnPages ∧ ∀ s ∈ boot, s.touches f = false
  | [], acc, res, h, h1 => by
    simp only [List.foldlM_nil, except_pure_ok] at h
    subst h
    exact ⟨rfl, h1⟩
  | r :: l, acc, res, h, h1 => by
    rw [List.foldlM_cons] at h
    obtain ⟨acc', ha, h⟩ := except_bind_ok.1 h
    unfold addFirmware at ha
    obtain ⟨pages, hp, ha1⟩ := except_bind_ok.1 ha
    obtain ⟨hany, ha2⟩ := except_jp_ok ha1
    rw [except_pure_ok] at ha2
    subst ha2
    have hpg := pagesOf_ok hp
    simp only [Bool.not_eq_true, List.any_eq_false] at hany
    obtain ⟨r1, r2⟩ := addFirmware_fold boot l _ res h (by
      intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact h1 x hx
      · rw [List.mem_singleton] at hx
        subst hx
        exact ⟨hpg.1, hpg.2, fun s hs => by simpa using hany s hs⟩)
    refine ⟨by rw [r1]; simp; omega, r2⟩

/-! ## The entries -/

/-- The boot memory map of `MemoryPlan::all_ram` is well-formed. -/
theorem allRam_wellFormed {ram boot : List Span} {firmware : List ReservedRegion}
    {p : MemoryPlan} (h : MemoryPlan.allRam ram boot firmware = .ok p) : p.WellFormed := by
  unfold MemoryPlan.allRam at h
  obtain ⟨hcap, h⟩ := except_jp_ok h
  obtain ⟨banks0, hb0, h⟩ := except_bind_ok.1 h
  obtain ⟨⟨n', managed⟩, hadm, h⟩ := except_bind_ok.1 h
  obtain ⟨hme, h⟩ := except_jp_ok h
  obtain ⟨bootPages, hbp, h⟩ := except_bind_ok.1 h
  obtain ⟨fwPages, hfw, h⟩ := except_bind_ok.1 h
  rw [except_pure_ok] at h
  subst h
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, List.isEmpty_iff] at hcap
  obtain ⟨⟨⟨⟨hram, hramlen⟩, hboot⟩, hbootlen⟩, hfwlen⟩ := hcap
  obtain ⟨hb0eq, hb0p, hb0n⟩ := addBank_fold ram [] banks0 hb0 List.Pairwise.nil
  simp only [List.nil_append] at hb0eq
  subst hb0eq
  have hperm := sortByStart_perm banks0
  have hbn : ∀ b ∈ sortByStart banks0, b.Nonempty := fun b hb => hb0n b (hperm.mem_iff.1 hb)
  have hsorted := sortByStart_pairwise banks0 hb0n hb0p
  obtain ⟨hsum, hmax, hman⟩ := admitBank_fold _ _ _ hadm (Nat.zero_le _)
  simp only [List.nil_append] at hman
  simp only at hsum hmax hman
  subst hman
  simp only [List.isEmpty_iff] at hme
  obtain ⟨hbl, hbs, hbp⟩ := addBoot_fold (sortByStart banks0) boot [] bootPages hbp
    (by simp) List.Pairwise.nil
  obtain ⟨hfl, hfs⟩ := addFirmware_fold bootPages firmware [] fwPages hfw (by simp)
  refine ⟨?_, ?_, hbn, hsorted, ?_, hme, ?_, ?_, ?_, ?_, hbs, hbp, ?_, hfs⟩
  · intro h0
    simp only at h0
    have := hperm.length_eq
    rw [h0] at this
    exact hram (List.length_eq_zero_iff.1 this.symm)
  · rw [hperm.length_eq]
    exact Nat.le_of_not_lt hramlen
  · unfold spansBytes
    rw [← hsum]
    exact hmax
  · intro x hx
    obtain ⟨b, hb, hbx⟩ := List.mem_filterMap.1 hx
    obtain ⟨h1, h2, h3, h4⟩ := managedOf_spec (hbn b hb).2 hbx
    exact ⟨h1, h2, List.any_eq_true.2 ⟨b, hb, holds_iff.2 ⟨h3, h4⟩⟩⟩
  · rw [List.pairwise_filterMap]
    refine List.Pairwise.imp_of_mem ?_ hsorted
    intro a b ha hb hab x hx y hy
    obtain ⟨-, -, -, hx4⟩ := managedOf_spec (hbn a ha).2 hx
    obtain ⟨-, -, hy3, -⟩ := managedOf_spec (hbn b hb).2 hy
    exact Nat.le_trans hx4 (Nat.le_trans hab hy3)
  · intro h0
    simp only at h0
    rw [h0] at hbl
    simp only [List.length_nil, Nat.zero_add] at hbl
    exact hboot (List.length_eq_zero_iff.1 hbl.symm)
  · rw [hbl]
    simp only [List.length_nil, Nat.zero_add]
    exact Nat.le_of_not_lt hbootlen
  · rw [hfl]
    simp only [List.length_nil, Nat.zero_add]
    exact Nat.le_of_not_lt hfwlen

/-- The boot memory map of `MemoryPlan::new` is well-formed. -/
theorem new_wellFormed {window : Span} {ram boot : List Span} {firmware : List ReservedRegion}
    {p : MemoryPlan} (h : MemoryPlan.new window ram boot firmware = .ok p) : p.WellFormed := by
  unfold MemoryPlan.new at h
  obtain ⟨u, hu, h⟩ := except_bind_ok.1 h
  have hw := checkPlanSpan_ok hu
  obtain ⟨hal, h⟩ := except_jp_ok h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨plan, hplan, h⟩ := except_bind_ok.1 h
  obtain ⟨hin, h⟩ := except_jp_ok h
  rw [except_pure_ok] at h
  subst h
  have hwf := allRam_wellFormed hplan
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hal
  simp only [Bool.not_eq_true', Bool.not_eq_false] at hin
  unfold MemoryPlan.containsRam at hin
  simp only [Bool.and_eq_true] at hin
  obtain ⟨h1, h2, h3, h4, h5, -, -, -, h9, h10, h11, h12, h13, h14⟩ := hwf
  exact ⟨h1, h2, h3, h4, h5, List.cons_ne_nil _ _,
    fun s hs => by
      rw [List.mem_singleton] at hs
      subst hs
      exact ⟨hw, hal, hin.2⟩,
    List.pairwise_singleton _ _, h9, h10, h11, h12, h13, h14⟩

/-! ## The usable ranges -/

/-- The reservations that hold the cursor `c` of `usableFrom`. -/
def holdingOf (excl : List Span) (c : Nat) : List Span :=
  excl.filter fun r => r.start.toNat ≤ c && c < r.endNat

/-- The end of the usable range that starts at the cursor `c` of `usableFrom`. -/
def nextOf (excl : List Span) (stop c : Nat) : Nat :=
  excl.foldl (fun e r => if c < r.start.toNat then min e r.start.toNat else e) stop

/-- The furthest end of the reservations that hold the cursor `c`, or `c`. -/
def maxEndOf (excl : List Span) (c : Nat) : Nat :=
  (holdingOf excl c).foldl (fun e r => max e r.endNat) c

/-- One step of `usableFrom`, written with `holdingOf`, `nextOf` and `maxEndOf`. -/
theorem usableFrom_succ (excl : List Span) (stop fuel c : Nat) :
    usableFrom excl stop (fuel + 1) c =
      if stop ≤ c then []
      else if (holdingOf excl c).isEmpty then
        spanBetween c (nextOf excl stop c) :: usableFrom excl stop fuel (nextOf excl stop c)
      else usableFrom excl stop fuel (min stop (maxEndOf excl c)) := rfl

/-- The reservations that hold the cursor. -/
theorem mem_holdingOf {excl : List Span} {c : Nat} {x : Span} :
    x ∈ holdingOf excl c ↔ x ∈ excl ∧ x.start.toNat ≤ c ∧ c < x.endNat := by
  simp [holdingOf]

/-- No reservation holds a cursor whose `holdingOf` is empty. -/
theorem holdingOf_empty {excl : List Span} {c : Nat} (h : (holdingOf excl c).isEmpty = true) :
    ∀ x ∈ excl, ¬ (x.start.toNat ≤ c ∧ c < x.endNat) := by
  intro x hx hh
  rw [List.isEmpty_iff] at h
  have : x ∈ holdingOf excl c := mem_holdingOf.2 ⟨hx, hh⟩
  rw [h] at this
  exact List.not_mem_nil this

/-- Some reservation holds a cursor whose `holdingOf` is not empty. -/
theorem holdingOf_nonempty {excl : List Span} {c : Nat}
    (h : ¬ (holdingOf excl c).isEmpty = true) :
    ∃ y ∈ excl, y.start.toNat ≤ c ∧ c < y.endNat := by
  cases hh : holdingOf excl c with
  | nil => rw [hh] at h; exact absurd rfl h
  | cons y _ =>
    have hy : y ∈ holdingOf excl c := by rw [hh]; exact List.mem_cons_self
    exact ⟨y, (mem_holdingOf.1 hy).1, (mem_holdingOf.1 hy).2⟩

/-- The end of a usable range: at most the end of the bank and every start above
the cursor, and one of them. -/
theorem nextOf_spec (excl : List Span) (stop c : Nat) :
    nextOf excl stop c ≤ stop ∧
    (∀ x ∈ excl, c < x.start.toNat → nextOf excl stop c ≤ x.start.toNat) ∧
    (nextOf excl stop c = stop ∨
      ∃ x ∈ excl, c < x.start.toNat ∧ nextOf excl stop c = x.start.toNat) :=
  foldl_min_spec c excl stop

/-- The furthest end of the reservations that hold the cursor: at least the cursor
and each of their ends, and the cursor or one of their ends. -/
theorem maxEndOf_spec (excl : List Span) (c : Nat) :
    c ≤ maxEndOf excl c ∧
    (∀ x ∈ excl, x.start.toNat ≤ c → c < x.endNat → x.endNat ≤ maxEndOf excl c) ∧
    (maxEndOf excl c = c ∨ ∃ x ∈ excl, x.start.toNat ≤ c ∧ c < x.endNat ∧
      maxEndOf excl c = x.endNat) := by
  obtain ⟨h1, h2, h3⟩ := foldl_max_spec Span.endNat (holdingOf excl c) c
  refine ⟨h1, fun x hx hs he => h2 x (mem_holdingOf.2 ⟨hx, hs, he⟩), ?_⟩
  rcases h3 with h3 | ⟨x, hx, h3⟩
  · exact Or.inl h3
  · obtain ⟨hx1, hx2, hx3⟩ := mem_holdingOf.1 hx
    exact Or.inr ⟨x, hx1, hx2, hx3, h3⟩

/-- A usable range of `usableFrom` is a span from `t` to `n` within the bank, past
the cursor, that no reservation holds or reaches into; it starts at the cursor or
at the end of a reservation, and ends at the end of the bank or at the start of a
reservation. -/
theorem usableFrom_mem {excl : List Span} {stop : Nat} (hstop : stop < 2 ^ 64)
    (hne : ∀ x ∈ excl, x.start.toNat < x.endNat) :
    ∀ fuel c r, r ∈ usableFrom excl stop fuel c →
      ∃ t n, r = spanBetween t n ∧ c ≤ t ∧ t < n ∧ n ≤ stop ∧
        (∀ x ∈ excl, ¬ (x.start.toNat ≤ t ∧ t < x.endNat)) ∧
        (∀ x ∈ excl, t < x.start.toNat → n ≤ x.start.toNat) ∧
        (t = c ∨ ∃ x ∈ excl, x.endNat = t) ∧
        (n = stop ∨ ∃ x ∈ excl, x.start.toNat = n)
  | 0, c, r, h => by simp [usableFrom] at h
  | fuel + 1, c, r, h => by
    rw [usableFrom_succ] at h
    split at h
    · exact absurd h List.not_mem_nil
    · rename_i hcs
      split at h
      · rename_i hemp
        have hfree := holdingOf_empty hemp
        obtain ⟨hn1, hn2, hn3⟩ := nextOf_spec excl stop c
        have hcn : c < nextOf excl stop c := by
          rcases hn3 with h3 | ⟨x, -, hx, h3⟩ <;> omega
        rcases List.mem_cons.1 h with rfl | h
        · refine ⟨c, nextOf excl stop c, rfl, Nat.le_refl _, hcn, hn1, hfree, hn2, Or.inl rfl,
            ?_⟩
          rcases hn3 with h3 | ⟨x, hx, -, h3⟩
          · exact Or.inl h3
          · exact Or.inr ⟨x, hx, h3.symm⟩
        · obtain ⟨t, n, hr, h1, h2, h3, h4, h5, h6, h7⟩ := usableFrom_mem hstop hne fuel _ r h
          refine ⟨t, n, hr, by omega, h2, h3, h4, h5, ?_, h7⟩
          rcases h6 with h6 | h6
          · rcases hn3 with h8 | ⟨x, hx, -, h8⟩
            · omega
            · exact absurd ⟨by omega, by have := hne x hx; omega⟩ (h4 x hx)
          · exact Or.inr h6
      · rename_i hemp
        obtain ⟨hm1, hm2, hm3⟩ := maxEndOf_spec excl c
        obtain ⟨y, hy, hy1, hy2⟩ := holdingOf_nonempty hemp
        have hyM := hm2 y hy hy1 hy2
        obtain ⟨t, n, hr, h1, h2, h3, h4, h5, h6, h7⟩ :=
          usableFrom_mem hstop hne fuel (min stop (maxEndOf excl c)) r h
        have hmin : min stop (maxEndOf excl c) ≤ maxEndOf excl c := Nat.min_le_right _ _
        have hmin' : c ≤ min stop (maxEndOf excl c) := Nat.le_min.2 ⟨by omega, hm1⟩
        refine ⟨t, n, hr, Nat.le_trans hmin' h1, h2, h3, h4, h5, ?_, h7⟩
        rcases h6 with h6 | h6
        · have hst : min stop (maxEndOf excl c) = maxEndOf excl c := by
            rw [Nat.min_def]
            split <;> omega
          rcases hm3 with h8 | ⟨x, hx, _, _, h8⟩
          · omega
          · exact Or.inr ⟨x, hx, by omega⟩
        · exact Or.inr h6

/-- The usable ranges of `usableFrom` are in address order and disjoint. -/
theorem usableFrom_pairwise {excl : List Span} {stop : Nat} (hstop : stop < 2 ^ 64)
    (hne : ∀ x ∈ excl, x.start.toNat < x.endNat) :
    ∀ fuel c, (usableFrom excl stop fuel c).Pairwise (fun a b => a.endNat ≤ b.start.toNat)
  | 0, c => by simp [usableFrom]
  | fuel + 1, c => by
    rw [usableFrom_succ]
    split
    · exact List.Pairwise.nil
    · rename_i hcs
      split
      · obtain ⟨hn1, -, hn3⟩ := nextOf_spec excl stop c
        have hcn : c < nextOf excl stop c := by
          rcases hn3 with h3 | ⟨x, -, hx, h3⟩ <;> omega
        refine List.pairwise_cons.2 ⟨fun r hr => ?_, usableFrom_pairwise hstop hne fuel _⟩
        obtain ⟨t, n, rfl, h1, h2, h3, -⟩ := usableFrom_mem hstop hne fuel _ r hr
        obtain ⟨-, he, -⟩ := spanBetween_spec hcn (by omega)
        obtain ⟨hs, -, -⟩ := spanBetween_spec h2 (by omega)
        rw [he, hs]
        exact h1
      · exact usableFrom_pairwise hstop hne fuel _

/-- Every address from the cursor to the end of the bank that no reservation holds
lies in a usable range, when the fuel exceeds twice the reservations that end
after the cursor, plus one if none holds it. -/
theorem usableFrom_covers {excl : List Span} {stop a : Nat} (hstop : stop < 2 ^ 64)
    (hne : ∀ x ∈ excl, x.start.toNat < x.endNat)
    (ha : ∀ x ∈ excl, ¬ (x.start.toNat ≤ a ∧ a < x.endNat)) (has : a < stop) :
    ∀ fuel c, c ≤ a →
      2 * excl.countP (fun x => decide (c < x.endNat)) +
        (if (holdingOf excl c).isEmpty then 1 else 0) < fuel →
      ∃ r ∈ usableFrom excl stop fuel c, r.start.toNat ≤ a ∧ a < r.endNat
  | 0, _, _, hf => absurd hf (Nat.not_lt_zero _)
  | fuel + 1, c, hca, hf => by
    rw [usableFrom_succ, ite_eq_right (by omega : ¬ stop ≤ c)]
    by_cases hemp : (holdingOf excl c).isEmpty = true
    · rw [ite_eq_left hemp]
      rw [ite_eq_left hemp] at hf
      obtain ⟨hn1, hn2, hn3⟩ := nextOf_spec excl stop c
      have hcn : c < nextOf excl stop c := by
        rcases hn3 with h3 | ⟨x, -, hx, h3⟩ <;> omega
      by_cases han : a < nextOf excl stop c
      · obtain ⟨h1, h2, -⟩ := spanBetween_spec hcn (by omega)
        exact ⟨_, List.mem_cons_self, by rw [h1]; exact hca, by rw [h2]; exact han⟩
      · rcases hn3 with h3 | ⟨x, hx, hcx, h3⟩
        · omega
        · have hheld : ¬ (holdingOf excl (nextOf excl stop c)).isEmpty = true := by
            intro h0
            exact holdingOf_empty h0 x hx ⟨by omega, by have := hne x hx; omega⟩
          have hmono : excl.countP (fun x => decide (nextOf excl stop c < x.endNat)) ≤
              excl.countP (fun x => decide (c < x.endNat)) :=
            List.countP_mono_left (fun y _ hy => by
              simp only [decide_eq_true_eq] at hy ⊢
              omega)
          obtain ⟨r, hr, hr2⟩ := usableFrom_covers hstop hne ha has fuel (nextOf excl stop c)
            (by omega) (by rw [ite_eq_right hheld]; omega)
          exact ⟨r, List.mem_cons_of_mem _ hr, hr2⟩
    · rw [ite_eq_right hemp]
      rw [ite_eq_right hemp] at hf
      obtain ⟨hm1, hm2, hm3⟩ := maxEndOf_spec excl c
      obtain ⟨y, hy, hy1, hy2⟩ := holdingOf_nonempty hemp
      have hyM := hm2 y hy hy1 hy2
      have hMa : maxEndOf excl c ≤ a := by
        rcases hm3 with h3 | ⟨x, hx, hx1, hx2, h3⟩
        · omega
        · have := ha x hx
          omega
      have hlt : excl.countP (fun x => decide (min stop (maxEndOf excl c) < x.endNat)) <
          excl.countP (fun x => decide (c < x.endNat)) :=
        countP_lt (fun z _ hz => by
          simp only [decide_eq_true_eq] at hz ⊢
          omega) ⟨y, hy, by simp only [decide_eq_true_eq]; omega,
            by simp only [decide_eq_false_iff_not]; omega⟩
      have hst : min stop (maxEndOf excl c) = maxEndOf excl c := by
        rw [Nat.min_def]
        split <;> omega
      obtain ⟨r, hr, hr2⟩ := usableFrom_covers hstop hne ha has fuel
        (min stop (maxEndOf excl c)) (by omega) (by split <;> omega)
      exact ⟨r, hr, hr2⟩

/-- The reservations of a well-formed boot memory map are nonempty and on pages. -/
theorem reservations_wf {p : MemoryPlan} (hp : p.WellFormed) :
    ∀ x ∈ p.reservations, x.Nonempty ∧ x.OnPages := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hboot, -, -, hfw⟩ := hp
  intro x hx
  rcases List.mem_append.1 hx with hx | hx
  · exact ⟨(hboot x hx).1, (hboot x hx).2.1⟩
  · exact ⟨(hfw x hx).1, (hfw x hx).2.1⟩

/-- A usable range of a well-formed boot memory map, from the managed bank that
holds it. -/
theorem availableRanges_mem {p : MemoryPlan} (hp : p.WellFormed) {r : Span}
    (hr : r ∈ p.availableRanges) :
    ∃ b ∈ p.managed, ∃ t n, r = spanBetween t n ∧ b.start.toNat ≤ t ∧ t < n ∧
      n ≤ b.endNat ∧ n < 2 ^ 64 ∧
      (∀ x ∈ p.reservations, ¬ (x.start.toNat ≤ t ∧ t < x.endNat)) ∧
      (∀ x ∈ p.reservations, t < x.start.toNat → n ≤ x.start.toNat) ∧
      (t = b.start.toNat ∨ ∃ x ∈ p.reservations, x.endNat = t) ∧
      (n = b.endNat ∨ ∃ x ∈ p.reservations, x.start.toNat = n) := by
  have hres := reservations_wf hp
  obtain ⟨-, -, -, -, -, -, hman, -⟩ := hp
  unfold MemoryPlan.availableRanges at hr
  obtain ⟨b, hb, hr⟩ := List.mem_flatMap.1 hr
  have hbv := (hman b hb).1.2
  unfold Span.Valid at hbv
  obtain ⟨t, n, h0, h1, h2, h3, h4, h5, h6, h7⟩ :=
    usableFrom_mem hbv (fun x hx => nonempty_lt (hres x hx).1) _ _ r hr
  exact ⟨b, hb, t, n, h0, h1, h2, h3, by omega, h4, h5, h6, h7⟩

end Krepi.Proofs.Fdt
