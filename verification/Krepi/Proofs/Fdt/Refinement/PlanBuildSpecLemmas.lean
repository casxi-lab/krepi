module

public import Krepi.Proofs.Fdt.PlanLemmas
public import Krepi.Proofs.Fdt.ExceptLemmas

/-!
# Device tree: lemmas about the construction of a boot memory map

Lemmas about the entries `MemoryPlan.allRam` and `MemoryPlan.new` of
`Krepi.Spec.Fdt.Plan`, for the refinement proofs of `MemoryPlan::all_ram`,
`new` and `from_boot_memory`. The module imports no generated definitions,
so it is built once and not again for every mutant of the code.

- Pages: `land_mask`, the `&&&` with all ones but the low bits as a rounding
  down.
- Sorting: `eq_of_perm_of_lt` (two lists with the same items, each strictly
  increasing by a key, are equal) and `map_eq_sortByStart` (a list with the
  items of nonempty spans no two of which touch, sorted by their start, is
  `sortByStart` of them), so that the insertion sort of the code, which
  inserts from the left, gives the banks of the specification, which inserts
  from the right; the steps of an insertion: `set_swap`,
  `pairwise_insert_between` and `le_of_take`.
- Lists of the arrays: `getElem_of_append_cons` and `take_succ_set`.
- Folds from a position, the invariants of the loops: `foldlM_drop_step` and
  `foldlM_drop_end`.
- The steps of the entries: `addBank_of_check`, `addBank_of_error`,
  `admitBank_eq`, `addBoot_of_pages`, `addBoot_of_error`,
  `addFirmware_of_pages` and `addFirmware_of_error`; the entries as chains of
  binds: `capacity_iff`, `allRam_eq`, `allRam_of_boot_gt` (more than four
  spans of boot storage, `Capacity`), `windowCheck` (the window of
  `MemoryPlan.new`) and `new_eq`.
-/

@[expose] public section

open Krepi.Spec.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## Pages -/

/-- The `&&&` of a number of `w` bits with all ones but the `k` low bits
rounds it down to a multiple of `2 ^ k`. -/
theorem land_mask {x w k : Nat} (hk : k ≤ w) (hx : x < 2 ^ w) :
    x &&& (2 ^ w - 1 - (2 ^ k - 1)) = x / 2 ^ k * 2 ^ k := by
  have e1 : 2 ^ w - 1 - (2 ^ k - 1) = (2 ^ (w - k) - 1) <<< k := by
    have : 2 ^ w = 2 ^ (w - k) * 2 ^ k := by
      rw [← Nat.pow_add, Nat.sub_add_cancel hk]
    have h1 : 1 ≤ 2 ^ (w - k) := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    rw [Nat.shiftLeft_eq, this, Nat.sub_mul, Nat.one_mul]
    omega
  have e2 : x / 2 ^ k * 2 ^ k = (x >>> k) <<< k := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [e1, e2]
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : k ≤ i
  · rw [show k + (i - k) = i by omega]
    by_cases hiw : i < w
    · simp [hi, show i - k < w - k by omega]
    · have : x.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
      simp [this]
  · simp [hi]

/-! ## Sorting -/

/-- Two lists with the same items, each strictly increasing by a key, are
equal. -/
theorem eq_of_perm_of_lt {α : Type} (k : α → Nat) :
    ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.Pairwise (fun a b => k a < k b) →
      l₂.Pairwise (fun a b => k a < k b) → l₁ = l₂
  | [], l₂, hp, _, _ => List.Perm.nil_eq hp
  | a :: t₁, [], hp, _, _ => absurd hp.length_eq (by simp)
  | a :: t₁, b :: t₂, hp, h₁, h₂ => by
    rw [List.pairwise_cons] at h₁ h₂
    have hab : a = b := by
      have ha : a ∈ b :: t₂ := hp.mem_iff.1 List.mem_cons_self
      have hb : b ∈ a :: t₁ := hp.mem_iff.2 List.mem_cons_self
      rcases List.mem_cons.1 ha with ha | ha
      · exact ha
      · rcases List.mem_cons.1 hb with hb | hb
        · exact hb.symm
        · exact absurd (h₁.1 b hb) (Nat.lt_asymm (h₂.1 a ha))
    subst hab
    rw [eq_of_perm_of_lt k (hp.cons_inv) h₁.2 h₂.2]

/-- The spans of a list with the items of a list of nonempty spans no two of
which touch, sorted by their start, are those of `sortByStart`. -/
theorem map_eq_sortByStart {α : Type} (f : α → Span) {L L' : List α} (hp : L'.Perm L)
    (hs : L'.Pairwise (fun x y => (f x).start.toNat ≤ (f y).start.toNat))
    (hn : ∀ b ∈ L.map f, b.Nonempty)
    (ht : (L.map f).Pairwise (fun a b => a.touches b = false)) :
    L'.map f = sortByStart (L.map f) := by
  have hp' : (L'.map f).Perm (L.map f) := hp.map f
  have hne : (L.map f).Pairwise (fun a b => a.start.toNat ≠ b.start.toNat) := by
    refine List.Pairwise.imp_of_mem ?_ ht
    intro a b ha hb hab
    have h1 := touches_false (hn a ha) (hn b hb) hab
    have h2 := nonempty_lt (hn a ha)
    have h3 := nonempty_lt (hn b hb)
    omega
  have hne' : (L'.map f).Pairwise (fun a b => a.start.toNat ≠ b.start.toNat) :=
    (hp'.pairwise_iff (fun h => Ne.symm h)).2 hne
  apply eq_of_perm_of_lt (fun s : Span => s.start.toNat) (hp'.trans (sortByStart_perm _).symm)
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ (hs.and ((List.pairwise_map).1 hne'))
    intro a b _ _ h
    exact Nat.lt_of_le_of_ne h.1 h.2
  · refine List.Pairwise.imp_of_mem ?_ (sortByStart_pairwise _ hn ht)
    intro a b ha _ h
    have := nonempty_lt (hn a ((sortByStart_perm _).mem_iff.1 ha))
    exact Nat.lt_of_lt_of_le this h

/-- The swap of two neighbours of a list by two writes. -/
theorem set_swap {α : Type} (A R : List α) (x y : α) :
    ((A ++ y :: x :: R).set (A.length + 1) y).set A.length x = A ++ x :: y :: R := by
  induction A with
  | nil => rfl
  | cons a A ih => simp only [List.cons_append, List.length_cons, List.set_cons_succ, ih]

/-- An item put between the items of a sorted list that are not above it and
those that are above it keeps the list sorted. -/
theorem pairwise_insert_between {α : Type} (k : α → Nat) {A B : List α} {x : α}
    (hAB : (A ++ B).Pairwise (fun a b => k a ≤ k b)) (hA : ∀ a ∈ A, k a ≤ k x)
    (hB : ∀ b ∈ B, k x < k b) : (A ++ x :: B).Pairwise (fun a b => k a ≤ k b) := by
  rw [List.pairwise_append] at hAB ⊢
  refine ⟨hAB.1, List.pairwise_cons.2 ⟨fun b hb => Nat.le_of_lt (hB b hb), hAB.2.1⟩, ?_⟩
  intro a ha b hb
  rcases List.mem_cons.1 hb with rfl | hb
  · exact hA a ha
  · exact hAB.2.2 a ha b hb

/-- In a sorted list, every item before the one at `j` is not above it. -/
theorem le_of_take {α : Type} (k : α → Nat) {L : List α}
    (hL : L.Pairwise (fun a b => k a ≤ k b)) {j : Nat} (hj : j < L.length) :
    ∀ a ∈ L.take (j + 1), k a ≤ k L[j] := by
  intro a ha
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some] at ha
  rcases List.mem_append.1 ha with ha | ha
  · have hp := List.pairwise_append.1 (show (L.take j ++ L.drop j).Pairwise _ by
      rw [List.take_append_drop]; exact hL)
    exact hp.2.2 a ha L[j] (by rw [List.drop_eq_getElem_cons hj]; exact List.mem_cons_self)
  · rw [List.mem_singleton] at ha; subst ha; exact Nat.le_refl _

/-- The capacity condition of `MemoryPlan.allRam` as numbers. -/
theorem capacity_iff (ram boot : List Span) (firmware : List ReservedRegion) :
    ((ram.isEmpty || MemoryPlan.MAX_BANKS < ram.length || boot.isEmpty ||
        MemoryPlan.MAX_BOOT_SPANS < boot.length ||
        MemoryPlan.MAX_FIRMWARE < firmware.length) = true) ↔
      (ram.length = 0 ∨ 32 < ram.length ∨ boot.length = 0 ∨ 4 < boot.length ∨
        128 < firmware.length) := by
  simp only [Bool.or_eq_true, List.isEmpty_iff_length_eq_zero, decide_eq_true_eq, or_assoc]
  exact Iff.rfl

/-! ## Lists of the arrays -/

/-- The item of a list at the length of a prefix. -/
theorem getElem_of_append_cons {α : Type} {l A R : List α} {y : α} (h : l = A ++ y :: R)
    {i : Nat} (hi : i = A.length) (hil : i < l.length) : l[i] = y := by
  subst h; subst hi; simp

/-- The prefix of a list up to a written position. -/
theorem take_succ_set {α : Type} {l : List α} {i : Nat} (hi : i < l.length) (x : α) :
    (l.set i x).take (i + 1) = l.take i ++ [x] := by
  rw [List.take_add_one, List.getElem?_set_self (by exact hi), Option.toList_some,
    List.take_set_of_le (Nat.le_refl i)]

/-! ## Folds from a position -/

section Folds

variable {α β ε : Type} {f : β → α → Except ε β}

/-- A fold from a position below the length: one step and the fold from the next
position. -/
theorem foldlM_drop_step {L : List α} {i : Nat} (hi : i < L.length) (acc : β) :
    (L.drop i).foldlM f acc = f acc L[i] >>= fun a => (L.drop (i + 1)).foldlM f a := by
  rw [List.drop_eq_getElem_cons hi, List.foldlM_cons]

/-- A fold from a position past the end: the accumulator. -/
theorem foldlM_drop_end {L : List α} {i : Nat} (hi : L.length ≤ i) (acc : β) :
    (L.drop i).foldlM f acc = .ok acc := by
  rw [List.drop_eq_nil_of_le hi, List.foldlM_nil]; rfl

end Folds

/-! ## Steps of the entries -/

/-- `addBank` of a span that `checkPlanSpan` accepts. -/
theorem addBank_of_check {acc : List Span} {s : Span} {u : Unit} (h : checkPlanSpan s = .ok u) :
    addBank acc s = if acc.any (·.touches s) then .error .overlap else .ok (acc ++ [s]) := by
  unfold addBank; rw [h]; rfl

/-- `addBank` of a span that `checkPlanSpan` refuses. -/
theorem addBank_of_error {acc : List Span} {s : Span} {e : PlanError}
    (h : checkPlanSpan s = .error e) :
    addBank acc s = .error e := by
  unfold addBank; rw [h]; rfl

/-- `admitBank` as a choice of its outcomes. -/
theorem admitBank_eq (acc : Nat × List Span) (b : Span) :
    admitBank acc b =
      if 2 ^ 64 ≤ acc.1 + b.size.toNat then .error .overflow
      else if MemoryPlan.MAX_RAM_BYTES < acc.1 + b.size.toNat then .error .arenaTooLarge
      else if 2 ^ 64 ≤ (b.start.toNat + 4096 - 1) / 4096 * 4096 then .error .overflow
      else .ok (acc.1 + b.size.toNat,
        if (b.start.toNat + 4096 - 1) / 4096 * 4096 < b.endNat / 4096 * 4096 then
          acc.2 ++ [spanBetween ((b.start.toNat + 4096 - 1) / 4096 * 4096) (b.endNat / 4096 * 4096)]
        else acc.2) := rfl

/-- `addBoot` of a span whose pages are `p`. -/
theorem addBoot_of_pages {banks boot : List Span} {s p : Span} (h : pagesOf s = .ok p) :
    addBoot banks boot s =
      if (!inOneRange banks p) = true then .error .outsideRam
      else if boot.any (·.touches p) then .error .overlap else .ok (boot ++ [p]) := by
  unfold addBoot; rw [h]; rfl

/-- `addBoot` of a span whose pages are refused. -/
theorem addBoot_of_error {banks boot : List Span} {s : Span} {e : PlanError}
    (h : pagesOf s = .error e) : addBoot banks boot s = .error e := by
  unfold addBoot; rw [h]; rfl

/-- `addFirmware` of a reservation whose pages are `p`. -/
theorem addFirmware_of_pages {boot fw : List Span} {r : ReservedRegion} {p : Span}
    (h : pagesOf r.span = .ok p) :
    addFirmware boot fw r =
      if boot.any (·.touches p) then .error .overlap else .ok (fw ++ [p]) := by
  unfold addFirmware; rw [h]; rfl

/-- `addFirmware` of a reservation whose pages are refused. -/
theorem addFirmware_of_error {boot fw : List Span} {r : ReservedRegion} {e : PlanError}
    (h : pagesOf r.span = .error e) : addFirmware boot fw r = .error e := by
  unfold addFirmware; rw [h]; rfl

/-- `MemoryPlan.allRam` as a chain of binds, one for each step of the code. -/
theorem allRam_eq (ram boot : List Span) (firmware : List ReservedRegion) :
    MemoryPlan.allRam ram boot firmware =
      if (ram.isEmpty || MemoryPlan.MAX_BANKS < ram.length || boot.isEmpty ||
          MemoryPlan.MAX_BOOT_SPANS < boot.length ||
          MemoryPlan.MAX_FIRMWARE < firmware.length) = true
      then .error .capacity
      else ram.foldlM addBank [] >>= fun b0 =>
        (sortByStart b0).foldlM admitBank (0, []) >>= fun acc =>
          if acc.2.isEmpty then .error .alignment
          else boot.foldlM (addBoot (sortByStart b0)) [] >>= fun bp =>
            firmware.foldlM (addFirmware bp) [] >>= fun fp =>
              .ok { ram := sortByStart b0, managed := acc.2, boot := bp, firmware := fp } := by
  unfold MemoryPlan.allRam
  rfl

/-- `MemoryPlan.allRam` with more than four spans of boot storage: `Capacity`. -/
theorem allRam_of_boot_gt (ram boot : List Span) (firmware : List ReservedRegion)
    (h : 4 < boot.length) : MemoryPlan.allRam ram boot firmware = .error .capacity := by
  have hc := (capacity_iff ram boot firmware).2 (Or.inr (Or.inr (Or.inr (Or.inl h))))
  rw [allRam_eq]
  simp only [hc, ↓reduceIte]

/-- Step 1 of the error order of the boot memory map, the first three rules of
`MemoryPlan.new`: the window (`checkPlanSpan`), its ends on pages and its size. -/
def windowCheck (window : Span) : Except PlanError Unit :=
  checkPlanSpan window >>= fun _ =>
    if window.start.toNat % MemoryPlan.PAGE_SIZE != 0 || window.endNat % MemoryPlan.PAGE_SIZE != 0
    then .error .alignment
    else if MemoryPlan.MAX_WINDOW_BYTES < window.size.toNat then .error .arenaTooLarge
    else .ok ()

/-- `MemoryPlan.new` as the window, then `MemoryPlan.allRam`, then the window
inside one bank. -/
theorem new_eq (window : Span) (ram boot : List Span) (firmware : List ReservedRegion) :
    MemoryPlan.new window ram boot firmware =
      windowCheck window >>= fun _ => MemoryPlan.allRam ram boot firmware >>= fun plan =>
        if plan.containsRam window = false then .error .outsideRam
        else .ok { plan with managed := [window] } := by
  unfold MemoryPlan.new windowCheck
  cases checkPlanSpan window with
  | error e => rfl
  | ok u =>
    simp only [except_ok_bind]
    split
    · rfl
    · split
      · rfl
      · simp only [except_ok_bind]
        congr
        funext plan
        cases plan.containsRam window <;> rfl

end Krepi.Proofs.Fdt.Refinement
