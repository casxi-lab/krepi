module

public import Krepi.SpecProperties.PageTables.Properties
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.OwnerLemmas
import Krepi.Proofs.PageTables.WriteLemmas

/-!
# Page tables: lemmas about the placement of `choose`

What the placement of `Ownership::choose` gives, extent by extent and over
its scan, against the ranges that an extent holds and gives a request
(`Extent.Holds`, `Extent.Gives`):

- one extent: `extent_holds_iff` (an extent holds a range exactly when the
  range is of the request, aligned and inside the part of the extent in the
  window, `Placement.part`), `fit_gives` (the range that `fit` finds in a free
  extent is the one that the extent gives), `fit_none` (when `fit` finds none,
  the extent holds no range of the request) and `fit_high_ne_overflow` (a
  high placement never overflows); privately, `fit_spec` (the same on
  numbers, from the rounding of `alignUp` and `alignDown`) and
  `gives_unique` (an extent gives at most one range);
- the scan: `Passed` (an extent that the scan passes over: held, without a
  range, or with one that needs more extents than the capacity has free),
  `passed_gives` (every range that such an extent gives needs more extents
  than the capacity has free), `scan_ok` (the extent where the scan finds its
  range, and that every extent before it was passed over) and `scan_error`
  (`AddressOverflow` from an extent where `fit` overflows; otherwise every
  extent was passed over, `OutOfMemory` when none had a range and
  `MetadataExhausted` when one had);
- `choose`: `mem_scanOrder` (the scan order has the extents of the table),
  `choose_error` (the error of a refused request: one of the first checks, or
  that of the scan) and `choose_extent` (a choice lies inside a free extent
  of the table, with the room that taking it needs).
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables Krepi.SpecProperties.PageTables

/-! ## Rounding -/

private theorem alignUp_le {lo a s : Nat} (ha : 0 < a) (hs : s % a = 0) (hl : lo ≤ s) :
    alignUp lo a ≤ s := by
  unfold alignUp
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero hs
  have : (lo + a - 1) / a < k + 1 := by
    rw [Nat.div_lt_iff_lt_mul ha, Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    omega
  calc (lo + a - 1) / a * a ≤ k * a := Nat.mul_le_mul_right _ (by omega)
    _ = a * k := Nat.mul_comm _ _

private theorem le_alignUp (lo a : Nat) (ha : 0 < a) : lo ≤ alignUp lo a := by
  unfold alignUp
  have h1 := Nat.div_add_mod (lo + a - 1) a
  have h2 := Nat.mod_lt (lo + a - 1) ha
  rw [Nat.mul_comm] at h1
  omega

private theorem alignUp_mod (lo a : Nat) : alignUp lo a % a = 0 := Nat.mul_mod_left _ _

private theorem le_alignDown {x a s : Nat} (ha : 0 < a) (hs : s % a = 0) (hl : s ≤ x) :
    s ≤ alignDown x a := by
  unfold alignDown
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero hs
  have : k ≤ x / a := (Nat.le_div_iff_mul_le ha).2 (by rw [Nat.mul_comm]; exact hl)
  calc a * k = k * a := Nat.mul_comm _ _
    _ ≤ x / a * a := Nat.mul_le_mul_right _ this

private theorem alignDown_le (x a : Nat) : alignDown x a ≤ x := Nat.div_mul_le_self _ _

private theorem alignDown_mod (x a : Nat) : alignDown x a % a = 0 := Nat.mul_mod_left _ _

/-! ## One extent -/

/-- What `fit` gives, on numbers: a range of the request at an aligned start
inside `[lo, hi)`, the lowest for a low placement and the highest for a high
one; and none only when no aligned start has its range inside. -/
private theorem fit_spec {d : Direction} {lo hi bytes align : Nat} (hb : 0 < bytes) (ha : 0 < align)
    (hhi : hi < 2 ^ 64) :
    (∀ r, fit d lo hi bytes align = .range r →
      (r.start.toNat % align = 0 ∧ lo ≤ r.start.toNat ∧ r.endNat = r.start.toNat + bytes ∧
        r.start.toNat + bytes ≤ hi) ∧
      ∀ s, s % align = 0 → lo ≤ s → s + bytes ≤ hi →
        (d = .low → r.start.toNat ≤ s) ∧ (d = .high → s ≤ r.start.toNat)) ∧
    (fit d lo hi bytes align = .none → ∀ s, s % align = 0 → lo ≤ s → s + bytes ≤ hi → False) := by
  unfold fit
  by_cases hlh : hi ≤ lo
  · simp only [hlh, ↓reduceIte, reduceCtorEq, false_implies, implies_true, true_and]
    intro _ s _ h1 h2; omega
  simp only [hlh, ↓reduceIte]
  cases d with
  | low =>
    dsimp only
    have hle := le_alignUp lo align ha
    have hmod := alignUp_mod lo align
    by_cases hov : 2 ^ 64 ≤ alignUp lo align + bytes
    · simp [hov]
    simp only [hov, ↓reduceIte]
    obtain ⟨r, hr, h1, h2⟩ := rangeOf?_exists (s := alignUp lo align) (l := bytes) hb (by omega)
    rw [hr]
    dsimp only
    by_cases hfit : alignUp lo align + bytes ≤ hi
    · simp only [hfit, ↓reduceIte, Fit.range.injEq, reduceCtorEq, false_implies, and_true]
      rintro _ rfl
      refine ⟨⟨by rw [h1]; exact hmod, by omega, by rw [h1, h2], by omega⟩, fun s hs hl _ => ?_⟩
      rw [h1]; exact fun _ => alignUp_le ha hs hl
    · simp only [hfit, ↓reduceIte, reduceCtorEq, false_implies, implies_true, true_and]
      intro _ s hs hl hh
      have := alignUp_le ha hs hl
      omega
  | high =>
    dsimp only
    by_cases hb' : hi < bytes
    · simp only [hb', ↓reduceIte, reduceCtorEq, false_implies, implies_true, true_and]
      intro _ s _ _ h; omega
    simp only [hb', ↓reduceIte]
    have hle := alignDown_le (hi - bytes) align
    have hmod := alignDown_mod (hi - bytes) align
    obtain ⟨r, hr, h1, h2⟩ := rangeOf?_exists (s := alignDown (hi - bytes) align) (l := bytes) hb
      (by omega)
    rw [hr]
    dsimp only
    by_cases hlo : lo ≤ alignDown (hi - bytes) align
    · simp only [hlo, ↓reduceIte, Fit.range.injEq, reduceCtorEq, false_implies, and_true]
      rintro _ rfl
      refine ⟨⟨by rw [h1]; exact hmod, by omega, by rw [h1, h2], by omega⟩, fun s hs _ hh => ?_⟩
      rw [h1]; exact ⟨trivial, fun _ => le_alignDown ha hs (by omega)⟩
    · simp only [hlo, ↓reduceIte, reduceCtorEq, false_implies, implies_true, true_and]
      intro _ s hs hl hh
      have := le_alignDown ha hs (show s ≤ hi - bytes by omega)
      omega

/-- `fit` of a high placement never overflows: the start that it rounds down
lies below the end of the part. -/
theorem fit_high_ne_overflow (lo hi bytes align : Nat) : fit .high lo hi bytes align ≠ .overflow := by
  unfold fit
  split
  · exact nofun
  dsimp only
  split
  · exact nofun
  split
  · split <;> exact nofun
  · exact nofun

private theorem part_bounds (p : Placement) (r : PhysRange) :
    r.start.toNat ≤ (p.part r).1 ∧ (p.part r).2 ≤ r.endNat := by
  unfold Placement.part
  split <;> simp only [Nat.le_refl, and_self, Nat.le_max_left, Nat.min_le_left]

/-- An extent holds a range of a request exactly when it is free and the range
is of the bytes of the request, at an aligned start, inside the part of the
extent in the window. -/
theorem extent_holds_iff {e : Extent} {pages alignment : UInt64} {p : Placement} {r : PhysRange} :
    e.Holds pages alignment p r ↔ e.holding = .free ∧
      r.start.toNat % (alignment.toNat * PAGE_SIZE) = 0 ∧ (p.part e.range).1 ≤ r.start.toNat ∧
      r.endNat = r.start.toNat + pages.toNat * PAGE_SIZE ∧
      r.start.toNat + pages.toNat * PAGE_SIZE ≤ (p.part e.range).2 := by
  unfold Extent.Holds Placement.part
  have hr : r.endNat = r.start.toNat + r.len.toNat := rfl
  cases hw : p.window with
  | none =>
    simp only [PhysRange.contains, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq,
      false_implies, implies_true, and_true]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, h3, h4, by omega, by omega⟩
    · rintro ⟨h1, h2, h3, h4, h5⟩; exact ⟨h1, by omega, h2, h3, by omega⟩
  | some w =>
    simp only [PhysRange.contains, Bool.and_eq_true, decide_eq_true_eq, Option.some.injEq,
      forall_eq', Nat.max_le, Nat.le_min]
    constructor
    · rintro ⟨h1, h2, h3, ⟨h4, h5⟩, h6, h7⟩; exact ⟨h1, h3, ⟨h4, h6⟩, by omega, by omega, by omega⟩
    · rintro ⟨h1, h2, ⟨h3, h4⟩, h5, h6, h7⟩; exact ⟨h1, by omega, h2, ⟨h3, by omega⟩, h4, by omega⟩

private theorem align_pos {alignment : UInt64} (h : isPowerOfTwo alignment.toNat = true) :
    0 < alignment.toNat * PAGE_SIZE := by
  unfold isPowerOfTwo at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  have := h.1
  simp only [PAGE_SIZE]
  omega

private theorem bytes_pos {pages : UInt64} (h : pages ≠ 0) : 0 < pages.toNat * PAGE_SIZE := by
  have : pages.toNat ≠ 0 := fun h0 => h (UInt64.toNat_inj.1 (by simpa using h0))
  simp only [PAGE_SIZE]
  omega

/-- The range that `fit` finds in a free extent is the one that the extent
gives the request. -/
theorem fit_gives {e : Extent} {pages alignment : UInt64} {p : Placement} {r : PhysRange}
    (hf : e.holding = .free) (hpg : pages ≠ 0) (hal : isPowerOfTwo alignment.toNat = true)
    (h : fit p.direction (p.part e.range).1 (p.part e.range).2 (pages.toNat * PAGE_SIZE)
      (alignment.toNat * PAGE_SIZE) = .range r) :
    e.Gives pages alignment p r := by
  have hhi : (p.part e.range).2 < 2 ^ 64 := by
    have := (part_bounds p e.range).2; have := e.range.fits; unfold PhysRange.endNat at *; omega
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := (fit_spec (bytes_pos hpg) (align_pos hal) hhi).1 r h
  refine ⟨extent_holds_iff.2 ⟨hf, h1, h2, h3, h4⟩, fun r' hr' => ?_⟩
  obtain ⟨-, h1', h2', -, h4'⟩ := extent_holds_iff.1 hr'
  have := h5 _ h1' h2' h4'
  split
  · exact this.1 ‹_›
  · exact this.2 ‹_›

/-- When `fit` finds no range in an extent, the extent holds none of the
request. -/
theorem fit_none {e : Extent} {pages alignment : UInt64} {p : Placement}
    (hpg : pages ≠ 0) (hal : isPowerOfTwo alignment.toNat = true)
    (h : fit p.direction (p.part e.range).1 (p.part e.range).2 (pages.toNat * PAGE_SIZE)
      (alignment.toNat * PAGE_SIZE) = .none) (r : PhysRange) :
    ¬ e.Holds pages alignment p r := by
  have hhi : (p.part e.range).2 < 2 ^ 64 := by
    have := (part_bounds p e.range).2; have := e.range.fits; unfold PhysRange.endNat at *; omega
  intro hr
  obtain ⟨-, h1, h2, -, h4⟩ := extent_holds_iff.1 hr
  exact (fit_spec (bytes_pos hpg) (align_pos hal) hhi).2 h _ h1 h2 h4

private theorem gives_unique {e : Extent} {pages alignment : UInt64} {p : Placement} {r r' : PhysRange}
    (h : e.Gives pages alignment p r) (h' : e.Gives pages alignment p r') : r = r' := by
  have a := h.2 r' h'.1
  have b := h'.2 r h.1
  have hr := (extent_holds_iff.1 h.1).2.2.2.1
  have hr' := (extent_holds_iff.1 h'.1).2.2.2.1
  have hs : r.start.toNat = r'.start.toNat := by
    split at a <;> split at b <;> first | omega | (rename_i h1 _ h2; rw [h1] at h2; cases h2)
  exact range_eq hs (by omega)

/-! ## The scan -/

/-- An extent that the scan of `choose` passes over: held, without a range of
the request, or with one that needs more extents than the capacity has
free. -/
def Passed (room bytes align : Nat) (p : Placement) (e : Extent) : Prop :=
  e.holding ≠ .free ∨ fit p.direction (p.part e.range).1 (p.part e.range).2 bytes align = .none ∨
    ∃ r, fit p.direction (p.part e.range).1 (p.part e.range).2 bytes align = .range r ∧
      room < e.extra r

/-- Every range that an extent passed over gives needs more extents than the
capacity has free. -/
theorem passed_gives {room : Nat} {e : Extent} {pages alignment : UInt64} {p : Placement}
    (hpg : pages ≠ 0) (hal : isPowerOfTwo alignment.toNat = true)
    (h : Passed room (pages.toNat * PAGE_SIZE) (alignment.toNat * PAGE_SIZE) p e) {r : PhysRange}
    (hr : e.Gives pages alignment p r) : room < e.extra r := by
  rcases h with h | h | ⟨r', h1, h2⟩
  · exact absurd (extent_holds_iff.1 hr.1).1 h
  · exact absurd hr.1 (fit_none hpg hal h r)
  · have := gives_unique (fit_gives (extent_holds_iff.1 hr.1).1 hpg hal h1) hr
    subst this; exact h2

/-- The scan that finds a range: the extent where it finds it, within the room,
and every extent before it passed over. -/
theorem scan_ok {room bytes align : Nat} {p : Placement} :
    ∀ {l : List Extent} {limited : Bool} {r : PhysRange},
      scan room bytes align p l limited = .ok r →
      ∃ i e, l[i]? = some e ∧ e.holding = .free ∧
        fit p.direction (p.part e.range).1 (p.part e.range).2 bytes align = .range r ∧
        e.extra r ≤ room ∧ ∀ e' ∈ l.take i, Passed room bytes align p e'
  | [], limited, r, h => by unfold scan at h; exact absurd h (by simp)
  | e :: rest, limited, r, h => by
    unfold scan at h
    split at h
    · rename_i hh
      obtain ⟨i, e', h1, h2, h3, h4, h5⟩ := scan_ok h
      refine ⟨i + 1, e', by simpa using h1, h2, h3, h4, fun e'' he'' => ?_⟩
      rcases List.mem_cons.1 (by simpa using he'') with rfl | he''
      · exact Or.inl (by rw [hh]; exact nofun)
      · exact h5 _ he''
    · rename_i hh
      dsimp only at h
      split at h
      · rename_i hfit
        obtain ⟨i, e', h1, h2, h3, h4, h5⟩ := scan_ok h
        refine ⟨i + 1, e', by simpa using h1, h2, h3, h4, fun e'' he'' => ?_⟩
        rcases List.mem_cons.1 (by simpa using he'') with rfl | he''
        · exact Or.inr (Or.inl hfit)
        · exact h5 _ he''
      · exact absurd h (by simp)
      · rename_i r' hfit
        split at h
        · rename_i hroom
          obtain ⟨i, e', h1, h2, h3, h4, h5⟩ := scan_ok h
          refine ⟨i + 1, e', by simpa using h1, h2, h3, h4, fun e'' he'' => ?_⟩
          rcases List.mem_cons.1 (by simpa using he'') with rfl | he''
          · exact Or.inr (Or.inr ⟨r', hfit, hroom⟩)
          · exact h5 _ he''
        · rename_i hroom
          cases h
          exact ⟨0, e, rfl, hh, hfit, by omega, by simp⟩

/-- The scan that fails: `AddressOverflow` from a free extent where `fit`
overflows; otherwise every extent was passed over, with `OutOfMemory` when
none gave a range and `MetadataExhausted` when one did. -/
theorem scan_error {room bytes align : Nat} {p : Placement} :
    ∀ {l : List Extent} {limited : Bool} {err : OwnershipError},
      scan room bytes align p l limited = .error err →
      (err = .addressOverflow ∧ ∃ e ∈ l, e.holding = .free ∧
          fit p.direction (p.part e.range).1 (p.part e.range).2 bytes align = .overflow) ∨
      ((∀ e ∈ l, Passed room bytes align p e) ∧
        ((err = .outOfMemory ∧ limited = false ∧ ∀ e ∈ l, e.holding ≠ .free ∨
            fit p.direction (p.part e.range).1 (p.part e.range).2 bytes align = .none) ∨
          (err = .metadataExhausted ∧ (limited = true ∨ ∃ e ∈ l, e.holding = .free ∧
            ∃ r, fit p.direction (p.part e.range).1 (p.part e.range).2 bytes align = .range r))))
  | [], limited, err, h => by
    unfold scan at h
    cases limited <;> cases h <;> simp
  | e :: rest, limited, err, h => by
    unfold scan at h
    split at h
    · rename_i hh
      have hne : e.holding ≠ .free := by rw [hh]; exact nofun
      rcases scan_error h with ⟨h1, e', he', h2⟩ | ⟨h1, ⟨h2, h3, h4⟩ | ⟨h2, h3⟩⟩
      · exact Or.inl ⟨h1, e', List.mem_cons_of_mem _ he', h2⟩
      · refine Or.inr ⟨?_, Or.inl ⟨h2, h3, ?_⟩⟩
        · intro x hx; rcases List.mem_cons.1 hx with rfl | hx
          · exact Or.inl hne
          · exact h1 x hx
        · intro x hx; rcases List.mem_cons.1 hx with rfl | hx
          · exact Or.inl hne
          · exact h4 x hx
      · refine Or.inr ⟨?_, Or.inr ⟨h2, ?_⟩⟩
        · intro x hx; rcases List.mem_cons.1 hx with rfl | hx
          · exact Or.inl hne
          · exact h1 x hx
        · rcases h3 with h3 | ⟨x, hx, h4⟩
          · exact Or.inl h3
          · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, h4⟩
    · rename_i hh
      dsimp only at h
      split at h
      · rename_i hfit
        rcases scan_error h with ⟨h1, e', he', h2⟩ | ⟨h1, ⟨h2, h3, h4⟩ | ⟨h2, h3⟩⟩
        · exact Or.inl ⟨h1, e', List.mem_cons_of_mem _ he', h2⟩
        · refine Or.inr ⟨?_, Or.inl ⟨h2, h3, ?_⟩⟩
          · intro x hx; rcases List.mem_cons.1 hx with rfl | hx
            · exact Or.inr (Or.inl hfit)
            · exact h1 x hx
          · intro x hx; rcases List.mem_cons.1 hx with rfl | hx
            · exact Or.inr hfit
            · exact h4 x hx
        · refine Or.inr ⟨?_, Or.inr ⟨h2, ?_⟩⟩
          · intro x hx; rcases List.mem_cons.1 hx with rfl | hx
            · exact Or.inr (Or.inl hfit)
            · exact h1 x hx
          · rcases h3 with h3 | ⟨x, hx, h4⟩
            · exact Or.inl h3
            · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, h4⟩
      · rename_i hfit
        cases h
        exact Or.inl ⟨rfl, e, List.mem_cons_self .., hh, hfit⟩
      · rename_i r' hfit
        split at h
        · rename_i hroom
          rcases scan_error h with ⟨h1, e', he', h2⟩ | ⟨h1, ⟨h2, h3, h4⟩ | ⟨h2, h3⟩⟩
          · exact Or.inl ⟨h1, e', List.mem_cons_of_mem _ he', h2⟩
          · cases h3
          · refine Or.inr ⟨?_, Or.inr ⟨h2, Or.inr ⟨e, List.mem_cons_self .., hh, r', hfit⟩⟩⟩
            intro x hx; rcases List.mem_cons.1 hx with rfl | hx
            · exact Or.inr (Or.inr ⟨r', hfit, hroom⟩)
            · exact h1 x hx
        · exact absurd h (by simp)

/-! ## `choose` -/

/-- The scan order of a placement has the extents of the table. -/
theorem mem_scanOrder {E X : Nat} {t : Ownership E X} {p : Placement} {e : Extent} :
    e ∈ t.scanOrder p ↔ e ∈ t.extents := by
  unfold Ownership.scanOrder
  split <;> simp

/-- The error of a request that `choose` refuses: that of one of its first
checks, or that of the scan of the extents in the order of the placement. -/
theorem choose_error {E X : Nat} {t : Ownership E X} {owner pages alignment : UInt64}
    {p : Placement} {err : OwnershipError} (h : t.choose owner pages alignment p = .error err) :
    (err = .addressOverflow ∧
      (2 ^ 64 ≤ pages.toNat * PAGE_SIZE ∨ 2 ^ 64 ≤ alignment.toNat * PAGE_SIZE)) ∨
    err = .invalidSize ∨ err = .invalidAlignment ∨ err = .generationExhausted ∨
    (pages ≠ 0 ∧ isPowerOfTwo alignment.toNat = true ∧
      scan (E - t.extents.length) (pages.toNat * PAGE_SIZE) (alignment.toNat * PAGE_SIZE) p
        (t.scanOrder p) false = .error err) := by
  unfold Ownership.choose at h
  by_cases h1 : (decide (2 ^ 64 ≤ pages.toNat * PAGE_SIZE) ||
      decide (2 ^ 64 ≤ alignment.toNat * PAGE_SIZE)) = true
  · simp only [h1, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, bind, Except.bind,
      Except.error.injEq] at h
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
    exact Or.inl ⟨h.symm, h1⟩
  simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h2 : pages = 0
  · simp only [h2, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, bind, Except.bind,
      Except.error.injEq] at h
    exact Or.inr (Or.inl h.symm)
  simp only [h2, ↓reduceIte] at h
  by_cases h3 : (!isPowerOfTwo alignment.toNat) = true
  · simp only [h3, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, bind, Except.bind,
      Except.error.injEq] at h
    exact Or.inr (Or.inr (Or.inl h.symm))
  simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
  by_cases h4 : t.counter = .exhausted
  · simp only [h4, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, bind, Except.bind,
      Except.error.injEq] at h
    exact Or.inr (Or.inr (Or.inr (Or.inl h.symm)))
  simp only [h4, ↓reduceIte, bind, Except.bind] at h
  simp only [Bool.not_eq_true', Bool.not_eq_false] at h3
  refine Or.inr (Or.inr (Or.inr (Or.inr ⟨h2, by simpa using h3, ?_⟩)))
  split at h
  · rename_i e he
    cases h
    exact he
  · exact absurd h (by simp [pure, Except.pure])

/-- The scan of a choice found its range inside a free extent of the table,
with the room that it needs. -/
theorem choose_extent {E X : Nat} {t : Ownership E X} {owner pages alignment : UInt64}
    {p : Placement} {c : Choice} (h : t.choose owner pages alignment p = .ok c) :
    ∃ e ∈ t.extents, e.holding = .free ∧ e.range.contains c.range = true ∧
      e.extra c.range ≤ E - t.extents.length := by
  obtain ⟨-, -, hpg, hal, -, -, hs⟩ := choose_ok h
  obtain ⟨i, e, h1, h2, h3, h4, -⟩ := scan_ok hs
  have hhi : (p.part e.range).2 < 2 ^ 64 := by
    have := (part_bounds p e.range).2; have := e.range.fits; unfold PhysRange.endNat at *; omega
  obtain ⟨⟨-, hlo, hend, hle⟩, -⟩ := (fit_spec (bytes_pos hpg) (align_pos hal) hhi).1 _ h3
  have hb := part_bounds p e.range
  refine ⟨e, mem_scanOrder.1 (List.mem_of_getElem? h1), h2, ?_, h4⟩
  simp only [PhysRange.contains, Bool.and_eq_true, decide_eq_true_eq]
  omega

end Krepi.Proofs.PageTables
