module

public import Krepi.Proofs.PageTables.Refinement.BasicLemmas
public import Krepi.Proofs.PageTables.NewLemmas
public import Krepi.Proofs.PageTables.ListLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: specification lemmas for `Ownership::new`, `owner` and `stats`

Lemmas about the specification of the page ownership table, in the forms
that the triples of `Ownership::new`, `Ownership::owner` and
`Ownership::stats` need. The module imports no generated definitions.

- Lists that `ListRel` relates: `own_listRel_getElem` (items of one index
  are related), `own_listRel_take_getElem` (the same for the first `count`
  items of an array).
- Pages: `own_page_mask` (a mask of the bits from 12 to 63 rounds a 64-bit
  number down to a page), `own_and_not_4095` (the same on a word of the
  code).
- Statistics: `statsStep`, one step of the fold of `Ownership.stats`, with
  `stats_eq_foldl`, `statsStep_free`, `statsStep_held`, and
  `extents_len_sum_lt` (the lengths of extents in address order sum to less
  than $2^{64}$).
- The first excluder: `rankOf` (the order firmware, image, boot storage),
  `minEx` (the first of two optional owners in that order), `minEx_assoc`,
  `minEx_none_right`, and `firstExcluder_cons` (`firstExcluder` of a list
  from that of its tail).
-/

@[expose] public section

open Aeneas Aeneas.Std
open Krepi.Statements Krepi.Spec.PageTables Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

/-! ## Lists -/

/-- Items of one index of lists that `ListRel` relates are related. -/
theorem own_listRel_getElem {α β : Type} {rel : α → β → Prop} :
    ∀ {l : List α} {m : List β} (_ : ListRel rel l m) (i : Nat) (hi : i < l.length)
      (hm : i < m.length), rel l[i] m[i]
  | [], [], _, _, hi, _ => absurd hi (by simp)
  | a :: l, b :: m, h, 0, _, _ => h.1
  | a :: l, b :: m, h, i + 1, hi, hm =>
    own_listRel_getElem h.2 i (by simpa using hi) (by simpa using hm)
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim

/-- The item of index `i` of the first `count` items of an array of the code
is related to the item of index `i` of the list that they stand for. -/
theorem own_listRel_take_getElem {α β : Type} {rel : α → β → Prop} {l : List α} {m : List β}
    {count : Nat} (h : ListRel rel (l.take count) m) (hc : count ≤ l.length) (i : Nat)
    (hi : i < count) : ∃ hm : i < m.length, rel (l[i]'(by omega)) m[i] := by
  have hl := listRel_length h
  rw [List.length_take, Nat.min_eq_left hc] at hl
  refine ⟨by omega, ?_⟩
  have := own_listRel_getElem h i (by simp; omega) (by omega)
  simpa using this

/-! ## Pages -/

/-- A mask of the bits from 12 to 63 rounds a number below $2^{64}$ down to a
multiple of 4096. -/
theorem own_page_mask {n : Nat} (h : n < 2 ^ 64) :
    n &&& (2 ^ 64 - 1 - 4095) = n / 4096 * 4096 := by
  rw [show 2 ^ 64 - 1 - 4095 = (2 ^ 52 - 1) * 2 ^ 12 by norm_num,
    show (4096 : Nat) = 2 ^ 12 by norm_num]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases hj : 12 ≤ j
  · rw [Nat.sub_add_cancel hj]
    by_cases hj2 : j < 64
    · simp [hj, show j - 12 < 52 by omega]
    · have : n.testBit j = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hj, this]
  · simp [hj]

/-- A word of the code masked with the complement of 4095 is its value
rounded down to a page. -/
theorem own_and_not_4095 (x i : U64) (hi : i.val = 4095) :
    (x &&& ~~~i).val = x.val / 4096 * 4096 := by
  rw [← word64_toNat, word64_and, word64_not, UInt64.toNat_and, UInt64.toNat_not, word64_toNat,
    word64_toNat, hi]
  exact own_page_mask (u64_lt x)

/-! ## Statistics -/

/-- One step of the fold of `Ownership.stats`. -/
def statsStep (s : Stats) (e : Extent) : Stats :=
  match e.holding with
  | .free =>
    ⟨s.managed + e.range.len.toNat, s.free + e.range.len.toNat, s.allocated, s.allocations,
      s.freeExtents + 1, max s.largestFree e.range.len.toNat, s.extents, s.capacity⟩
  | .held .. =>
    ⟨s.managed + e.range.len.toNat, s.free, s.allocated + e.range.len.toNat,
      s.allocations + 1, s.freeExtents, s.largestFree, s.extents, s.capacity⟩

theorem stats_eq_foldl {E X : Nat} (t : Ownership E X) :
    t.stats = t.extents.foldl statsStep ⟨0, 0, 0, 0, 0, 0, t.extents.length, E⟩ := by
  unfold Ownership.stats statsStep
  rfl

theorem statsStep_free {s : Stats} {e : Extent} (h : e.holding = .free) :
    statsStep s e = ⟨s.managed + e.range.len.toNat, s.free + e.range.len.toNat, s.allocated,
      s.allocations, s.freeExtents + 1, max s.largestFree e.range.len.toNat, s.extents,
      s.capacity⟩ := by
  unfold statsStep; rw [h]

theorem statsStep_held {s : Stats} {e : Extent} (h : e.holding ≠ .free) :
    statsStep s e = ⟨s.managed + e.range.len.toNat, s.free, s.allocated + e.range.len.toNat,
      s.allocations + 1, s.freeExtents, s.largestFree, s.extents, s.capacity⟩ := by
  unfold statsStep
  cases hh : e.holding with
  | free => exact absurd hh h
  | held o n st => rfl

/-- The fold of `Ownership.stats` keeps the count of extents and the
capacity. -/
theorem foldl_statsStep_fixed : ∀ (l : List Extent) (s : Stats),
    (l.foldl statsStep s).extents = s.extents ∧ (l.foldl statsStep s).capacity = s.capacity
  | [], _ => ⟨rfl, rfl⟩
  | e :: rest, s => by
    rw [List.foldl_cons]
    refine (foldl_statsStep_fixed rest _).imp (fun h => h.trans ?_) (fun h => h.trans ?_) <;>
      (unfold statsStep; cases e.holding <;> rfl)

/-- The lengths of extents in address order, from `m` on, sum to less than
$2^{64}$ with `m`. -/
theorem extents_len_sum_lt : ∀ (l : List Extent) (m : Nat),
    l.Pairwise (fun a b => a.range.endNat ≤ b.range.start.toNat) →
    (∀ e ∈ l, m ≤ e.range.start.toNat) → m < 2 ^ 64 →
    m + (l.map (·.range.len.toNat)).sum < 2 ^ 64
  | [], m, _, _, hm => by simpa using hm
  | e :: rest, m, hp, hs, _ => by
    rw [List.pairwise_cons] at hp
    have h1 := hs e List.mem_cons_self
    have h2 := e.range.fits
    have ih := extents_len_sum_lt rest e.range.endNat hp.2 (fun x hx => hp.1 x hx)
      (by unfold PhysRange.endNat; omega)
    simp only [List.map_cons, List.sum_cons]
    unfold PhysRange.endNat at ih
    omega

/-! ## The first excluder -/

/-- The rank of an owner of an exclusion: firmware, image, boot storage. -/
def rankOf : Excluder → Nat
  | .firmware => 0
  | .image => 1
  | .bootStorage => 2

/-- The first of two optional owners of exclusions in the order of
`rankOf`. -/
def minEx : Option Excluder → Option Excluder → Option Excluder
  | none, b => b
  | some a, none => some a
  | some a, some b => if rankOf b < rankOf a then some b else some a

theorem minEx_none_right (a : Option Excluder) : minEx a none = a := by
  cases a <;> rfl

theorem minEx_none_left (a : Option Excluder) : minEx none a = a := rfl

theorem minEx_assoc (a b c : Option Excluder) : minEx (minEx a b) c = minEx a (minEx b c) := by
  rcases a with _ | ⟨_ | _ | _⟩ <;> rcases b with _ | ⟨_ | _ | _⟩ <;>
    rcases c with _ | ⟨_ | _ | _⟩ <;> rfl

theorem firstExcluder_nil (q : Nat) : firstExcluder [] q = none := rfl

theorem firstExcluder_cons (x : Exclusion) (xs : List Exclusion) (q : Nat) :
    firstExcluder (x :: xs) q =
      minEx (if x.range.touchesPage q then some x.owner else none) (firstExcluder xs q) := by
  unfold firstExcluder
  by_cases ht : x.range.touchesPage q = true
  · simp only [List.filter_cons, ht, ↓reduceIte, List.any_cons]
    generalize List.filter (fun x => x.range.touchesPage q) xs = l
    rcases hx : x.owner with _ | _ | _ <;>
      cases h1 : l.any (·.owner == .firmware) <;> cases h2 : l.any (·.owner == .image) <;>
      cases h3 : l.any (·.owner == .bootStorage) <;> simp [minEx, rankOf]
  · simp only [List.filter_cons, ht, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- `List.find?` of the suffix from an index whose item satisfies the test. -/
theorem own_find?_drop_true {α : Type} {l : List α} {p : α → Bool} {i : Nat} (h : i < l.length)
    (hp : p l[i] = true) : (l.drop i).find? p = some l[i] := by
  rw [List.drop_eq_getElem_cons h, List.find?_cons, hp]

/-- `List.find?` of the suffix from an index whose item fails the test. -/
theorem own_find?_drop_false {α : Type} {l : List α} {p : α → Bool} {i : Nat} (h : i < l.length)
    (hp : p l[i] = false) : (l.drop i).find? p = (l.drop (i + 1)).find? p := by
  rw [List.drop_eq_getElem_cons h, List.find?_cons, hp]

/-- `firstExcluder` of the suffix from an index. -/
theorem own_firstExcluder_drop {l : List Exclusion} {i : Nat} (h : i < l.length) (q : Nat) :
    firstExcluder (l.drop i) q =
      minEx (if l[i].range.touchesPage q then some l[i].owner else none)
        (firstExcluder (l.drop (i + 1)) q) := by
  rw [List.drop_eq_getElem_cons h, firstExcluder_cons]

/-- The fold of `Ownership.stats` over the suffix from an index. -/
theorem own_foldl_drop {α β : Type} {f : β → α → β} {l : List α} {i : Nat} (h : i < l.length)
    (b : β) : (l.drop i).foldl f b = (l.drop (i + 1)).foldl f (f b l[i]) := by
  rw [List.drop_eq_getElem_cons h, List.foldl_cons]

/-- The sum of a map over the suffix from an index. -/
theorem own_sum_drop {α : Type} {g : α → Nat} {l : List α} {i : Nat} (h : i < l.length) :
    ((l.drop i).map g).sum = g l[i] + ((l.drop (i + 1)).map g).sum := by
  rw [List.drop_eq_getElem_cons h, List.map_cons, List.sum_cons]

end Krepi.Proofs.PageTables.Refinement
