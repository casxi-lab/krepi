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

- Lists that `ListRel` relates: `own_listRel_getElem`,
  `own_listRel_take_getElem`, `own_listRel_append`, `own_listRel_take`,
  `own_listRel_drop`, `own_listRel_forall`, `own_listRel_pairwise`; lists
  and their suffixes: `own_find?_drop_true`, `own_find?_drop_false`,
  `own_foldl_drop`, `own_sum_drop`, `own_all_drop`, `own_take_set_succ`,
  `own_set_middle`, `own_ite_ok` (a choice between two values of a step).
- Pages: `own_page_mask` (a mask of the bits from 12 to 63 rounds a 64-bit
  number down to a page) and `own_and_not_4095` (the same on a word of the
  code).
- Statistics: `statsStep`, one step of the fold of `Ownership.stats`, with
  `stats_eq_foldl`, `statsStep_free`, `statsStep_held`,
  `foldl_statsStep_fixed` and `extents_len_sum_lt` (the lengths of extents
  in address order sum to less than $2^{64}$).
- The first excluder: `rankOf` (the order firmware, image, boot storage),
  `minEx` (the first of two optional owners in that order),
  `minEx_none_left`, `minEx_none_right`, `minEx_assoc`, `firstExcluder_nil`,
  `firstExcluder_cons` and `own_firstExcluder_drop`.
- The banks in address order: `own_eq_of_perm_of_lt`, `own_starts_ne`,
  `own_sorted_eq` (a permutation of banks that do not overlap, sorted by
  start, is their `sortByKey`), `own_take_le_of_sorted`,
  `own_insert_sorted`, and the moves of the insertion loop,
  `own_shift_step`, `own_getElem_prefix`, `own_take_insert`.
- The free runs of a bank: `cutNat` (`Exclusion.cut` in numbers) with
  `own_cut_start_lt`, `own_cut_start_ge`, `own_cut_stop_lt`,
  `own_cut_stop_ge`; `sweepStep` and `cutStep`, one step of `cuts_at`, with
  `foldl_cutStep`, `sweep_reach` (the furthest end of the cuts at or below
  an address) and `sweep_nearest` (the nearest start above it);
  `NotInside` (no run has the address strictly inside it); the runs of
  `cutAll` from an address on: `own_runs_facts`, `own_runs_start`,
  `own_runs_skip` (over a cut), `own_runs_take` (a free address gives the
  run up to the nearest cut), `own_runs_end`; `extentsOfRuns` with
  `own_bankExtents_eq` and `own_go_drop` (`initialExtents.go` bank by
  bank).
- `Ownership.new`: `own_new_eq`, the cascade of its checks, and
  `own_anyOverlap_drop`.
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

/-! ## Lists that `ListRel` relates -/

theorem own_listRel_append {α β : Type} {rel : α → β → Prop} :
    ∀ {l₁ : List α} {m₁ : List β} {l₂ : List α} {m₂ : List β}, ListRel rel l₁ m₁ →
      ListRel rel l₂ m₂ → ListRel rel (l₁ ++ l₂) (m₁ ++ m₂)
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, h, h' => ⟨h.1, own_listRel_append h.2 h'⟩
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim

theorem own_listRel_take {α β : Type} {rel : α → β → Prop} :
    ∀ {l : List α} {m : List β} (n : Nat), ListRel rel l m → ListRel rel (l.take n) (m.take n)
  | [], [], _, _ => by rw [List.take_nil, List.take_nil]; trivial
  | _ :: _, _ :: _, 0, _ => trivial
  | _ :: _, _ :: _, n + 1, h => ⟨h.1, own_listRel_take n h.2⟩
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

theorem own_listRel_drop {α β : Type} {rel : α → β → Prop} :
    ∀ {l : List α} {m : List β} (n : Nat), ListRel rel l m → ListRel rel (l.drop n) (m.drop n)
  | [], [], _, _ => by rw [List.drop_nil, List.drop_nil]; trivial
  | _ :: _, _ :: _, 0, h => h
  | _ :: _, _ :: _, n + 1, h => own_listRel_drop n h.2
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

/-- Items that `ListRel` relates satisfy related tests. -/
theorem own_listRel_forall {α β : Type} {rel : α → β → Prop} {P : α → Prop} {Q : β → Prop}
    (hPQ : ∀ a b, rel a b → (P a ↔ Q b)) :
    ∀ {l : List α} {m : List β}, ListRel rel l m → ((∀ x ∈ l, P x) ↔ (∀ y ∈ m, Q y))
  | [], [], _ => by simp
  | a :: l, b :: m, h => by
    simp only [List.mem_cons, forall_eq_or_imp]
    rw [hPQ a b h.1, own_listRel_forall hPQ h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- The first `i + 1` items of a list in which item `i` is set. -/
theorem own_take_set_succ {α : Type} {l : List α} {i : Nat} (h : i < l.length) (x : α) :
    (l.set i x).take (i + 1) = l.take i ++ [x] := by
  apply List.ext_getElem
  · simp; omega
  · intro j h1 h2
    simp only [List.length_take, List.length_set] at h1
    rw [List.getElem_take, List.getElem_set]
    by_cases hj : j < i
    · rw [List.getElem_append_left (by simp; omega), List.getElem_take]
      simp only [show i ≠ j by omega, ↓reduceIte]
    · have : j = i := by omega
      subst this
      rw [List.getElem_append_right (by simp)]
      simp

/-- A choice between two values of a step of the code, as one value. -/
theorem own_ite_ok {α : Type} (c : Prop) [Decidable c] (a b : α) :
    (if c then Aeneas.Std.Result.ok a else Aeneas.Std.Result.ok b) =
      Aeneas.Std.Result.ok (if c then a else b) := by
  split <;> rfl

/-- A list whose item `i` is set: the items before it, the new item, and
the items after it. -/
theorem own_set_middle {α : Type} : ∀ (l₁ : List α) (x y : α) (l₂ : List α),
    (l₁ ++ x :: l₂).set l₁.length y = l₁ ++ y :: l₂
  | [], _, _, _ => rfl
  | a :: l₁, x, y, l₂ => by
    simp only [List.cons_append, List.length_cons, List.set_cons_succ]
    rw [own_set_middle l₁ x y l₂]

/-! ## Sorting -/

/-- Two permutations of one list, both in strictly ascending order of a key,
are equal. -/
theorem own_eq_of_perm_of_lt {α : Type} {key : α → Nat} :
    ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.Pairwise (fun a b => key a < key b) →
      l₂.Pairwise (fun a b => key a < key b) → l₁ = l₂
  | [], l₂, hp, _, _ => List.Perm.nil_eq hp
  | a :: t₁, [], hp, _, _ => absurd hp.length_eq (by simp)
  | a :: t₁, b :: t₂, hp, h₁, h₂ => by
    rw [List.pairwise_cons] at h₁ h₂
    have ha : a ∈ b :: t₂ := hp.mem_iff.1 List.mem_cons_self
    have hb : b ∈ a :: t₁ := hp.mem_iff.2 List.mem_cons_self
    have hab : a = b := by
      rcases List.mem_cons.1 ha with h | h
      · exact h
      · rcases List.mem_cons.1 hb with h' | h'
        · exact h'.symm
        · have := h₂.1 a h; have := h₁.1 b h'; omega
    subst hab
    rw [own_eq_of_perm_of_lt hp.cons_inv h₁.2 h₂.2]

/-- Ranges that pairwise do not overlap have pairwise distinct starts. -/
theorem own_starts_ne {Bs : List PhysRange} (h : anyOverlap Bs = false) :
    Bs.Pairwise (fun a b => a.start.toNat ≠ b.start.toNat) := by
  refine (anyOverlap_eq_false h).imp fun {a b} hab hs => ?_
  have := range_lt a
  have := range_lt b
  simp only [PhysRange.overlaps, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hab
  omega

/-- A permutation of ranges that do not overlap, in ascending order of their
starts, is their `sortByKey` by start. -/
theorem own_sorted_eq {Bs Q : List PhysRange} (ho : anyOverlap Bs = false) (hp : Q.Perm Bs)
    (hs : Q.Pairwise (fun a b => a.start.toNat ≤ b.start.toNat)) :
    Q = sortByKey (·.start.toNat) Bs := by
  have hne := own_starts_ne ho
  have hsym : ∀ {a b : PhysRange}, a.start.toNat ≠ b.start.toNat →
      b.start.toNat ≠ a.start.toNat := fun h h' => h h'.symm
  have h1 : Q.Pairwise (fun a b => a.start.toNat ≠ b.start.toNat) :=
    (List.Perm.pairwise_iff hsym hp).2 hne
  have h2 : (sortByKey (·.start.toNat) Bs).Pairwise (fun a b => a.start.toNat ≠ b.start.toNat) :=
    (List.Perm.pairwise_iff hsym (sortByKey_perm _ Bs)).2 hne
  refine own_eq_of_perm_of_lt (key := fun r : PhysRange => r.start.toNat)
    (hp.trans (sortByKey_perm _ Bs).symm) ((hs.and h1).imp fun h => ?_)
    (((sortByKey_pairwise _ Bs).and h2).imp fun h => ?_)
  · exact Nat.lt_of_le_of_ne h.1 h.2
  · exact Nat.lt_of_le_of_ne h.1 h.2

/-- The items before index `k` of a list in ascending order of a key are at
most a bound that the item before `k` is at most. -/
theorem own_take_le_of_sorted {α : Type} {key : α → Nat} {P : List α} {k b : Nat}
    (hs : P.Pairwise (fun x y => key x ≤ key y)) (hk : k ≤ P.length)
    (hlast : ∀ y, 0 < k → P[k - 1]? = some y → key y ≤ b) : ∀ y ∈ P.take k, key y ≤ b := by
  intro y hy
  cases k with
  | zero => simp at hy
  | succ k =>
    have hb := hlast P[k] (by omega)
      (by simp [List.getElem?_eq_getElem (show k < P.length by omega)])
    rw [List.take_succ_eq_append_getElem (by omega)] at hy
    rcases List.mem_append.1 hy with hy | hy
    · have hs' := hs
      rw [← List.take_append_drop k P, List.pairwise_append] at hs'
      have := hs'.2.2 y hy P[k] (by
        rw [List.drop_eq_getElem_cons (by omega)]; exact List.mem_cons_self)
      omega
    · rw [List.mem_singleton] at hy; subst hy; exact hb

/-- The insertion of a range into ranges in ascending order of their starts,
after those at or below its start and before those above it: ascending
again, and a permutation. -/
theorem own_insert_sorted {Q : List PhysRange} {B : PhysRange} {k : Nat}
    (hs : Q.Pairwise (fun a b => a.start.toNat ≤ b.start.toNat))
    (hbefore : ∀ y ∈ Q.take k, y.start.toNat ≤ B.start.toNat)
    (hafter : ∀ y ∈ Q.drop k, B.start.toNat < y.start.toNat) :
    (Q.take k ++ B :: Q.drop k).Perm (B :: Q) ∧
      (Q.take k ++ B :: Q.drop k).Pairwise (fun a b => a.start.toNat ≤ b.start.toNat) := by
  refine ⟨?_, ?_⟩
  · have := (List.perm_middle (a := B) (l₁ := Q.take k) (l₂ := Q.drop k))
    rwa [List.take_append_drop] at this
  · have hQ := hs
    rw [← List.take_append_drop k Q, List.pairwise_append] at hQ
    obtain ⟨h1, h2, h3⟩ := hQ
    rw [List.pairwise_append, List.pairwise_cons]
    refine ⟨h1, ⟨fun b hb => Nat.le_of_lt (hafter b hb), h2⟩, fun a ha b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hbefore a ha
    · exact h3 a ha b hb

/-- `Pairwise` of lists that `ListRel` relates, for related relations. -/
theorem own_listRel_pairwise {α β : Type} {rel : α → β → Prop} {P : α → α → Prop}
    {Q : β → β → Prop} (hPQ : ∀ a b a' b', rel a b → rel a' b' → (P a a' ↔ Q b b')) :
    ∀ {l : List α} {m : List β}, ListRel rel l m → (l.Pairwise P ↔ m.Pairwise Q)
  | [], [], _ => by simp
  | a :: l, b :: m, h => by
    rw [List.pairwise_cons, List.pairwise_cons, own_listRel_pairwise hPQ h.2,
      own_listRel_forall (fun a' b' h' => hPQ a b a' b' h.1 h') h.2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- One move of the insertion loop: the item before the gap moves into it. -/
theorem own_shift_step {α : Type} {P rest : List α} {X : α} {j : Nat} (h0 : 0 < j)
    (hj : j ≤ P.length) :
    (P.take j ++ X :: (P.drop j ++ rest)).set j (P[j - 1]'(by omega)) =
      P.take (j - 1) ++ P[j - 1]'(by omega) :: (P.drop (j - 1) ++ rest) := by
  have hl : (P.take j).length = j := by simp; omega
  have hset := own_set_middle (P.take j) X (P[j - 1]'(by omega)) (P.drop j ++ rest)
  rw [hl] at hset
  rw [hset]
  have h1 : P.take j = P.take (j - 1) ++ [P[j - 1]'(by omega)] := by
    rw [← List.take_succ_eq_append_getElem (by omega)]; congr 1; omega
  have h2 : P.drop (j - 1) = P[j - 1]'(by omega) :: P.drop j := by
    rw [List.drop_eq_getElem_cons (by omega)]; congr 2; omega
  rw [h1, h2]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- An item before the gap of the insertion loop. -/
theorem own_getElem_prefix {α : Type} {P rest : List α} {X : α} {j k : Nat} (hk : k < j)
    (hj : j ≤ P.length) (h : k < (P.take j ++ X :: (P.drop j ++ rest)).length) :
    (P.take j ++ X :: (P.drop j ++ rest))[k] = P[k]'(by omega) := by
  rw [List.getElem_append_left (by simp; omega), List.getElem_take]

/-- `Exclusion.cut` in numbers: the cut of `[xs, xs + xl)` in the bank
`[bs, bs + bl)`. -/
def cutNat (xs xl bs bl : Nat) : Option (Nat × Nat) :=
  if xs < bs + bl ∧ bs < xs + xl then
    some (max (xs / 4096 * 4096) bs, min ((xs + xl + 4096 - 1) / 4096 * 4096) (bs + bl))
  else none

/-! ## The free runs of a bank -/

/-- One step of `cuts_at` over a cut `[c.1, c.2)` at the address `p`: the
first component is the furthest end of the cuts that start at or below `p`,
the second the nearest start of the cuts above `p`. -/
def sweepStep (p : Nat) (acc : Nat × Nat) (c : Nat × Nat) : Nat × Nat :=
  (if c.1 ≤ p ∧ acc.1 < c.2 then c.2 else acc.1, if p < c.1 ∧ c.1 < acc.2 then c.1 else acc.2)

/-- One step of `cuts_at` over an exclusion of the bank `b`. -/
def cutStep (b : PhysRange) (p : Nat) (acc : Nat × Nat) (x : Exclusion) : Nat × Nat :=
  match x.cut b with
  | none => acc
  | some c => sweepStep p acc c

theorem foldl_cutStep (b : PhysRange) (p : Nat) : ∀ (xs : List Exclusion) (acc : Nat × Nat),
    xs.foldl (cutStep b p) acc = (xs.filterMap (·.cut b)).foldl (sweepStep p) acc
  | [], _ => rfl
  | x :: xs, acc => by
    rw [List.foldl_cons, List.filterMap_cons]
    cases h : x.cut b with
    | none => simp only [cutStep, h]; exact foldl_cutStep b p xs acc
    | some c => simp only [cutStep, h, List.foldl_cons]; exact foldl_cutStep b p xs _

theorem sweep_reach (p : Nat) : ∀ (cs : List (Nat × Nat)) (acc : Nat × Nat),
    acc.1 ≤ (cs.foldl (sweepStep p) acc).1 ∧
    (∀ c ∈ cs, c.1 ≤ p → c.2 ≤ (cs.foldl (sweepStep p) acc).1) ∧
    ((cs.foldl (sweepStep p) acc).1 = acc.1 ∨
      ∃ c ∈ cs, c.1 ≤ p ∧ c.2 = (cs.foldl (sweepStep p) acc).1)
  | [], acc => by simp
  | c :: cs, acc => by
    have ih := sweep_reach p cs (sweepStep p acc c)
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp, exists_eq_or_imp]
    generalize cs.foldl (sweepStep p) (sweepStep p acc c) = res at ih ⊢
    obtain ⟨h1, h2, h3⟩ := ih
    unfold sweepStep at h1 h3
    by_cases hc : c.1 ≤ p ∧ acc.1 < c.2
    · simp only [hc, and_self, ↓reduceIte] at h1 h3
      refine ⟨by omega, ⟨fun _ => h1, h2⟩, ?_⟩
      rcases h3 with h3 | h3
      · exact Or.inr (Or.inl ⟨hc.1, h3.symm⟩)
      · exact Or.inr (Or.inr h3)
    · simp only [hc, ↓reduceIte] at h1 h3
      refine ⟨h1, ⟨fun hp => by omega, h2⟩, ?_⟩
      rcases h3 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (Or.inr h3)

theorem sweep_nearest (p : Nat) : ∀ (cs : List (Nat × Nat)) (acc : Nat × Nat),
    (cs.foldl (sweepStep p) acc).2 ≤ acc.2 ∧
    (∀ c ∈ cs, p < c.1 → (cs.foldl (sweepStep p) acc).2 ≤ c.1) ∧
    ((cs.foldl (sweepStep p) acc).2 = acc.2 ∨
      ∃ c ∈ cs, p < c.1 ∧ c.1 = (cs.foldl (sweepStep p) acc).2)
  | [], acc => by simp
  | c :: cs, acc => by
    have ih := sweep_nearest p cs (sweepStep p acc c)
    simp only [List.foldl_cons, List.mem_cons, forall_eq_or_imp, exists_eq_or_imp]
    generalize cs.foldl (sweepStep p) (sweepStep p acc c) = res at ih ⊢
    obtain ⟨h1, h2, h3⟩ := ih
    unfold sweepStep at h1 h3
    by_cases hc : p < c.1 ∧ c.1 < acc.2
    · simp only [hc, and_self, ↓reduceIte] at h1 h3
      refine ⟨by omega, ⟨fun _ => h1, h2⟩, ?_⟩
      rcases h3 with h3 | h3
      · exact Or.inr (Or.inl ⟨hc.1, h3.symm⟩)
      · exact Or.inr (Or.inr h3)
    · simp only [hc, ↓reduceIte] at h1 h3
      refine ⟨h1, ⟨fun hp => by omega, h2⟩, ?_⟩
      rcases h3 with h3 | h3
      · exact Or.inl h3
      · exact Or.inr (Or.inr h3)

/-- No run of `runs` has the address `p` strictly inside it. -/
def NotInside (runs : List (Nat × Nat)) (p : Nat) : Prop :=
  ∀ r ∈ runs, ¬ (r.1 < p ∧ p < r.2)

section Runs

variable {C : List (Nat × Nat)} {lo hi : Nat}

/-- What `cutAll` of nonempty cuts gives from one nonempty run. -/
theorem own_runs_facts (hC : ∀ c ∈ C, c.1 < c.2) (hlh : lo < hi) :
    (∀ p, (∃ r ∈ cutAll C [(lo, hi)], r.1 ≤ p ∧ p < r.2) ↔
      (lo ≤ p ∧ p < hi) ∧ ∀ c ∈ C, ¬ (c.1 ≤ p ∧ p < c.2)) ∧
    (cutAll C [(lo, hi)]).Pairwise (fun x y => x.2 < y.1) ∧
    (∀ r ∈ cutAll C [(lo, hi)], r.1 < r.2 ∧ lo ≤ r.1 ∧ r.2 ≤ hi) := by
  refine ⟨fun p => ?_, cutAll_pairwise C _ hC (by simp), fun r hr => ⟨?_, ?_⟩⟩
  · rw [cutAll_mem]; simp
  · exact cutAll_nonempty C _ (by simpa using hlh) r hr
  · obtain ⟨r', h1, h2⟩ := cutAll_sub C _ r hr
    simp only [List.mem_singleton] at h1
    subst h1
    exact ⟨h2.1, h2.2⟩

/-- A cut that covers `[p, q)`: the runs from `p` on are those from `q` on. -/
theorem own_runs_skip (hC : ∀ c ∈ C, c.1 < c.2) (hlh : lo < hi) {p q : Nat} (hpq : p < q)
    (hc : ∃ c ∈ C, c.1 ≤ p ∧ c.2 = q) (hin : NotInside (cutAll C [(lo, hi)]) p) :
    (cutAll C [(lo, hi)]).filter (fun r => decide (p ≤ r.1)) =
      (cutAll C [(lo, hi)]).filter (fun r => decide (q ≤ r.1)) ∧
    NotInside (cutAll C [(lo, hi)]) q := by
  obtain ⟨hfree, -, hrun⟩ := own_runs_facts hC hlh
  obtain ⟨c, hcC, hc1, hc2⟩ := hc
  have key : ∀ r ∈ cutAll C [(lo, hi)], ¬ (p ≤ r.1 ∧ r.1 < q) := by
    rintro r hr ⟨h1, h2⟩
    have hf := (hfree r.1).1 ⟨r, hr, Nat.le_refl _, (hrun r hr).1⟩
    exact hf.2 c hcC ⟨by omega, by omega⟩
  refine ⟨List.filter_congr fun r hr => ?_, fun r hr h => ?_⟩
  · have := key r hr
    simp only [decide_eq_decide]
    omega
  · by_cases h' : r.1 < p
    · exact hin r hr ⟨h', by omega⟩
    · exact key r hr ⟨by omega, h.1⟩

/-- A free address `p` whose free pages reach `q`, the nearest start of a cut
above `p` or the end: the runs from `p` on are `[p, q)` and the runs from `q`
on. -/
theorem own_runs_take (hC : ∀ c ∈ C, c.1 < c.2) (hlh : lo < hi) {p q : Nat} (hp : lo ≤ p)
    (hph : p < hi) (hreach : ∀ c ∈ C, c.1 ≤ p → c.2 ≤ p) (hpq : p < q) (hqh : q ≤ hi)
    (hnear : ∀ c ∈ C, p < c.1 → q ≤ c.1) (hq : q = hi ∨ ∃ c ∈ C, p < c.1 ∧ c.1 = q)
    (hin : NotInside (cutAll C [(lo, hi)]) p) :
    (cutAll C [(lo, hi)]).filter (fun r => decide (p ≤ r.1)) =
      (p, q) :: (cutAll C [(lo, hi)]).filter (fun r => decide (q ≤ r.1)) ∧
    NotInside (cutAll C [(lo, hi)]) q := by
  obtain ⟨hfree, hpair, hrun⟩ := own_runs_facts hC hlh
  obtain ⟨r0, hr0, h01, h02⟩ := (hfree p).2 ⟨⟨hp, hph⟩, fun c hc h => by
    have := hreach c hc h.1; omega⟩
  have h0s : r0.1 = p := by
    by_contra hne
    exact hin r0 hr0 ⟨by omega, h02⟩
  have hsep : ∀ r ∈ cutAll C [(lo, hi)], r ≠ r0 → r.2 < r0.1 ∨ r0.2 < r.1 := by
    intro r hr hne
    rcases pairwise_mem_cases hpair hr hr0 with h | h | h
    · exact absurd h hne
    · exact Or.inl h
    · exact Or.inr h
  have h0e : r0.2 = q := by
    apply Nat.le_antisymm
    · rcases hq with hq | ⟨c, hc, hc1, hc2⟩
      · have := (hrun r0 hr0).2.2; omega
      · by_contra hlt
        have hin' := (hfree q).1 ⟨r0, hr0, by omega, by omega⟩
        exact hin'.2 c hc ⟨by omega, by have := hC c hc; omega⟩
    · by_contra hlt
      obtain ⟨r1, hr1, h11, h12⟩ := (hfree r0.2).2 ⟨⟨by omega, by omega⟩, fun c hc h => by
        by_cases hcp : c.1 ≤ p
        · have := hreach c hc hcp; omega
        · have := hnear c hc (by omega); omega⟩
      have hne : r1 ≠ r0 := fun h => by subst h; omega
      rcases hsep r1 hr1 hne with h | h <;> omega
  have hr0eq : r0 = (p, q) := by rw [← h0s, ← h0e]
  obtain ⟨A, B, hAB⟩ := List.append_of_mem hr0
  have hpw := hpair
  rw [hAB, List.pairwise_append, List.pairwise_cons] at hpw
  have hA : ∀ a ∈ A, a.2 < r0.1 := fun a ha => hpw.2.2 a ha r0 List.mem_cons_self
  have hB : ∀ b ∈ B, r0.2 < b.1 := hpw.2.1.1
  have hAr : ∀ a ∈ A, a.1 < a.2 := fun a ha =>
    (hrun a (by rw [hAB]; exact List.mem_append_left _ ha)).1
  refine ⟨?_, fun r hr h => ?_⟩
  · rw [hAB, List.filter_append, List.filter_append, List.filter_cons, List.filter_cons]
    have hA1 : A.filter (fun r => decide (p ≤ r.1)) = [] :=
      List.filter_eq_nil_iff.2 fun a ha => by
        have := hA a ha; have := hAr a ha; simp only [decide_eq_true_eq]; omega
    have hA2 : A.filter (fun r => decide (q ≤ r.1)) = [] :=
      List.filter_eq_nil_iff.2 fun a ha => by
        have := hA a ha; have := hAr a ha; simp only [decide_eq_true_eq]; omega
    have hB1 : B.filter (fun r => decide (p ≤ r.1)) = B :=
      List.filter_eq_self.2 fun b hb => by have := hB b hb; simp only [decide_eq_true_eq]; omega
    have hB2 : B.filter (fun r => decide (q ≤ r.1)) = B :=
      List.filter_eq_self.2 fun b hb => by have := hB b hb; simp only [decide_eq_true_eq]; omega
    have hp1 : decide (p ≤ r0.1) = true := by simp only [decide_eq_true_eq]; omega
    have hq1 : decide (q ≤ r0.1) = false := by simp only [decide_eq_false_iff_not]; omega
    rw [hA1, hA2, hB1, hB2, hp1, hq1, hr0eq]
    simp
  · by_cases hr' : r = r0
    · subst hr'; omega
    · rcases hsep r hr hr' with h' | h' <;> omega

/-- No run starts at or above the end. -/
theorem own_runs_end (hC : ∀ c ∈ C, c.1 < c.2) (hlh : lo < hi) {p : Nat} (hp : hi ≤ p) :
    (cutAll C [(lo, hi)]).filter (fun r => decide (p ≤ r.1)) = [] := by
  obtain ⟨-, -, hrun⟩ := own_runs_facts hC hlh
  exact List.filter_eq_nil_iff.2 fun r hr => by
    have := hrun r hr; simp only [decide_eq_true_eq]; omega

/-- From the start of the bank, every run is ahead and none is around. -/
theorem own_runs_start (hC : ∀ c ∈ C, c.1 < c.2) (hlh : lo < hi) :
    (cutAll C [(lo, hi)]).filter (fun r => decide (lo ≤ r.1)) = cutAll C [(lo, hi)] ∧
    NotInside (cutAll C [(lo, hi)]) lo := by
  obtain ⟨-, -, hrun⟩ := own_runs_facts hC hlh
  refine ⟨List.filter_eq_self.2 fun r hr => by
    have := hrun r hr; simp only [decide_eq_true_eq]; omega, fun r hr h => ?_⟩
  have := hrun r hr; omega

end Runs

/-- The extents of a list of runs of the bank of index `i`. -/
def extentsOfRuns (i : Nat) (runs : List (Nat × Nat)) : List Extent :=
  runs.filterMap fun r => (rangeOf? r.1 (r.2 - r.1)).map (⟨·, i, .free⟩)

theorem own_bankExtents_eq (exclusions : List Exclusion) (i : Nat) (b : PhysRange) :
    bankExtents exclusions i b =
      extentsOfRuns i (cutAll (exclusions.filterMap (·.cut b)) [(b.start.toNat, b.endNat)]) := by
  unfold bankExtents extentsOfRuns
  dsimp only
  congr 1
  generalize [(b.start.toNat, b.endNat)] = init
  induction exclusions generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, List.filterMap_cons]
    cases h : x.cut b with
    | none => exact ih init
    | some c =>
      obtain ⟨s, t⟩ := c
      exact ih _

/-- The extents of the banks from index `k`, `initialExtents.go`, from the
extents of the bank of index `k`. -/
theorem own_go_drop {exclusions : List Exclusion} {banks : List PhysRange} {k : Nat}
    (h : k < banks.length) :
    initialExtents.go exclusions k (banks.drop k) =
      bankExtents exclusions k banks[k] ++
        initialExtents.go exclusions (k + 1) (banks.drop (k + 1)) := by
  rw [List.drop_eq_getElem_cons h, initialExtents.go]

/-- `List.all` of the suffix from an index within the list. -/
theorem own_all_drop {α : Type} {l : List α} {p : α → Bool} {i : Nat} (h : i < l.length) :
    (l.drop i).all p = (p l[i] && (l.drop (i + 1)).all p) := by
  rw [List.drop_eq_getElem_cons h, List.all_cons]

/-- `anyOverlap` of the suffix from an index within the list. -/
theorem own_anyOverlap_drop {l : List PhysRange} {i : Nat} (h : i < l.length) :
    anyOverlap (l.drop i) =
      ((l.drop (i + 1)).any l[i].overlaps || anyOverlap (l.drop (i + 1))) := by
  rw [List.drop_eq_getElem_cons h, anyOverlap]


/-- The start of a cut: the start of the exclusion rounded down to a page,
or the start of the bank when it is above. -/
theorem own_cut_start_lt {xs b d : Nat} (hd : d = xs / 4096 * 4096) (h : b < d) :
    d = max (xs / 4096 * 4096) b := by
  subst hd; rw [Nat.max_def]; split <;> omega

theorem own_cut_start_ge {xs b d : Nat} (hd : d = xs / 4096 * 4096) (h : ¬ b < d) :
    b = max (xs / 4096 * 4096) b := by
  subst hd; rw [Nat.max_def]; split <;> omega

/-- The end of a cut of an exclusion that ends inside a bank on pages: its
end rounded up to a page. -/
theorem own_cut_stop_lt {xs xl bs bl i2 st : Nat} (h2 : i2 = xs + xl)
    (hbe : (bs + bl) % 4096 = 0) (hlt : i2 < bs + bl) (hst : st = (i2 + 4095) / 4096 * 4096) :
    st = min ((xs + xl + 4096 - 1) / 4096 * 4096) (bs + bl) := by
  subst h2 hst; rw [Nat.min_def]; split <;> omega

/-- The end of a cut of an exclusion that ends at or past the end of a bank:
the end of the bank. -/
theorem own_cut_stop_ge {xs xl bs bl i2 : Nat} (h2 : i2 = xs + xl) (hlt : ¬ i2 < bs + bl) :
    bs + bl = min ((xs + xl + 4096 - 1) / 4096 * 4096) (bs + bl) := by
  subst h2; rw [Nat.min_def]; split <;> omega

/-- The first `n + 1` items after an insertion into a list of `n` items. -/
theorem own_take_insert {α : Type} {P rest : List α} {k : Nat} (hk : k ≤ P.length) (b : α) :
    (P.take k ++ b :: (P.drop k ++ rest)).take (P.length + 1) = P.take k ++ b :: P.drop k := by
  have : P.take k ++ b :: (P.drop k ++ rest) = (P.take k ++ b :: P.drop k) ++ rest := by simp
  rw [this, List.take_left' (by simp; omega)]

/-- `Ownership.new` as the cascade of its checks. -/
theorem own_new_eq {E X : Nat} (arena : UInt64) (banks : List PhysRange)
    (exclusions : List Exclusion) :
    (Ownership.new arena banks exclusions : Except OwnershipError (Ownership E X)) =
      if !banks.all (·.onPages) then .error .invalidAlignment
      else if arena = 0 then .error .invalidArena
      else if banks.isEmpty then .error .invalidRange
      else if E < banks.length then .error .metadataExhausted
      else if anyOverlap banks then .error .invalidRange
      else if X < exclusions.length then .error .metadataExhausted
      else if E < (initialExtents (sortByKey (·.start.toNat) banks) exclusions).length then
        .error .metadataExhausted
      else .ok ⟨arena, sortByKey (·.start.toNat) banks,
        initialExtents (sortByKey (·.start.toNat) banks) exclusions, exclusions, .next 1⟩ := by
  unfold Ownership.new
  by_cases h1 : banks.all (·.onPages) = true
  · by_cases h2 : arena = 0
    · simp only [h1, h2, Bool.not_true, Bool.false_eq_true, ↓reduceIte, throw, throwThe,
        MonadExceptOf.throw, Bind.bind, Except.bind]
    · by_cases h3 : banks.isEmpty = true
      · simp only [h1, h2, h3, Bool.not_true, Bool.false_eq_true, ↓reduceIte, throw, throwThe,
          MonadExceptOf.throw, Bind.bind, Except.bind]
      · by_cases h4 : E < banks.length
        · simp only [h1, h2, h3, h4, Bool.not_true, Bool.false_eq_true, ↓reduceIte, throw,
            throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
        · by_cases h5 : anyOverlap banks = true
          · simp only [h1, h2, h3, h4, h5, Bool.not_true, Bool.false_eq_true, ↓reduceIte, throw,
              throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
          · by_cases h6 : X < exclusions.length
            · simp only [h1, h2, h3, h4, h5, h6, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
            · by_cases h7 : E < (initialExtents (sortByKey (·.start.toNat) banks) exclusions).length
              · simp only [h1, h2, h3, h4, h5, h6, h7, Bool.not_true, Bool.false_eq_true,
                  ↓reduceIte, throw, throwThe, MonadExceptOf.throw, Bind.bind, Except.bind]
              · simp only [h1, h2, h3, h4, h5, h6, h7, Bool.not_true, Bool.false_eq_true,
                  ↓reduceIte, Pure.pure, Except.pure]
  · simp only [h1, Bool.not_false, ↓reduceIte, throw, throwThe, MonadExceptOf.throw, Bind.bind,
      Except.bind]

end Krepi.Proofs.PageTables.Refinement
