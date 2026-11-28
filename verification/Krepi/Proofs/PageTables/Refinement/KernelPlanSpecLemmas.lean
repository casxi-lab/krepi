module

public import Krepi.Proofs.PageTables.Refinement.PlanSimSpecLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: the leaves of the kernel map, for the simulation of its plan

What the checks of `Tables.kernelMap` give about the leaves of a layout, in
the form that the simulation of `mapPlan` by the cursor of the code needs
(`SimOk` of `Krepi.Proofs.PageTables.Refinement.PlanSimSpecLemmas`), with the
leaf search `layoutFind` of the plan iterator of `kernel_map`. The module
imports no generated definitions. None of it reads the record of the tables
that the checks of the code count.

- The place of a leaf on a record of more tables in use: `childIndex_mono`,
  `child?_mono`, `walk2_mono`, `place_mono`; the places of the leaves of one
  slot: `place_ok_some`, `place_root_iff` (one 1 GiB slot), `place_eq_of_slot`
  (one 2 MiB slot), and `placeLe_of_place` (the tables that a place names are
  tables of the pool).
- The leaves of a layout: `rangePages`, `mem_layoutPages`,
  `checkPlace_ok_inv`, `checkPages_ok`, `LayoutLeaves` (the leaves that pass
  the checks of sorted ranges: the pages of the ranges in order with their
  places, the ranges aligned, below `2 ^ 39` and apart) and `layout_fold`.
- The leaf search: `viewOfL`, `leafFirst_split`, `find?_pages`,
  `layoutFind_flatMap`.
- `kernel_simOk`: the leaves of a layout that passed its checks satisfy
  `SimOk` with the search `layoutFind` of their ranges and the place that the
  cursor reads on the set after the write phase.
- `kernelMap_used_le`: the record of the set of a success of
  `Tables.kernelMap` is at or above that of the set.
-/

@[expose] public section

open Krepi.Spec.PageTables Krepi.Statements Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

variable {r : Region} {N : Nat}

/-! ## The place of a leaf on a record of more tables in use -/

theorem childIndex_mono {a b l l' t : Nat} (h : childIndex a b l = some t) (hl : l ≤ l') :
    childIndex a b l' = some t := by
  unfold childIndex at h ⊢
  split at h
  · rename_i hc
    have h1 : b ≤ a := hc.1
    have h2 : (a - b) / PAGE_SIZE < l' := lt_of_lt_of_le hc.2 hl
    simp only [h1, h2, and_self, ↓reduceIte, h]
  · cases h

theorem child?_mono {pool : Pool N} {u u' : Nat} {base d : UInt64} {t : Nat}
    (h : (⟨pool, u⟩ : Tables r N).child? base d = some t) (hu : u ≤ u') :
    (⟨pool, u'⟩ : Tables r N).child? base d = some t := by
  rw [child?_eq] at h ⊢
  exact childIndex_mono h (by show min u N ≤ min u' N; omega)

theorem walk2_mono {pool : Pool N} {u u' : Nat} {base v : UInt64} {o : Option (Nat × UInt64)}
    (h : (⟨pool, u⟩ : Tables r N).walk2 base v = .ok o) (hu : u ≤ u') :
    (⟨pool, u'⟩ : Tables r N).walk2 base v = .ok o := by
  cases hv : isValid ((⟨pool, u⟩ : Tables r N).entry 0 (index1 v)) with
  | false =>
    rw [walk2_invalid hv] at h
    rw [walk2_invalid (s := (⟨pool, u'⟩ : Tables r N)) hv]
    exact h
  | true =>
    cases hc : (⟨pool, u⟩ : Tables r N).child? base ((⟨pool, u⟩ : Tables r N).entry 0 (index1 v)) with
    | none => rw [walk2_backing hv hc] at h; cases h
    | some t =>
      rw [walk2_some hv hc] at h
      rw [walk2_some (s := (⟨pool, u'⟩ : Tables r N)) hv (child?_mono hc hu)]
      exact h

theorem place_mono {pool : Pool N} {u u' : Nat} {base : UInt64} {l : MapLeaf} {p : Place}
    (h : (⟨pool, u⟩ : Tables r N).place base l = .ok p) (hu : u ≤ u') :
    (⟨pool, u'⟩ : Tables r N).place base l = .ok p := by
  cases hw : (⟨pool, u⟩ : Tables r N).walk2 base l.va with
  | error x => rw [place_walk_error hw] at h; cases h
  | ok o =>
    have hw' := walk2_mono hw hu
    cases o with
    | none => rw [place_walk_root hw] at h; rw [place_walk_root hw']; exact h
    | some te =>
      obtain ⟨t2, e2⟩ := te
      cases hv : isValid e2 with
      | false => rw [place_walk_invalid hw hv] at h; rw [place_walk_invalid hw' hv]; exact h
      | true =>
        by_cases hb : typeBits e2 = BLOCK
        · rw [place_walk_block hw hv hb] at h; cases h
        · cases hc : (⟨pool, u⟩ : Tables r N).child? base e2 with
          | none => rw [place_walk_backing hw hv hb hc] at h; cases h
          | some t3 =>
            have hc' := child?_mono hc hu
            cases hf : l.form with
            | block => rw [place_walk_covered hw hv hb hc hf] at h; cases h
            | page =>
              cases h3 : isValid ((⟨pool, u⟩ : Tables r N).entry t3 (index3 l.va)) with
              | false =>
                rw [place_walk_level3 hw hv hb hc hf h3] at h
                rw [place_walk_level3 hw' hv hb hc' hf h3]; exact h
              | true => rw [place_walk_mapped hw hv hb hc hf h3] at h; cases h

/-- A leaf with a place whose level 2 step finds a table: its level 2 entry
is invalid and the place is that table, or it is a page under a level 3
table of the set. -/
theorem place_ok_some {s : Tables r N} {base : UInt64} {l : MapLeaf} {p : Place} {t2 : Nat}
    {e2 : UInt64} (hw : s.walk2 base l.va = .ok (some (t2, e2))) (hp : s.place base l = .ok p) :
    (isValid e2 = false ∧ p = .level2 t2) ∨
      (isValid e2 = true ∧ l.form = .page ∧ ∃ t3, s.child? base e2 = some t3 ∧ p = .level3 t2 t3) := by
  cases hv : isValid e2 with
  | false => rw [place_walk_invalid hw hv] at hp; cases hp; exact Or.inl ⟨rfl, rfl⟩
  | true =>
    by_cases hb : typeBits e2 = BLOCK
    · rw [place_walk_block hw hv hb] at hp; cases hp
    · cases hc : s.child? base e2 with
      | none => rw [place_walk_backing hw hv hb hc] at hp; cases hp
      | some t3 =>
        cases hf : l.form with
        | block => rw [place_walk_covered hw hv hb hc hf] at hp; cases hp
        | page =>
          cases h3 : isValid (s.entry t3 (index3 l.va)) with
          | false =>
            rw [place_walk_level3 hw hv hb hc hf h3] at hp; cases hp
            exact Or.inr ⟨rfl, rfl, t3, rfl, rfl⟩
          | true => rw [place_walk_mapped hw hv hb hc hf h3] at hp; cases hp

/-- Two leaves of one 1 GiB slot with places: both at the root or neither. -/
theorem place_root_iff {s : Tables r N} {base : UInt64} {l l' : MapLeaf} {p p' : Place}
    (h1 : index1 l.va = index1 l'.va) (hp : s.place base l = .ok p)
    (hp' : s.place base l' = .ok p') : p = .root ↔ p' = .root := by
  have key : ∀ {m : MapLeaf} {q : Place}, s.place base m = .ok q →
      (q = .root ↔ isValid (s.entry 0 (index1 m.va)) = false) := by
    intro m q hq
    cases hv : isValid (s.entry 0 (index1 m.va)) with
    | false => rw [place_walk_root (walk2_invalid hv)] at hq; cases hq; simp
    | true =>
      cases hc : s.child? base (s.entry 0 (index1 m.va)) with
      | none => rw [place_walk_error (walk2_backing hv hc)] at hq; cases hq
      | some t =>
        simp only [Bool.true_eq_false, iff_false]
        rcases place_ok_some (walk2_some hv hc) hq with ⟨-, rfl⟩ | ⟨-, -, t3, -, rfl⟩ <;> simp
  rw [key hp, key hp', h1]

/-- Two leaves of one 2 MiB slot with places: one place. -/
theorem place_eq_of_slot {s : Tables r N} {base : UInt64} {l l' : MapLeaf} {p p' : Place}
    (h1 : index1 l.va = index1 l'.va) (h2 : index2 l.va = index2 l'.va)
    (hp : s.place base l = .ok p) (hp' : s.place base l' = .ok p') : p = p' := by
  have hw : s.walk2 base l'.va = s.walk2 base l.va := (walk2_congr s base h1 h2).symm
  cases hwl : s.walk2 base l.va with
  | error x => rw [place_walk_error hwl] at hp; cases hp
  | ok o =>
    rw [hwl] at hw
    cases o with
    | none =>
      rw [place_walk_root hwl] at hp; rw [place_walk_root hw] at hp'
      cases hp; cases hp'; rfl
    | some te =>
      obtain ⟨t2, e2⟩ := te
      rcases place_ok_some hwl hp with ⟨hv, rfl⟩ | ⟨hv, -, t3, hc, rfl⟩ <;>
        rcases place_ok_some hw hp' with ⟨hv', rfl⟩ | ⟨hv', -, t3', hc', rfl⟩
      · rfl
      · rw [hv] at hv'; cases hv'
      · rw [hv] at hv'; cases hv'
      · rw [hc] at hc'; cases hc'; rfl

/-- The tables that the place of a leaf names: tables of the pool. -/
theorem placeLe_of_place {s : Tables r N} {base : UInt64} {l : MapLeaf} {p : Place}
    (hp : s.place base l = .ok p) : PlaceLe N p := by
  cases hw : s.walk2 base l.va with
  | error x => rw [place_walk_error hw] at hp; cases hp
  | ok o =>
    cases o with
    | none => rw [place_walk_root hw] at hp; cases hp; trivial
    | some te =>
      obtain ⟨t2, e2⟩ := te
      have h2 := walk2_lt hw
      rcases place_ok_some hw hp with ⟨-, rfl⟩ | ⟨-, -, t3, hc, rfl⟩
      · exact le_of_lt h2
      · exact ⟨le_of_lt h2, le_of_lt (child?_lt hc)⟩

/-! ## The leaves of a layout -/

/-- The pages of a range of a layout, each mapped at its address. -/
def rangePages (j : LayoutRange) : List MapLeaf :=
  layoutPages j.kind (j.range.len.toNat / PAGE_SIZE) j.range.start.toNat

theorem mem_layoutPages {k : Kind} :
    ∀ {n pa : Nat} {l : MapLeaf}, l ∈ layoutPages k n pa → ∃ i < n, l = pageLeaf k (pa + PAGE_SIZE * i)
  | 0, pa, l, h => by simp [layoutPages] at h
  | n + 1, pa, l, h => by
    rw [layoutPages_succ, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨0, by omega, by simp⟩
    · obtain ⟨i, hi, rfl⟩ := mem_layoutPages h
      exact ⟨i + 1, by omega, by congr 1; simp only [PAGE_SIZE]; omega⟩

theorem pageLeaf_pa {k : Kind} {pa : Nat} (h : pa < 2 ^ 64) : (pageLeaf k pa).pa.toNat = pa := by
  simp only [pageLeaf]; exact UInt64.toNat_ofNat_of_lt' h

theorem pageLeaf_mem_layoutPages {k : Kind} :
    ∀ {n pa i : Nat}, i < n → pageLeaf k (pa + PAGE_SIZE * i) ∈ layoutPages k n pa
  | 0, _, _, h => absurd h (by omega)
  | n + 1, pa, 0, _ => by rw [layoutPages_succ]; simp
  | n + 1, pa, i + 1, h => by
    rw [layoutPages_succ]
    refine List.mem_cons_of_mem _ ?_
    have := pageLeaf_mem_layoutPages (k := k) (n := n) (pa := pa + PAGE_SIZE) (i := i) (by omega)
    rw [show pa + PAGE_SIZE * (i + 1) = pa + PAGE_SIZE + PAGE_SIZE * i by simp only [PAGE_SIZE]; omega]
    exact this

/-- The pages of a run from `pa` below `2 ^ 39`, in ascending order and apart. -/
theorem layoutPages_pairwise {k : Kind} : ∀ (n pa : Nat), pa + PAGE_SIZE * n ≤ 2 ^ 39 →
    (layoutPages k n pa).Pairwise (fun l l' => l.pa.toNat + l.form.size ≤ l'.pa.toNat)
  | 0, _, _ => List.Pairwise.nil
  | n + 1, pa, h => by
    have h' : pa + PAGE_SIZE + PAGE_SIZE * n ≤ 2 ^ 39 := by
      rw [Nat.mul_add, Nat.mul_one] at h; omega
    rw [layoutPages_succ, List.pairwise_cons]
    refine ⟨fun l hl => ?_, layoutPages_pairwise n (pa + PAGE_SIZE) h'⟩
    obtain ⟨i, hi, rfl⟩ := mem_layoutPages hl
    have hi' : PAGE_SIZE * i < PAGE_SIZE * n := Nat.mul_lt_mul_of_pos_left hi (by decide)
    rw [pageLeaf_pa (by omega), pageLeaf_pa (by omega)]
    show pa + PAGE_SIZE ≤ pa + PAGE_SIZE + PAGE_SIZE * i
    omega

theorem checkPlace_ok_inv {s : Tables r N} {base : UInt64} {l : MapLeaf} {taken : Bool} {p : Place}
    (h : checkPlace s base l taken = .ok p) : s.place base l = .ok p ∧ taken = false := by
  cases hp : s.place base l with
  | error x => rw [checkPlace_error hp] at h; cases h
  | ok q =>
    cases taken with
    | true => rw [checkPlace_taken hp] at h; cases h
    | false => rw [checkPlace_ok hp] at h; cases h; exact ⟨rfl, rfl⟩

/-- The checks of the pages of a range that pass: the pages, latest first,
each with its place, none of them taken. -/
theorem checkPages_ok (s : Tables r N) (base : UInt64) (taken : MapLeaf → Bool) (k : Kind) :
    ∀ (n pa : Nat) (acc res : List (MapLeaf × Place)), checkPages s base taken k n pa acc = .ok res →
      ∃ new, res = new ++ acc ∧ new.reverse.map Prod.fst = layoutPages k n pa ∧
        ∀ x ∈ new, s.place base x.1 = .ok x.2 ∧ taken x.1 = false
  | 0, pa, acc, res, h => by
    rw [checkPages_zero] at h; cases h; exact ⟨[], rfl, rfl, by simp⟩
  | n + 1, pa, acc, res, h => by
    rw [checkPages_succ] at h
    cases hc : checkPlace s base (pageLeaf k pa) (taken (pageLeaf k pa)) with
    | error x => rw [hc] at h; cases h
    | ok p =>
      rw [hc] at h
      obtain ⟨new, hres, hmap, hall⟩ := checkPages_ok s base taken k n (pa + PAGE_SIZE) _ res h
      have hpl := checkPlace_ok_inv hc
      refine ⟨new ++ [(pageLeaf k pa, p)], by rw [hres, List.append_assoc]; rfl, ?_, ?_⟩
      · simp [hmap, layoutPages_succ]
      · intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact hall x hx
        · rw [List.mem_singleton] at hx; subst hx; exact hpl

/-- The leaves `LP` that pass the checks of the sorted ranges `rs` of a layout:
the pages of the ranges in order, each with its place; each range aligned and
ending at or below `2 ^ 39`; each range ending at or below the start of every
later one. -/
structure LayoutLeaves (s : Tables .lower N) (base : UInt64) (rs : List LayoutRange)
    (LP : List (MapLeaf × Place)) : Prop where
  pages : LP.map Prod.fst = rs.flatMap rangePages
  place : ∀ x ∈ LP, s.place base x.1 = .ok x.2
  ranges : ∀ j ∈ rs, j.range.start.toNat % PAGE_SIZE = 0 ∧ j.range.endNat % PAGE_SIZE = 0 ∧
    j.range.endNat ≤ 2 ^ 39
  apart : rs.Pairwise (fun j j' => j.range.endNat ≤ j'.range.start.toNat)

/-- The fold of the checks of sorted ranges after ranges that start at or
below them: the leaves that pass are `LayoutLeaves`, and each range starts at
or above the end of the ranges before. -/
theorem layout_fold (s : Tables .lower N) (base : UInt64) (bits : UInt8) (guards : List UInt64) :
    ∀ (rs : List LayoutRange) (earlier : List PhysRange) (acc : List (MapLeaf × Place))
      (res : List PhysRange × List (MapLeaf × Place)),
      rs.Pairwise (fun j j' => j.range.start.toNat ≤ j'.range.start.toNat) →
      (∀ e ∈ earlier, ∀ j ∈ rs, e.start.toNat ≤ j.range.start.toNat) →
      rs.foldlM (s.checkLayoutRange base bits guards) (earlier, acc) = .ok res →
      ∃ new, res.2 = new ++ acc ∧ LayoutLeaves s base rs new.reverse ∧
        ∀ j ∈ rs, reachOf earlier ≤ j.range.start.toNat
  | [], earlier, acc, res, _, _, h => by
    cases h
    exact ⟨[], rfl, ⟨rfl, by simp, by simp, by simp⟩, by simp⟩
  | j :: rs, earlier, acc, res, hs, he, h => by
    rw [List.foldlM_cons] at h
    cases hj : s.checkLayoutRange base bits guards (earlier, acc) j with
    | error x => rw [hj] at h; cases h
    | ok mid =>
      rw [hj] at h
      obtain ⟨earlier', ls⟩ := mid
      rw [checkLayoutRange_eq] at hj
      split at hj
      · cases hj
      · rename_i h1
        split at hj
        · cases hj
        · rename_i h2
          cases hc : checkPages s base (layoutTaken earlier guards) j.kind
              (j.range.len.toNat / PAGE_SIZE) j.range.start.toNat acc with
          | error x => rw [hc] at hj; cases hj
          | ok ls' =>
            rw [hc] at hj
            simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hj
            obtain ⟨rfl, rfl⟩ := hj
            obtain ⟨new1, hls, hmap1, hall1⟩ := checkPages_ok s base _ j.kind _ _ acc ls' hc
            have hrs := List.pairwise_cons.1 hs
            obtain ⟨new2, hres, hLL, hreach⟩ := layout_fold s base bits guards rs (earlier ++ [j.range])
              ls' res hrs.2 (fun e he' j' hj' => by
                rcases List.mem_append.1 he' with he' | he'
                · exact he e he' j' (List.mem_cons_of_mem _ hj')
                · rw [List.mem_singleton] at he'; rw [he']; exact hrs.1 j' hj') h
            have ha : j.range.start.toNat % PAGE_SIZE = 0 ∧ j.range.endNat % PAGE_SIZE = 0 := by
              simp only [ne_eq, not_or, Decidable.not_not] at h1; exact h1
            have hw : j.range.endNat ≤ 2 ^ 39 := by
              simp only [not_or, Nat.not_lt, VA_LIMIT] at h2; exact h2.1
            -- the first page of the range is not taken: the range starts at or above the reach
            have hlen : j.range.len.toNat ≠ 0 := by
              have := j.range.nonempty
              intro h0; apply this; exact UInt64.toNat_inj.1 (by rw [h0]; rfl)
            have hn : 0 < j.range.len.toNat / PAGE_SIZE := by
              simp only [PhysRange.endNat, PAGE_SIZE] at ha ⊢; omega
            have hfirst : reachOf earlier ≤ j.range.start.toNat := by
              obtain ⟨m, hm⟩ : ∃ m, j.range.len.toNat / PAGE_SIZE = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hn).symm⟩
              have hmem : pageLeaf j.kind j.range.start.toNat ∈ new1.reverse.map Prod.fst := by
                rw [hmap1, hm, layoutPages_succ]; exact List.mem_cons_self
              obtain ⟨x, hx, hxe⟩ := List.mem_map.1 hmem
              have ht := (hall1 x (List.mem_reverse.1 hx)).2
              rw [hxe] at ht
              have hpa : (pageLeaf j.kind j.range.start.toNat).pa.toNat = j.range.start.toNat :=
                pageLeaf_pa (by have := j.range.fits; omega)
              have hany := any_meets_eq (l := pageLeaf j.kind j.range.start.toNat) (earlier := earlier)
                hpa rfl (fun e he' => he e he' j List.mem_cons_self)
              simp only [layoutTaken, Bool.or_eq_false_iff] at ht
              rw [hany] at ht
              simpa using ht.1
            refine ⟨new2 ++ new1, by rw [hres, hls, List.append_assoc], ⟨?_, ?_, ?_, ?_⟩, ?_⟩
            · rw [List.reverse_append, List.map_append, hmap1, hLL.pages, List.flatMap_cons]; rfl
            · intro x hx
              rw [List.reverse_append, List.mem_append] at hx
              rcases hx with hx | hx
              · exact (hall1 x (List.mem_reverse.1 hx)).1
              · exact hLL.place x hx
            · intro j' hj'
              rcases List.mem_cons.1 hj' with rfl | hj'
              · exact ⟨ha.1, ha.2, hw⟩
              · exact hLL.ranges j' hj'
            · refine List.pairwise_cons.2 ⟨fun j' hj' => ?_, hLL.apart⟩
              have := hreach j' hj'
              rw [reachOf_append] at this
              omega
            · intro j' hj'
              rcases List.mem_cons.1 hj' with rfl | hj'
              · exact hfirst
              · have := hreach j' hj'
                rw [reachOf_append] at this
                omega

/-! ## The leaf search -/

/-- A range of a layout of the specification on numbers. -/
def viewOfL (j : LayoutRange) : RangeView := ⟨j.range.start.toNat, j.range.endNat, j.kind⟩

/-- The first leaf after an address that splits leaves of pages: the first
leaf at or above it of all the leaves. -/
theorem leafFirst_split {LP L' : List (MapLeaf × Place)} {frm : Nat} (h : SplitAt LP frm L')
    (hpg : ∀ x ∈ L', x.1.form = .page) (limit : Nat) (pages : Bool) :
    leafFirst L' limit pages =
      match (LP.map Prod.fst).find? (fun l => decide (frm ≤ l.pa.toNat)) with
      | none => none
      | some l => if l.pa.toNat < limit then some (fOf l) else none := by
  obtain ⟨A, hA, hA1, hL1⟩ := h
  have hfA : (A.map Prod.fst).find? (fun l => decide (frm ≤ l.pa.toNat)) = none := by
    rw [List.find?_eq_none]
    intro l hl
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
    have h1 := hA1 x hx
    have h2 : 0 < x.1.form.size := by rcases form_size x.1 with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
    simp only [decide_eq_true_eq]
    omega
  rw [hA, List.map_append, List.find?_append, hfA, Option.none_or]
  cases L' with
  | nil => rfl
  | cons x L'' =>
    have hx : decide (frm ≤ x.1.pa.toNat) = true := by simpa using hL1 x List.mem_cons_self
    simp only [List.map_cons, List.find?_cons, hx, leafFirst_cons (Or.inr (hpg x List.mem_cons_self))]

/-- The first page at or above an address in a run of pages that reaches
above it, when no page straddles the address: the page at the address or the
first page. -/
theorem find?_pages {k : Kind} {frm : Nat} (n : Nat) :
    ∀ (pa : Nat), pa + PAGE_SIZE * n + PAGE_SIZE < 2 ^ 64 → frm < pa + PAGE_SIZE * n + PAGE_SIZE →
      (∀ i < n + 1, pa + PAGE_SIZE * i + PAGE_SIZE ≤ frm ∨ frm ≤ pa + PAGE_SIZE * i) →
      (layoutPages k (n + 1) pa).find? (fun l => decide (frm ≤ l.pa.toNat)) =
        some (pageLeaf k (max pa frm)) := by
  induction n with
  | zero =>
    intro pa h64 hlt hns
    have h0 := hns 0 (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at h64 hlt h0
    rw [layoutPages_succ, List.find?_cons, pageLeaf_pa (by omega)]
    have hf : frm ≤ pa := by omega
    simp only [hf, decide_true]
    congr 2; omega
  | succ m ih =>
    intro pa h64 hlt hns
    simp only [Nat.mul_add, Nat.mul_one] at h64 hlt
    rw [layoutPages_succ, List.find?_cons, pageLeaf_pa (by omega)]
    by_cases hf : frm ≤ pa
    · simp only [hf, decide_true]
      congr 2; omega
    · have h0 := hns 0 (by omega)
      simp only [Nat.mul_zero, Nat.add_zero] at h0
      simp only [hf, decide_false]
      rw [ih (pa + PAGE_SIZE) (by omega) (by omega)
        (fun i hi => by
          have := hns (i + 1) (by omega)
          simp only [Nat.mul_add, Nat.mul_one] at this
          omega)]
      congr 2; omega

theorem fOf_pageLeaf {k : Kind} {pa : Nat} (h : pa < 2 ^ 64) :
    fOf (pageLeaf k pa) = ⟨pa, descriptor k (UInt64.ofNat pa), false⟩ := by
  simp only [fOf, pageLeaf, UInt64.toNat_ofNat_of_lt' h, reduceCtorEq, decide_false]

/-- `layoutFind` of aligned nonempty ranges below `2 ^ 39` is the first of
their pages at or above an address that no page straddles. -/
theorem layoutFind_flatMap : ∀ (rs : List LayoutRange) (frm limit : Nat),
    (∀ j ∈ rs, j.range.start.toNat % PAGE_SIZE = 0 ∧ j.range.endNat % PAGE_SIZE = 0 ∧
      j.range.endNat ≤ 2 ^ 39) →
    (∀ l ∈ rs.flatMap rangePages, l.pa.toNat + PAGE_SIZE ≤ frm ∨ frm ≤ l.pa.toNat) →
    layoutFind (rs.map viewOfL) frm limit =
      match (rs.flatMap rangePages).find? (fun l => decide (frm ≤ l.pa.toNat)) with
      | none => none
      | some l => if l.pa.toNat < limit then some (fOf l) else none
  | [], _, _, _, _ => rfl
  | j :: rs, frm, limit, hr, hns => by
    obtain ⟨ha1, ha2, hw⟩ := hr j List.mem_cons_self
    have hlen : j.range.len.toNat ≠ 0 := by
      have := j.range.nonempty
      intro h0; apply this; exact UInt64.toNat_inj.1 (by rw [h0]; rfl)
    have hend : j.range.endNat = j.range.start.toNat + j.range.len.toNat := rfl
    rw [List.map_cons, List.flatMap_cons, List.find?_append]
    by_cases hlt : frm < j.range.endNat
    · rw [layoutFind_cons_lt (r := viewOfL j) hlt]
      obtain ⟨m, hm⟩ : ∃ m, j.range.len.toNat / PAGE_SIZE = m + 1 :=
        ⟨j.range.len.toNat / PAGE_SIZE - 1, by simp only [PAGE_SIZE] at ha1 ha2 ⊢; omega⟩
      have hmul : PAGE_SIZE * m + PAGE_SIZE = j.range.len.toNat := by
        simp only [PAGE_SIZE] at hm ha1 ha2 ⊢; omega
      have hf := find?_pages (k := j.kind) (frm := frm) m j.range.start.toNat
        (by omega) (by omega)
        (fun i hi => by
          have hmem : pageLeaf j.kind (j.range.start.toNat + PAGE_SIZE * i) ∈ rangePages j := by
            simp only [rangePages, hm]; exact pageLeaf_mem_layoutPages hi
          have := hns _ (List.mem_append_left _ hmem)
          rw [pageLeaf_pa (by
            have : PAGE_SIZE * i ≤ PAGE_SIZE * m := Nat.mul_le_mul_left _ (by omega)
            omega)] at this
          exact this)
      have hf' : (rangePages j).find? (fun l => decide (frm ≤ l.pa.toNat)) =
          some (pageLeaf j.kind (max j.range.start.toNat frm)) := by
        simp only [rangePages, hm]; exact hf
      have hmax : max j.range.start.toNat frm < 2 ^ 64 := by omega
      rw [hf', Option.some_or]
      dsimp only
      rw [pageLeaf_pa hmax, fOf_pageLeaf hmax]
      rfl
    · rw [layoutFind_cons_ge (r := viewOfL j) hlt]
      have hnone : (rangePages j).find? (fun l => decide (frm ≤ l.pa.toNat)) = none := by
        rw [List.find?_eq_none]
        intro l hl
        simp only [rangePages] at hl
        obtain ⟨i, hi, rfl⟩ := mem_layoutPages hl
        have hi' : PAGE_SIZE * i + PAGE_SIZE ≤ j.range.len.toNat := by
          simp only [PAGE_SIZE] at hi ⊢; omega
        rw [pageLeaf_pa (by omega)]
        simp only [decide_eq_true_eq]
        simp only [PAGE_SIZE] at hi' ⊢
        omega
      rw [hnone, Option.none_or]
      exact layoutFind_flatMap rs frm limit (fun j' hj' => hr j' (List.mem_cons_of_mem _ hj'))
        (fun l hl => hns l (List.mem_append_right _ hl))

/-! ## The leaves of the kernel map satisfy `SimOk` -/

/-- **The leaves of a layout for the simulation.** The leaves that passed the
checks of the sorted ranges `rs` of a layout on a set satisfy `SimOk` at the
offset 0, with the search `layoutFind` of the ranges and the place that the
cursor reads on a set of the same pool with a record of tables in use at or
above that of the set. -/
theorem kernel_simOk {s : Tables .lower N} {base : UInt64} {rs : List LayoutRange}
    {LP : List (MapLeaf × Place)} (hL : LayoutLeaves s base rs LP) {u' : Nat} (hu : s.used ≤ u') :
    SimOk 0 (fun f l _ => layoutFind (rs.map viewOfL) f l)
      (placeOr (⟨s.pool, u'⟩ : Tables .lower N) base) LP := by
  have hx : ∀ x ∈ LP, ∃ j ∈ rs, ∃ i < j.range.len.toNat / PAGE_SIZE,
      x.1 = pageLeaf j.kind (j.range.start.toNat + PAGE_SIZE * i) := by
    intro x hx
    have : x.1 ∈ rs.flatMap rangePages := by rw [← hL.pages]; exact List.mem_map_of_mem hx
    obtain ⟨j, hj, hm⟩ := List.mem_flatMap.1 this
    obtain ⟨i, hi, he⟩ := mem_layoutPages hm
    exact ⟨j, hj, i, hi, he⟩
  have hpg : ∀ j ∈ rs, ∀ i < j.range.len.toNat / PAGE_SIZE,
      j.range.start.toNat + PAGE_SIZE * i + PAGE_SIZE ≤ j.range.endNat := by
    intro j hj i hi
    simp only [PhysRange.endNat, PAGE_SIZE] at hi ⊢
    omega
  have hnum : ∀ x ∈ LP, x.1.form = .page ∧ x.1.va = x.1.pa ∧ x.1.pa.toNat % PAGE_SIZE = 0 ∧
      x.1.pa.toNat + PAGE_SIZE ≤ 2 ^ 39 := by
    intro x hxm
    obtain ⟨j, hj, i, hi, he⟩ := hx x hxm
    obtain ⟨ha1, -, hw⟩ := hL.ranges j hj
    have h1 := hpg j hj i hi
    rw [he]
    refine ⟨rfl, rfl, ?_, ?_⟩ <;> rw [pageLeaf_pa (by omega)] <;> simp only [PAGE_SIZE] at ha1 h1 ⊢ <;>
      omega
  refine ⟨Nat.zero_mod _, fun x hxm => ?_, fun x hxm => ?_, fun x hxm => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [(hnum x hxm).2.1, Nat.zero_add]
  · rw [(hnum x hxm).1]; exact (hnum x hxm).2.2.2
  · rw [(hnum x hxm).1]; exact (hnum x hxm).2.2.1
  · -- sorted
    have hfl : (rs.flatMap rangePages).Pairwise
        (fun l l' => l.pa.toNat + l.form.size ≤ l'.pa.toNat) := by
      refine List.pairwise_flatMap.2 ⟨fun j hj => ?_, ?_⟩
      · obtain ⟨ha1, ha2, hw⟩ := hL.ranges j hj
        refine layoutPages_pairwise _ _ ?_
        simp only [PhysRange.endNat, PAGE_SIZE] at hw ⊢
        omega
      · refine List.Pairwise.imp_of_mem (fun {j j'} hj hj' hjj' => ?_) hL.apart
        intro l hl l' hl'
        simp only [rangePages] at hl hl'
        obtain ⟨i, hi, rfl⟩ := mem_layoutPages hl
        obtain ⟨i', hi', rfl⟩ := mem_layoutPages hl'
        have h1 := hpg j hj i hi
        have h2 := hpg j' hj' i' hi'
        have hw' := (hL.ranges j' hj').2.2
        rw [pageLeaf_pa (by omega), pageLeaf_pa (by omega)]
        simp only [pageLeaf, Form.size]
        omega
    have := hfl
    rw [← hL.pages, List.pairwise_map] at this
    exact this
  · intro x hxm y hym hg
    exact place_root_iff (index1_of_gib hg) (hL.place x hxm) (hL.place y hym)
  · intro x hxm y hym hb
    exact place_eq_of_slot (index1_of_gib (gib_of_block hb)) (index2_of_block hb)
      (hL.place x hxm) (hL.place y hym)
  · intro x hxm hf
    rw [(hnum x hxm).1] at hf; cases hf
  · intro x hxm
    have hpl : (⟨s.pool, u'⟩ : Tables .lower N).place base x.1 = .ok x.2 :=
      place_mono (u := s.used) (hL.place x hxm) hu
    have hpr : (⟨s.pool, u'⟩ : Tables .lower N).place base
        (placeProbe (UInt64.ofNat (fOf x.1).pa) (fOf x.1).block) = .ok x.2 := by
      rw [← hpl]
      refine place_congr _ base ?_ ?_ ?_ ?_ <;>
        simp only [placeProbe, fOf, (hnum x hxm).1, (hnum x hxm).2.1, UInt64.ofNat_toNat,
          reduceCtorEq, decide_false, Bool.false_eq_true, ↓reduceIte]
    simp only [placeOr, hpr]
  · intro frm L' h limit pages
    have hL'p : ∀ x ∈ L', x.1.form = .page := fun x hx' => (hnum x (splitAt_mem h hx')).1
    rw [leafFirst_split h hL'p limit pages, hL.pages]
    refine layoutFind_flatMap rs frm limit hL.ranges (fun l hl => ?_)
    rw [← hL.pages] at hl
    obtain ⟨x, hxm, rfl⟩ := List.mem_map.1 hl
    obtain ⟨A, hA, hA1, hL1⟩ := h
    rw [hA] at hxm
    rcases List.mem_append.1 hxm with hxa | hxl
    · left
      have := hA1 x hxa
      rw [(hnum x (by rw [hA]; exact List.mem_append_left _ hxa)).1] at this
      exact this
    · right; exact hL1 x hxl

/-- A success of `Tables.kernelMap`: the record of its set is at or above
that of the set. -/
theorem kernelMap_used_le {s : Tables .lower N} {L : Layout} {base : UInt64} {bits : UInt8}
    {S : Tables .lower N} {plan : Plan} (h : s.kernelMap L base bits = .ok (S, plan)) :
    s.used ≤ S.used := by
  cases hp : checkPool N base bits with
  | error x => rw [kernelMap_pool_error hp] at h; cases h
  | ok u =>
    cases u
    cases hfo : (sortByKey (·.range.start.toNat) L.ranges).foldlM
        (s.checkLayoutRange base bits L.guards) ([], []) with
    | error x => rw [kernelMap_fold_error hp hfo] at h; cases h
    | ok res =>
      obtain ⟨e, ls⟩ := res
      rw [kernelMap_fold_ok hp hfo] at h
      split at h
      · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact next_le_stOf ls.reverse ⟨s.used, none, none, []⟩

end Krepi.Proofs.PageTables.Refinement
