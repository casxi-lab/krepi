module

public import Krepi.SpecProperties.PageTables.Properties
import Mathlib.Util.CountHeartbeats
import Mathlib.Data.List.Nodup
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.PoolLemmas
import Krepi.Proofs.PageTables.WellFormedLemmas
import Krepi.Proofs.PageTables.WalkLemmas
import Krepi.Proofs.PageTables.TreeLemmas
import Krepi.Proofs.PageTables.ListLemmas
import Krepi.Proofs.PageTables.LeavesLemmas
import Krepi.Proofs.PageTables.EntryLemmas
import Krepi.Proofs.PageTables.CloneLemmas
import Krepi.Proofs.PageTables.MapCheckLemmas
import Krepi.Proofs.PageTables.OrderPlanLemmas
import Krepi.Proofs.PageTables.CloneWalkLemmas
import Krepi.Proofs.PageTables.AfterMapLemmas
import Krepi.Proofs.PageTables.DirectMapLemmas
import Krepi.Proofs.PageTables.Tables
import Krepi.Proofs.PageTables.OwnerLemmas
import Krepi.Proofs.PageTables.NewLemmas
import Krepi.Proofs.PageTables.WriteLemmas
import Krepi.Proofs.PageTables.Ownership

/-!
# Page tables: proofs about the abstract mapping and the plans

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about the abstract mapping and the plans,
whose type is exactly that statement: that every write changes the abstract
mapping as the contract says, that the tables in use are counted by $G$ and
$P$, and that the plans publish in order.

Every theorem here is proved. The tables of a well-formed set are the root,
the level 2 tables that the root points at and the level 3 tables that those
point at, once each, and the 1 GiB and 2 MiB slots of `Tables.gSlots` and
`Tables.pSlots` are the slots whose entries point at them, one for each
(`tablesInUseCounted`). The plan of a map passes `Plan.inOrder` by
`Krepi.Proofs.PageTables.OrderPlanLemmas`, and `map_page` and `map_block`
are maps of one leaf; the plans of `unmap_page` and `clone_kernel_from` are
read off their definitions (`plansPublishInOrder`).

`afterEveryWrite` is proved one row at a time, by a private theorem for
each of the 14 write entries:

- `Tables::new` and `reset` leave every root entry 0, so the walk of every
  address ends at the root (`root_zero` of
  `Krepi.Proofs.PageTables.WalkLemmas`);
- `map_page`, `map_block`, `kernel_map` and `direct_map` leave the set of the
  map of their leaves (`finalSet`), whose $M$, $G$ and $P$ are those of the
  set before it and the pages and slots of the leaves
  (`Krepi.Proofs.PageTables.AfterMapLemmas`); the leaves are the page or the
  block of the entry, the pages of the ranges of the layout (no page of a
  range holds a guard address or meets an earlier range,
  `kernelMap_checks`), and the leaves of the usable ranges, which hold no
  page in common (`directMap_apart`), so that the form of each page of the
  direct map is that of `blockForm` (`directMap_M_of_usable`, `M_unique`);
- `unmap_page` clears one page leaf of a well-formed set, so the walk of
  every other address is unchanged;
- the copy is read through what the walk of its source checked
  (`clone_facts`): the target's root and level 2 entries point at the
  tables of the same index, and its level 3 entries are those of the
  source;
- the six rows of the page ownership table restate the lemmas of each entry
  in `Krepi.Proofs.PageTables.WriteLemmas` and of `Ownership::new` in
  `Krepi.Proofs.PageTables.NewLemmas`, with `HolderRanges` of the table for
  the pages that a receipt or a reservation names.

Mathlib is imported so that the gate counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.PageTables.Mapping

open Krepi.SpecProperties.PageTables
open Krepi.Spec.PageTables
open Krepi.Proofs.PageTables
open Krepi.Proofs.Fdt (except_bind_ok except_jp_ok)

/-! ## The tables in use -/


private theorem len_filterMap_congr {α β γ : Type} {f : α → Option β} {g : α → Option γ} :
    ∀ {l : List α}, (∀ x ∈ l, (f x).isSome = (g x).isSome) →
      (l.filterMap f).length = (l.filterMap g).length
  | [], _ => rfl
  | x :: rest, h => by
    have ih := len_filterMap_congr (l := rest) (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    simp only [List.filterMap_cons]
    cases hf : f x <;> cases hg : g x <;> simp_all

private theorem len_flatMap_congr {α β γ : Type} {A : α → List β} {B : α → List γ} :
    ∀ {l : List α}, (∀ x ∈ l, (A x).length = (B x).length) →
      (l.flatMap A).length = (l.flatMap B).length
  | [], _ => rfl
  | x :: rest, h => by
    simp only [List.flatMap_cons, List.length_append]
    rw [h x List.mem_cons_self, len_flatMap_congr (fun y hy => h y (List.mem_cons_of_mem _ hy))]

private theorem filterMap_flatMap {α β γ : Type} (f : α → Option β) (F : β → List γ) :
    ∀ l : List α, (l.filterMap f).flatMap F =
      l.flatMap (fun x => match f x with | some y => F y | none => [])
  | [] => rfl
  | x :: rest => by
    simp only [List.filterMap_cons, List.flatMap_cons]
    cases f x <;> simp [filterMap_flatMap f F rest]

private theorem nodup_filterMap {α β : Type} {f : α → Option β} :
    ∀ {l : List α}, l.Nodup → (∀ a ∈ l, ∀ a' ∈ l, ∀ b, f a = some b → f a' = some b → a = a') →
      (l.filterMap f).Nodup
  | [], _, _ => List.nodup_nil
  | x :: rest, hn, h => by
    rw [List.nodup_cons] at hn
    have ih := nodup_filterMap hn.2 (fun a ha a' ha' =>
      h a (List.mem_cons_of_mem _ ha) a' (List.mem_cons_of_mem _ ha'))
    simp only [List.filterMap_cons]
    cases hx : f x with
    | none => exact ih
    | some b =>
      refine List.nodup_cons.2 ⟨fun hb => ?_, ih⟩
      obtain ⟨a, ha, hab⟩ := List.mem_filterMap.1 hb
      have := h x List.mem_cons_self a (List.mem_cons_of_mem _ ha) b hx hab
      subst this; exact hn.1 ha

/-- The address of the 2 MiB slot `j` of the 1 GiB slot `i` of a region. -/
private def slotAt (r : Region) (i j : Nat) : UInt64 :=
  UInt64.ofNat (r.first + i * GIB_SIZE + j * BLOCK_SIZE)

private theorem slotAt_add (r : Region) (i j : Nat) :
    UInt64.ofNat (r.first + i * GIB_SIZE) + UInt64.ofNat (j * BLOCK_SIZE) = slotAt r i j :=
  (UInt64.ofNat_add _ _).symm

private theorem slot_nat (r : Region) {i j : Nat} (hi : i < ENTRIES) (hj : j < ENTRIES) :
    r.first + i * GIB_SIZE + j * BLOCK_SIZE < 2 ^ 64 ∧
    (r.first + i * GIB_SIZE + j * BLOCK_SIZE) / GIB_SIZE % ENTRIES = i ∧
    (r.first + i * GIB_SIZE + j * BLOCK_SIZE) / BLOCK_SIZE % ENTRIES = j ∧
    (r.first + i * GIB_SIZE + j * BLOCK_SIZE) % BLOCK_SIZE = 0 ∧
    (r.first + i * GIB_SIZE) % GIB_SIZE = 0 ∧
    r.holds (UInt64.ofNat (r.first + i * GIB_SIZE + j * BLOCK_SIZE)) = true := by
  cases r with
  | lower =>
    simp only [Region.first, Region.holds, VA_LIMIT, GIB_SIZE, BLOCK_SIZE, ENTRIES, decide_eq_true_eq,
      UInt64.toNat_ofNat'] at hi hj ⊢
    refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  | upper =>
    simp only [Region.first, Region.holds, direct_base_toNat, GIB_SIZE, BLOCK_SIZE, ENTRIES,
      decide_eq_true_eq, UInt64.toNat_ofNat'] at hi hj ⊢
    refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
    rw [Nat.mod_eq_of_lt (by omega)]; omega

private theorem slotAt_toNat (r : Region) {i j : Nat} (hi : i < ENTRIES) (hj : j < ENTRIES) :
    (slotAt r i j).toNat = r.first + i * GIB_SIZE + j * BLOCK_SIZE :=
  UInt64.toNat_ofNat_of_lt' (slot_nat r hi hj).1

private theorem slotAt_facts (r : Region) {i j : Nat} (hi : i < ENTRIES) (hj : j < ENTRIES) :
    index1 (slotAt r i j) = i ∧ index2 (slotAt r i j) = j ∧ r.holds (slotAt r i j) = true ∧
      (slotAt r i j).toNat % BLOCK_SIZE = 0 := by
  have := slot_nat r hi hj
  have ht := slotAt_toNat r hi hj
  refine ⟨by rw [index1, ht]; exact this.2.1, by rw [index2, ht]; exact this.2.2.1, ?_,
    by rw [ht]; exact this.2.2.2.1⟩
  exact this.2.2.2.2.2

private theorem slotAt_zero (r : Region) (i : Nat) :
    slotAt r i 0 = UInt64.ofNat (r.first + i * GIB_SIZE) := by
  unfold slotAt; rw [Nat.zero_mul, Nat.add_zero]

private theorem slotAt_of (r : Region) {v : UInt64} (hv : r.holds v = true) (ha : v.toNat % BLOCK_SIZE = 0) :
    slotAt r (index1 v) (index2 v) = v := by
  apply UInt64.toNat_inj.1
  rw [slotAt_toNat r (index1_lt v) (index2_lt v)]
  have hlt := v.toNat_lt
  cases r with
  | lower =>
    simp only [Region.holds, VA_LIMIT] at hv
    have : v.toNat < 549755813888 := of_decide_eq_true hv
    simp only [Region.first, index1, index2, GIB_SIZE, BLOCK_SIZE, ENTRIES] at ha ⊢; omega
  | upper =>
    simp only [Region.holds, decide_eq_true_eq] at hv
    have hD : DIRECT_BASE.toNat = 2 ^ 30 * (2 ^ 34 - 512) := by decide
    simp only [Region.first, index1, index2, GIB_SIZE, BLOCK_SIZE, ENTRIES]
    rw [hD] at hv ⊢
    simp only [BLOCK_SIZE] at ha
    generalize v.toNat = x at hv hlt ha ⊢
    omega


section Count

variable {r : Region} {N : Nat} {s : Tables r N} {base : UInt64} {bits : UInt8}

private theorem walk2_some_iff (hs : s.WellFormed base bits) (v : UInt64) :
    (∃ t2 e2, s.walk2 base v = .ok (some (t2, e2))) ↔ (s.pointsAt? base 0 (index1 v)).isSome := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨t2, e2, h⟩
    exact ⟨t2, (pointsAt?_eq_some s base (index1_lt v)).2 (wf_walk2_some hs h).1⟩
  · rintro ⟨c, h⟩
    exact ⟨c, _, walk2_of_pointsAt ((pointsAt?_eq_some s base (index1_lt v)).1 h)⟩

private theorem level3_iff (hs : s.WellFormed base bits) {v : UInt64} {t2 : Nat}
    (h2 : s.PointsAt base 0 (index1 v) t2) :
    (∃ a b d, s.walk base v = .ok (.level3 a b d)) ↔ (s.pointsAt? base t2 (index2 v)).isSome := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨a, b, d, h⟩
    obtain ⟨-, hp, -, -⟩ := wf_walk_level3 hs h
    obtain ⟨e2, hw, -⟩ := walk_ok_level3.1 h
    have hat : a = t2 := pointsAt_inj (wf_walk2_some hs hw).1 h2
    subst hat
    exact ⟨b, (pointsAt?_eq_some s base (index2_lt v)).2 hp⟩
  · rintro ⟨c, h⟩
    have hp := (pointsAt?_eq_some s base (index2_lt v)).1 h
    refine ⟨t2, c, _, walk_ok_level3.2 ⟨_, walk2_of_pointsAt h2, isValid_of_isPlain hp.2.1, ?_, hp.2.2, rfl⟩⟩
    rw [typeBits_of_isPlain hp.2.1]; decide

private theorem gSlots_eq (hs : s.WellFormed base bits) :
    s.gSlots base = (List.range ENTRIES).filterMap fun i =>
      (s.pointsAt? base 0 i).map fun _ => slotAt r i 0 := by
  unfold Tables.gSlots
  refine filterMap_congr' fun i hi => ?_
  have hi' := List.mem_range.1 hi
  have h1 := (slotAt_facts r hi' (j := 0) (by decide)).1
  dsimp only
  rw [← slotAt_zero r i]
  cases hp : s.pointsAt? base 0 i with
  | none =>
    have hn : ¬ ∃ t2 e2, s.walk2 base (slotAt r i 0) = .ok (some (t2, e2)) := by
      rw [walk2_some_iff hs, h1, hp]; simp
    split
    · rename_i x heq; exact absurd ⟨x.1, x.2, heq⟩ hn
    · rfl
  | some c =>
    have hpa := (pointsAt?_eq_some s base hi').1 hp
    rw [← h1] at hpa
    rw [walk2_of_pointsAt hpa]; rfl

private theorem pSlots_eq (hs : s.WellFormed base bits) :
    s.pSlots base = (List.range ENTRIES).flatMap fun i =>
      match s.pointsAt? base 0 i with
      | some c => (List.range ENTRIES).filterMap fun j => (s.pointsAt? base c j).map fun _ => slotAt r i j
      | none => [] := by
  unfold Tables.pSlots
  rw [gSlots_eq hs, filterMap_flatMap]
  apply flatMap_congr'
  intro i hi
  have hi' := List.mem_range.1 hi
  cases hpi : s.pointsAt? base 0 i with
  | none => rfl
  | some c =>
    have hc := (pointsAt?_eq_some s base hi').1 hpi
    show List.filterMap _ _ = _
    refine filterMap_congr' fun j hj => ?_
    have hj' := List.mem_range.1 hj
    obtain ⟨h1, h2, -, -⟩ := slotAt_facts r hi' hj'
    simp only [slotAt_zero, slotAt_add]
    rw [← h1] at hc
    have key := level3_iff hs hc
    rw [h2] at key
    cases hp : s.pointsAt? base c j with
    | none =>
      rw [hp] at key
      split
      · rename_i x a b d heq; exact absurd (key.1 ⟨a, b, d, heq⟩) (by simp)
      · rfl
    | some c' =>
      rw [hp] at key
      obtain ⟨a, b, d, heq⟩ := key.2 rfl
      rw [heq]; rfl

private theorem tables_count (hs : s.WellFormed base bits) :
    s.used = 1 + (s.level2Tables base).length + (s.level3Tables base).length := by
  have h8 := hs.2.2.2.2.2.2.2.1
  have h9 := hs.2.2.2.2.2.2.2.2.1
  have h0 : 0 ∉ s.level2Tables base ++ s.level3Tables base := fun h => by
    obtain ⟨t, i, hp, h⟩ := (mem_tablesOf s base).1 h
    exact h8 t i hp h
  have hsort := (sort_eq_range_iff (s.level2Tables base ++ s.level3Tables base) s.used).2
    ⟨(tablesOf_nodup_iff s base h0).2 hs.2.2.2.2.2.2.2.2.2, fun c => ⟨fun h => ?_,
      fun ⟨h1, h2⟩ => (mem_tablesOf s base).2 (h9 c h1 h2)⟩⟩
  · have := congrArg List.length hsort
    rw [(sortByKey_perm id _).length_eq, List.length_append, List.length_range'] at this
    have := hs.2.1; omega
  · obtain ⟨t, i, hp, h⟩ := (mem_tablesOf s base).1 h
    refine ⟨Nat.pos_of_ne_zero fun hc => ?_, (pointsAt_lt h).1⟩
    subst hc; exact h8 t i hp h


private theorem phi_index {i : Nat} (hi : i < ENTRIES) {b : UInt64}
    (h : b ∈ (match s.pointsAt? base 0 i with
      | some c => (List.range ENTRIES).filterMap fun j => (s.pointsAt? base c j).map fun _ => slotAt r i j
      | none => [])) : index1 b = i := by
  split at h
  · obtain ⟨j, hj, hm⟩ := List.mem_filterMap.1 h
    obtain ⟨c', -, rfl⟩ := Option.map_eq_some_iff.1 hm
    exact (slotAt_facts r hi (List.mem_range.1 hj)).1
  · cases h

end Count

public theorem tablesInUseCounted : TablesInUseCounted := by
  intro r N s base bits hs
  have hg := gSlots_eq hs
  have hp := pSlots_eq hs
  have hL3 : s.level3Tables base = (List.range ENTRIES).flatMap fun i =>
      match s.pointsAt? base 0 i with
      | some c => s.childrenOf base c
      | none => [] := by
    unfold Tables.level3Tables Tables.level2Tables
    rw [Tables.childrenOf, filterMap_flatMap]
    apply flatMap_congr'
    intro i _
    cases s.pointsAt? base 0 i <;> rfl
  refine ⟨?_, ?_, ?_, fun g => ?_, fun b => ?_⟩
  · unfold Tables.usedTables
    rw [tables_count hs]
    have e1 : (s.gSlots base).length = (s.level2Tables base).length := by
      rw [hg, Tables.level2Tables, Tables.childrenOf]
      exact len_filterMap_congr fun i _ => Option.isSome_map
    have e2 : (s.pSlots base).length = (s.level3Tables base).length := by
      rw [hp, hL3]
      apply len_flatMap_congr
      intro i _
      cases s.pointsAt? base 0 i with
      | none => rfl
      | some c =>
        show List.length (List.filterMap _ _) = List.length (List.filterMap _ _)
        exact len_filterMap_congr fun j _ => Option.isSome_map
    omega
  · rw [hg]
    apply nodup_filterMap List.nodup_range
    intro a ha a' ha' b h h'
    obtain ⟨_, -, e⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨_, -, e'⟩ := Option.map_eq_some_iff.1 h'
    have k := (slotAt_facts r (List.mem_range.1 ha) (j := 0) (by decide)).1
    have k' := (slotAt_facts r (List.mem_range.1 ha') (j := 0) (by decide)).1
    rw [e] at k; rw [e'] at k'
    exact k.symm.trans k'
  · rw [hp, List.nodup_flatMap]
    refine ⟨fun i hi => ?_, ?_⟩
    · have hi' := List.mem_range.1 hi
      split
      · apply nodup_filterMap List.nodup_range
        intro a ha a' ha' b h h'
        obtain ⟨_, -, e⟩ := Option.map_eq_some_iff.1 h
        obtain ⟨_, -, e'⟩ := Option.map_eq_some_iff.1 h'
        have k := (slotAt_facts r hi' (List.mem_range.1 ha)).2.1
        have k' := (slotAt_facts r hi' (List.mem_range.1 ha')).2.1
        rw [e] at k; rw [e'] at k'
        exact k.symm.trans k'
      · exact List.nodup_nil
    · refine List.pairwise_lt_range.imp_of_mem fun {a a'} ha ha' hlt => ?_
      intro x hx hx'
      have := (phi_index (List.mem_range.1 ha) hx).symm.trans (phi_index (List.mem_range.1 ha') hx')
      omega
  · rw [hg, List.mem_filterMap]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨index1 g, List.mem_range.2 (index1_lt g), ?_⟩
      have hb : g.toNat % BLOCK_SIZE = 0 := by simp only [GIB_SIZE, BLOCK_SIZE] at h2 ⊢; omega
      have hi2 : index2 g = 0 := by simp only [index2, GIB_SIZE, BLOCK_SIZE, ENTRIES] at h2 ⊢; omega
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 ((walk2_some_iff hs g).1 h3)
      rw [hc]
      show some (slotAt r (index1 g) 0) = some g
      rw [← hi2, slotAt_of r h1 hb]
    · rintro ⟨i, hi, h⟩
      obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
      have hi' := List.mem_range.1 hi
      obtain ⟨f1, -, f3, -⟩ := slotAt_facts r hi' (j := 0) (by decide)
      refine ⟨f3, ?_, (walk2_some_iff hs _).2 (by rw [f1, hc]; rfl)⟩
      rw [slotAt_toNat r hi' (by decide), Nat.zero_mul, Nat.add_zero]
      exact (slot_nat r hi' (j := 0) (by decide)).2.2.2.2.1
  · rw [hp, List.mem_flatMap]
    constructor
    · rintro ⟨h1, h2, a, t3, d, hw⟩
      obtain ⟨e2, hw2, -⟩ := walk_ok_level3.1 hw
      have hpa := (wf_walk2_some hs hw2).1
      have key := (level3_iff hs hpa).1 ⟨a, t3, d, hw⟩
      refine ⟨index1 b, List.mem_range.2 (index1_lt b), ?_⟩
      rw [(pointsAt?_eq_some s base (index1_lt b)).2 hpa]
      show b ∈ List.filterMap _ _
      rw [List.mem_filterMap]
      obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.1 key
      refine ⟨index2 b, List.mem_range.2 (index2_lt b), ?_⟩
      rw [hc']
      show some (slotAt r (index1 b) (index2 b)) = some b
      rw [slotAt_of r h1 h2]
    · rintro ⟨i, hi, hb⟩
      have hi' := List.mem_range.1 hi
      cases hpi : s.pointsAt? base 0 i with
      | none => rw [hpi] at hb; cases hb
      | some c =>
        rw [hpi] at hb
        obtain ⟨j, hj, hm⟩ := List.mem_filterMap.1 hb
        obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.1 hm
        have hj' := List.mem_range.1 hj
        obtain ⟨f1, f2, f3, f4⟩ := slotAt_facts r hi' hj'
        refine ⟨f3, f4, ?_⟩
        have hpa := (pointsAt?_eq_some s base hi').1 hpi
        rw [← f1] at hpa
        exact (level3_iff hs hpa).2 (by rw [f2, hc']; rfl)


/-! ## The order of the plans -/

section Order

variable {r : Region} {N : Nat} {s : Tables r N} {base : UInt64} {bits : UInt8}

private theorem mapPage_order {v p : UInt64} {k : Kind} {s' : Tables r N} {plan : Plan}
    (hs : s.WellFormed base bits) (h : s.mapPage v p k base bits = .ok (s', plan)) :
    plan.publishesInOrder base s.pool = true := by
  obtain ⟨pl, hl, -, hN, rfl, -⟩ := mapPage_single hs h
  exact mapPlan_inOrder hs hl hN

private theorem mapBlock_order {v p : UInt64} {s' : Tables r N} {plan : Plan}
    (hs : s.WellFormed base bits) (h : s.mapBlock v p base bits = .ok (s', plan)) :
    plan.publishesInOrder base s.pool = true := by
  obtain ⟨pl, hl, -, hN, rfl, -⟩ := mapBlock_single hs h
  exact mapPlan_inOrder hs hl hN

/-! ## The copy of the kernel tables -/

/-- The stores of the copy as triples of a table, an entry and a descriptor. -/
private def copyTriples (sb base : UInt64) (leaf : Bool) (t : Nat) :
    List UInt64 → Nat → List (Nat × Nat × UInt64)
  | [], _ => []
  | d :: rest, i =>
    if isValid d then (t, i, copyValue sb base leaf d) :: copyTriples sb base leaf t rest (i + 1)
    else copyTriples sb base leaf t rest (i + 1)

private theorem copyStores_eq (sb base : UInt64) (leaf : Bool) (t : Nat) :
    ∀ (ds : List UInt64) (i : Nat), copyStores sb base leaf t ds i =
      (copyTriples sb base leaf t ds i).map fun x => Step.store x.1 x.2.1 x.2.2
  | [], _ => rfl
  | d :: rest, i => by
    simp only [copyStores, copyTriples]
    cases hv : isValid d <;> simp [copyStores_eq sb base leaf t rest (i + 1), copyValue]

private theorem copyTriples_facts (sb base : UInt64) (leaf : Bool) (t : Nat) :
    ∀ (ds : List UInt64) (i : Nat),
      (∀ x ∈ copyTriples sb base leaf t ds i, x.1 = t ∧ i ≤ x.2.1 ∧
        ∃ d, ds[x.2.1 - i]? = some d ∧ isValid d = true ∧ x.2.2 = copyValue sb base leaf d) ∧
      (copyTriples sb base leaf t ds i).Pairwise (fun x y => x.2.1 < y.2.1) ∧
      (∀ j d, ds[j]? = some d → isValid d = true → ∃ v, (t, i + j, v) ∈ copyTriples sb base leaf t ds i)
  | [], i => by simp [copyTriples]
  | d :: rest, i => by
    obtain ⟨a, b, c⟩ := copyTriples_facts sb base leaf t rest (i + 1)
    have a' : ∀ x ∈ copyTriples sb base leaf t rest (i + 1), x.1 = t ∧ i ≤ x.2.1 ∧
        ∃ d', (d :: rest)[x.2.1 - i]? = some d' ∧ isValid d' = true ∧
          x.2.2 = copyValue sb base leaf d' := fun x hx => by
      obtain ⟨h1, h2, d', h3, h4, h5⟩ := a x hx
      refine ⟨h1, by omega, d', ?_, h4, h5⟩
      rw [show x.2.1 - i = (x.2.1 - (i + 1)) + 1 by omega]; exact h3
    have c' : ∀ j d', rest[j]? = some d' → isValid d' = true →
        ∃ v, (t, i + (j + 1), v) ∈ copyTriples sb base leaf t rest (i + 1) := fun j d' h1 h2 => by
      obtain ⟨v, hv⟩ := c j d' h1 h2; exact ⟨v, by rw [show i + (j + 1) = i + 1 + j by omega]; exact hv⟩
    simp only [copyTriples]
    cases hv : isValid d
    · simp only [Bool.false_eq_true, ite_false]
      refine ⟨a', b, fun j d' h1 h2 => ?_⟩
      cases j with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at h1; subst h1; simp_all
      | succ j => exact c' j d' h1 h2
    · simp only [ite_true]
      refine ⟨fun x hx => ?_, List.pairwise_cons.2 ⟨fun x hx => by have := (a x hx).2.1; show i < x.2.1; omega, b⟩,
        fun j d' h1 h2 => ?_⟩
      · rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨rfl, Nat.le_refl _, d, by simp, hv, rfl⟩
        · exact a' x hx
      · cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h1; subst h1
          exact ⟨_, List.mem_cons_self⟩
        | succ j =>
          obtain ⟨v, hv'⟩ := c' j d' h1 h2; exact ⟨v, List.mem_cons_of_mem _ hv'⟩

private theorem clone_order {target source s : Tables r N} {sourceBase : UInt64} {plan : Plan}
    (h : target.cloneKernelFrom source sourceBase base bits = .ok (s, plan)) :
    ∃ stores : List (Nat × Nat × UInt64),
      plan = (List.range (min target.used N)).map Step.zero ++
        stores.map (fun x => Step.store x.1 x.2.1 x.2.2) ++ [.sync] ∧
      stores.Pairwise (fun a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2.1 < b.2.1)) ∧
      (∀ x ∈ stores, x.1 < source.used ∧ x.2.1 < ENTRIES ∧
        isValid (source.entry x.1 x.2.1) = true ∧
        if x.1 ∈ source.level3Tables sourceBase then x.2.2 = source.entry x.1 x.2.1
        else ∃ c, source.child? sourceBase (source.entry x.1 x.2.1) = some c ∧
          x.2.2 = tableDescriptor (tableAddress base c)) ∧
      ∀ t i, t < source.used → i < ENTRIES → isValid (source.entry t i) = true →
        ∃ d, (t, i, d) ∈ stores := by
  unfold Tables.cloneKernelFrom at h
  obtain ⟨u1, -, h⟩ := except_bind_ok.1 h
  obtain ⟨u2, -, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨st, hw, h⟩ := except_bind_ok.1 h
  obtain ⟨hreach, h⟩ := except_jp_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  have hall0 : ∀ t, t < source.used → t ∈ st.reached := by
    intro t ht
    simp only [List.any_eq_true, List.mem_range, not_exists, not_and] at hreach
    simpa using hreach t ht
  obtain ⟨w1, w2, w3, -⟩ := walkRoot_ok source sourceBase bits hw
  simp only [table_toList_eq, List.singleton_append, List.nil_append] at w1 w2 w3
  have hmem : ∀ t i, i < ENTRIES → source.entry t i ∈ (List.range ENTRIES).map (source.entry t) :=
    fun t i hi => List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
  have hkid : ∀ t, (∀ i, i < ENTRIES → isValid (source.entry t i) = true →
      isPlainTableDescriptor (source.entry t i) = true) →
      ((List.range ENTRIES).map (source.entry t)).filterMap (kidOf source sourceBase) =
        source.childrenOf sourceBase t := fun t ht => by
    rw [List.filterMap_map, Tables.childrenOf]
    refine filterMap_congr' fun i hi => ?_
    have hi' := List.mem_range.1 hi
    simp only [Function.comp_apply, kidOf, Tables.pointsAt?]
    cases hv : isValid (source.entry t i)
    · cases hp : isPlainTableDescriptor (source.entry t i)
      · rfl
      · rw [isValid_of_isPlain hp] at hv; cases hv
    · simp [ht i hi' hv]
  have hK0 := hkid 0 fun i hi hv => (w1 _ (hmem 0 i hi) hv).1
  have hKc : ∀ c ∈ ((List.range ENTRIES).map (source.entry 0)).filterMap (kidOf source sourceBase),
      ∀ i, i < ENTRIES → isValid (source.entry c i) = true →
        isPlainTableDescriptor (source.entry c i) = true ∧
          ∃ c', source.child? sourceBase (source.entry c i) = some c' := by
    intro c hc i hi hv
    obtain ⟨j, hj, hvj, hcj⟩ := mem_kids.1 hc
    obtain ⟨-, c'', hc'', hn⟩ := w1 _ (hmem 0 j hj) hvj
    rw [hcj, Option.some.injEq] at hc''; subst hc''
    obtain ⟨a, c', b, -⟩ := hn _ (hmem c i hi) hv
    exact ⟨a, c', b⟩
  have hleaves : st.leaves = source.level3Tables sourceBase := by
    rw [w3, flatMap_congr' fun c hc => hkid c fun i hi hv => (hKc c hc i hi hv).1, hK0]
    rfl
  have hget : ∀ t j d, (source.table t).toList[j]? = some d → j < ENTRIES ∧ d = source.entry t j := by
    intro t j d h
    rw [table_toList_eq, List.getElem?_eq_some_iff] at h
    obtain ⟨hj, rfl⟩ := h
    simp only [List.length_map, List.length_range] at hj
    exact ⟨hj, by simp⟩
  refine ⟨(List.range source.used).flatMap fun t =>
    copyTriples sourceBase base (st.leaves.contains t) t (source.table t).toList 0, ?_, ?_, ?_, ?_⟩
  · rw [flatMap_congr' fun t _ => copyStores_eq sourceBase base (st.leaves.contains t) t
      (source.table t).toList 0, List.map_flatMap]
  · rw [List.pairwise_flatMap]
    refine ⟨fun t _ => ?_, List.pairwise_lt_range.imp fun {a b} h x hx y hy => ?_⟩
    · obtain ⟨a, b, -⟩ := copyTriples_facts sourceBase base (st.leaves.contains t) t
        (source.table t).toList 0
      exact b.imp_of_mem fun {x y} hx hy h => Or.inr ⟨(a x hx).1.trans (a y hy).1.symm, h⟩
    · have e1 := ((copyTriples_facts _ _ _ _ _ _).1 x hx).1
      have e2 := ((copyTriples_facts _ _ _ _ _ _).1 y hy).1
      exact Or.inl (by rw [e1, e2]; exact h)
  · intro x hx
    obtain ⟨t, ht, hx⟩ := List.mem_flatMap.1 hx
    obtain ⟨rfl, -, d, hd, hv, he⟩ := (copyTriples_facts _ _ _ _ _ _).1 x hx
    rw [Nat.sub_zero] at hd
    obtain ⟨hj, rfl⟩ := hget _ _ _ hd
    refine ⟨List.mem_range.1 ht, hj, hv, ?_⟩
    split
    · rename_i h3
      rw [he, show st.leaves.contains x.1 = true from contains_iff.2 (hleaves ▸ h3)]; rfl
    · rename_i h3
      rw [he, show st.leaves.contains x.1 = false by
        cases h : st.leaves.contains x.1
        · rfl
        · exact absurd (hleaves ▸ contains_iff.1 h) h3]
      have hc : ∃ c, source.child? sourceBase (source.entry x.1 x.2.1) = some c := by
        have hr := hall0 x.1 (List.mem_range.1 ht)
        rw [w2] at hr
        simp only [List.mem_cons, List.mem_flatMap] at hr
        rcases hr with h0 | ⟨c, hc, h0 | hl⟩
        · rw [h0] at hv ⊢; exact (w1 _ (hmem 0 _ hj) hv).2.imp fun c h => h.1
        · rw [h0] at hv ⊢; exact (hKc c hc _ hj hv).2
        · refine absurd ?_ h3
          rw [← hleaves, w3]; exact List.mem_flatMap.2 ⟨c, hc, hl⟩
      obtain ⟨c, hc⟩ := hc
      exact ⟨c, hc, by rw [child?_index hc]; rfl⟩
  · intro t i ht hi hv
    obtain ⟨v, hv'⟩ := (copyTriples_facts sourceBase base (st.leaves.contains t) t
      (source.table t).toList 0).2.2 i _ (by
        rw [table_toList_eq]; simp [List.getElem?_range hi]) hv
    rw [Nat.zero_add] at hv'
    exact ⟨v, List.mem_flatMap.2 ⟨t, List.mem_range.2 ht, hv'⟩⟩

end Order

public theorem plansPublishInOrder : PlansPublishInOrder := by
  refine ⟨fun r N s v p k base bits s' plan hs h => mapPage_order hs h,
    fun r N s v p base bits s' plan hs h => mapBlock_order hs h,
    fun N s layout base bits s' plan hs h => ?_, fun N s B base bits s' plan hs h => ?_,
    fun r N s v base bits plan p hs h => ?_,
    fun r N target source sourceBase base bits s plan h => clone_order h⟩
  · obtain ⟨leaves, hl, -, hN, hplan, -⟩ := kernelMap_facts hs h
    rw [hplan]; exact mapPlan_inOrder hs hl hN
  · obtain ⟨leaves, hl, -, hN, -, hplan, -⟩ := directMap_facts hs h
    rw [hplan]; exact mapPlan_inOrder hs hl hN
  · unfold Tables.unmapPage at h
    obtain ⟨u, -, h⟩ := except_bind_ok.1 h
    obtain ⟨⟨t3, d⟩, hl, h⟩ := except_bind_ok.1 h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨t2, hw, -⟩ := pageLeaf_ok.1 hl
    exact ⟨t2, t3, d, hw, rfl⟩

/-! ## After every write: the table sets -/

private theorem afterNew : AfterNew := by
  intro r N base
  dsimp only
  have h0 : ∀ i, (Tables.new (Pool.zero N) : Tables r N).entry 0 i = 0 := fun i => by
    rw [entry_eq_get]; simp [Tables.new, Pool.zero, Pool.get, Table.zero]
  exact ⟨(root_zero h0).1, (root_zero h0).2.1, (root_zero h0).2.2, rfl⟩

private theorem afterReset : AfterReset := by
  intro r N s base hz
  dsimp only
  have h0 : ∀ t i, (s.reset.1.apply s.reset.2).entry t i = 0 := by
    intro t i
    rw [entry_eq_get]
    by_cases ht : t < N
    · by_cases hi : i < ENTRIES
      · show (Plan.exec _ s.pool).get t i = 0
        rw [get_exec _ _ ht hi]
        simp only [Tables.reset]
        rw [lastAt_zeros]
        simp only [List.mem_range]
        by_cases htu : t < s.used
        · rw [ite_of_pos (by omega)]; rfl
        · rw [ite_of_neg (by omega), Option.getD_none, ← entry_eq_get]
          exact entry_of_table_zero (hz t (by omega) ht) i
      · exact get_of_ge_entries _ _ (by omega)
    · exact get_of_ge _ _ (by omega)
  obtain ⟨h1, h2, h3⟩ := root_zero (base := base) (fun i => h0 0 i)
  exact ⟨h1, h2, h3, rfl, fun i => h0 0 i⟩

private theorem afterMapPage : AfterMapPage := by
  intro r N s v p k base bits s₁ plan hs h
  obtain ⟨pl, hl, happ, hN, -, hpa, hpb, -⟩ := mapPage_single hs h
  dsimp only
  rw [happ]
  have hx : (⟨v, p, descriptor k p, .page⟩ : MapLeaf) ∈
      [((⟨v, p, descriptor k p, .page⟩ : MapLeaf), pl)].map Prod.fst := by simp
  have hmem : ∀ x, x ∈ [((⟨v, p, descriptor k p, .page⟩ : MapLeaf), pl)].map Prod.fst →
      x = ⟨v, p, descriptor k p, .page⟩ := by simp
  have hal : v.toNat % PAGE_SIZE = 0 := hl.align _ List.mem_cons_self
  have hout : outputAddress (descriptor k p) = p := by
    have := (pool_ok_facts hs.1).2.2.2
    rw [outputAddress_descriptor, outputAddress_of_aligned hpa (by omega)]
  have hun : s.Unmapped base v :=
    leaf_unmapped hs hl hx hal (Nat.le_refl _) (by simp only [Form.size, PAGE_SIZE]; omega)
  refine ⟨hun, fun v' l => ?_, fun g => ?_, fun b => ?_⟩
  · rw [final_M_iff hs hl hN]
    constructor
    · rintro (hm | ⟨x, hx', h1, h2, h3, h4, h5, -⟩)
      · refine Or.inr ⟨fun he => ?_, hm⟩
        subst he; exact hun l hm
      · obtain rfl := hmem x hx'
        obtain ⟨hpa', hk⟩ := h5 rfl
        rw [ofPage_descriptor, Option.some.injEq] at hk
        rw [hout] at hpa'
        refine Or.inl ⟨?_, ?_⟩
        · apply UInt64.toNat_inj.1
          simp only [Form.size, PAGE_SIZE] at h1 h2 h3 hal ⊢; omega
        · obtain ⟨pa, kd, fm⟩ := l
          simp only at hpa' hk h4
          rw [hpa', hk, h4]
    · rintro (⟨rfl, rfl⟩ | ⟨-, hm⟩)
      · exact Or.inr ⟨_, hx, hal, Nat.le_refl _, by simp only [Form.size, PAGE_SIZE]; omega, rfl,
          fun _ => ⟨hout.symm, ofPage_descriptor _ _⟩, fun hb => by cases hb⟩
      · exact Or.inl hm
  · rw [final_G_iff hs hl hN]
    constructor
    · rintro (h | ⟨x, hx', rfl⟩)
      · exact Or.inl h
      · rw [hmem x hx']; exact Or.inr rfl
    · rintro (h | rfl)
      · exact Or.inl h
      · exact Or.inr ⟨_, hx, rfl⟩
  · rw [final_P_iff hs hl hN]
    constructor
    · rintro (h | ⟨x, hx', -, rfl⟩)
      · exact Or.inl h
      · rw [hmem x hx']; exact Or.inr rfl
    · rintro (h | rfl)
      · exact Or.inl h
      · exact Or.inr ⟨_, hx, rfl, rfl⟩

/-- A block leaf of a map is in no 2 MiB slot of $P$ of the set before it. -/
private theorem block_not_P {r : Region} {N : Nat} {s : Tables r N} {base : UInt64} {bits : UInt8}
    (hs : s.WellFormed base bits) {l : MapLeaf} {pl : Place} (hp : s.place base l = .ok pl)
    (hb : l.form = .block) : ¬ s.P base l.va := by
  have hsp := place_spec hs hp
  rintro ⟨-, -, t2, t3, d, hw⟩
  obtain ⟨e2, hw2, hv, -⟩ := walk_ok_level3.1 hw
  cases pl with
  | root =>
    rw [walk2_ok.2 (Or.inl ⟨by rw [hsp]; decide, rfl⟩)] at hw2; simp at hw2
  | level2 t =>
    rw [walk2_of_pointsAt hsp.1, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hw2
    rw [← hw2.2, hsp.2.2] at hv; exact absurd hv (by decide)
  | level3 _ _ => rw [hsp.1] at hb; cases hb

private theorem afterMapBlock : AfterMapBlock := by
  intro r N s v p base bits s₁ plan hs h
  obtain ⟨pl, hl, happ, hN, -, hpa, hpb, -⟩ := mapBlock_single hs h
  dsimp only
  rw [happ]
  have hx : (⟨v, p, blockDescriptor p, .block⟩ : MapLeaf) ∈
      [((⟨v, p, blockDescriptor p, .block⟩ : MapLeaf), pl)].map Prod.fst := by simp
  have hmem : ∀ x, x ∈ [((⟨v, p, blockDescriptor p, .block⟩ : MapLeaf), pl)].map Prod.fst →
      x = ⟨v, p, blockDescriptor p, .block⟩ := by simp
  have hreg : r.holds v = true := hl.region _ List.mem_cons_self
  have hal : v.toNat % BLOCK_SIZE = 0 := hl.align _ List.mem_cons_self
  have hba : (blockAddress (blockDescriptor p)).toNat = p.toNat := by
    have := (pool_ok_facts hs.1).2.2.2
    rw [blockAddress_blockDescriptor, blockAddress_of_aligned hpa (by omega)]
  have hpv : ∀ i, i < ENTRIES → (UInt64.ofNat (v.toNat + PAGE_SIZE * i)).toNat = v.toNat + PAGE_SIZE * i :=
    fun i hi => UInt64.toNat_ofNat_of_lt' (by
      have := v.toNat_lt
      simp only [ENTRIES, PAGE_SIZE, BLOCK_SIZE, UInt64.size] at hi hal this ⊢; omega)
  refine ⟨blk_of_index hreg hreg rfl rfl hal, fun i hi l => ?_,
    block_not_P hs (hl.place _ List.mem_cons_self) rfl, fun v' l => ?_, fun g => ?_, fun b => ?_⟩
  · refine leaf_unmapped hs hl hx ?_ ?_ ?_ l <;> rw [hpv i hi] <;>
      simp only [Form.size, ENTRIES, PAGE_SIZE, BLOCK_SIZE] at hi hal ⊢ <;> omega
  · rw [final_M_iff hs hl hN]
    constructor
    · rintro (hm | ⟨x, hx', h1, h2, h3, h4, -, h5⟩)
      · exact Or.inl hm
      · obtain rfl := hmem x hx'
        obtain ⟨hpa', hk⟩ := h5 rfl
        rw [hba] at hpa'
        refine Or.inr ⟨(v'.toNat - v.toNat) / PAGE_SIZE, ?_, ?_, ?_⟩
        · simp only [Form.size, ENTRIES, PAGE_SIZE, BLOCK_SIZE] at h1 h2 h3 hal ⊢; omega
        · simp only [Form.size, PAGE_SIZE, BLOCK_SIZE] at h1 h2 h3 hal ⊢; omega
        · obtain ⟨pa, kd, fm⟩ := l
          simp only [Leaf.mk.injEq] at hpa' hk h4 ⊢
          refine ⟨UInt64.toNat_inj.1 ?_, hk, h4⟩
          rw [hpa', UInt64.toNat_ofNat_of_lt' (by
            have := (pool_ok_facts hs.1).2.2.2
            simp only [Form.size, PAGE_SIZE, BLOCK_SIZE, UInt64.size] at h1 h2 h3 hal hpb this ⊢
            omega)]
          simp only [Form.size, PAGE_SIZE, BLOCK_SIZE] at h1 h2 h3 hal ⊢; omega
    · rintro (hm | ⟨i, hi, hv', rfl⟩)
      · exact Or.inl hm
      · refine Or.inr ⟨_, hx, ?_, ?_, ?_, rfl, (fun hb => by cases hb), fun _ => ⟨?_, rfl⟩⟩
        · rw [hv']; simp only [ENTRIES, PAGE_SIZE, BLOCK_SIZE] at hi hal ⊢; omega
        · rw [hv']; simp only [ENTRIES, PAGE_SIZE, BLOCK_SIZE] at hi hal ⊢; omega
        · rw [hv']; simp only [Form.size, ENTRIES, PAGE_SIZE, BLOCK_SIZE] at hi hal ⊢; omega
        · rw [hba, UInt64.toNat_ofNat_of_lt' (by
            have := (pool_ok_facts hs.1).2.2.2
            simp only [ENTRIES, PAGE_SIZE, UInt64.size] at hi hpb this ⊢; omega), hv']
          simp only [ENTRIES, PAGE_SIZE, BLOCK_SIZE] at hi hal ⊢; omega
  · rw [final_G_iff hs hl hN]
    constructor
    · rintro (h | ⟨x, hx', rfl⟩)
      · exact Or.inl h
      · rw [hmem x hx']; exact Or.inr rfl
    · rintro (h | rfl)
      · exact Or.inl h
      · exact Or.inr ⟨_, hx, rfl⟩
  · rw [final_P_iff hs hl hN]
    constructor
    · rintro (h | ⟨x, hx', hf, -⟩)
      · exact h
      · rw [hmem x hx'] at hf; cases hf
    · exact Or.inl

/-- A set `s'` whose entries are those of a well-formed set `s` but the page
leaf of `v`, cleared: $M' = M \setminus \{v\}$, $G' = G$, $P' = P$. -/
private theorem unmap_after {r : Region} {N : Nat} {s s' : Tables r N} {base : UInt64}
    {bits : UInt8} (hs : s.WellFormed base bits) {v : UInt64} {t2 t3 : Nat} {d : UInt64}
    (hw : s.walk base v = .ok (.level3 t2 t3 d)) (hreg : r.holds v = true)
    (hv : v.toNat % PAGE_SIZE = 0) (hu : s'.used = s.used)
    (hent : ∀ t i, s'.entry t i = if t = t3 ∧ i = index3 v then 0 else s.entry t i) :
    (∀ v' l, s'.M base v' l ↔ v' ≠ v ∧ s.M base v' l) ∧
    (∀ g, s'.G base g ↔ s.G base g) ∧ (∀ b, s'.P base b ↔ s.P base b) := by
  have huniq := hs.2.2.2.2.2.2.2.2.2
  obtain ⟨hl2, hp2, hl3, -⟩ := wf_walk_level3 hs hw
  obtain ⟨e2v, hw2v, -⟩ := walk_ok_level3.1 hw
  have hp1 := (wf_walk2_some hs hw2v).1
  have hchild : ∀ e, s'.child? base e = s.child? base e := fun e => by
    unfold Tables.child?; rw [hu]
  have hroot : ∀ i, s'.entry 0 i = s.entry 0 i := fun i => by
    rw [hent, ite_of_neg (fun h => wf_level3_ne_zero hs hl3 h.1.symm)]
  have hne2 : ∀ w c, isValid (s.entry 0 (index1 w)) = true →
      s.child? base (s.entry 0 (index1 w)) = some c → c ≠ t3 := by
    intro w c hvw hc he
    subst he
    rcases hs.2.2.2.2.1 (index1 w) (index1_lt w) with h0 | ⟨c', hc'⟩
    · rw [h0] at hvw; exact absurd hvw (by decide)
    · obtain rfl : c' = c := Option.some.inj (hc'.2.2.symm.trans hc)
      exact wf_not_level2_level3 hs ⟨_, hc'⟩ hl3
  have hw2 : ∀ w x, s'.walk2 base w = .ok x ↔ s.walk2 base w = .ok x := by
    intro w x
    rw [walk2_ok, walk2_ok, hroot, hchild]
    constructor
    · rintro (h | ⟨c, hvw, hc, rfl⟩)
      · exact Or.inl h
      · refine Or.inr ⟨c, hvw, hc, ?_⟩
        rw [hent, ite_of_neg (fun h => hne2 w c hvw hc h.1)]
    · rintro (h | ⟨c, hvw, hc, rfl⟩)
      · exact Or.inl h
      · refine Or.inr ⟨c, hvw, hc, ?_⟩
        rw [hent, ite_of_neg (fun h => hne2 w c hvw hc h.1)]
  refine ⟨fun w l => ⟨fun hm => ?_, fun ⟨hne, hm⟩ => ?_⟩, fun g => ?_, fun b => ?_⟩
  · obtain ⟨hreg', hal', ⟨a, c, d', hw', htb', hk', hpa', hf'⟩ | ⟨a, d', hw', hrw', hk', hf', hpa'⟩⟩ := hm
    · obtain ⟨e2, h1, h2, h3, h4, hd'⟩ := walk_ok_level3.1 hw'
      rw [hent] at hd'
      by_cases hc : c = t3 ∧ index3 w = index3 v
      · rw [ite_of_pos hc] at hd'; rw [hd'] at htb'; exact absurd htb' (by decide)
      · rw [ite_of_neg hc] at hd'
        have hsw : s.walk base w = .ok (.level3 a c d') :=
          walk_ok_level3.2 ⟨e2, (hw2 w _).1 h1, h2, h3, by rw [← hchild]; exact h4, hd'⟩
        refine ⟨fun he => hc ?_, ⟨hreg', hal', Or.inl ⟨a, c, d', hsw, htb', hk', hpa', hf'⟩⟩⟩
        subst he
        rw [hw, Except.ok.injEq, Reach.level3.injEq] at hsw
        exact ⟨hsw.2.1.symm, rfl⟩
    · obtain ⟨h1, h2, h3⟩ := walk_ok_block.1 hw'
      have hsw : s.walk base w = .ok (.block a d') := walk_ok_block.2 ⟨(hw2 w _).1 h1, h2, h3⟩
      refine ⟨fun he => ?_, ⟨hreg', hal', Or.inr ⟨a, d', hsw, hrw', hk', hf', hpa'⟩⟩⟩
      subst he; rw [hw] at hsw; simp at hsw
  · obtain ⟨hreg', hal', ⟨a, c, d', hw', htb', hk', hpa', hf'⟩ | ⟨a, d', hw', hrw', hk', hf', hpa'⟩⟩ := hm
    · obtain ⟨e2, h1, h2, h3, h4, hd'⟩ := walk_ok_level3.1 hw'
      have hc : ¬ (c = t3 ∧ index3 w = index3 v) := by
        rintro ⟨rfl, h3eq⟩
        obtain ⟨hl2', hp2', -, -⟩ := wf_walk_level3 hs hw'
        obtain ⟨rfl, e2eq⟩ := huniq _ _ _ _ _ (Or.inr hl2') (Or.inr hl2) hp2' hp2
        have hp1' := (wf_walk2_some hs h1).1
        obtain ⟨-, e1eq⟩ := huniq _ _ _ _ _ (Or.inl rfl) (Or.inl rfl) hp1' hp1
        exact hne (eq_of_index hreg' hreg e1eq e2eq h3eq hal' hv)
      refine ⟨hreg', hal', Or.inl ⟨a, c, d', walk_ok_level3.2 ⟨e2, (hw2 w _).2 h1, h2, h3,
        by rw [hchild]; exact h4, by rw [hent, ite_of_neg hc]; exact hd'⟩, htb', hk', hpa', hf'⟩⟩
    · obtain ⟨h1, h2, h3⟩ := walk_ok_block.1 hw'
      exact ⟨hreg', hal', Or.inr ⟨a, d', walk_ok_block.2 ⟨(hw2 w _).2 h1, h2, h3⟩, hrw', hk', hf',
        hpa'⟩⟩
  · simp only [Tables.G, hw2]
  · have hw3 : ∀ w a c, (∃ d, s'.walk base w = .ok (.level3 a c d)) ↔
        (∃ d, s.walk base w = .ok (.level3 a c d)) := by
      intro w a c
      simp only [walk_ok_level3, hw2, hchild]
      constructor
      · rintro ⟨-, e2, h1, h2, h3, h4, -⟩; exact ⟨_, e2, h1, h2, h3, h4, rfl⟩
      · rintro ⟨-, e2, h1, h2, h3, h4, -⟩; exact ⟨_, e2, h1, h2, h3, h4, rfl⟩
    constructor
    · rintro ⟨h1, h2, a, c, d', hw'⟩
      obtain ⟨d'', h⟩ := (hw3 b a c).1 ⟨d', hw'⟩
      exact ⟨h1, h2, a, c, d'', h⟩
    · rintro ⟨h1, h2, a, c, d', hw'⟩
      obtain ⟨d'', h⟩ := (hw3 b a c).2 ⟨d', hw'⟩
      exact ⟨h1, h2, a, c, d'', h⟩

private theorem afterUnmapPage : AfterUnmapPage := by
  intro r N s v base bits plan p hs h
  unfold Tables.unmapPage at h
  obtain ⟨u, hce, h⟩ := except_bind_ok.1 h
  obtain ⟨⟨t3, d⟩, hlf, h⟩ := except_bind_ok.1 h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hv, -, hreg, -, -⟩ := checkEntry_ok.1 hce
  obtain ⟨t2, hw, htb⟩ := pageLeaf_ok.1 hlf
  obtain ⟨-, -, hl3, hd⟩ := wf_walk_level3 hs hw
  have hk : ∃ k, Kind.ofPage d = some k := by
    rcases hs.2.2.2.2.2.2.1 t3 hl3 (index3 v) (index3_lt v) with h0 | ⟨⟨k, hk⟩, -⟩
    · rw [← hd] at h0; rw [h0] at htb; exact absurd htb (by decide)
    · exact ⟨k, by rw [hd, hk, ofPage_descriptor]⟩
  obtain ⟨k, hk⟩ := hk
  obtain ⟨h1, h2, h3⟩ := unmap_after (s' := s.apply [.store t3 (index3 v) INVALID, .invalidate v])
    hs hw hreg hv rfl (fun t i => entry_store (s := s) (u := s.used) (d := 0) (wf_level3_lt hl3).2
      (index3_lt v) t i)
  exact ⟨⟨k, hreg, hv, Or.inl ⟨t2, t3, d, hw, htb, hk, rfl, rfl⟩⟩, h1, h2, h3⟩

private theorem afterCloneKernelFrom : AfterCloneKernelFrom := by
  intro r N target source sb base bits s₁ plan hz h
  have hT := Tables.cloneKernelFromWellFormed r N target source sb base bits s₁ plan hz h
  obtain ⟨leaves, -, hpb, hused, h1, h3, hnl, hcp, hent⟩ := clone_facts hz h
  dsimp only
  generalize s₁.apply plan = T at hT hused hent ⊢
  have hu0 : 0 < source.used := by have := hT.2.1; omega
  -- the root and the level 2 entries of the walk of the source
  let R1 (w : UInt64) (t2 : Nat) : Prop := isValid (source.entry 0 (index1 w)) = true ∧
    source.child? sb (source.entry 0 (index1 w)) = some t2
  let R2 (w : UInt64) (t2 t3 : Nat) : Prop := isValid (source.entry t2 (index2 w)) = true ∧
    source.child? sb (source.entry t2 (index2 w)) = some t3
  have hTv : ∀ t i, isValid (source.entry t i) = false → T.entry t i = 0 := fun t i hv => by
    rw [hent, ite_of_neg (fun h => by rw [h.2.2] at hv; cases hv)]
  have hTt : ∀ t i c, t ∉ leaves → t < source.used → i < ENTRIES →
      isValid (source.entry t i) = true → source.child? sb (source.entry t i) = some c →
      T.entry t i = tableAt base c ∧ T.child? base (tableAt base c) = some c := by
    intro t i c htl ht hi hv hc
    have hcu := child?_some hc
    refine ⟨?_, child?_tableAt hpb (by rw [hused]; exact hcu.1) hcu.2⟩
    rw [hent, ite_of_pos ⟨ht, hi, hv⟩, copyValue, ite_of_neg (by simpa using htl), ← child?_index hc]
    rfl
  have hTl : ∀ t i, t ∈ leaves → t < source.used → i < ENTRIES →
      isValid (source.entry t i) = true → T.entry t i = source.entry t i := by
    intro t i htl ht hi hv
    rw [hent, ite_of_pos ⟨ht, hi, hv⟩, copyValue, ite_of_pos (by simpa using htl)]
  have hlvl : ∀ w t2, R1 w t2 → ∀ j, j < ENTRIES → isValid (source.entry t2 j) = true →
      isPlainTableDescriptor (source.entry t2 j) = true ∧
        ∃ c', source.child? sb (source.entry t2 j) = some c' := by
    rintro w t2 ⟨hv, hc⟩ j hj hvj
    obtain ⟨-, c, hc', h2⟩ := h1 _ (index1_lt w) hv
    obtain rfl : t2 = c := Option.some.inj (hc.symm.trans hc')
    exact h2 j hj hvj
  have hnl2 : ∀ w t2, R1 w t2 → t2 ∉ leaves := fun w t2 hr =>
    hnl t2 (Or.inr ⟨index1 w, index1_lt w, hr.1, hr.2⟩)
  have hleaf : ∀ w t2 t3, R1 w t2 → R2 w t2 t3 → t3 ∈ leaves := fun w t2 t3 hr1 hr2 =>
    (h3 t3).2 ⟨t2, ⟨index1 w, index1_lt w, hr1.1, hr1.2⟩, index2 w, index2_lt w, hr2.1, hr2.2⟩
  have hT2 : ∀ w t2 e, T.walk2 base w = .ok (some (t2, e)) ↔ R1 w t2 ∧ e = T.entry t2 (index2 w) := by
    intro w t2 e
    rw [walk2_ok]
    by_cases hv : isValid (source.entry 0 (index1 w)) = true
    · obtain ⟨-, c, hc, -⟩ := h1 _ (index1_lt w) hv
      obtain ⟨he, hc'⟩ := hTt 0 _ c (hnl 0 (Or.inl rfl)) hu0 (index1_lt w) hv hc
      rw [he]
      constructor
      · rintro (⟨hf, -⟩ | ⟨t2', -, hc2, hx⟩)
        · rw [tableAt, isValid_tableDescriptor] at hf; cases hf
        · rw [hc', Option.some.injEq] at hc2
          subst hc2
          simp only [Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          exact ⟨⟨hv, hc⟩, rfl⟩
      · rintro ⟨⟨-, hc2⟩, rfl⟩
        obtain rfl : c = t2 := Option.some.inj (hc.symm.trans hc2)
        exact Or.inr ⟨c, by rw [tableAt, isValid_tableDescriptor], hc', rfl⟩
    · have h0 := hTv 0 _ (Bool.eq_false_iff.2 hv)
      rw [h0]
      constructor
      · rintro (⟨-, hn⟩ | ⟨t2', hv', -⟩)
        · cases hn
        · exact absurd hv' (by decide)
      · rintro ⟨⟨hv', -⟩, -⟩; exact absurd hv' hv
  have hS2 : ∀ w t2 e, source.walk2 sb w = .ok (some (t2, e)) ↔
      R1 w t2 ∧ e = source.entry t2 (index2 w) := by
    intro w t2 e
    rw [walk2_ok]
    constructor
    · rintro (⟨-, hn⟩ | ⟨t2', hv, hc, hx⟩)
      · cases hn
      · simp only [Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        exact ⟨⟨hv, hc⟩, rfl⟩
    · rintro ⟨⟨hv, hc⟩, rfl⟩; exact Or.inr ⟨t2, hv, hc, rfl⟩
  have hT3 : ∀ w t2 t3 d, T.walk base w = .ok (.level3 t2 t3 d) ↔
      R1 w t2 ∧ R2 w t2 t3 ∧ d = T.entry t3 (index3 w) := by
    intro w t2 t3 d
    rw [walk_ok_level3]
    constructor
    · rintro ⟨e2, hw2, hv2, -, hc2, rfl⟩
      obtain ⟨hr1, rfl⟩ := (hT2 w t2 _).1 hw2
      by_cases hvs : isValid (source.entry t2 (index2 w)) = true
      · obtain ⟨-, c', hc'⟩ := hlvl w t2 hr1 _ (index2_lt w) hvs
        obtain ⟨he, hct⟩ := hTt t2 _ c' (hnl2 w t2 hr1) (child?_some hr1.2).1 (index2_lt w) hvs hc'
        rw [he, hct] at hc2
        obtain rfl : c' = t3 := Option.some.inj hc2
        exact ⟨hr1, ⟨hvs, hc'⟩, rfl⟩
      · rw [hTv _ _ (Bool.eq_false_iff.2 hvs)] at hv2; exact absurd hv2 (by decide)
    · rintro ⟨hr1, ⟨hvs, hc'⟩, rfl⟩
      obtain ⟨he, hct⟩ := hTt t2 _ t3 (hnl2 w t2 hr1) (child?_some hr1.2).1 (index2_lt w) hvs hc'
      exact ⟨_, (hT2 w t2 _).2 ⟨hr1, rfl⟩, by rw [he, tableAt, isValid_tableDescriptor],
        by rw [he, tableAt, typeBits_tableDescriptor]; decide, by rw [he]; exact hct, rfl⟩
  have hS3 : ∀ w t2 t3 d, source.walk sb w = .ok (.level3 t2 t3 d) ↔
      R1 w t2 ∧ R2 w t2 t3 ∧ d = source.entry t3 (index3 w) := by
    intro w t2 t3 d
    rw [walk_ok_level3]
    constructor
    · rintro ⟨e2, hw2, hv2, -, hc2, rfl⟩
      obtain ⟨hr1, rfl⟩ := (hS2 w t2 e2).1 hw2
      exact ⟨hr1, ⟨hv2, hc2⟩, rfl⟩
    · rintro ⟨hr1, ⟨hvs, hc'⟩, rfl⟩
      exact ⟨_, (hS2 w t2 _).2 ⟨hr1, rfl⟩, hvs,
        by rw [typeBits_of_isPlain (hlvl w t2 hr1 _ (index2_lt w) hvs).1]; decide, hc', rfl⟩
  have hTb : ∀ w t2 d, T.walk base w ≠ .ok (.block t2 d) := by
    intro w t2 d hw
    obtain ⟨hw2, hv, hb⟩ := walk_ok_block.1 hw
    obtain ⟨hr1, rfl⟩ := (hT2 w t2 d).1 hw2
    by_cases hvs : isValid (source.entry t2 (index2 w)) = true
    · obtain ⟨-, c', hc'⟩ := hlvl w t2 hr1 _ (index2_lt w) hvs
      rw [(hTt t2 _ c' (hnl2 w t2 hr1) (child?_some hr1.2).1 (index2_lt w) hvs hc').1, tableAt,
        typeBits_tableDescriptor] at hb
      exact absurd hb (by decide)
    · rw [hTv _ _ (Bool.eq_false_iff.2 hvs)] at hv; exact absurd hv (by decide)
  have hSb : ∀ w t2 d, source.walk sb w ≠ .ok (.block t2 d) := by
    intro w t2 d hw
    obtain ⟨hw2, hv, hb⟩ := walk_ok_block.1 hw
    obtain ⟨hr1, rfl⟩ := (hS2 w t2 d).1 hw2
    rw [typeBits_of_isPlain (hlvl w t2 hr1 _ (index2_lt w) hv).1] at hb
    exact absurd hb (by decide)
  have hval : ∀ {e : UInt64}, typeBits e = TABLE_OR_PAGE → isValid e = true := fun h => by
    simp only [isValid, h, TABLE_OR_PAGE]; decide
  refine ⟨fun w l hm => ?_, fun w l => ⟨fun hm => ?_, fun hm => ?_⟩, fun g => ⟨?_, ?_⟩,
    fun b => ⟨?_, ?_⟩, fun w t2 => ⟨?_, ?_⟩, fun w t2 t3 => ⟨?_, ?_⟩, hused⟩
  · obtain ⟨-, -, ⟨t2, t3, d, hw, htb, hk, hpa, hf⟩ | ⟨t2, d, hw, -⟩⟩ := hm
    · obtain ⟨hr1, hr2, rfl⟩ := (hS3 w t2 t3 d).1 hw
      have hc := hcp t3 (hleaf w t2 t3 hr1 hr2) _ (index3_lt w) (hval htb)
      simp only [copyableLeaf, Bool.and_eq_true, List.any_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hc
      obtain ⟨⟨k, hkm, hkd⟩, hlt⟩ := hc
      rw [← hkd, ofPage_descriptor, Option.some.injEq] at hk
      refine ⟨hf, ?_, by rw [hpa]; exact hlt⟩
      rw [← hk]; exact List.contains_iff_mem.2 hkm
    · exact absurd hw (hSb w t2 d)
  · obtain ⟨hreg, hal, ⟨t2, t3, d, hw, htb, hk, hpa, hf⟩ | ⟨t2, d, hw, -⟩⟩ := hm
    · obtain ⟨hr1, hr2, rfl⟩ := (hT3 w t2 t3 d).1 hw
      by_cases hvs : isValid (source.entry t3 (index3 w)) = true
      · rw [hTl t3 _ (hleaf w t2 t3 hr1 hr2) (child?_some hr2.2).1 (index3_lt w) hvs] at htb hk hpa
        exact ⟨hreg, hal, Or.inl ⟨t2, t3, _, (hS3 w t2 t3 _).2 ⟨hr1, hr2, rfl⟩, htb, hk, hpa, hf⟩⟩
      · rw [hTv _ _ (Bool.eq_false_iff.2 hvs)] at htb; exact absurd htb (by decide)
    · exact absurd hw (hTb w t2 d)
  · obtain ⟨hreg, hal, ⟨t2, t3, d, hw, htb, hk, hpa, hf⟩ | ⟨t2, d, hw, -⟩⟩ := hm
    · obtain ⟨hr1, hr2, rfl⟩ := (hS3 w t2 t3 d).1 hw
      have he := hTl t3 _ (hleaf w t2 t3 hr1 hr2) (child?_some hr2.2).1 (index3_lt w) (hval htb)
      refine ⟨hreg, hal, Or.inl ⟨t2, t3, _, (hT3 w t2 t3 _).2 ⟨hr1, hr2, rfl⟩, ?_, ?_, ?_, hf⟩⟩ <;>
        rw [he] <;> assumption
    · exact absurd hw (hSb w t2 d)
  · rintro ⟨g1, g2, t2, e, he⟩
    exact ⟨g1, g2, t2, _, (hS2 g t2 _).2 ⟨((hT2 g t2 e).1 he).1, rfl⟩⟩
  · rintro ⟨g1, g2, t2, e, he⟩
    exact ⟨g1, g2, t2, _, (hT2 g t2 _).2 ⟨((hS2 g t2 e).1 he).1, rfl⟩⟩
  · rintro ⟨b1, b2, t2, t3, d, hw⟩
    obtain ⟨hr1, hr2, -⟩ := (hT3 b t2 t3 d).1 hw
    exact ⟨b1, b2, t2, t3, _, (hS3 b t2 t3 _).2 ⟨hr1, hr2, rfl⟩⟩
  · rintro ⟨b1, b2, t2, t3, d, hw⟩
    obtain ⟨hr1, hr2, -⟩ := (hS3 b t2 t3 d).1 hw
    exact ⟨b1, b2, t2, t3, _, (hT3 b t2 t3 _).2 ⟨hr1, hr2, rfl⟩⟩
  · rintro ⟨e, he⟩; exact ⟨_, (hS2 w t2 _).2 ⟨((hT2 w t2 e).1 he).1, rfl⟩⟩
  · rintro ⟨e, he⟩; exact ⟨_, (hT2 w t2 _).2 ⟨((hS2 w t2 e).1 he).1, rfl⟩⟩
  · rintro ⟨d, hw⟩
    obtain ⟨hr1, hr2, -⟩ := (hT3 w t2 t3 d).1 hw
    exact ⟨_, (hS3 w t2 t3 _).2 ⟨hr1, hr2, rfl⟩⟩
  · rintro ⟨d, hw⟩
    obtain ⟨hr1, hr2, -⟩ := (hS3 w t2 t3 d).1 hw
    exact ⟨_, (hT3 w t2 t3 _).2 ⟨hr1, hr2, rfl⟩⟩

private theorem layoutPages_mem (k : Kind) : ∀ (count pa v : Nat), pa ≤ v →
    v + PAGE_SIZE ≤ pa + count * PAGE_SIZE → (v - pa) % PAGE_SIZE = 0 → v < UInt64.size →
    ∃ x ∈ layoutPages k count pa, x.va.toNat = v
  | 0, pa, v, h1, h2, _, _ => by simp only [PAGE_SIZE] at h2; omega
  | count + 1, pa, v, h1, h2, h3, h4 => by
    by_cases he : v = pa
    · subst he
      exact ⟨_, List.mem_cons_self, UInt64.toNat_ofNat_of_lt' h4⟩
    · obtain ⟨x, hx, hxv⟩ := layoutPages_mem k count (pa + PAGE_SIZE) v
        (by simp only [PAGE_SIZE] at h3 ⊢; omega) (by simp only [PAGE_SIZE] at h2 ⊢; omega)
        (by simp only [PAGE_SIZE] at h3 ⊢; omega) h4
      exact ⟨x, List.mem_cons_of_mem _ hx, hxv⟩

private theorem mem_rangePages {bits : UInt8} {j : LayoutRange} (hj : LayoutOk bits j) {v : Nat}
    (h1 : v % PAGE_SIZE = 0) (h2 : j.range.start.toNat ≤ v) (h3 : v + PAGE_SIZE ≤ j.range.endNat) :
    ∃ x ∈ rangePages j, x.va.toNat = v := by
  obtain ⟨a1, a2, a3, -⟩ := hj
  simp only [PhysRange.endNat] at a2 a3 h3
  exact layoutPages_mem j.kind _ _ v h2 (by simp only [PAGE_SIZE] at a1 a2 h3 ⊢; omega)
    (by simp only [PAGE_SIZE] at a1 h1 h2 ⊢; omega)
    (by simp only [VA_LIMIT, PAGE_SIZE, UInt64.size] at a3 h3 ⊢; omega)

private theorem afterKernelMap : AfterKernelMap := by
  intro N s layout base bits s₁ plan hs h
  obtain ⟨leaves, hl, happ, hN, -, -, hmap, hok⟩ := kernelMap_facts hs h
  obtain ⟨hgd, hpw⟩ := kernelMap_checks h
  dsimp only
  rw [happ]
  have hsrt : ∀ j, j ∈ sortByKey (·.range.start.toNat) layout.ranges ↔ j ∈ layout.ranges :=
    fun j => (sortByKey_perm _ _).mem_iff
  have hx : ∀ x ∈ leaves.map Prod.fst, ∃ j ∈ layout.ranges, x ∈ rangePages j ∧
      j.HoldsPage x.va.toNat ∧ x.form = .page ∧ x.desc = descriptor j.kind x.va ∧
      x.va.toNat + PAGE_SIZE ≤ VA_LIMIT := by
    intro x hxm
    rw [hmap, List.mem_flatMap] at hxm
    obtain ⟨j, hj, hxj⟩ := hxm
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (rangePages_spec (hok j hj)).1 x hxj
    have := (hok j hj).2.2.1
    rw [h4]
    exact ⟨j, (hsrt j).1 hj, hxj, ⟨h3, h1, h2⟩, h5, h6, by omega⟩
  have hj : ∀ j ∈ layout.ranges, ∀ v, j.HoldsPage v →
      ∃ x ∈ leaves.map Prod.fst, x ∈ rangePages j ∧ x.va.toNat = v := by
    rintro j hjm v ⟨h1, h2, h3⟩
    have hj' := (hsrt j).2 hjm
    obtain ⟨x, hxj, hxv⟩ := mem_rangePages (hok j hj') h1 h2 h3
    exact ⟨x, by rw [hmap]; exact List.mem_flatMap.2 ⟨j, hj', hxj⟩, hxj, hxv⟩
  have hpage : ∀ x ∈ leaves.map Prod.fst, ∀ w : UInt64, w.toNat % PAGE_SIZE = 0 →
      x.va.toNat ≤ w.toNat → w.toNat < x.va.toNat + x.form.size → w = x.va := by
    intro x hxm w h1 h2 h3
    obtain ⟨j, -, -, hhold, hxf, -⟩ := hx x hxm
    rw [hxf] at h3
    apply UInt64.toNat_inj.1
    have := hhold.1
    simp only [Form.size, PAGE_SIZE] at h1 h2 h3 this; omega
  refine ⟨fun j hjm v hv l => ?_, ?_, fun j hjm g hg hin => ?_, fun v l => ?_, fun g => ?_,
    fun b => ?_, fun g hg hun l hm => ?_⟩
  · obtain ⟨x, hxm, -, hxv⟩ := hj j hjm v hv
    have hxe : UInt64.ofNat v = x.va := by rw [← hxv]; exact UInt64.ofNat_toNat
    rw [hxe]
    exact leaf_unmapped hs hl hxm (by rw [hxv]; exact hv.1) (Nat.le_refl _)
      (by have := form_size_pos x.form; omega) l
  · have hR : ∀ {a b : LayoutRange}, (∀ v, ¬ (a.HoldsPage v ∧ b.HoldsPage v)) →
        ∀ v, ¬ (b.HoldsPage v ∧ a.HoldsPage v) := fun h v hv => h v ⟨hv.2, hv.1⟩
    refine (List.Perm.pairwise_iff hR (sortByKey_perm (·.range.start.toNat) layout.ranges)).1 ?_
    refine hpw.imp_of_mem fun {j j'} hjm hj'm hmeet v hv => ?_
    obtain ⟨⟨-, a2, a3⟩, hv'⟩ := hv
    obtain ⟨x, -, hxj, hxv⟩ := hj j' ((hsrt j').1 hj'm) v hv'
    have hm := hmeet x hxj
    obtain ⟨-, -, -, hxva, hxf, -⟩ := (rangePages_spec (hok j' hj'm)).1 x hxj
    simp only [MapLeaf.meets, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt, hxf,
      Form.size] at hm
    rw [← hxva, hxv] at hm
    simp only [PAGE_SIZE] at hm a3; omega
  · obtain ⟨h1, h2⟩ := hin
    have hj' := (hsrt j).2 hjm
    obtain ⟨a1, a2, -, -⟩ := hok j hj'
    obtain ⟨x, -, hxj, hxv⟩ := hj j hjm (g.toNat / PAGE_SIZE * PAGE_SIZE)
      ⟨by simp only [PAGE_SIZE]; omega, by simp only [PAGE_SIZE] at a1 ⊢; omega,
        by simp only [PAGE_SIZE] at a2 ⊢; omega⟩
    have hgx := hgd j hj' x hxj
    simp only [MapLeaf.isGuard, List.any_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hgx
    exact hgx g hg ⟨by rw [hxv]; simp only [PAGE_SIZE]; omega, by rw [hxv]; simp only [PAGE_SIZE]; omega⟩
  · rw [final_M_iff hs hl hN]
    constructor
    · rintro (hm | ⟨x, hxm, hal, h1, h2, h3, h4, -⟩)
      · exact Or.inl hm
      · obtain ⟨j, hjm, -, hhold, hxf, hxd, hlim⟩ := hx x hxm
        obtain rfl := hpage x hxm v hal h1 h2
        obtain ⟨hpa, hk⟩ := h4 hxf
        rw [hxd, ofPage_descriptor, Option.some.injEq] at hk
        rw [hxd, outputAddress_descriptor, outputAddress_of_aligned hhold.1
          (by simp only [VA_LIMIT, PAGE_SIZE] at hlim; omega)] at hpa
        refine Or.inr ⟨j, hjm, hhold, ?_⟩
        obtain ⟨pa, kd, fm⟩ := l
        simp only [Leaf.mk.injEq] at hpa hk h3 ⊢
        exact ⟨hpa, hk.symm, by rw [h3, hxf]⟩
    · rintro (hm | ⟨j, hjm, hhold, rfl⟩)
      · exact Or.inl hm
      · obtain ⟨x, hxm, hxj, hxv⟩ := hj j hjm _ hhold
        obtain ⟨-, hp2, hpal, hxva, hxf, hxd⟩ :=
          (rangePages_spec (hok j ((hsrt j).2 hjm))).1 x hxj
        have hlim := (hok j ((hsrt j).2 hjm)).2.2.1
        obtain rfl : v = x.va := UInt64.toNat_inj.1 hxv.symm
        rw [← hxva] at hxd
        refine Or.inr ⟨x, hxm, hhold.1, Nat.le_refl _, by have := form_size_pos x.form; omega,
          by rw [hxf], fun _ => ⟨?_, ?_⟩, (fun hb => by rw [hxf] at hb; cases hb)⟩
        · rw [hxd, outputAddress_descriptor, outputAddress_of_aligned hhold.1
            (by rw [← hxva] at hp2; simp only [VA_LIMIT, PAGE_SIZE] at hlim hp2; omega)]
        · rw [hxd, ofPage_descriptor]
  · rw [final_G_iff hs hl hN]
    constructor
    · rintro (h | ⟨x, hxm, rfl⟩)
      · exact Or.inl h
      · obtain ⟨j, hjm, -, hhold, -⟩ := hx x hxm
        exact Or.inr ⟨j, hjm, x.va, hhold, rfl⟩
    · rintro (h | ⟨j, hjm, v, hhold, rfl⟩)
      · exact Or.inl h
      · obtain ⟨x, hxm, -, hxv⟩ := hj j hjm _ hhold
        exact Or.inr ⟨x, hxm, by rw [UInt64.toNat_inj.1 hxv]⟩
  · rw [final_P_iff hs hl hN]
    constructor
    · rintro (h | ⟨x, hxm, -, rfl⟩)
      · exact Or.inl h
      · obtain ⟨j, hjm, -, hhold, -⟩ := hx x hxm
        exact Or.inr ⟨j, hjm, x.va, hhold, rfl⟩
    · rintro (h | ⟨j, hjm, v, hhold, rfl⟩)
      · exact Or.inl h
      · obtain ⟨x, hxm, -, hxv⟩ := hj j hjm _ hhold
        obtain ⟨j', -, -, -, hxf, -⟩ := hx x hxm
        exact Or.inr ⟨x, hxm, hxf, by rw [UInt64.toNat_inj.1 hxv]⟩
  · rw [final_M_iff hs hl hN] at hm
    rcases hm with hm | ⟨x, hxm, hal, h1, h2, -⟩
    · exact hun l hm
    · obtain ⟨j, hjm, hxj, -, -, -, -⟩ := hx x hxm
      have hgx := hgd j ((hsrt j).2 hjm) x hxj
      simp only [MapLeaf.isGuard, List.any_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hgx
      have hw : (UInt64.ofNat (pageDown g.toNat)).toNat = pageDown g.toNat :=
        UInt64.toNat_ofNat_of_lt' (by
          have := g.toNat_lt
          simp only [pageDown, PAGE_SIZE, UInt64.size] at this ⊢; omega)
      rw [hpage x hxm _ hal h1 h2] at hw
      apply hgx g hg
      rw [hw]
      simp only [pageDown, PAGE_SIZE]; omega

/-- A page of a usable range lies in a leaf of the range. -/
private theorem cover_pa {bits : UInt8} {u : Krepi.Spec.Fdt.Span} (hu : UsableOk bits u) {p : Nat}
    (hp : p % PAGE_SIZE = 0) (h1 : u.start.toNat ≤ p) (h2 : p + PAGE_SIZE ≤ u.endNat) :
    ∃ y ∈ usableLeaves u, y.pa.toNat ≤ p ∧ p < y.pa.toNat + y.form.size := by
  have hlim := hu.2.2.1
  rcases usableLeaves_cover hu hp h1 h2 with ⟨hy, -⟩ | ⟨hy, -, -⟩
  · refine ⟨_, hy, ?_⟩
    show (UInt64.ofNat p).toNat ≤ p ∧ p < (UInt64.ofNat p).toNat + PAGE_SIZE
    rw [UInt64.toNat_ofNat_of_lt' (by simp only [VA_LIMIT, PAGE_SIZE, UInt64.size] at hlim h2 ⊢; omega)]
    simp only [PAGE_SIZE]; omega
  · refine ⟨_, hy, ?_⟩
    show (UInt64.ofNat (p / BLOCK_SIZE * BLOCK_SIZE)).toNat ≤ p ∧
      p < (UInt64.ofNat (p / BLOCK_SIZE * BLOCK_SIZE)).toNat + BLOCK_SIZE
    rw [UInt64.toNat_ofNat_of_lt' (by
      simp only [VA_LIMIT, PAGE_SIZE, BLOCK_SIZE, UInt64.size] at hlim h2 ⊢; omega)]
    simp only [BLOCK_SIZE]; omega

private theorem afterDirectMap : AfterDirectMap := by
  intro N s B base bits s₁ plan hs h
  obtain ⟨leaves, hl, happ, hN, -, -, -, hmap, hok⟩ := directMap_facts hs h
  have hpw := directMap_apart h
  dsimp only
  rw [happ]
  have hsrt : ∀ u, u ∈ sortByKey (·.start.toNat) B.availableRanges ↔ u ∈ B.availableRanges :=
    fun u => (sortByKey_perm _ _).mem_iff
  have hD : DIRECT_BASE.toNat % BLOCK_SIZE = 0 := by decide
  have hup : ∀ p, usablePage B p = true ↔ p % PAGE_SIZE = 0 ∧
      ∃ u ∈ B.availableRanges, u.start.toNat ≤ p ∧ p + PAGE_SIZE ≤ u.endNat := by
    intro p; simp [usablePage]
  have hbf : ∀ p, blockForm B p = true ↔ ∃ u ∈ B.availableRanges,
      u.start.toNat ≤ p / BLOCK_SIZE * BLOCK_SIZE ∧
        p / BLOCK_SIZE * BLOCK_SIZE + BLOCK_SIZE ≤ u.endNat := by
    intro p; simp [blockForm]
  have apart : ∀ u ∈ B.availableRanges, ∀ u' ∈ B.availableRanges, ∀ p, p % PAGE_SIZE = 0 →
      u.start.toNat ≤ p → p + PAGE_SIZE ≤ u.endNat → u'.start.toNat ≤ p →
      p + PAGE_SIZE ≤ u'.endNat → u = u' := by
    intro u hu u' hu' p hp h1 h2 h1' h2'
    have meet : ∀ a b : Krepi.Spec.Fdt.Span, b ∈ sortByKey (·.start.toNat) B.availableRanges → a.start.toNat ≤ p →
        p + PAGE_SIZE ≤ a.endNat → b.start.toNat ≤ p → p + PAGE_SIZE ≤ b.endNat →
        ¬ ∀ y ∈ usableLeaves b, y.meets a.start.toNat a.endNat = false := by
      intro a b hb ha1 ha2 hb1 hb2 hR
      obtain ⟨y, hy, hy1, hy2⟩ := cover_pa (hok b hb) hp hb1 hb2
      have := hR y hy
      simp only [MapLeaf.meets, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt] at this
      simp only [PAGE_SIZE] at ha2; omega
    rcases pairwise_mem hpw ((hsrt u).2 hu) ((hsrt u').2 hu') with he | hR | hR
    · exact he
    · exact absurd hR (meet u u' ((hsrt u').2 hu') h1 h2 h1' h2')
    · exact absurd hR (meet u' u ((hsrt u).2 hu) h1' h2' h1 h2)
  have hcan : ∀ p, usablePage B p = true → p < VA_LIMIT ∧
      (finalSet s base leaves).M base (DIRECT_BASE ||| UInt64.ofNat p)
        ⟨UInt64.ofNat p, .readWrite, if blockForm B p then .block else .page⟩ := by
    intro p hp
    obtain ⟨hpa, u, hu, h1, h2⟩ := (hup p).1 hp
    obtain ⟨hlt, hm⟩ := directMap_M_of_usable hs h hu hpa h1 h2
    rw [happ] at hm
    refine ⟨hlt, ?_⟩
    have hiff : (u.start.toNat ≤ p / BLOCK_SIZE * BLOCK_SIZE ∧
        p / BLOCK_SIZE * BLOCK_SIZE + BLOCK_SIZE ≤ u.endNat) ↔ blockForm B p = true := by
      rw [hbf]
      constructor
      · intro hc; exact ⟨u, hu, hc⟩
      · rintro ⟨u', hu', hc'⟩
        obtain rfl := apart u hu u' hu' p hpa h1 h2
          (by simp only [BLOCK_SIZE] at hc' ⊢; omega)
          (by simp only [PAGE_SIZE, BLOCK_SIZE] at hpa hc' ⊢; omega)
        exact hc'
    by_cases hb : blockForm B p = true
    · rw [ite_of_pos (hiff.2 hb)] at hm; rw [ite_of_pos hb]; exact hm
    · rw [ite_of_neg (fun h => hb (hiff.1 h))] at hm; rw [ite_of_neg hb]; exact hm
  have hleaf : ∀ x ∈ leaves.map Prod.fst, ∃ u ∈ B.availableRanges, u.start.toNat ≤ x.pa.toNat ∧
      x.pa.toNat + x.form.size ≤ u.endNat ∧ u.endNat ≤ VA_LIMIT ∧ DirectLeaf x ∧
      x.va.toNat = DIRECT_BASE.toNat + x.pa.toNat := by
    intro x hxm
    have hxm' := hxm
    rw [hmap, List.mem_flatMap] at hxm'
    obtain ⟨u, hu, hxu⟩ := hxm'
    obtain ⟨h1, h2, h3⟩ := (usableLeaves_spec (hok u hu)).1 x hxu
    have hlim := (hok u hu).2.2.1
    exact ⟨u, (hsrt u).1 hu, h1, h2, hlim, h3,
      directLeaf_va h3 (by have := form_size_pos x.form; omega)⟩
  have hpal : ∀ x ∈ leaves.map Prod.fst, x.pa.toNat % PAGE_SIZE = 0 := by
    intro x hxm
    obtain ⟨u, -, -, -, -, ⟨-, hal, -, -⟩, -⟩ := hleaf x hxm
    cases hf : x.form <;> rw [hf] at hal <;> simp only [Form.size, PAGE_SIZE, BLOCK_SIZE] at hal ⊢ <;>
      omega
  have husable : ∀ x ∈ leaves.map Prod.fst, ∀ q, q % PAGE_SIZE = 0 → x.pa.toNat ≤ q →
      q < x.pa.toNat + x.form.size → usablePage B q = true := by
    intro x hxm q hq h1 h2
    obtain ⟨u, hu, hu1, hu2, -, ⟨-, hal, -, -⟩, -⟩ := hleaf x hxm
    refine (hup q).2 ⟨hq, u, hu, by omega, ?_⟩
    cases hf : x.form <;> rw [hf] at hal h2 hu2 <;>
      simp only [Form.size, PAGE_SIZE, BLOCK_SIZE] at hal h2 hu2 hq ⊢ <;> omega
  have hdir : ∀ p, p < VA_LIMIT → (DIRECT_BASE ||| UInt64.ofNat p).toNat = DIRECT_BASE.toNat + p := by
    intro p hp
    have hpn : (UInt64.ofNat p).toNat = p :=
      UInt64.toNat_ofNat_of_lt' (by simp only [VA_LIMIT, UInt64.size] at hp ⊢; omega)
    rw [direct_or (by rw [hpn]; exact hp), hpn]
  refine ⟨fun p hp => ⟨(hcan p hp).1, fun l => ?_⟩, fun v l => ⟨fun hm => ?_, ?_⟩,
    fun g => ⟨fun hg => ?_, ?_⟩, fun b => ⟨fun hb => ?_, ?_⟩⟩
  · obtain ⟨hpa, u, hu, h1, h2⟩ := (hup p).1 hp
    have hu' := (hsrt u).2 hu
    obtain ⟨y, hy, hy1, hy2⟩ := cover_pa (hok u hu') hpa h1 h2
    have hym : y ∈ leaves.map Prod.fst := by rw [hmap]; exact List.mem_flatMap.2 ⟨u, hu', hy⟩
    obtain ⟨u2, -, -, -, -, -, hyva⟩ := hleaf y hym
    have hv := hdir p (hcan p hp).1
    refine leaf_unmapped hs hl hym ?_ ?_ ?_ l <;> rw [hv] <;> (try rw [hyva]) <;>
      generalize DIRECT_BASE.toNat = D at hD ⊢
    · simp only [BLOCK_SIZE, PAGE_SIZE] at hD hpa ⊢; omega
    · omega
    · omega
  · rcases (final_M_iff hs hl hN).1 hm with hm' | ⟨x, hxm, hal, h1, h2, -⟩
    · exact Or.inl hm'
    · obtain ⟨u, hu, hu1, hu2, -, -, hxva⟩ := hleaf x hxm
      have hxp := hpal x hxm
      rw [hxva] at h1 h2
      obtain ⟨p, hp⟩ : ∃ p, v.toNat = DIRECT_BASE.toNat + p := ⟨v.toNat - DIRECT_BASE.toNat, by omega⟩
      rw [hp] at hal h1 h2
      have hpu : usablePage B p = true := husable x hxm p (by
          generalize DIRECT_BASE.toNat = D at hD hal
          simp only [BLOCK_SIZE, PAGE_SIZE] at hD hal ⊢; omega) (by omega) (by omega)
      have hve : v = DIRECT_BASE ||| UInt64.ofNat p :=
        UInt64.toNat_inj.1 (by rw [hdir p (hcan p hpu).1, hp])
      subst hve
      exact Or.inr ⟨p, hpu, rfl, M_unique hm (hcan p hpu).2⟩
  · rintro (hm | ⟨p, hp, rfl, rfl⟩)
    · exact final_old_M hs hl hN hm
    · exact (hcan p hp).2
  · rcases (final_G_iff hs hl hN).1 hg with h | ⟨x, hxm, rfl⟩
    · exact Or.inl h
    · obtain ⟨u, -, -, -, -, ⟨hxv, -, -, -⟩, -⟩ := hleaf x hxm
      refine Or.inr ⟨x.pa.toNat, husable x hxm _ (hpal x hxm) (Nat.le_refl _)
        (by have := form_size_pos x.form; omega), ?_⟩
      rw [UInt64.ofNat_toNat, ← hxv]
  · rintro (h | ⟨p, hp, rfl⟩)
    · exact (final_G_iff hs hl hN).2 (Or.inl h)
    · exact G_of_M (hcan p hp).2
  · rcases (final_P_iff hs hl hN).1 hb with h | ⟨x, hxm, hxf, rfl⟩
    · exact Or.inl h
    · obtain ⟨u, -, -, hu2, hulim, ⟨hxv, -, hxd, -⟩, hxva⟩ := hleaf x hxm
      have hxp := hpal x hxm
      have hpu := husable x hxm x.pa.toNat hxp (Nat.le_refl _)
        (by rw [hxf]; simp only [Form.size, PAGE_SIZE]; omega)
      have hlim : x.pa.toNat < 2 ^ 48 := by
        rw [hxf] at hu2; simp only [Form.size, VA_LIMIT, PAGE_SIZE] at hu2 hulim; omega
      have hm1 : (finalSet s base leaves).M base x.va ⟨x.pa, .readWrite, .page⟩ :=
        final_new_M hs hl hN hxm (by
            rw [hxva]; generalize DIRECT_BASE.toNat = D at hD
            simp only [BLOCK_SIZE, PAGE_SIZE] at hD hxp ⊢; omega) (Nat.le_refl _)
          (by have := form_size_pos x.form; omega) (by rw [hxf])
          (fun _ => ⟨by rw [hxd hxf, outputAddress_descriptor, outputAddress_of_aligned hxp hlim],
            by rw [hxd hxf, ofPage_descriptor]⟩) (fun hb' => by rw [hxf] at hb'; cases hb')
      have hm2 := (hcan _ hpu).2
      rw [UInt64.ofNat_toNat, ← hxv] at hm2
      have hfe := congrArg Leaf.form (M_unique hm1 hm2)
      have hbf' : blockForm B x.pa.toNat = false := by
        cases hb' : blockForm B x.pa.toNat
        · rfl
        · rw [hb'] at hfe; cases hfe
      exact Or.inr ⟨x.pa.toNat, hpu, hbf', by rw [UInt64.ofNat_toNat, ← hxv]⟩
  · rintro (h | ⟨p, hp, hbf', rfl⟩)
    · exact (final_P_iff hs hl hN).2 (Or.inl h)
    · refine P_of_M (hcan p hp).2 ?_
      show (if blockForm B p = true then Form.block else Form.page) = Form.page
      rw [hbf']; rfl

/-! ## After every write: the page ownership table -/

private theorem afterOwnershipNew : AfterOwnershipNew := by
  intro E X arena banks exclusions t h
  have hwf := Ownership.newOwnershipWellFormed E X arena banks exclusions t h
  obtain ⟨hp, ha, hne, hlen, ho, hx, hl, rfl⟩ := new_ok h
  have hperm := sortByKey_perm (·.start.toNat) banks
  refine ⟨ha, hne, hp, anyOverlap_eq_false ho, hlen, hx, hl, fun q hq ⟨b, hb, hbq⟩ => ?_, rfl⟩
  by_cases hin : ∃ e ∈ initialExtents (sortByKey (·.start.toNat) banks) exclusions,
      e.range.holdsPage q = true
  · obtain ⟨e, he, heq⟩ := hin
    have hfree : e.holding = .free := by
      obtain ⟨j, c, -, he'⟩ := mem_initialExtents.1 he
      exact (mem_bankExtents he').2.1
    rw [ownerOf_of_mem hwf.2.2.2.2.2.2.1 he heq, hfree]
    have hnt := ((initialExtents_holds_iff hwf.2.2.1 hq).1 ⟨e, he, heq⟩).2
    cases hfx : firstExcluder exclusions q with
    | none => rfl
    | some x =>
      obtain ⟨y, hy, hyt⟩ := (firstExcluder_isSome exclusions q).1 (by rw [hfx]; rfl)
      rw [hnt y hy] at hyt; cases hyt
  · rw [ownerOf_of_forall (fun x hx => by
      cases hxq : x.range.holdsPage q
      · rfl
      · exact absurd ⟨x, hx, hxq⟩ hin)]
    have hany : (sortByKey (·.start.toNat) banks).any (·.holdsPage q) = true :=
      List.any_eq_true.2 ⟨b, hperm.mem_iff.2 hb, hbq⟩
    simp only [hany, ite_true]
    cases hfx : firstExcluder exclusions q with
    | none =>
      refine absurd ((initialExtents_holds_iff hwf.2.2.1 hq).2 ⟨⟨b, hperm.mem_iff.2 hb, hbq⟩,
        fun y hy => ?_⟩) hin
      cases hyt : y.range.touchesPage q with
      | false => rfl
      | true =>
        have := (firstExcluder_isSome exclusions q).2 ⟨y, hy, hyt⟩
        rw [hfx] at this; cases this
    | some x => rfl

/-- A page of a range inside an extent is a page of the extent. -/
private theorem holds_of_contains {e r : PhysRange} (hc : e.contains r = true) {q : Nat}
    (hq : r.holdsPage q = true) : e.holdsPage q = true := by
  simp only [PhysRange.contains, Bool.and_eq_true, decide_eq_true_eq] at hc
  rw [holdsPage_iff] at hq ⊢
  exact ⟨Nat.le_trans hc.1 hq.1, Nat.le_trans hq.2 hc.2⟩

private theorem afterAssign : AfterAssign := by
  refine ⟨fun E X t c zeroed t' a hinv hch h => ?_, fun E X t c => rfl⟩
  have hwf := hinv.1
  obtain ⟨hz, ht⟩ := assign_ok h
  obtain ⟨g, hg, hg', ha, -, -, -, -, hown⟩ := assign_spec hwf hch h
  obtain ⟨⟨e, he, hef, hec⟩, -⟩ := take_extents ht
  refine ⟨hz, g, hg, fun q hq hqr => ?_, ⟨e, he, hef, hec⟩, hown, hg', ha⟩
  rw [ownerOf_of_mem hwf.2.2.2.2.2.2.1 he (holds_of_contains hec hqr), hef]; rfl

private theorem afterReserve : AfterReserve := by
  intro E X t owner pages alignment p t' r hinv h
  obtain ⟨c, g, hch, hg, hg', hr, -, -, -, -, hown⟩ := reserve_spec hinv.1 h
  obtain ⟨-, -, -, -, -, hco, -⟩ := choose_ok hch
  rw [hco] at hown hr
  exact ⟨c, g, hch, hg, hown, hg', hr⟩

/-- The pages of an extent of a table that keeps `HolderRanges`, held by a
holder, are exactly those whose owner is that holder. -/
private theorem holder_pages {E X : Nat} {t : Ownership E X} (hinv : t.Invariant) {e : Extent}
    (he : e ∈ t.extents) {o n : UInt64} {s : HoldState} (hh : e.holding = .held o n s) {q : Nat}
    (hq : q % PAGE_SIZE = 0) : t.ownerOf q = some (.held o n s) ↔ e.range.holdsPage q = true := by
  constructor
  · intro hown
    exact (hinv.2.2.1 e he o n s hh q hq).1 ⟨o, s, hown⟩
  · intro hqe
    rw [ownerOf_of_mem hinv.1.2.2.2.2.2.2.1 he hqe, hh]; rfl

private theorem afterPublish : AfterPublish := by
  intro E X t owner x t' a hinv h
  obtain ⟨ha, -, -, -, -, hc, ⟨e, he, her, heh⟩, hown, harena, howner⟩ := publish_spec hinv.1 h
  refine ⟨harena, howner, fun q hq => ?_, fun q _ => hown q, hc, ha⟩
  rw [← her]
  exact holder_pages hinv he heh hq

private theorem afterCancel : AfterCancel := by
  refine ⟨fun E X t owner r t' hinv h => ?_, fun E X t owner r hr => ?_⟩
  · obtain ⟨hatt, -, -, -, -, hc, ⟨e, he, her, heh⟩, hown, harena, howner⟩ := cancel_spec hinv.1 h
    refine ⟨hatt, harena, howner, fun q hq => ?_, hown, hc⟩
    rw [← her]
    exact holder_pages hinv he heh hq
  · unfold Ownership.cancel
    rw [hr]; rfl

private theorem afterRelease : AfterRelease := by
  intro E X t owner x t' hinv h
  obtain ⟨-, -, -, -, hc, ⟨e, he, her, heh⟩, hown, harena, howner⟩ := release_spec hinv.1 h
  refine ⟨harena, howner, fun q hq => ?_, hown, hc⟩
  rw [← her]
  exact holder_pages hinv he heh hq

/-! ## After every write -/

public theorem afterEveryWrite : AfterEveryWrite :=
  ⟨afterNew, afterReset, afterMapPage, afterMapBlock, afterUnmapPage, afterCloneKernelFrom,
    afterKernelMap, afterDirectMap, afterOwnershipNew, afterAssign, afterReserve, afterPublish,
    afterCancel, afterRelease⟩

end Krepi.Proofs.PageTables.Mapping
