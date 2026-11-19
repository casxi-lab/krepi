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

/-!
# Page tables: proofs about the abstract mapping and the plans

One theorem for each registered statement of
`Krepi.SpecProperties.PageTables` about the abstract mapping and the plans,
whose type is exactly that statement: that every write changes the abstract
mapping as the contract says, that the tables in use are counted by $G$ and
$P$, and that the plans publish in order.

`tablesInUseCounted` and `plansPublishInOrder` are proved. The tables of a
well-formed set are the root, the level 2 tables that the root points at and
the level 3 tables that those point at, once each, and the 1 GiB and 2 MiB
slots of `Tables.gSlots` and `Tables.pSlots` are the slots whose entries point
at them, one for each. The plan of a map passes `Plan.inOrder` by
`Krepi.Proofs.PageTables.OrderPlanLemmas`, and `map_page` and `map_block`
are maps of one leaf; the plans of `unmap_page` and `clone_kernel_from` are
read off their definitions. `afterEveryWrite` is still planned: its proof is
`sorry`, and `verification/statements.json` registers it as `planned`.
Mathlib is imported so that the gate counts the heartbeats of each theorem.
-/

namespace Krepi.Proofs.PageTables.Mapping

open Krepi.SpecProperties.PageTables
open Krepi.Spec.PageTables
open Krepi.Proofs.PageTables
open Krepi.Proofs.Fdt (except_bind_ok except_jp_ok)

public theorem afterEveryWrite : AfterEveryWrite := by
  sorry

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

private theorem walk2_pointsAt {v : UInt64} {c : Nat} (h : s.PointsAt base 0 (index1 v) c) :
    s.walk2 base v = .ok (some (c, s.entry c (index2 v))) :=
  walk2_ok.2 (Or.inr ⟨c, isValid_of_isPlain h.2.1, h.2.2, rfl⟩)

private theorem walk2_some_iff (hs : s.WellFormed base bits) (v : UInt64) :
    (∃ t2 e2, s.walk2 base v = .ok (some (t2, e2))) ↔ (s.pointsAt? base 0 (index1 v)).isSome := by
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨t2, e2, h⟩
    exact ⟨t2, (pointsAt?_eq_some s base (index1_lt v)).2 (wf_walk2_some hs h).1⟩
  · rintro ⟨c, h⟩
    exact ⟨c, _, walk2_pointsAt ((pointsAt?_eq_some s base (index1_lt v)).1 h)⟩

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
    refine ⟨t2, c, _, walk_ok_level3.2 ⟨_, walk2_pointsAt h2, isValid_of_isPlain hp.2.1, ?_, hp.2.2, rfl⟩⟩
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
    rw [walk2_pointsAt hpa]; rfl

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

private theorem single_inOrder (hs : s.WellFormed base bits) {l : MapLeaf} {pl : Place}
    (hpl : s.place base l = .ok pl) (hr : r.holds l.va = true) (ha : l.va.toNat % l.form.size = 0)
    (hd : LeafDesc bits l) (hN : (assignTables s.used [(l, pl)]).1 ≤ N) :
    (mapPlan base (assignTables s.used [(l, pl)]).2).publishesInOrder base s.pool = true := by
  refine mapPlan_inOrder hs ⟨fun lp h => ?_, List.pairwise_singleton _ _, fun lp h => ?_,
    fun lp h => ?_, fun lp h => ?_⟩ hN <;> rw [List.mem_singleton] at h <;> subst h
  · exact hpl
  · exact hr
  · exact ha
  · exact hd

private theorem mapPage_order {v p : UInt64} {k : Kind} {s' : Tables r N} {plan : Plan}
    (hs : s.WellFormed base bits) (h : s.mapPage v p k base bits = .ok (s', plan)) :
    plan.publishesInOrder base s.pool = true := by
  unfold Tables.mapPage at h
  obtain ⟨u1, hce, h⟩ := except_bind_ok.1 h
  obtain ⟨u2, hcp, h⟩ := except_bind_ok.1 h
  obtain ⟨w, hw, h⟩ := except_bind_ok.1 h
  obtain ⟨hv, -, hr, -, -⟩ := checkEntry_ok.1 hce
  have hpb := (checkPhysical_ok.1 hcp).2
  have huN := hs.2.2.1
  have hd : LeafDesc bits ⟨v, p, descriptor k p, .page⟩ :=
    ⟨fun _ => ⟨⟨k, by rw [outputAddress_descriptor, descriptor_outputAddress]⟩, by
      rw [outputAddress_descriptor]; exact Nat.lt_of_le_of_lt (outputAddress_le p) hpb⟩,
      fun hb => by cases hb⟩
  have key : ∀ pl, s.place base ⟨v, p, descriptor k p, .page⟩ = .ok pl →
      (assignTables s.used [(⟨v, p, descriptor k p, .page⟩, pl)]).1 ≤ N →
      plan = mapPlan base (assignTables s.used [(⟨v, p, descriptor k p, .page⟩, pl)]).2 →
      plan.publishesInOrder base s.pool = true :=
    fun pl h1 h2 h3 => h3 ▸ single_inOrder hs h1 hr hv hd h2
  rcases w with _ | ⟨t2, e2⟩
  · obtain ⟨hlt, h⟩ := except_jp_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact key .root (by unfold Tables.place; rw [hw]; rfl) (by show s.used + 1 + 1 ≤ N; omega) rfl
  · dsimp only at h
    split at h
    · rename_i hv2
      obtain ⟨hlt, h⟩ := except_jp_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine key (.level2 t2) ?_ (by show s.used + 1 ≤ N; omega) rfl
      unfold Tables.place; rw [hw]
      simp only [bind, Except.bind, hv2, ite_true]; rfl
    · rename_i hv2
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw] at h
      · rename_i hb
        split at h
        next t3 hc =>
          split at h
          next => simp [throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at h
          next hv3 =>
            simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine key (.level3 t2 t3) ?_ huN rfl
            unfold Tables.place; rw [hw]
            simp only [bind, Except.bind, hv2, hb, hc, hv3, Bool.false_eq_true, ite_false]; rfl
        next => simp [throw, throwThe, MonadExceptOf.throw] at h

private theorem mapBlock_order {v p : UInt64} {s' : Tables r N} {plan : Plan}
    (hs : s.WellFormed base bits) (h : s.mapBlock v p base bits = .ok (s', plan)) :
    plan.publishesInOrder base s.pool = true := by
  unfold Tables.mapBlock at h
  obtain ⟨u1, hce, h⟩ := except_bind_ok.1 h
  obtain ⟨u2, hcp, h⟩ := except_bind_ok.1 h
  obtain ⟨w, hw, h⟩ := except_bind_ok.1 h
  obtain ⟨hv, -, hr, -, -⟩ := checkEntry_ok.1 hce
  have hpb := (checkPhysical_ok.1 hcp).2
  have huN := hs.2.2.1
  have hd : LeafDesc bits ⟨v, p, blockDescriptor p, .block⟩ :=
    ⟨(fun h => by cases h), fun _ => ⟨isReadWriteBlock_blockDescriptor p, by
      rw [blockAddress_blockDescriptor]; exact Nat.lt_of_le_of_lt (blockAddress_le p) hpb⟩⟩
  have key : ∀ pl, s.place base ⟨v, p, blockDescriptor p, .block⟩ = .ok pl →
      (assignTables s.used [(⟨v, p, blockDescriptor p, .block⟩, pl)]).1 ≤ N →
      plan = mapPlan base (assignTables s.used [(⟨v, p, blockDescriptor p, .block⟩, pl)]).2 →
      plan.publishesInOrder base s.pool = true :=
    fun pl h1 h2 h3 => h3 ▸ single_inOrder hs h1 hr hv hd h2
  rcases w with _ | ⟨t2, e2⟩
  · obtain ⟨hlt, h⟩ := except_jp_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact key .root (by unfold Tables.place; rw [hw]; rfl) (by show s.used + 1 ≤ N; omega) rfl
  · obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨hv2, h⟩ := except_jp_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    refine key (.level2 t2) ?_ huN rfl
    unfold Tables.place; rw [hw]
    simp only [bind, Except.bind, Bool.not_eq_true] at hv2 ⊢
    simp only [hv2, Bool.not_false, ite_true]; rfl

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

end Krepi.Proofs.PageTables.Mapping
