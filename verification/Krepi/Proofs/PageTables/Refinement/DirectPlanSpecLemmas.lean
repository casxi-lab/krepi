module

public import Krepi.Proofs.PageTables.Refinement.KernelPlanSpecLemmas
public import Krepi.Proofs.PageTables.Refinement.DirectSpecLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: the leaves and the search of the direct map, for the simulation of its plan

What the checks of `Tables.directMap` give about the leaves of the usable
ranges, in the form that the simulation of `mapPlan` by the cursor of the
code needs (`SimOk` of `Krepi.Proofs.PageTables.Refinement.PlanSimSpecLemmas`),
with the leaf search `usableFind` of all the usable ranges; and what the
cursor keeps so that the search of the plan iterator of `direct_map`, which
reads a saved state of the iterator of the usable ranges, is that search at
every call. The module imports no generated definitions. None of it reads
the record of the tables that the checks of the code count.

- The leaves that pass the checks: `checkLeavesFrom_ok` (one range) and
  `direct_fold` (the fold over the usable ranges: the leaves of the ranges in
  order, `usableLeaves`, each with its place).
- The leaves of the walk of a usable range: `mem_directLeaves`,
  `directLeaves_pairwise`, `directLeaves_cover` (each address of the range
  lies in a leaf), `leafStart_directLeaves` (each leaf starts where a leaf
  can start, `LeafStart`) and `leafStart_of_split` (an address that splits
  the leaves is such a start); `place_block_not_level3`.
- The search: `firstFound_split` (the first leaf found at or above an
  address that splits the leaves is `leafFirst` of the leaves after it).
- `direct_simOk`: the leaves of the usable ranges with their places satisfy
  `SimOk` at the offset `DIRECT_BASE`, with the search `usableFind` of the
  ranges and the place that the cursor reads on the set after the write
  phase; `directMap_used_le` (a success of `Tables.directMap` records at
  least the tables in use of the set).
- The cursor and the search state: `lowB` (the lowest address that the
  searches of the cursor read from now on), `SearchK` (what the cursor
  keeps: its address within its 1 GiB slot, a 2 MiB slot within it in the
  phases of a run of pages), `FindOk`, `searchK_mk`, `searchK_start`,
  `searchK_low`, `lowB_of_ne`, `findOk_of_split`, `split_of_found`,
  `step_congr_find` (two searches that agree from `lowB` give one call),
  `children_gib`,
  `gib_change_le`, `searchK_children`, `searchK_leaf` and `searchK_step`
  (each call keeps `SearchK`, and a call that changes the 1 GiB slot starts
  at or below the `lowB` after it).
-/

@[expose] public section

open Krepi.Spec.PageTables Krepi.Statements Krepi.Proofs.Fdt.Refinement

namespace Krepi.Proofs.PageTables.Refinement

variable {N : Nat}

/-! ## The leaves that pass the checks of the usable ranges -/

/-- The checks of the leaves of the walk of a usable range that pass: the
leaves of the walk, latest first, each with its place. -/
theorem checkLeavesFrom_ok (s : Tables .upper N) (base : UInt64) (taken : MapLeaf → Bool)
    (stop : Nat) : ∀ (fuel pa : Nat) (acc res : List (MapLeaf × Place)),
      checkLeavesFrom s base taken stop fuel pa acc = .ok res →
      ∃ new, res = new ++ acc ∧ new.reverse.map Prod.fst = directLeaves stop fuel pa ∧
        ∀ x ∈ new, s.place base x.1 = .ok x.2
  | 0, pa, acc, res, h => by
    simp only [checkLeavesFrom, directLeaves, List.foldlM_nil] at h
    cases h
    exact ⟨[], rfl, rfl, by simp⟩
  | fuel + 1, pa, acc, res, h => by
    by_cases hp : pa < stop
    · rw [checkLeavesFrom_succ s base taken stop fuel acc hp] at h
      cases hc : checkPlace s base (directLeaf stop pa) (taken (directLeaf stop pa)) with
      | error x => rw [hc] at h; cases h
      | ok p =>
        rw [hc] at h
        obtain ⟨new, hres, hmap, hall⟩ := checkLeavesFrom_ok s base taken stop fuel _ _ res h
        refine ⟨new ++ [(directLeaf stop pa, p)], by rw [hres, List.append_assoc]; rfl, ?_, ?_⟩
        · rw [directLeaves_succ stop fuel hp]; simp [hmap]
        · intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact hall x hx
          · rw [List.mem_singleton] at hx; subst hx; exact (checkPlace_ok_inv hc).1
    · rw [checkLeavesFrom_stop s base taken _ acc (Nat.le_of_not_lt hp)] at h
      cases h
      exact ⟨[], rfl, by rw [directLeaves_stop _ (Nat.le_of_not_lt hp)]; rfl, by simp⟩

/-- The fold of the checks of usable ranges after the leaves `acc` that
passed: the leaves that pass are the leaves of the ranges in order
(`usableLeaves`), each with its place, put latest first before `acc`. -/
theorem direct_fold (s : Tables .upper N) (base : UInt64) (bits : UInt8) :
    ∀ (us earlier : List Krepi.Spec.Fdt.Span) (acc : List (MapLeaf × Place))
      (res : List Krepi.Spec.Fdt.Span × List (MapLeaf × Place)),
      us.foldlM (s.checkUsableRange base bits) (earlier, acc) = .ok res →
      ∃ new, res.2 = new ++ acc ∧ new.reverse.map Prod.fst = us.flatMap usableLeaves ∧
        ∀ x ∈ new, s.place base x.1 = .ok x.2
  | [], earlier, acc, res, h => by
    cases h
    exact ⟨[], rfl, rfl, by simp⟩
  | u :: us, earlier, acc, res, h => by
    rw [List.foldlM_cons] at h
    cases hu : s.checkUsableRange base bits (earlier, acc) u with
    | error x => rw [hu] at h; cases h
    | ok mid =>
      rw [hu] at h
      obtain ⟨earlier', ls⟩ := mid
      rw [checkUsableRange_eq] at hu
      split at hu
      · cases hu
      · split at hu
        · cases hu
        · cases hc : checkLeavesFrom s base (usableTaken earlier) u.endNat
              (directFuel (u.endNat - u.start.toNat)) u.start.toNat acc with
          | error x => rw [hc] at hu; cases hu
          | ok ls' =>
            rw [hc] at hu
            simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at hu
            obtain ⟨rfl, rfl⟩ := hu
            obtain ⟨new1, hls, hmap1, hall1⟩ := checkLeavesFrom_ok s base _ _ _ _ acc ls' hc
            obtain ⟨new2, hres, hmap2, hall2⟩ := direct_fold s base bits us _ ls' res h
            refine ⟨new2 ++ new1, by rw [hres, hls, List.append_assoc], ?_, ?_⟩
            · rw [List.reverse_append, List.map_append, hmap1, hmap2, List.flatMap_cons]; rfl
            · intro x hx
              rcases List.mem_append.1 hx with hx | hx
              · exact hall2 x hx
              · exact hall1 x hx

/-! ## The leaves of the walk of a usable range -/

/-- A leaf of the walk of a usable range is the leaf of `directLeaf` at an
address of the walk, on the page grid of its start. -/
theorem mem_directLeaves {e : Nat} :
    ∀ (fuel pa : Nat) {y : MapLeaf}, y ∈ directLeaves e fuel pa →
    ∃ q, y = directLeaf e q ∧ pa ≤ q ∧ q < e ∧ q % PAGE_SIZE = pa % PAGE_SIZE
  | 0, _, y, hy => by simp [directLeaves] at hy
  | fuel + 1, pa, y, hy => by
    by_cases hlt : pa < e
    · rw [directLeaves_succ e fuel hlt] at hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨pa, rfl, Nat.le_refl _, hlt, rfl⟩
      · obtain ⟨q, rfl, h1, h2, h3⟩ := mem_directLeaves fuel _ hy
        refine ⟨q, rfl, by omega, h2, ?_⟩
        rw [h3, directLeaf_size]
        split <;> simp only [PAGE_SIZE, BLOCK_SIZE] <;> omega
    · rw [directLeaves_stop _ (by omega)] at hy; exact absurd hy List.not_mem_nil

/-- The leaves of the walk of a usable range lie in address order, apart. -/
theorem directLeaves_pairwise {e : Nat} (he : e < 2 ^ 64) : ∀ (fuel pa : Nat),
    (directLeaves e fuel pa).Pairwise (fun l l' => l.pa.toNat + l.form.size ≤ l'.pa.toNat)
  | 0, _ => by simp [directLeaves]
  | fuel + 1, pa => by
    by_cases hlt : pa < e
    · rw [directLeaves_succ e fuel hlt]
      refine List.pairwise_cons.2 ⟨fun l' hl' => ?_, directLeaves_pairwise he fuel _⟩
      have := (directLeaves_bounds he fuel _ l' hl').1
      rw [directLeaf_pa, UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hlt he)]
      exact this
    · rw [directLeaves_stop _ (by omega)]; exact List.Pairwise.nil

/-- Each address of a usable range at or above the start of the walk, below
its end, lies in a leaf of the walk. -/
theorem directLeaves_cover {e : Nat} (hs : e % PAGE_SIZE = 0) (he : e < 2 ^ 64) :
    ∀ (fuel pa x : Nat), pa % PAGE_SIZE = 0 → leafFuel e pa ≤ fuel → pa ≤ x → x < e →
      ∃ y ∈ directLeaves e fuel pa, y.pa.toNat ≤ x ∧ x < y.pa.toNat + y.form.size
  | 0, pa, x, hpa, hf, h1, h2 => by
    have := leafFuel_pos hpa hs (show pa < e by omega); omega
  | fuel + 1, pa, x, hpa, hf, h1, h2 => by
    have hlt : pa < e := by omega
    rw [directLeaves_succ e fuel hlt]
    have hstep := leafFuel_leaf hpa hs hlt
    have hpa' : (directLeaf e pa).pa.toNat = pa := by
      rw [directLeaf_pa, UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hlt he)]
    by_cases hx : x < pa + (directLeaf e pa).form.size
    · exact ⟨_, List.mem_cons_self, by rw [hpa']; exact h1, by rw [hpa']; exact hx⟩
    · obtain ⟨y, hy, hq⟩ := directLeaves_cover hs he fuel (pa + (directLeaf e pa).form.size) x
        (by rw [directLeaf_size]; split <;> simp only [PAGE_SIZE, BLOCK_SIZE] at hpa ⊢ <;> omega)
        (by omega) (by omega) h2
      exact ⟨y, List.mem_cons_of_mem _ hy, hq⟩

/-- Every leaf of the walk of a usable range from `pa0`, from an address where
a leaf can start, starts where a leaf can start. -/
theorem leafStart_directLeaves {e pa0 : Nat} (he : e < 2 ^ 64) : ∀ (fuel pa : Nat),
    pa % PAGE_SIZE = 0 → LeafStart pa0 e pa →
      ∀ y ∈ directLeaves e fuel pa, LeafStart pa0 e y.pa.toNat
  | 0, _, _, _, y, hy => by simp [directLeaves] at hy
  | fuel + 1, pa, hpa, hls, y, hy => by
    by_cases hlt : pa < e
    · rw [directLeaves_succ e fuel hlt] at hy
      rcases List.mem_cons.1 hy with rfl | hy
      · rw [directLeaf_pa, UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hlt he)]; exact hls
      · rw [directLeaf_size] at hy
        by_cases hc : pa % BLOCK_SIZE = 0 ∧ pa + BLOCK_SIZE ≤ e
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hc)] at hy
          refine leafStart_directLeaves he fuel _ ?_ ?_ y hy
          · simp only [PAGE_SIZE, BLOCK_SIZE] at hpa hc ⊢; omega
          · simp only [LeafStart, PAGE_SIZE, BLOCK_SIZE] at hls hpa hc ⊢; omega
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at hy
          refine leafStart_directLeaves he fuel _ ?_ ?_ y hy
          · simp only [PAGE_SIZE] at hpa ⊢; omega
          · simp only [LeafStart, PAGE_SIZE, BLOCK_SIZE] at hls hpa hc ⊢; omega
    · rw [directLeaves_stop _ (by omega)] at hy; exact absurd hy List.not_mem_nil

/-- An address that splits leaves `LP` of usable ranges `Us` (the leaves of
the ranges in order), strictly inside a range, is where a leaf of the walk of
that range starts. -/
theorem leafStart_of_split {Us : List Krepi.Spec.Fdt.Span} {LP : List (MapLeaf × Place)}
    (hmap : LP.map Prod.fst = Us.flatMap usableLeaves)
    (hUs : ∀ u ∈ Us, u.start.toNat < u.endNat ∧ u.start.toNat % PAGE_SIZE = 0 ∧
      u.endNat % PAGE_SIZE = 0 ∧ u.endNat < 2 ^ 64)
    {frm : Nat} {L : List (MapLeaf × Place)} (h : SplitAt LP frm L) :
    ∀ u ∈ Us, u.start.toNat < frm → frm < u.endNat → LeafStart u.start.toNat u.endNat frm := by
  intro u hu h1 h2
  obtain ⟨-, hs4, he4, he64⟩ := hUs u hu
  obtain ⟨y, hy, hy1, hy2⟩ := directLeaves_cover he4 he64 (directFuel (u.endNat - u.start.toNat))
    u.start.toNat frm hs4 (leafFuel_start hs4 he4) (Nat.le_of_lt h1) h2
  have hyLP : y ∈ LP.map Prod.fst := by
    rw [hmap]; exact List.mem_flatMap.2 ⟨u, hu, hy⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hyLP
  obtain ⟨A, hA, hA1, hL1⟩ := h
  rw [hA] at hx
  have hfx : x.1.pa.toNat = frm := by
    rcases List.mem_append.1 hx with hx | hx
    · have := hA1 x hx; omega
    · have := hL1 x hx; omega
  rw [← hfx]
  refine leafStart_directLeaves he64 _ u.start.toNat hs4 ?_ x.1 hy
  simp only [LeafStart, PAGE_SIZE, BLOCK_SIZE] at hs4 ⊢
  omega

/-- A block with a place: at the root or at level 2, never at level 3. -/
theorem place_block_not_level3 {r : Region} {s : Tables r N} {base : UInt64} {l : MapLeaf}
    {p : Place} (hp : s.place base l = .ok p) (hb : l.form = .block) (t2 t3 : Nat) :
    p ≠ .level3 t2 t3 := by
  cases hw : s.walk2 base l.va with
  | error x => rw [place_walk_error hw] at hp; cases hp
  | ok o =>
    cases o with
    | none => rw [place_walk_root hw] at hp; cases hp; simp
    | some te =>
      obtain ⟨t2', e2⟩ := te
      rcases place_ok_some hw hp with ⟨-, rfl⟩ | ⟨-, hf, -⟩
      · simp
      · rw [hb] at hf; cases hf

/-! ## The search -/

/-- The first of the leaves of usable ranges found at or above an address
that splits leaves `LP` (the leaves of the ranges in order): the first leaf
after it, `leafFirst`. -/
theorem firstFound_split {Us : List Krepi.Spec.Fdt.Span} {LP L : List (MapLeaf × Place)}
    {frm : Nat} (hmap : LP.map Prod.fst = Us.flatMap usableLeaves) (h : SplitAt LP frm L)
    (limit : Nat) (pages : Bool) :
    firstFound ((Us.flatMap usableLeaves).map foundOfLeaf) frm limit pages =
      leafFirst L limit pages := by
  obtain ⟨A, hA, hA1, hL1⟩ := h
  have hfA : ((A.map Prod.fst).map foundOfLeaf).find?
      (fun l => decide (frm ≤ l.pa) && (!pages || !l.block)) = none := by
    rw [List.find?_eq_none]
    intro l hl
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hl
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    have h1 := hA1 x hx
    have h2 : 0 < x.1.form.size := by rcases form_size x.1 with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
    have h3 : ¬ frm ≤ (foundOfLeaf x.1).pa := by simp only [foundOfLeaf]; omega
    simp [h3]
  have hfL : ((L.map Prod.fst).map foundOfLeaf).find?
      (fun l => decide (frm ≤ l.pa) && (!pages || !l.block)) =
      (L.find? (fun x => !pages || decide (x.1.form = .page))).map (foundOfLeaf ∘ Prod.fst) := by
    rw [List.map_map, List.find?_map]
    congr 1
    apply find?_congr
    intro x hx
    have h1 := hL1 x hx
    simp only [Function.comp, foundOfLeaf]
    cases x.1.form <;> simp [h1]
  unfold firstFound leafFirst
  rw [← hmap, hA, List.map_append, List.map_append, List.find?_append, hfA, Option.none_or, hfL]
  cases L.find? (fun x => !pages || decide (x.1.form = .page)) with
  | none => rfl
  | some x => rfl

/-! ## The leaves of the direct map satisfy `SimOk` -/

/-- **The leaves of the direct map for the simulation.** Leaves `LP` that are
the leaves of usable ranges `Us` in order (`usableLeaves`), each with its
place on a set `s`, for ranges nonempty, on pages, within 64 bits, ending at
or below `2 ^ 39` and apart in address order, satisfy `SimOk` at the offset
`DIRECT_BASE`, with the leaf search `usableFind` of the ranges and the place
that the cursor reads on the set with a record of tables in use at or above
that of `s`. -/
theorem direct_simOk {s : Tables .upper N} {base : UInt64} {Us : List Krepi.Spec.Fdt.Span}
    {LP : List (MapLeaf × Place)} (hmap : LP.map Prod.fst = Us.flatMap usableLeaves)
    (hplace : ∀ x ∈ LP, s.place base x.1 = .ok x.2)
    (hUs : ∀ u ∈ Us, u.start.toNat < u.endNat ∧ u.start.toNat % PAGE_SIZE = 0 ∧
      u.endNat % PAGE_SIZE = 0 ∧ u.endNat < 2 ^ 64)
    (hlow : ∀ u ∈ Us, u.endNat ≤ 2 ^ 39)
    (hpw : Us.Pairwise (fun a b => a.endNat ≤ b.start.toNat))
    {u' : Nat} (hu : s.used ≤ u') :
    SimOk DIRECT_BASE.toNat (fun f l p => usableFind (Us.map spanView) f l p)
      (placeOr ({ s with used := u' } : Tables .upper N) base) LP := by
  -- each leaf is the leaf of `directLeaf` at an address of its range
  have hx : ∀ x ∈ LP, ∃ u ∈ Us, ∃ q, x.1 = directLeaf u.endNat q ∧ u.start.toNat ≤ q ∧
      q < u.endNat ∧ q % PAGE_SIZE = 0 := by
    intro x hxm
    have : x.1 ∈ Us.flatMap usableLeaves := by rw [← hmap]; exact List.mem_map_of_mem hxm
    obtain ⟨u, hu', hm⟩ := List.mem_flatMap.1 this
    obtain ⟨q, hq, h1, h2, h3⟩ := mem_directLeaves _ _ hm
    exact ⟨u, hu', q, hq, h1, h2, by rw [h3]; exact (hUs u hu').2.1⟩
  -- the numbers of a leaf of a range
  have hleaf : ∀ u ∈ Us, ∀ q, u.start.toNat ≤ q → q < u.endNat → q % PAGE_SIZE = 0 →
      (directLeaf u.endNat q).pa.toNat = q ∧
      (directLeaf u.endNat q).va.toNat = DIRECT_BASE.toNat + q ∧
      q + (directLeaf u.endNat q).form.size ≤ u.endNat ∧
      q % (directLeaf u.endNat q).form.size = 0 := by
    intro u hu' q h1 h2 h3
    obtain ⟨-, -, he4, he64⟩ := hUs u hu'
    have hl := hlow u hu'
    refine ⟨by rw [directLeaf_pa, UInt64.toNat_ofNat_of_lt' (Nat.lt_trans h2 he64)],
      directLeaf_va_toNat (by omega), ?_, ?_⟩ <;>
    · rw [directLeaf_size]
      split
      · rename_i hc; simp only [BLOCK_SIZE] at hc ⊢; omega
      · simp only [PAGE_SIZE] at he4 h3 ⊢; omega
  have hnum : ∀ x ∈ LP, x.1.va.toNat = DIRECT_BASE.toNat + x.1.pa.toNat ∧
      x.1.pa.toNat + x.1.form.size ≤ 2 ^ 39 ∧ x.1.pa.toNat % x.1.form.size = 0 := by
    intro x hxm
    obtain ⟨u, hu', q, hq, h1, h2, h3⟩ := hx x hxm
    obtain ⟨e1, e2, e3, e4⟩ := hleaf u hu' q h1 h2 h3
    have := hlow u hu'
    rw [hq, e1, e2]
    exact ⟨rfl, by omega, e4⟩
  refine ⟨by rw [DIRECT_BASE_toNat]; rfl, fun x hxm => (hnum x hxm).1,
    fun x hxm => (hnum x hxm).2.1, fun x hxm => (hnum x hxm).2.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- sorted
    have hfl : (Us.flatMap usableLeaves).Pairwise
        (fun l l' => l.pa.toNat + l.form.size ≤ l'.pa.toNat) := by
      refine List.pairwise_flatMap.2
        ⟨fun u hu' => directLeaves_pairwise (hUs u hu').2.2.2 _ _, ?_⟩
      refine List.Pairwise.imp_of_mem (fun {u v} hu' hv huv => ?_) hpw
      intro l hl l' hl'
      obtain ⟨q, rfl, h1, h2, h3⟩ := mem_directLeaves _ _ hl
      obtain ⟨q', rfl, h1', h2', h3'⟩ := mem_directLeaves _ _ hl'
      obtain ⟨e1, -, e3, -⟩ := hleaf u hu' q h1 h2 (by rw [h3]; exact (hUs u hu').2.1)
      obtain ⟨e1', -, -, -⟩ := hleaf v hv q' h1' h2' (by rw [h3']; exact (hUs v hv).2.1)
      rw [e1, e1']
      omega
    rw [← hmap, List.pairwise_map] at hfl
    exact hfl
  · intro x hxm y hym hg
    exact place_root_iff (index1_of_gib hg) (hplace x hxm) (hplace y hym)
  · intro x hxm y hym hb
    exact place_eq_of_slot (index1_of_gib (gib_of_block hb)) (index2_of_block hb)
      (hplace x hxm) (hplace y hym)
  · intro x hxm hf t2 t3
    exact place_block_not_level3 (hplace x hxm) hf t2 t3
  · intro x hxm
    obtain ⟨u, hu', q, hq, h1, h2, h3⟩ := hx x hxm
    have hl := hlow u hu'
    have hpl := hplace x hxm
    rw [hq] at hpl ⊢
    have hf : fOf (directLeaf u.endNat q) = leafAtFound u.endNat q :=
      foundOfLeaf_directLeaf (by omega)
    rw [hf]
    exact placeOr_directLeaf hu (by omega) hpl
  · intro frm L h limit pages
    show usableFind (Us.map spanView) frm limit pages = leafFirst L limit pages
    rw [usableFind_eq_firstFound Us frm hUs hpw (leafStart_of_split hmap hUs h)]
    exact firstFound_split hmap h limit pages

/-- A success of `Tables.directMap`: the record of its set is at or above
that of the set. -/
theorem directMap_used_le {s : Tables .upper N} {P : Krepi.Spec.Fdt.MemoryPlan} {base : UInt64}
    {bits : UInt8} {S : Tables .upper N} {plan : Plan} (h : s.directMap P base bits = .ok (S, plan)) :
    s.used ≤ S.used := by
  cases hp : checkPool N base bits with
  | error x => rw [directMap_pool_error hp] at h; cases h
  | ok u =>
    cases u
    cases hfo : (sortByKey (·.start.toNat) P.availableRanges).foldlM
        (s.checkUsableRange base bits) ([], []) with
    | error x => rw [directMap_fold_error hp hfo] at h; cases h
    | ok res =>
      obtain ⟨e, ls⟩ := res
      rw [directMap_fold_ok hp hfo] at h
      split at h
      · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact next_le_stOf ls.reverse ⟨s.used, none, none, []⟩

/-! ## The cursor and the search state of the plan iterator -/

/-- The lowest address that the searches of the cursor read from now on: the
first address of its 1 GiB slot, 0 before the first leaf. -/
def lowB (c : Cur) : Nat := if c.gib = noSlot then 0 else c.gib

/-- What the cursor keeps for the search state of the plan iterator of the
direct map: before the first leaf (no 1 GiB slot) the phase `leaf` or `done`
at the address 0; otherwise a 1 GiB slot whose start and end hold the
address between them, and in the phases of a run of pages a 2 MiB slot of
that 1 GiB slot. -/
def SearchK (c : Cur) : Prop :=
  (c.gib = noSlot → (c.phase = .leaf ∨ c.phase = .done) ∧ c.frm = 0) ∧
  (c.gib ≠ noSlot → c.gib % GIB_SIZE = 0 ∧ c.gib ≤ c.frm ∧ c.frm ≤ c.gib + GIB_SIZE) ∧
  (c.phase = .newPages ∨ c.phase = .newTable ∨ c.phase = .heldPages →
    c.gib ≤ c.slot ∧ c.slot % BLOCK_SIZE = 0 ∧ c.slot + BLOCK_SIZE ≤ c.gib + GIB_SIZE)

/-- What a search finds from an address: a leaf at or above it, below the
limit and below `2 ^ 39`, on a page boundary, a block on a 2 MiB boundary. -/
def FindOk (find : Nat → Nat → Bool → Option Found) (frm : Nat) : Prop :=
  ∀ limit pages f, find frm limit pages = some f →
    frm ≤ f.pa ∧ f.pa < limit ∧ f.pa < 2 ^ 39 ∧ f.pa % PAGE_SIZE = 0 ∧
      (f.block = true → f.pa % BLOCK_SIZE = 0)

theorem searchK_mk {c : Cur} (hg : c.gib ≠ noSlot) (h1 : c.gib % GIB_SIZE = 0) (h2 : c.gib ≤ c.frm)
    (h3 : c.frm ≤ c.gib + GIB_SIZE)
    (h4 : c.phase = .newPages ∨ c.phase = .newTable ∨ c.phase = .heldPages →
      c.gib ≤ c.slot ∧ c.slot % BLOCK_SIZE = 0 ∧ c.slot + BLOCK_SIZE ≤ c.gib + GIB_SIZE) :
    SearchK c :=
  ⟨fun h => absurd h hg, fun _ => ⟨h1, h2, h3⟩, h4⟩

/-- The cursor before the first leaf keeps `SearchK`. -/
theorem searchK_start (used : Nat) : SearchK ⟨.leaf, 0, used, noSlot, noSlot, 0, 0⟩ :=
  ⟨fun _ => ⟨Or.inl rfl, rfl⟩, fun h => absurd rfl h,
    fun h => by rcases h with h | h | h <;> cases h⟩

/-- The searches of a cursor of `SearchK` start at or above its `lowB`. -/
theorem searchK_low {c : Cur} (h : SearchK c) : lowB c ≤ c.frm := by
  unfold lowB
  split
  · exact Nat.zero_le _
  · rename_i hg; exact (h.2.1 hg).2.1

theorem lowB_of_ne {c : Cur} (h : c.gib ≠ noSlot) : lowB c = c.gib := by
  simp only [lowB, h, ↓reduceIte]

/-- A cursor of `SearchK` whose 1 GiB slot changes to that of `pa`, at or
above its address: its address is at or below the start of the new slot. -/
theorem gib_change_le {c : Cur} (h : SearchK c) {pa : Nat} (hpa : c.frm ≤ pa)
    (hne : gibOf pa ≠ c.gib) : c.frm ≤ gibOf pa := by
  by_cases hg : c.gib = noSlot
  · rw [(h.1 hg).2]; exact Nat.zero_le _
  · obtain ⟨h1, h2, h3⟩ := h.2.1 hg
    simp only [gibOf, GIB_SIZE] at hne h1 h3 ⊢
    omega

section Search

variable {off : Nat} {find : Nat → Nat → Bool → Option Found} {place : Found → Place}
  {LP : List (MapLeaf × Place)} {base : UInt64}

/-- A search of `SimOk` from an address that splits the leaves finds what
`FindOk` says. -/
theorem findOk_of_split (H : SimOk off find place LP) {frm : Nat} {L : List (MapLeaf × Place)}
    (h : SplitAt LP frm L) : FindOk find frm := by
  intro limit pages f hf
  rw [H.find frm L h] at hf
  unfold leafFirst at hf
  split at hf
  · cases hf
  · rename_i x hx
    split at hf
    · rename_i hl
      cases hf
      have hxL := List.mem_of_find?_eq_some hx
      have hxP := splitAt_mem h hxL
      obtain ⟨k, -, -, hlo, hal, -, -, hfs⟩ := leaf_nums H hxP
      have hge := h.choose_spec.2.2 x hxL
      refine ⟨hge, hl, ?_, ?_, ?_⟩
      · rcases hfs with ⟨-, h4⟩ | ⟨-, h4⟩ <;> simp only [fOf] <;> omega
      · rcases hfs with ⟨-, h4⟩ | ⟨-, h4⟩ <;> rw [h4] at hal <;> simp only [fOf, PAGE_SIZE] <;>
          omega
      · intro hb
        simp only [fOf, decide_eq_true_eq] at hb
        rcases hfs with ⟨h3, -⟩ | ⟨-, h4⟩
        · rw [h3] at hb; cases hb
        · rw [h4] at hal; simp only [fOf, BLOCK_SIZE]; omega
    · cases hf

/-- The leaf that the search of a leaf of either form finds from an address
that splits the leaves: the first leaf after it, whose address splits the
leaves before it. -/
theorem split_of_found (H : SimOk off find place LP) {frm : Nat} {L : List (MapLeaf × Place)}
    (h : SplitAt LP frm L) {limit : Nat} {f : Found} (hf : find frm limit false = some f) :
    ∃ x L', fOf x.1 = f ∧ SplitAt LP f.pa (x :: L') := by
  rw [H.find frm L h] at hf
  cases L with
  | nil => simp [leafFirst] at hf
  | cons x L' =>
    rw [leafFirst_cons (Or.inl rfl)] at hf
    split at hf
    · cases hf
      refine ⟨x, L', rfl, splitAt_mono h (h.choose_spec.2.2 x List.mem_cons_self) ?_⟩
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact Nat.le_refl _
      · have := splitAt_after H h y hy; simp only [fOf]; omega
    · cases hf

end Search

/-- Two searches that agree from an address `b` at or below the address of
the cursor give the same call of `Cur.step`, when the leaves that the second
finds from the address of the cursor lie at or above it. -/
theorem step_congr_find {find find' : Nat → Nat → Bool → Option Found} {place : Found → Place}
    {base : UInt64} {c : Cur} {b : Nat} (hb : b ≤ c.frm)
    (hge : ∀ l p f, find c.frm l p = some f → c.frm ≤ f.pa)
    (heq : ∀ f l p, b ≤ f → find' f l p = find f l p) :
    Cur.step find' place base c = Cur.step find place base c := by
  have h1 : find' c.search.1 c.search.2.1 c.search.2.2 =
      find c.search.1 c.search.2.1 c.search.2.2 := by
    rw [cur_search_frm]; exact heq _ _ _ hb
  unfold Cur.step
  simp only [h1]
  generalize ht : c.take place base (find c.search.1 c.search.2.1 c.search.2.2) = t
  obtain ⟨t1, t2⟩ := t
  cases t1 with
  | give s => rfl
  | stop => rfl
  | seek =>
    obtain ⟨l, hl, hfr, -⟩ := cur_take_seek place base c _ (by rw [ht])
    rw [ht] at hfr
    have hl' : c.frm ≤ l.pa :=
      hge c.search.2.1 c.search.2.2 l (by rw [← cur_search_frm c]; exact hl)
    have h2 : find' t2.search.1 t2.search.2.1 t2.search.2.2 =
        find t2.search.1 t2.search.2.1 t2.search.2.2 := by
      rw [cur_search_frm]; exact heq _ _ _ (by simp only at hfr; omega)
    simp only [h2]

/-- A call of `children` keeps the 1 GiB slot. -/
theorem children_gib (c : Cur) (o : Option Found) : (c.children o).2.gib = c.gib := by
  cases o with
  | none => rfl
  | some p =>
    simp only [Cur.children]
    by_cases h : slotOf p.pa = c.slot
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte]

section Step

variable {off : Nat} {find : Nat → Nat → Bool → Option Found} {place : Found → Place}
  {LP : List (MapLeaf × Place)} {base : UInt64}

/-- A call in `children`, with a search of `FindOk` from its address, keeps
`SearchK` and the 1 GiB slot. -/
theorem searchK_children {c : Cur} (hK : SearchK c) (hp : c.phase = .children)
    (hfo : FindOk find c.frm) :
    SearchK (Cur.step find place base c).2 ∧ (Cur.step find place base c).2.gib = c.gib := by
  have hg : c.gib ≠ noSlot := fun h => by
    rcases (hK.1 h).1 with h' | h' <;> rw [hp] at h' <;> cases h'
  obtain ⟨g1, g2, g3⟩ := hK.2.1 hg
  cases hf : find c.frm (c.gib + GIB_SIZE) true with
  | none =>
    rw [step_children_none find place base hp hf]
    exact ⟨searchK_mk hg g1 (Nat.le_refl _) (Nat.le_add_right _ _) (fun h => by simp at h), rfl⟩
  | some f =>
    obtain ⟨f1, f2, -, f4, -⟩ := hfo _ _ f hf
    by_cases hs : slotOf f.pa = c.slot
    · rw [step_children_same find place base hp hf hs]
      refine ⟨searchK_mk hg g1 (by dsimp only; omega) ?_ (fun h => by simp [hp] at h), rfl⟩
      dsimp only
      simp only [PAGE_SIZE, GIB_SIZE] at f4 g1 f2 ⊢; omega
    · rw [step_children_new find place base hp hf hs]
      refine ⟨searchK_mk hg g1 (by dsimp only; omega) (by dsimp only; omega)
        (fun h => by simp [hp] at h), rfl⟩

/-- A call in `leaf` from an address that splits the leaves, for leaves and a
search of `SimOk`, keeps `SearchK`; when it changes the 1 GiB slot, the
address of the cursor before it is at or below the `lowB` after it. -/
theorem searchK_leaf (H : SimOk off find place LP) {c : Cur} (hK : SearchK c)
    (hp : c.phase = .leaf) {L : List (MapLeaf × Place)} (hsp : SplitAt LP c.frm L) :
    SearchK (Cur.step find place base c).2 ∧
      ((Cur.step find place base c).2.gib ≠ c.gib →
        c.frm ≤ lowB (Cur.step find place base c).2) := by
  have hfo := findOk_of_split H hsp
  cases hf : find c.frm (2 ^ 64 - 1) false with
  | none =>
    rw [step_leaf_none find place base hp hf]
    exact ⟨⟨fun h => ⟨Or.inr rfl, (hK.1 h).2⟩, hK.2.1, fun h => by simp at h⟩,
      fun h => (h rfl).elim⟩
  | some f =>
    obtain ⟨f1, -, -, f4, f5⟩ := hfo _ _ f hf
    have hg0 := gibOf_ne_noSlot f.pa
    have hgl : c.frm ≤ f.pa → gibOf f.pa ≠ c.gib → c.frm ≤ gibOf f.pa := gib_change_le hK
    have hgf1 : gibOf f.pa % GIB_SIZE = 0 := by simp only [gibOf, GIB_SIZE]; omega
    have hgf2 : gibOf f.pa ≤ f.pa := by simp only [gibOf, GIB_SIZE]; omega
    have hgf3 : f.pa < gibOf f.pa + GIB_SIZE := by simp only [gibOf, GIB_SIZE]; omega
    have hsl : gibOf f.pa ≤ slotOf f.pa ∧ slotOf f.pa % BLOCK_SIZE = 0 ∧
        slotOf f.pa + BLOCK_SIZE ≤ gibOf f.pa + GIB_SIZE := by
      simp only [gibOf, slotOf, GIB_SIZE, BLOCK_SIZE]; omega
    cases hpl : place f with
    | root =>
      obtain ⟨x, L', hxf, hsp'⟩ := split_of_found H hsp hf
      have hfo' := findOk_of_split H hsp'
      have hf' : f.block = false → find f.pa (gibOf f.pa + GIB_SIZE) true = some f := by
        intro hb
        have hxp : x.1.form = .page := by
          rw [← hxf] at hb
          cases hx : x.1.form
          · rfl
          · simp [fOf, hx] at hb
        rw [H.find _ _ hsp', leafFirst_cons (Or.inr hxp)]
        have : x.1.pa.toNat = f.pa := by rw [← hxf]; rfl
        simp only [this, hgf3, ↓reduceIte, hxf]
      rw [step_leaf_root find place base hp hf hpl hf']
      have hK1 : SearchK ⟨.children, f.pa, c.next + 1, gibOf f.pa, noSlot, c.next, c.t3⟩ :=
        searchK_mk hg0 hgf1 hgf2 (Nat.le_of_lt hgf3) (fun h => by simp at h)
      obtain ⟨hK2, hg2⟩ := searchK_children (place := place) (base := base) hK1 rfl hfo'
      refine ⟨hK2, fun hne => ?_⟩
      have hg3 : (Cur.step find place base
          (⟨.children, f.pa, c.next + 1, gibOf f.pa, noSlot, c.next, c.t3⟩ : Cur)).2.gib =
          gibOf f.pa := hg2
      rw [hg3] at hne
      rw [lowB_of_ne (by rw [hg3]; exact hg0), hg3]
      exact hgl f1 hne
    | level2 t2 =>
      cases hb : f.block with
      | true =>
        rw [step_leaf_level2_block find place base hp hf hpl hb]
        have hal := f5 hb
        refine ⟨searchK_mk hg0 hgf1 (by dsimp only; omega) ?_ (fun h => by simp [hp] at h),
          fun hne => ?_⟩
        · dsimp only
          simp only [gibOf, GIB_SIZE, BLOCK_SIZE] at hal ⊢; omega
        · rw [lowB_of_ne hg0]; exact hgl f1 hne
      | false =>
        rw [step_leaf_level2_page find place base hp hf hpl hb]
        exact ⟨searchK_mk hg0 hgf1 hgf2 (Nat.le_of_lt hgf3) (fun _ => hsl),
          fun hne => by rw [lowB_of_ne hg0]; exact hgl f1 hne⟩
    | level3 t2 t3 =>
      rw [step_leaf_level3 find place base hp hf hpl]
      refine ⟨searchK_mk hg0 hgf1 (by dsimp only; omega) ?_ (fun _ => hsl),
        fun hne => by rw [lowB_of_ne hg0]; exact hgl f1 hne⟩
      dsimp only
      simp only [gibOf, GIB_SIZE, PAGE_SIZE] at f4 ⊢; omega

/-- **Each call keeps `SearchK`.** A call of `Cur.step` from a cursor of
`SearchK` whose address splits the leaves, for leaves and a search of
`SimOk`, gives a cursor of `SearchK`; when it changes the 1 GiB slot, the
address of the cursor before it is at or below the `lowB` after it. -/
theorem searchK_step (H : SimOk off find place LP) {c : Cur} (hK : SearchK c)
    {L : List (MapLeaf × Place)} (hsp : SplitAt LP c.frm L) :
    SearchK (Cur.step find place base c).2 ∧
      ((Cur.step find place base c).2.gib ≠ c.gib →
        c.frm ≤ lowB (Cur.step find place base c).2) := by
  have hfo := findOk_of_split H hsp
  have hgne : c.phase ≠ .leaf → c.phase ≠ .done → c.gib ≠ noSlot := fun h1 h2 hg => by
    rcases (hK.1 hg).1 with h | h
    · exact h1 h
    · exact h2 h
  cases hp : c.phase with
  | leaf => exact searchK_leaf H hK hp hsp
  | heldPages =>
    have hg := hgne (by rw [hp]; simp) (by rw [hp]; simp)
    obtain ⟨g1, g2, g3⟩ := hK.2.1 hg
    obtain ⟨s1, s2, s3⟩ := hK.2.2 (Or.inr (Or.inr hp))
    by_cases hsame : ∃ f, find c.frm (2 ^ 64 - 1) false = some f ∧ slotOf f.pa = c.slot
    · obtain ⟨f, hf, hs⟩ := hsame
      obtain ⟨f1, -, -, f4, -⟩ := hfo _ _ f hf
      rw [step_held_same find place base hp hf hs]
      refine ⟨searchK_mk hg g1 (by dsimp only; omega) ?_ (fun _ => ⟨s1, s2, s3⟩),
        fun h => (h rfl).elim⟩
      dsimp only
      simp only [slotOf, BLOCK_SIZE, PAGE_SIZE, GIB_SIZE] at hs f4 s2 s3 ⊢; omega
    · rw [step_held_leaf find place base hp (fun f hf hs => hsame ⟨f, hf, hs⟩)]
      have hK' : SearchK { c with phase := .leaf } :=
        ⟨fun h => absurd h hg, fun _ => ⟨g1, g2, g3⟩, fun h => by simp at h⟩
      exact searchK_leaf H hK' rfl hsp
  | newPages =>
    have hg := hgne (by rw [hp]; simp) (by rw [hp]; simp)
    obtain ⟨g1, g2, g3⟩ := hK.2.1 hg
    obtain ⟨s1, s2, s3⟩ := hK.2.2 (Or.inl hp)
    cases hf : find c.frm (c.slot + BLOCK_SIZE) false with
    | none =>
      rw [step_newPages_none find place base hp hf]
      exact ⟨searchK_mk hg g1 g2 g3 (fun _ => ⟨s1, s2, s3⟩), fun h => (h rfl).elim⟩
    | some f =>
      obtain ⟨f1, f2, -, f4, -⟩ := hfo _ _ f hf
      rw [step_newPages_some find place base hp hf]
      refine ⟨searchK_mk hg g1 (by dsimp only; omega) ?_ (fun _ => ⟨s1, s2, s3⟩),
        fun h => (h rfl).elim⟩
      dsimp only
      simp only [BLOCK_SIZE, PAGE_SIZE, GIB_SIZE] at f2 f4 s2 s3 ⊢; omega
  | newTable =>
    have hg := hgne (by rw [hp]; simp) (by rw [hp]; simp)
    obtain ⟨g1, g2, g3⟩ := hK.2.1 hg
    obtain ⟨s1, s2, s3⟩ := hK.2.2 (Or.inr (Or.inl hp))
    rw [step_newTable find place base hp]
    exact ⟨searchK_mk hg g1 (by dsimp only; omega) (by dsimp only; omega) (fun h => by simp at h),
      fun h => (h rfl).elim⟩
  | children =>
    obtain ⟨h1, h2⟩ := searchK_children (place := place) (base := base) hK hp hfo
    exact ⟨h1, fun h => absurd h2 h⟩
  | entries =>
    have hg := hgne (by rw [hp]; simp) (by rw [hp]; simp)
    obtain ⟨g1, g2, g3⟩ := hK.2.1 hg
    cases hf : find c.frm (c.gib + GIB_SIZE) false with
    | none =>
      rw [step_entries_none find place base hp hf]
      exact ⟨searchK_mk hg g1 g2 g3 (fun h => by simp at h), fun h => (h rfl).elim⟩
    | some f =>
      obtain ⟨f1, f2, -, -, -⟩ := hfo _ _ f hf
      have e1 : c.gib ≤ slotOf f.pa + BLOCK_SIZE := by simp only [slotOf, BLOCK_SIZE]; omega
      have e2 : slotOf f.pa + BLOCK_SIZE ≤ c.gib + GIB_SIZE := by
        simp only [slotOf, BLOCK_SIZE, GIB_SIZE] at f2 g1 ⊢; omega
      cases hb : f.block
      · rw [step_entries_page find place base hp hf hb]
        exact ⟨searchK_mk hg g1 e1 e2 (fun h => by simp [hp] at h), fun h => (h rfl).elim⟩
      · rw [step_entries_block find place base hp hf hb]
        exact ⟨searchK_mk hg g1 e1 e2 (fun h => by simp [hp] at h), fun h => (h rfl).elim⟩
  | root =>
    have hg := hgne (by rw [hp]; simp) (by rw [hp]; simp)
    obtain ⟨g1, g2, g3⟩ := hK.2.1 hg
    rw [step_root find place base hp]
    exact ⟨searchK_mk hg g1 (by dsimp only; omega) (by dsimp only; omega) (fun h => by simp at h),
      fun h => (h rfl).elim⟩
  | done =>
    rw [step_done find place base hp]
    exact ⟨hK, fun h => (h rfl).elim⟩

end Step

end Krepi.Proofs.PageTables.Refinement
