module

public import Krepi.Proofs.PageTables.MapWriteLemmas
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.PageTables.EntryLemmas
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.ListLemmas
import Krepi.Proofs.Fdt.ExceptLemmas

/-!
# Page tables: the checks of `kernel_map` and `direct_map`

What the checks of the two maps give their leaves, so that the lemmas of
`Krepi.Proofs.PageTables.MapWriteLemmas` apply to them:

- the write phase, in private steps: the leaves that pass the free-slot
  check, each with its place and not taken; the set after the plan is
  `finalSet`, and the new tables fit in the pool; the plan is `mapPlan` of
  the placed leaves, and the pool is unchanged by the write phase;
- the direct map: `DirectLeaf`, `usableLeaves`, `UsableOk`,
  `usableLeaves_spec` (the leaves of a range lie in it, in ascending order,
  each at `DIRECT_BASE | pa`), `directLeaf_va` and **`directMap_facts`** (the
  leaves of a successful `direct_map` satisfy `LeafFacts`, each is a
  `DirectLeaf` below $2^{39}$, and they are the leaves of its usable ranges in
  address order);
- the kernel mappings: `LayoutOk`, `rangePages`, `layout_fold` (the fold of
  the checks of the ranges: the pages of the ranges with their places, and
  no page of a range meets a range checked before it), `rangePages_spec` and
  **`kernelMap_facts`** (also: the leaves are the pages of the ranges of the
  layout in address order);
- descriptors: `descriptor_kind_inj`, `ofPage_descriptor` (the kind of a page
  descriptor is its kind) and `blockAddress_of_aligned`;
- **`mapPage_single`**, **`mapBlock_single`**: a successful `map_page` or
  `map_block` is the map of its one leaf.
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables
open Krepi.Proofs.Fdt (except_bind_ok except_jp_ok except_pure_ok)

variable {r : Region} {N : Nat}

private theorem checkLeaf_ok {s : Tables r N} {base : UInt64} {taken : MapLeaf → Bool}
    {acc res : List (MapLeaf × Place)} {l : MapLeaf} (h : s.checkLeaf base taken acc l = .ok res) :
    ∃ p, s.place base l = .ok p ∧ taken l = false ∧ res = (l, p) :: acc := by
  unfold Tables.checkLeaf at h
  rw [except_bind_ok] at h
  obtain ⟨p, hp, h⟩ := h
  cases ht : taken l <;> simp_all [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, bind,
    Except.bind]

private theorem checkLeaf_fold {s : Tables r N} {base : UInt64} {taken : MapLeaf → Bool} :
    ∀ (ls : List MapLeaf) (acc res : List (MapLeaf × Place)),
      ls.foldlM (s.checkLeaf base taken) acc = .ok res →
      ∃ ps : List (MapLeaf × Place), res = ps.reverse ++ acc ∧ ps.map Prod.fst = ls ∧
        ∀ x ∈ ps, s.place base x.1 = .ok x.2 ∧ taken x.1 = false
  | [], acc, res, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨[], by simp [h], rfl, by simp⟩
  | l :: rest, acc, res, h => by
    rw [List.foldlM_cons, except_bind_ok] at h
    obtain ⟨acc', h1, h2⟩ := h
    obtain ⟨p, hp, ht, rfl⟩ := checkLeaf_ok h1
    obtain ⟨ps, rfl, hmap, hall⟩ := checkLeaf_fold rest _ res h2
    refine ⟨(l, p) :: ps, by simp, by simp [hmap], fun x hx => ?_⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨hp, ht⟩
    · exact hall x hx

private theorem mapLeaves_ok {s : Tables r N} {base : UInt64} {leaves : List (MapLeaf × Place)}
    {s₁ : Tables r N} {plan : Plan} (hs : s.used ≤ N) (h : s.mapLeaves base leaves = .ok (s₁, plan)) :
    s₁.apply plan = finalSet s base leaves ∧ (assignTables s.used leaves).1 ≤ N := by
  unfold Tables.mapLeaves at h
  generalize hr : assignTables s.used leaves = res at h
  obtain ⟨next, placed⟩ := res
  simp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at h
  · rename_i hlt
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simp only [Tables.apply, finalSet, hr], ?_⟩
    show next ≤ N; omega

private theorem mapLeaves_plan {s : Tables r N} {base : UInt64} {leaves : List (MapLeaf × Place)}
    {s₁ : Tables r N} {plan : Plan} (h : s.mapLeaves base leaves = .ok (s₁, plan)) :
    plan = mapPlan base (assignTables s.used leaves).2 ∧ s₁.pool = s.pool := by
  unfold Tables.mapLeaves at h
  generalize hr : assignTables s.used leaves = res at h
  obtain ⟨next, placed⟩ := res
  simp only at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at h
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩

/-- A leaf of the direct map: at `DIRECT_BASE | pa`, its physical address
aligned to its form, the page descriptor of `ReadWrite` or the block
descriptor of its physical address. -/
def DirectLeaf (x : MapLeaf) : Prop :=
  x.va = DIRECT_BASE ||| x.pa ∧ x.pa.toNat % x.form.size = 0 ∧
    (x.form = .page → x.desc = descriptor .readWrite x.pa) ∧
    (x.form = .block → x.desc = blockDescriptor x.pa)

private theorem directLeaves_spec (stop : Nat) (hstop : stop % PAGE_SIZE = 0) (hlim : stop ≤ VA_LIMIT) :
    ∀ fuel pa, pa % PAGE_SIZE = 0 →
      (∀ x ∈ directLeaves stop fuel pa, pa ≤ x.pa.toNat ∧ x.pa.toNat + x.form.size ≤ stop ∧
        DirectLeaf x) ∧
      (directLeaves stop fuel pa).Pairwise (fun x y => x.pa.toNat + x.form.size ≤ y.pa.toNat)
  | 0, _, _ => by simp [directLeaves]
  | fuel + 1, pa, hpa => by
    simp only [directLeaves]
    split
    · simp
    · rename_i hlt
      have hpa' : (UInt64.ofNat pa).toNat = pa := by
        rw [UInt64.toNat_ofNat']; apply Nat.mod_eq_of_lt; simp only [VA_LIMIT] at hlim; omega
      split
      · rename_i hb
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
        obtain ⟨ih1, ih2⟩ := directLeaves_spec stop hstop hlim fuel (pa + BLOCK_SIZE)
          (by simp only [BLOCK_SIZE, PAGE_SIZE] at hpa hb ⊢; omega)
        refine ⟨fun x hx => ?_, List.pairwise_cons.2 ⟨fun y hy => ?_, ih2⟩⟩
        · rcases List.mem_cons.1 hx with rfl | hx
          · refine ⟨by simp [hpa'], by simp only [hpa', Form.size]; exact hb.2, rfl, ?_,
              (fun h => by cases h), fun _ => rfl⟩
            simp only [hpa', Form.size]; exact hb.1
          · have := ih1 x hx; exact ⟨by omega, this.2⟩
        · have := (ih1 y hy).1; simp only [hpa', Form.size]; exact this
      · obtain ⟨ih1, ih2⟩ := directLeaves_spec stop hstop hlim fuel (pa + PAGE_SIZE)
          (by simp only [PAGE_SIZE] at hpa ⊢; omega)
        have hle : pa + PAGE_SIZE ≤ stop := by simp only [PAGE_SIZE] at hpa hstop ⊢; omega
        refine ⟨fun x hx => ?_, List.pairwise_cons.2 ⟨fun y hy => ?_, ih2⟩⟩
        · rcases List.mem_cons.1 hx with rfl | hx
          · refine ⟨by simp [hpa'], by simp only [hpa', Form.size]; exact hle, rfl, ?_,
              fun _ => rfl, (fun h => by cases h)⟩
            simp only [hpa', Form.size]; exact hpa
          · have := ih1 x hx; exact ⟨by omega, this.2⟩
        · have := (ih1 y hy).1; simp only [hpa', Form.size]; exact this

/-- The leaves of the direct map of one usable range. -/
def usableLeaves (u : Krepi.Spec.Fdt.Span) : List MapLeaf :=
  directLeaves u.endNat (directFuel (u.endNat - u.start.toNat)) u.start.toNat

/-- The checks of one usable range that pass. -/
def UsableOk (bits : UInt8) (u : Krepi.Spec.Fdt.Span) : Prop :=
  u.start.toNat % PAGE_SIZE = 0 ∧ u.endNat % PAGE_SIZE = 0 ∧ u.endNat ≤ VA_LIMIT ∧
    u.endNat ≤ 2 ^ bits.toNat

private theorem checkUsableRange_ok {s : Tables .upper N} {base : UInt64} {bits : UInt8}
    {earlier : List Krepi.Spec.Fdt.Span} {acc : List (MapLeaf × Place)} {u : Krepi.Spec.Fdt.Span}
    {res : List Krepi.Spec.Fdt.Span × List (MapLeaf × Place)}
    (h : s.checkUsableRange base bits (earlier, acc) u = .ok res) :
    UsableOk bits u ∧ ∃ leaves', (usableLeaves u).foldlM
      (s.checkLeaf base (fun l => earlier.any (fun e => l.meets e.start.toNat e.endNat))) acc = .ok leaves' ∧
      res = (earlier ++ [u], leaves') := by
  unfold Tables.checkUsableRange at h
  simp only at h
  obtain ⟨h1, h⟩ := except_jp_ok h
  obtain ⟨h2, h⟩ := except_jp_ok h
  rw [except_bind_ok] at h
  obtain ⟨leaves', h3, h4⟩ := h
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or, Decidable.not_not, Nat.not_lt] at h1 h2
  exact ⟨⟨h1.1, h1.2, h2.1, h2.2⟩, leaves', h3, (except_pure_ok.1 h4).symm⟩

private theorem usable_fold {s : Tables .upper N} {base : UInt64} {bits : UInt8} :
    ∀ (us earlier : List Krepi.Spec.Fdt.Span) (acc : List (MapLeaf × Place))
      (res : List Krepi.Spec.Fdt.Span × List (MapLeaf × Place)),
      us.foldlM (s.checkUsableRange base bits) (earlier, acc) = .ok res →
      ∃ new : List (MapLeaf × Place), res.2 = new.reverse ++ acc ∧
        new.map Prod.fst = us.flatMap usableLeaves ∧ (∀ x ∈ new, s.place base x.1 = .ok x.2) ∧
        (∀ u ∈ us, UsableOk bits u) ∧
        (∀ u ∈ us, ∀ y ∈ usableLeaves u, ∀ e ∈ earlier, y.meets e.start.toNat e.endNat = false) ∧
        us.Pairwise (fun u u' => ∀ y ∈ usableLeaves u', y.meets u.start.toNat u.endNat = false)
  | [], earlier, acc, res, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨[], by simp, by simp, by simp, by simp, by simp, by simp⟩
  | u :: rest, earlier, acc, res, h => by
    rw [List.foldlM_cons, except_bind_ok] at h
    obtain ⟨mid, h1, h2⟩ := h
    obtain ⟨hok, leaves', h3, rfl⟩ := checkUsableRange_ok h1
    obtain ⟨ps, rfl, hmap, hall⟩ := checkLeaf_fold _ _ _ h3
    obtain ⟨new, hres, hmap', hpl, hok', hear, hpw⟩ := usable_fold rest _ _ res h2
    refine ⟨ps ++ new, by rw [hres]; simp, by simp [hmap, hmap'], fun x hx => ?_, fun u' hu' => ?_,
      fun u' hu' y hy e he => ?_, List.pairwise_cons.2 ⟨fun u' hu' y hy => ?_, hpw⟩⟩
    · rcases List.mem_append.1 hx with hx | hx
      · exact (hall x hx).1
      · exact hpl x hx
    · rcases List.mem_cons.1 hu' with rfl | hu'
      · exact hok
      · exact hok' u' hu'
    · rcases List.mem_cons.1 hu' with rfl | hu'
      · have : y ∈ ps.map Prod.fst := by rw [hmap]; exact hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 this
        have := (hall x hx).2
        simp only [List.any_eq_false] at this
        exact Bool.eq_false_iff.2 (this e he)
      · exact hear u' hu' y hy e (List.mem_append_left _ he)
    · exact hear u' hu' y hy u (List.mem_append_right _ (List.mem_singleton_self _))

theorem usableLeaves_spec {bits : UInt8} {u : Krepi.Spec.Fdt.Span} (hu : UsableOk bits u) :
    (∀ x ∈ usableLeaves u, u.start.toNat ≤ x.pa.toNat ∧ x.pa.toNat + x.form.size ≤ u.endNat ∧
      DirectLeaf x) ∧
    (usableLeaves u).Pairwise (fun x y => x.pa.toNat + x.form.size ≤ y.pa.toNat) :=
  directLeaves_spec _ hu.2.1 hu.2.2.1 _ _ hu.1

theorem directLeaf_va {x : MapLeaf} (hx : DirectLeaf x) (hlt : x.pa.toNat < VA_LIMIT) :
    x.va.toNat = DIRECT_BASE.toNat + x.pa.toNat := by
  rw [hx.1, direct_or hlt]

private theorem form_size_dvd (f : Form) : BLOCK_SIZE % f.size = 0 := by cases f <;> decide

theorem directMap_facts {s : Tables .upper N} {memory : Krepi.Spec.Fdt.MemoryPlan} {base : UInt64}
    {bits : UInt8} {s₁ : Tables .upper N} {plan : Plan} (hs : s.WellFormed base bits)
    (h : s.directMap memory base bits = .ok (s₁, plan)) :
    ∃ leaves, LeafFacts s base bits leaves ∧ s₁.apply plan = finalSet s base leaves ∧
      (assignTables s.used leaves).1 ≤ N ∧
      (∀ lp ∈ leaves, DirectLeaf lp.1 ∧ lp.1.pa.toNat + lp.1.form.size ≤ VA_LIMIT) ∧
      plan = mapPlan base (assignTables s.used leaves).2 ∧ s₁.pool = s.pool ∧
      leaves.map Prod.fst = (sortByKey (·.start.toNat) memory.availableRanges).flatMap usableLeaves ∧
      ∀ u ∈ sortByKey (·.start.toNat) memory.availableRanges, UsableOk bits u := by
  unfold Tables.directMap at h
  rw [except_bind_ok] at h
  obtain ⟨-, -, h⟩ := h
  rw [except_bind_ok] at h
  obtain ⟨res, hf, h⟩ := h
  obtain ⟨new, hres, hmap, hpl, hok, -, hpw⟩ := usable_fold _ [] [] res hf
  obtain ⟨_, lv⟩ := res
  simp only [List.append_nil] at hres
  subst hres
  simp only [List.reverse_reverse] at h
  obtain ⟨happ, hN⟩ := mapLeaves_ok hs.2.2.1 h
  have hplan := mapLeaves_plan h
  have hleaf : ∀ x ∈ new.map Prod.fst, ∃ u ∈ sortByKey (·.start.toNat) memory.availableRanges,
      u.start.toNat ≤ x.pa.toNat ∧ x.pa.toNat + x.form.size ≤ u.endNat ∧ DirectLeaf x := by
    intro x hx
    rw [hmap] at hx
    obtain ⟨u, hu, hx⟩ := List.mem_flatMap.1 hx
    exact ⟨u, hu, (usableLeaves_spec (hok u hu)).1 x hx⟩
  have hD : DIRECT_BASE.toNat % BLOCK_SIZE = 0 := by decide
  have hlim : ∀ x ∈ new.map Prod.fst, x.pa.toNat + x.form.size ≤ VA_LIMIT ∧ DirectLeaf x ∧
      x.pa.toNat < 2 ^ bits.toNat := by
    intro x hx
    obtain ⟨u, hu, -, h2, h3⟩ := hleaf x hx
    obtain ⟨-, -, h4, h5⟩ := hok u hu
    have := form_size_pos x.form
    exact ⟨by omega, h3, by omega⟩
  refine ⟨new, ⟨hpl, ?_, fun lp hlp => ?_, fun lp hlp => ?_, fun lp hlp => ?_⟩, happ, hN,
    fun lp hlp => ⟨(hlim _ (List.mem_map_of_mem hlp)).2.1, (hlim _ (List.mem_map_of_mem hlp)).1⟩,
    hplan.1, hplan.2, hmap, hok⟩
  · have hva : ∀ x ∈ new.map Prod.fst, x.va.toNat = DIRECT_BASE.toNat + x.pa.toNat := fun x hx => by
      obtain ⟨h1, h2, -⟩ := hlim x hx
      exact directLeaf_va h2 (by have := form_size_pos x.form; omega)
    rw [hmap, List.pairwise_flatMap]
    refine ⟨fun u hu => ?_, ?_⟩
    · refine (usableLeaves_spec (hok u hu)).2.imp_of_mem fun {x y} hx hy h => ?_
      have hx' : x ∈ new.map Prod.fst := by rw [hmap]; exact List.mem_flatMap.2 ⟨u, hu, hx⟩
      have hy' : y ∈ new.map Prod.fst := by rw [hmap]; exact List.mem_flatMap.2 ⟨u, hu, hy⟩
      rw [hva x hx', hva y hy']; omega
    · refine ((sortByKey_pairwise (·.start.toNat) memory.availableRanges).and hpw).imp_of_mem
        fun {u u'} hu hu' ⟨hle, hnm⟩ x hx y hy => ?_
      have hx' : x ∈ new.map Prod.fst := by rw [hmap]; exact List.mem_flatMap.2 ⟨u, hu, hx⟩
      have hy' : y ∈ new.map Prod.fst := by rw [hmap]; exact List.mem_flatMap.2 ⟨u', hu', hy⟩
      obtain ⟨-, hx2, -⟩ := (usableLeaves_spec (hok u hu)).1 x hx
      obtain ⟨hy1, -, -⟩ := (usableLeaves_spec (hok u' hu')).1 y hy
      have hm := hnm y hy
      simp only [MapLeaf.meets, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt] at hm
      have := form_size_pos y.form
      rw [hva x hx', hva y hy']; omega
  · obtain ⟨h1, h2, -⟩ := hlim _ (List.mem_map_of_mem hlp)
    simp only [Region.holds, decide_eq_true_eq]
    rw [directLeaf_va h2 (by have := form_size_pos lp.1.form; omega)]; omega
  · obtain ⟨h1, h2, -⟩ := hlim _ (List.mem_map_of_mem hlp)
    rw [directLeaf_va h2 (by have := form_size_pos lp.1.form; omega)]
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add
      (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero (form_size_dvd lp.1.form)) (Nat.dvd_of_mod_eq_zero hD))
      (Nat.dvd_of_mod_eq_zero h2.2.1))
  · obtain ⟨-, h2, h3⟩ := hlim _ (List.mem_map_of_mem hlp)
    refine ⟨fun hp => ⟨⟨.readWrite, ?_⟩, ?_⟩, fun hb => ⟨?_, ?_⟩⟩
    · rw [h2.2.2.1 hp, outputAddress_descriptor, descriptor_outputAddress]
    · rw [h2.2.2.1 hp, outputAddress_descriptor]; have := outputAddress_le lp.1.pa; omega
    · rw [h2.2.2.2 hb]; exact isReadWriteBlock_blockDescriptor _
    · rw [h2.2.2.2 hb, blockAddress_blockDescriptor]; have := blockAddress_le lp.1.pa; omega

/-! ## The kernel mappings -/

private theorem layoutPages_spec (k : Kind) : ∀ count pa, pa + count * PAGE_SIZE ≤ VA_LIMIT →
    (∀ x ∈ layoutPages k count pa, pa ≤ x.pa.toNat ∧ x.pa.toNat + PAGE_SIZE ≤ pa + count * PAGE_SIZE ∧
      x.pa.toNat % PAGE_SIZE = pa % PAGE_SIZE ∧ x.va = x.pa ∧ x.form = .page ∧
      x.desc = descriptor k x.pa) ∧
    (layoutPages k count pa).Pairwise (fun x y => x.pa.toNat + PAGE_SIZE ≤ y.pa.toNat)
  | 0, _, _ => by simp [layoutPages]
  | count + 1, pa, hlim => by
    simp only [layoutPages]
    have hpa' : (UInt64.ofNat pa).toNat = pa := by
      rw [UInt64.toNat_ofNat']; apply Nat.mod_eq_of_lt; simp only [VA_LIMIT, PAGE_SIZE] at hlim; omega
    obtain ⟨ih1, ih2⟩ := layoutPages_spec k count (pa + PAGE_SIZE) (by
      simp only [PAGE_SIZE] at hlim ⊢; rw [Nat.add_mul] at hlim; omega)
    refine ⟨fun x hx => ?_, List.pairwise_cons.2 ⟨fun y hy => ?_, ih2⟩⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · simp only [hpa', PAGE_SIZE]; refine ⟨Nat.le_refl _, by omega, ?_⟩; simp
      · obtain ⟨h1, h2, h3, h4⟩ := ih1 x hx
        simp only [PAGE_SIZE] at h1 h2 h3 ⊢
        refine ⟨by omega, by rw [Nat.add_mul]; omega, by omega, h4⟩
    · have := (ih1 y hy).1; rw [hpa']; exact this

/-- The checks of one range of a layout that pass. -/
def LayoutOk (bits : UInt8) (j : LayoutRange) : Prop :=
  j.range.start.toNat % PAGE_SIZE = 0 ∧ j.range.endNat % PAGE_SIZE = 0 ∧ j.range.endNat ≤ VA_LIMIT ∧
    j.range.endNat ≤ 2 ^ bits.toNat

/-- The pages of one range of a layout. -/
def rangePages (j : LayoutRange) : List MapLeaf :=
  layoutPages j.kind (j.range.len.toNat / PAGE_SIZE) j.range.start.toNat

private theorem checkLayoutRange_ok {s : Tables .lower N} {base : UInt64} {bits : UInt8} {guards : List UInt64}
    {earlier : List PhysRange} {acc : List (MapLeaf × Place)} {j : LayoutRange}
    {res : List PhysRange × List (MapLeaf × Place)}
    (h : s.checkLayoutRange base bits guards (earlier, acc) j = .ok res) :
    LayoutOk bits j ∧ ∃ leaves', (rangePages j).foldlM (s.checkLeaf base (fun l =>
      earlier.any (fun e => l.meets e.start.toNat e.endNat) || l.isGuard guards)) acc = .ok leaves' ∧
      res = (earlier ++ [j.range], leaves') := by
  unfold Tables.checkLayoutRange at h
  simp only at h
  obtain ⟨h1, h⟩ := except_jp_ok h
  obtain ⟨h2, h⟩ := except_jp_ok h
  rw [except_bind_ok] at h
  obtain ⟨leaves', h3, h4⟩ := h
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or, Decidable.not_not, Nat.not_lt] at h1 h2
  exact ⟨⟨h1.1, h1.2, h2.1, h2.2⟩, leaves', h3, (except_pure_ok.1 h4).symm⟩

theorem layout_fold {s : Tables .lower N} {base : UInt64} {bits : UInt8} {guards : List UInt64} :
    ∀ (js : List LayoutRange) (earlier : List PhysRange) (acc : List (MapLeaf × Place))
      (res : List PhysRange × List (MapLeaf × Place)),
      js.foldlM (s.checkLayoutRange base bits guards) (earlier, acc) = .ok res →
      ∃ new : List (MapLeaf × Place), res.2 = new.reverse ++ acc ∧
        new.map Prod.fst = js.flatMap rangePages ∧ (∀ x ∈ new, s.place base x.1 = .ok x.2) ∧
        (∀ j ∈ js, LayoutOk bits j) ∧
        (∀ j ∈ js, ∀ y ∈ rangePages j, ∀ e ∈ earlier, y.meets e.start.toNat e.endNat = false) ∧
        js.Pairwise (fun j j' => ∀ y ∈ rangePages j', y.meets j.range.start.toNat j.range.endNat = false)
  | [], earlier, acc, res, h => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact ⟨[], by simp, by simp, by simp, by simp, by simp, by simp⟩
  | j :: rest, earlier, acc, res, h => by
    rw [List.foldlM_cons, except_bind_ok] at h
    obtain ⟨mid, h1, h2⟩ := h
    obtain ⟨hok, leaves', h3, rfl⟩ := checkLayoutRange_ok h1
    obtain ⟨ps, rfl, hmap, hall⟩ := checkLeaf_fold _ _ _ h3
    obtain ⟨new, hres, hmap', hpl, hok', hear, hpw⟩ := layout_fold rest _ _ res h2
    refine ⟨ps ++ new, by rw [hres]; simp, by simp [hmap, hmap'], fun x hx => ?_, fun j' hj' => ?_,
      fun j' hj' y hy e he => ?_, List.pairwise_cons.2 ⟨fun j' hj' y hy => ?_, hpw⟩⟩
    · rcases List.mem_append.1 hx with hx | hx
      · exact (hall x hx).1
      · exact hpl x hx
    · rcases List.mem_cons.1 hj' with rfl | hj'
      · exact hok
      · exact hok' j' hj'
    · rcases List.mem_cons.1 hj' with rfl | hj'
      · have : y ∈ ps.map Prod.fst := by rw [hmap]; exact hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.1 this
        have := (hall x hx).2
        simp only [Bool.or_eq_false_iff, List.any_eq_false] at this
        exact Bool.eq_false_iff.2 (this.1 e he)
      · exact hear j' hj' y hy e (List.mem_append_left _ he)
    · exact hear j' hj' y hy j.range (List.mem_append_right _ (List.mem_singleton_self _))

theorem rangePages_spec {bits : UInt8} {j : LayoutRange} (hj : LayoutOk bits j) :
    (∀ x ∈ rangePages j, j.range.start.toNat ≤ x.pa.toNat ∧ x.pa.toNat + PAGE_SIZE ≤ j.range.endNat ∧
      x.pa.toNat % PAGE_SIZE = 0 ∧ x.va = x.pa ∧ x.form = .page ∧ x.desc = descriptor j.kind x.pa) ∧
    (rangePages j).Pairwise (fun x y => x.pa.toNat + PAGE_SIZE ≤ y.pa.toNat) := by
  obtain ⟨h1, h2, h3, -⟩ := hj
  have hle : j.range.start.toNat + j.range.len.toNat / PAGE_SIZE * PAGE_SIZE ≤ j.range.endNat := by
    simp only [PhysRange.endNat, PAGE_SIZE]; omega
  obtain ⟨a, b⟩ := layoutPages_spec j.kind (j.range.len.toNat / PAGE_SIZE) j.range.start.toNat (by omega)
  refine ⟨fun x hx => ?_, b⟩
  obtain ⟨c1, c2, c3, c4⟩ := a x hx
  exact ⟨c1, by omega, by rw [c3]; exact h1, c4⟩

theorem kernelMap_facts {s : Tables .lower N} {layout : Layout} {base : UInt64}
    {bits : UInt8} {s₁ : Tables .lower N} {plan : Plan} (hs : s.WellFormed base bits)
    (h : s.kernelMap layout base bits = .ok (s₁, plan)) :
    ∃ leaves, LeafFacts s base bits leaves ∧ s₁.apply plan = finalSet s base leaves ∧
      (assignTables s.used leaves).1 ≤ N ∧
      plan = mapPlan base (assignTables s.used leaves).2 ∧ s₁.pool = s.pool ∧
      leaves.map Prod.fst = (sortByKey (·.range.start.toNat) layout.ranges).flatMap rangePages ∧
      ∀ j ∈ sortByKey (·.range.start.toNat) layout.ranges, LayoutOk bits j := by
  unfold Tables.kernelMap at h
  rw [except_bind_ok] at h
  obtain ⟨-, -, h⟩ := h
  rw [except_bind_ok] at h
  obtain ⟨res, hf, h⟩ := h
  obtain ⟨new, hres, hmap, hpl, hok, -, hpw⟩ := layout_fold _ [] [] res hf
  obtain ⟨_, lv⟩ := res
  simp only [List.append_nil] at hres
  subst hres
  simp only [List.reverse_reverse] at h
  obtain ⟨happ, hN⟩ := mapLeaves_ok hs.2.2.1 h
  have hplan := mapLeaves_plan h
  have hleaf : ∀ x ∈ new.map Prod.fst, ∃ j ∈ sortByKey (·.range.start.toNat) layout.ranges,
      j.range.start.toNat ≤ x.pa.toNat ∧ x.pa.toNat + PAGE_SIZE ≤ j.range.endNat ∧
      x.pa.toNat % PAGE_SIZE = 0 ∧ x.va = x.pa ∧ x.form = .page ∧ x.desc = descriptor j.kind x.pa := by
    intro x hx
    rw [hmap] at hx
    obtain ⟨j, hj, hx⟩ := List.mem_flatMap.1 hx
    exact ⟨j, hj, (rangePages_spec (hok j hj)).1 x hx⟩
  refine ⟨new, ⟨hpl, ?_, fun lp hlp => ?_, fun lp hlp => ?_, fun lp hlp => ?_⟩, happ, hN,
    hplan.1, hplan.2, hmap, hok⟩
  · rw [hmap, List.pairwise_flatMap]
    refine ⟨fun j hj => ?_, ?_⟩
    · refine (rangePages_spec (hok j hj)).2.imp_of_mem fun {x y} hx hy h => ?_
      obtain ⟨-, -, -, hxv, hxf, -⟩ := (rangePages_spec (hok j hj)).1 x hx
      obtain ⟨-, -, -, hyv, -, -⟩ := (rangePages_spec (hok j hj)).1 y hy
      rw [hxv, hyv, hxf]; exact h
    · refine ((sortByKey_pairwise (·.range.start.toNat) layout.ranges).and hpw).imp_of_mem
        fun {j j'} hj hj' ⟨hle, hnm⟩ x hx y hy => ?_
      obtain ⟨-, hx2, -, hxv, hxf, -⟩ := (rangePages_spec (hok j hj)).1 x hx
      obtain ⟨hy1, -, -, hyv, hyf, -⟩ := (rangePages_spec (hok j' hj')).1 y hy
      have hm := hnm y hy
      simp only [MapLeaf.meets, Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt, hyf,
        Form.size] at hm
      rw [hxv, hyv, hxf]; simp only [Form.size] at hle ⊢; simp only [PAGE_SIZE] at hm hx2 hy1 ⊢
      omega
  · obtain ⟨j, hj, -, h2, -, h4, -, -⟩ := hleaf _ (List.mem_map_of_mem hlp)
    obtain ⟨-, -, h3, -⟩ := hok j hj
    simp only [Region.holds, decide_eq_true_eq, h4]; simp only [PAGE_SIZE] at h2; omega
  · obtain ⟨j, hj, -, -, h3, h4, h5, -⟩ := hleaf _ (List.mem_map_of_mem hlp)
    rw [h4, h5]; exact h3
  · obtain ⟨j, hj, -, h2, -, -, h5, h6⟩ := hleaf _ (List.mem_map_of_mem hlp)
    obtain ⟨-, -, -, h7⟩ := hok j hj
    refine ⟨fun _ => ⟨⟨j.kind, ?_⟩, ?_⟩, fun hb => absurd (h5.symm.trans hb) (by decide)⟩
    · rw [h6, outputAddress_descriptor, descriptor_outputAddress]
    · rw [h6, outputAddress_descriptor]; have := outputAddress_le lp.1.pa; simp only [PAGE_SIZE] at h2; omega

/-! ## Descriptors of the direct map -/

private theorem descriptor_and_not_mask (k : Kind) (a : UInt64) :
    descriptor k a &&& ~~~ADDRESS_MASK = k.attributes.bits ||| TABLE_OR_PAGE := by
  simp only [descriptor, u64_or_and, UInt64.and_assoc, attr_and_not_mask]
  rw [show ADDRESS_MASK &&& ~~~ADDRESS_MASK = 0 by decide,
    show TABLE_OR_PAGE &&& ~~~ADDRESS_MASK = TABLE_OR_PAGE by decide, UInt64.and_zero, UInt64.zero_or]

theorem descriptor_kind_inj {k k' : Kind} {a : UInt64} (h : descriptor k a = descriptor k' a) : k = k' := by
  have := congrArg (· &&& ~~~ADDRESS_MASK) h
  simp only [descriptor_and_not_mask] at this
  revert this; cases k <;> cases k' <;> decide

theorem ofPage_descriptor (k : Kind) (a : UInt64) : Kind.ofPage (descriptor k a) = some k := by
  unfold Kind.ofPage
  simp only [outputAddress_descriptor, descriptor_outputAddress]
  have hiff : ∀ k', (descriptor k' a == descriptor k a) = decide (k' = k) := by
    intro k'
    by_cases h : k' = k
    · subst h; simp
    · simp only [h, decide_false]; exact beq_eq_false_iff_ne.2 fun e => h (descriptor_kind_inj e)
  simp only [hiff]
  cases k <;> decide

theorem blockAddress_of_aligned {a : UInt64} (h1 : a.toNat % BLOCK_SIZE = 0)
    (h2 : a.toNat < 2 ^ 48) : blockAddress a = a := by
  apply UInt64.toNat_inj.1
  rw [blockAddress, UInt64.toNat_and,
    show BLOCK_ADDRESS_MASK.toNat = (2 ^ 27 - 1) * 2 ^ 21 by decide]
  obtain ⟨q, hq⟩ : ∃ q, a.toNat = q * 2 ^ 21 := ⟨a.toNat / 2097152, by simp [BLOCK_SIZE] at h1; omega⟩
  have hq27 : q < 2 ^ 27 := by
    have : q * 2097152 < 2 ^ 48 := by rw [← hq]; exact h2
    simp only [Nat.reducePow] at this ⊢; omega
  rw [hq]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hb : q.testBit (j - 21) = true
  · have hge := Nat.ge_two_pow_of_testBit hb
    have hlt : j - 21 < 27 := by
      apply Nat.lt_of_not_le; intro hc
      have : 2 ^ 27 ≤ 2 ^ (j - 21) := Nat.pow_le_pow_right (by decide) hc
      omega
    simp [hb, hlt]
  · simp [hb]

/-! ## `map_page` as a map of one leaf -/

/-- A `map_page` that succeeds on a well-formed set is the map of its one
leaf: the leaf passes the checks of a map (`LeafFacts`) at the place of its
walk, the set after the plan is `finalSet`, and the plan is `mapPlan` of the
placed leaf; the physical page is aligned and below $2^{\mathrm{bits}}$, and the
write phase keeps the pool. -/
theorem mapPage_single {s s' : Tables r N} {v p base : UInt64} {k : Kind}
    {bits : UInt8} {plan : Plan} (hs : s.WellFormed base bits)
    (h : s.mapPage v p k base bits = .ok (s', plan)) :
    ∃ pl, LeafFacts s base bits [(⟨v, p, descriptor k p, .page⟩, pl)] ∧
      s'.apply plan = finalSet s base [(⟨v, p, descriptor k p, .page⟩, pl)] ∧
      (assignTables s.used [(⟨v, p, descriptor k p, .page⟩, pl)]).1 ≤ N ∧
      plan = mapPlan base (assignTables s.used [(⟨v, p, descriptor k p, .page⟩, pl)]).2 ∧
      p.toNat % PAGE_SIZE = 0 ∧ p.toNat < 2 ^ bits.toNat ∧ s'.pool = s.pool := by
  unfold Tables.mapPage at h
  obtain ⟨u1, hce, h⟩ := except_bind_ok.1 h
  obtain ⟨u2, hcp, h⟩ := except_bind_ok.1 h
  obtain ⟨w, hw, h⟩ := except_bind_ok.1 h
  obtain ⟨hv, -, hr, -, -⟩ := checkEntry_ok.1 hce
  obtain ⟨hpa, hpb⟩ := checkPhysical_ok.1 hcp
  have huN := hs.2.2.1
  have hd : LeafDesc bits ⟨v, p, descriptor k p, .page⟩ :=
    ⟨fun _ => ⟨⟨k, by rw [outputAddress_descriptor, descriptor_outputAddress]⟩, by
      rw [outputAddress_descriptor]; exact Nat.lt_of_le_of_lt (outputAddress_le p) hpb⟩,
      fun hb => by cases hb⟩
  have key : ∀ pl, s.place base ⟨v, p, descriptor k p, .page⟩ = .ok pl →
      LeafFacts s base bits [(⟨v, p, descriptor k p, .page⟩, pl)] := fun pl hpl =>
    ⟨fun lp h => by rw [List.mem_singleton] at h; subst h; exact hpl, List.pairwise_singleton _ _,
      fun lp h => by rw [List.mem_singleton] at h; subst h; exact hr,
      fun lp h => by rw [List.mem_singleton] at h; subst h; exact hv,
      fun lp h => by rw [List.mem_singleton] at h; subst h; exact hd⟩
  rcases w with _ | ⟨t2, e2⟩
  · obtain ⟨hlt, h⟩ := except_jp_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.root, key _ (by unfold Tables.place; rw [hw]; rfl), rfl,
      by show s.used + 1 + 1 ≤ N; omega, rfl, hpa, hpb, rfl⟩
  · dsimp only at h
    split at h
    · rename_i hv2
      obtain ⟨hlt, h⟩ := except_jp_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨.level2 t2, key _ ?_, rfl, by show s.used + 1 ≤ N; omega, rfl, hpa, hpb, rfl⟩
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
            refine ⟨.level3 t2 t3, key _ ?_, rfl, huN, rfl, hpa, hpb, rfl⟩
            unfold Tables.place; rw [hw]
            simp only [bind, Except.bind, hv2, hb, hc, hv3, Bool.false_eq_true, ite_false]; rfl
        next => simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A `map_block` that succeeds on a well-formed set is the map of its one
leaf, as `mapPage_single` for a page. -/
theorem mapBlock_single {s s' : Tables r N} {v p base : UInt64} {bits : UInt8} {plan : Plan}
    (hs : s.WellFormed base bits) (h : s.mapBlock v p base bits = .ok (s', plan)) :
    ∃ pl, LeafFacts s base bits [(⟨v, p, blockDescriptor p, .block⟩, pl)] ∧
      s'.apply plan = finalSet s base [(⟨v, p, blockDescriptor p, .block⟩, pl)] ∧
      (assignTables s.used [(⟨v, p, blockDescriptor p, .block⟩, pl)]).1 ≤ N ∧
      plan = mapPlan base (assignTables s.used [(⟨v, p, blockDescriptor p, .block⟩, pl)]).2 ∧
      s'.pool = s.pool := by
  unfold Tables.mapBlock at h
  obtain ⟨u1, hce, h⟩ := except_bind_ok.1 h
  obtain ⟨u2, hcp, h⟩ := except_bind_ok.1 h
  obtain ⟨w, hw, h⟩ := except_bind_ok.1 h
  obtain ⟨hv, -, hr, -, -⟩ := checkEntry_ok.1 hce
  have hpb := (checkPhysical_ok.1 hcp).2
  have hd : LeafDesc bits ⟨v, p, blockDescriptor p, .block⟩ :=
    ⟨(fun h => by cases h), fun _ => ⟨isReadWriteBlock_blockDescriptor p, by
      rw [blockAddress_blockDescriptor]; exact Nat.lt_of_le_of_lt (blockAddress_le p) hpb⟩⟩
  have key : ∀ pl, s.place base ⟨v, p, blockDescriptor p, .block⟩ = .ok pl →
      LeafFacts s base bits [(⟨v, p, blockDescriptor p, .block⟩, pl)] := fun pl hpl =>
    ⟨fun lp h => by rw [List.mem_singleton] at h; subst h; exact hpl, List.pairwise_singleton _ _,
      fun lp h => by rw [List.mem_singleton] at h; subst h; exact hr,
      fun lp h => by rw [List.mem_singleton] at h; subst h; exact hv,
      fun lp h => by rw [List.mem_singleton] at h; subst h; exact hd⟩
  rcases w with _ | ⟨t2, e2⟩
  · obtain ⟨hlt, h⟩ := except_jp_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨.root, key _ (by unfold Tables.place; rw [hw]; rfl), rfl,
      by show s.used + 1 ≤ N; omega, rfl, rfl⟩
  · obtain ⟨-, h⟩ := except_jp_ok h
    obtain ⟨hv2, h⟩ := except_jp_ok h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨.level2 t2, key _ ?_, rfl, hs.2.2.1, rfl, rfl⟩
    unfold Tables.place; rw [hw]
    simp only [bind, Except.bind, Bool.not_eq_true] at hv2 ⊢
    simp only [hv2, Bool.not_false, ite_true]; rfl

end Krepi.Proofs.PageTables
