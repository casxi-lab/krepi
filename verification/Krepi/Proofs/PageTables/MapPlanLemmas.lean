module

public import Krepi.Spec.PageTables.Boot
public import Krepi.Proofs.PageTables.PoolLemmas
import Mathlib.Util.CountHeartbeats

/-!
# Page tables: lemmas about the plan of a map

The plan of `kernel_map` and `direct_map` (`mapPlan`) as the set of stores
that its placed leaves need, for a list of placed leaves whose tables agree
slot by slot (`PlacedOk`):

- the execution of a plan whose stores into one entry agree and which zeroes
  each table before any store into it (`ZeroFirst`): `lastAt_of_no_store`,
  `lastAt_of_store`, `get_exec_store` (the entry holds the value of its
  stores) and `get_exec_old` (an entry that no step stores into keeps its
  value);
- runs (`runsBy`): `runsBy_flatten`, `runsBy_key` (each run is nonempty and
  of one key), `mem_runsBy` and `runsBy_pairwise` (the runs of a sorted list
  are in strictly ascending order of their keys);
- the stores that a placed leaf needs, `writesOf` (the link of its new level 2
  table into the root, the link `link3` of its new level 3 table into its
  level 2 table, and the leaf), and its new tables, `NewTable`;
- placed leaves whose tables agree slot by slot, `PlacedOk`, with the slot
  facts `gib_of_block`, `index1_of_gib` and `index2_of_block`;
- the plan: `runSteps`, `mapPlan_eq`, `childSteps`, `newLevel2Steps_eq`,
  `mem_writesOf`, `gib_run`, `block_run` (the leaves of a 1 GiB run and of a
  2 MiB run agree on their tables), `mem_map_store`, `mem_childSteps`,
  `mem_level2Entry`, `mem_newLevel2Steps`, `mem_heldLevel2Steps`,
  `mem_runSteps` and `mem_mapPlan` (a store is in the plan exactly when a
  placed leaf needs it); `store_table`, `conflict`, `store_ne_zero`,
  `zero_not_mem_map_store`, `zero_not_mem_level2Entry`, `zero_runSteps` and
  `zero_mapPlan` (the plan zeroes only new tables); `pairwise_of_no_zero`,
  `pairwise_runsBy_lt`, `pairwise_block_runs` and `pairwise_mapPlan` (it
  zeroes each new table before any store into it).
-/

@[expose] public section

namespace Krepi.Proofs.PageTables

open Krepi.Spec.PageTables

/-! ## Execution of a plan whose stores agree -/

/-- No step stores into a table that a later step zeroes. -/
def ZeroFirst (x y : Step) : Prop := ∀ t i d, x = .store t i d → y ≠ .zero t

theorem lastAt_of_no_store {t i : Nat} : ∀ {l : Plan}, (∀ d, .store t i d ∉ l) →
    lastAt t i l = none ∨ (lastAt t i l = some 0 ∧ .zero t ∈ l)
  | [], _ => Or.inl rfl
  | x :: rest, h => by
    have ih := lastAt_of_no_store (l := rest) (fun d hd => h d (List.mem_cons_of_mem _ hd))
    simp only [lastAt]
    rcases ih with ih | ⟨ih, hz⟩
    · rw [ih, Option.none_or]
      cases x with
      | zero t' =>
        by_cases ht : t' = t
        · subst ht; exact Or.inr ⟨by simp [stepAt], by simp⟩
        · exact Or.inl (by simp [stepAt, ht])
      | store t' i' d =>
        by_cases ht : t' = t ∧ i' = i
        · obtain ⟨rfl, rfl⟩ := ht; exact absurd (List.mem_cons_self) (h d)
        · exact Or.inl (by simp [stepAt, ht])
      | fence => exact Or.inl rfl
      | sync => exact Or.inl rfl
      | invalidate _ => exact Or.inl rfl
    · rw [ih]; exact Or.inr ⟨rfl, List.mem_cons_of_mem _ hz⟩

theorem lastAt_of_store {t i : Nat} {d : UInt64} : ∀ {l : Plan}, l.Pairwise ZeroFirst →
    (∀ d', .store t i d' ∈ l → d' = d) → .store t i d ∈ l → lastAt t i l = some d
  | [], _, _, h => absurd h (by simp)
  | x :: rest, hpw, hf, h => by
    rw [List.pairwise_cons] at hpw
    simp only [lastAt]
    by_cases hr : ∃ d', .store t i d' ∈ rest
    · obtain ⟨d', hd'⟩ := hr
      have := hf d' (List.mem_cons_of_mem _ hd'); subst this
      rw [lastAt_of_store hpw.2 (fun d'' h => hf d'' (List.mem_cons_of_mem _ h)) hd']; rfl
    · have hr' : ∀ d', .store t i d' ∉ rest := fun d' h => hr ⟨d', h⟩
      have hx : x = .store t i d := by
        rcases List.mem_cons.1 h with h | h
        · exact h.symm
        · exact absurd h (hr' d)
      subst hx
      rcases lastAt_of_no_store hr' with h0 | ⟨-, hz⟩
      · rw [h0]; simp [stepAt]
      · exact absurd rfl (hpw.1 _ hz t i d rfl)

/-- The entry of a pool after a plan whose stores into the entry agree, and
that zeroes only zero tables before any store into them: the value of its
stores, or the entry as it was. -/
theorem get_exec_store {plan : Plan} {p : Pool N} {t i : Nat} {d : UInt64} (ht : t < N)
    (hi : i < ENTRIES) (hpw : plan.Pairwise ZeroFirst)
    (hf : ∀ d', .store t i d' ∈ plan → d' = d) (h : .store t i d ∈ plan) :
    (plan.exec p).get t i = d := by
  rw [get_exec _ _ ht hi, lastAt_of_store hpw hf h]; rfl

theorem get_exec_old {plan : Plan} {p : Pool N} {t i : Nat} (ht : t < N) (hi : i < ENTRIES)
    (hz : .zero t ∈ plan → p.get t i = 0) (h : ∀ d, .store t i d ∉ plan) :
    (plan.exec p).get t i = p.get t i := by
  rw [get_exec _ _ ht hi]
  rcases lastAt_of_no_store h with h0 | ⟨h0, hzt⟩
  · rw [h0]; rfl
  · rw [h0]; exact (hz hzt).symm

/-! ## Runs -/

variable {α : Type}

theorem runsBy_flatten (key : α → Nat) : ∀ l : List α, (runsBy key l).flatten = l
  | [] => rfl
  | x :: rest => by
    have ih := runsBy_flatten key rest
    simp only [runsBy]
    split
    · rename_i y run runs h
      rw [h] at ih
      split <;> simp_all
    · simp_all

theorem runsBy_key (key : α → Nat) : ∀ l : List α, ∀ R ∈ runsBy key l,
    ∃ x xs, R = x :: xs ∧ ∀ y ∈ R, key y = key x
  | [] => by simp [runsBy]
  | x :: rest => by
    have ih := runsBy_key key rest
    simp only [runsBy]
    split
    · rename_i y run runs h
      rw [h] at ih
      split
      · rename_i hk
        intro R hR
        rcases List.mem_cons.1 hR with rfl | hR
        · obtain ⟨y', ys, hy, hall⟩ := ih _ List.mem_cons_self
          refine ⟨x, y :: run, rfl, ?_⟩
          intro z hz
          rcases List.mem_cons.1 hz with rfl | hz
          · rfl
          · rw [hall z hz, ← hall y List.mem_cons_self]; exact (beq_iff_eq.1 hk).symm
        · exact ih R (List.mem_cons_of_mem _ hR)
      · intro R hR
        rcases List.mem_cons.1 hR with rfl | hR
        · exact ⟨x, [], rfl, by simp⟩
        · exact ih R hR
    · intro R hR
      rcases List.mem_cons.1 hR with rfl | hR
      · exact ⟨x, [], rfl, by simp⟩
      · exact ih R hR

theorem mem_runsBy (key : α → Nat) {l : List α} {x : α} : x ∈ l ↔ ∃ R ∈ runsBy key l, x ∈ R := by
  have := List.mem_flatten (L := runsBy key l) (a := x)
  rwa [runsBy_flatten] at this

theorem runsBy_pairwise (key : α → Nat) : ∀ l : List α, l.Pairwise (fun a b => key a ≤ key b) →
    (runsBy key l).Pairwise (fun R R' => ∀ x ∈ R, ∀ y ∈ R', key x < key y)
  | [], _ => by simp [runsBy]
  | x :: rest, h => by
    rw [List.pairwise_cons] at h
    have ih := runsBy_pairwise key rest h.2
    have hk := runsBy_key key rest
    have hx : ∀ R ∈ runsBy key rest, ∀ y ∈ R, key x ≤ key y :=
      fun R hR y hy => h.1 y ((mem_runsBy key).2 ⟨R, hR, hy⟩)
    simp only [runsBy]
    split
    · rename_i y run runs hr
      rw [hr] at ih hk hx
      rw [List.pairwise_cons] at ih
      split
      · rename_i hxy
        rw [List.pairwise_cons]
        refine ⟨?_, ih.2⟩
        intro R' hR' z hz w hw
        rcases List.mem_cons.1 hz with rfl | hz
        · rw [beq_iff_eq.1 hxy]; exact ih.1 R' hR' y List.mem_cons_self w hw
        · exact ih.1 R' hR' z hz w hw
      · rename_i hxy
        rw [List.pairwise_cons, List.pairwise_cons]
        refine ⟨?_, ih.1, ih.2⟩
        intro R' hR' z hz w hw
        rw [List.mem_singleton] at hz; subst hz
        have hle := hx R' hR' w hw
        rcases List.mem_cons.1 hR' with rfl | hR'
        · obtain ⟨y', ys, hy', hall⟩ := hk _ List.mem_cons_self
          have : key w = key y := by rw [hall w hw, hall y List.mem_cons_self]
          have hne : key z ≠ key y := fun e => hxy (beq_iff_eq.2 e)
          omega
        · have := ih.1 R' hR' y List.mem_cons_self w hw
          have := hx _ List.mem_cons_self y List.mem_cons_self
          omega
    · rw [List.pairwise_cons]
      refine ⟨?_, ih⟩
      intro R' hR' z hz w hw
      rw [List.mem_singleton] at hz; subst hz
      rename_i hr
      exfalso
      cases h' : runsBy key rest with
      | nil => rw [h'] at hR'; simp at hR'
      | cons R0 Rs =>
        obtain ⟨y0, ys0, hR0, -⟩ := hk R0 (by rw [h']; exact List.mem_cons_self)
        exact hr y0 ys0 Rs (by rw [h', hR0])

/-- The steps of the leaves of one 1 GiB slot in `mapPlan`. -/
def runSteps (base : UInt64) : List Placed → Plan
  | p :: rest =>
    if p.new2 then newLevel2Steps base (p :: rest)
    else (runsBy (·.leaf.blockSlot) (p :: rest)).flatMap (heldLevel2Steps base)
  | [] => []

theorem mapPlan_eq (base : UInt64) (placed : List Placed) :
    mapPlan base placed = (runsBy (·.leaf.gibSlot) placed).flatMap (runSteps base) ++ [.sync] := by
  simp only [mapPlan]; congr 2; funext run; cases run <;> rfl

/-- The stores that one placed leaf needs. -/
def writesOf (base : UInt64) (q : Placed) : Plan :=
  (if q.new2 then [.store 0 (index1 q.leaf.va) (tableAt base q.t2)] else []) ++
  (if q.leaf.form = .page ∧ q.new3 = true then
    [.store q.t2 (index2 q.leaf.va) (tableAt base q.t3)] else []) ++ [q.store]

/-- The new tables of a placed leaf. -/
def NewTable (q : Placed) (t : Nat) : Prop :=
  (q.new2 = true ∧ t = q.t2) ∨ (q.leaf.form = .page ∧ q.new3 = true ∧ t = q.t3)

/-- Placed leaves whose tables agree slot by slot: in ascending address
order; one level 2 table for each 1 GiB slot and one level 3 table for each
2 MiB slot of pages; a block alone in its 2 MiB slot; a page under a new level
2 table in a new level 3 table; and the new tables apart from the root, from
each other and from the tables that the set holds. -/
structure PlacedOk (placed : List Placed) : Prop where
  mono : placed.Pairwise (fun q q' => q.leaf.va.toNat ≤ q'.leaf.va.toNat)
  gib : ∀ q ∈ placed, ∀ q' ∈ placed, q.leaf.gibSlot = q'.leaf.gibSlot →
    q.new2 = q'.new2 ∧ q.t2 = q'.t2
  block : ∀ q ∈ placed, ∀ q' ∈ placed, q.leaf.blockSlot = q'.leaf.blockSlot →
    q.leaf.form = q'.leaf.form ∧ q.new3 = q'.new3 ∧ q.t3 = q'.t3
  blockOne : ∀ q ∈ placed, ∀ q' ∈ placed, q.leaf.blockSlot = q'.leaf.blockSlot →
    q.leaf.form = .block → q = q'
  new3 : ∀ q ∈ placed, q.new2 = true → q.leaf.form = .page → q.new3 = true
  t2new : ∀ q ∈ placed, ∀ q' ∈ placed, q'.new2 = true → q'.t2 ≠ 0 ∧
    (q'.t2 = q.t2 → q.leaf.gibSlot = q'.leaf.gibSlot) ∧ (q.leaf.form = .page → q'.t2 ≠ q.t3)
  t3new : ∀ q ∈ placed, ∀ q' ∈ placed, q'.leaf.form = .page → q'.new3 = true → q'.t3 ≠ 0 ∧
    q'.t3 ≠ q.t2 ∧ (q.leaf.form = .page → q'.t3 = q.t3 → q.leaf.blockSlot = q'.leaf.blockSlot)

theorem gib_of_block {a b : MapLeaf} (h : a.blockSlot = b.blockSlot) : a.gibSlot = b.gibSlot := by
  simp only [MapLeaf.blockSlot, MapLeaf.gibSlot, BLOCK_SIZE, GIB_SIZE] at h ⊢; omega

theorem index1_of_gib {a b : MapLeaf} (h : a.gibSlot = b.gibSlot) : index1 a.va = index1 b.va := by
  simp only [MapLeaf.gibSlot, index1] at h ⊢; rw [h]

theorem index2_of_block {a b : MapLeaf} (h : a.blockSlot = b.blockSlot) : index2 a.va = index2 b.va := by
  simp only [MapLeaf.blockSlot, index2] at h ⊢; rw [h]

theorem store_table {base : UInt64} {q : Placed} {t i : Nat} {d : UInt64}
    (h : .store t i d ∈ writesOf base q) : t = 0 ∨ t = q.t2 ∨ (q.leaf.form = .page ∧ t = q.t3) := by
  simp only [writesOf, Placed.store, List.mem_append] at h
  rcases h with (h | h) | h
  · split at h <;> simp_all
  · split at h <;> simp_all
  · split at h <;> simp_all

/-- A store of one leaf into a table that another leaf takes new is in the
same 1 GiB slot, and in the same 2 MiB slot for a new level 3 table. -/
theorem conflict {placed : List Placed} (hp : PlacedOk placed) {base : UInt64} {q q' : Placed}
    (hq : q ∈ placed) (hq' : q' ∈ placed) {t i : Nat} {d : UInt64}
    (hx : .store t i d ∈ writesOf base q) (hz : NewTable q' t) :
    q.leaf.gibSlot = q'.leaf.gibSlot ∧
      (q'.leaf.form = .page ∧ q'.new3 = true ∧ t = q'.t3 → q.leaf.blockSlot = q'.leaf.blockSlot) ∧
      (q'.new2 = true ∧ t = q'.t2 → q.leaf.form = .page → t ≠ q.t3) := by
  rcases store_table hx with h | h | ⟨hpg, h⟩ <;> rcases hz with ⟨h2, ht⟩ | ⟨h3p, h3, ht⟩
  · exact absurd (ht.symm.trans h) (hp.t2new q hq q' hq' h2).1
  · exact absurd (ht.symm.trans h) (hp.t3new q hq q' hq' h3p h3).1
  · obtain ⟨-, a, b⟩ := hp.t2new q hq q' hq' h2
    refine ⟨a (ht.symm.trans h), fun ⟨h3p, h3, h'⟩ => ?_, fun _ hpg h' => b hpg (ht.symm.trans h')⟩
    exact absurd (h'.symm.trans h) (hp.t3new q hq q' hq' h3p h3).2.1
  · exact absurd (ht.symm.trans h) (hp.t3new q hq q' hq' h3p h3).2.1
  · exact absurd (ht.symm.trans h) ((hp.t2new q hq q' hq' h2).2.2 hpg)
  · have := (hp.t3new q hq q' hq' h3p h3).2.2 hpg (ht.symm.trans h)
    refine ⟨gib_of_block this, fun _ => this, fun ⟨h2, ht2⟩ => ?_⟩
    exact absurd (ht2.symm.trans h) ((hp.t2new q hq q' hq' h2).2.2 hpg)


/-- The steps of the leaves of one 2 MiB slot under a new level 2 table
before the level 2 table: its new level 3 table and its pages. -/
def childSteps : List Placed → Plan
  | q :: rest => if q.leaf.form == .page then Step.zero q.t3 :: (q :: rest).map Placed.store else []
  | [] => []

theorem newLevel2Steps_eq (base : UInt64) (p : Placed) (rest : List Placed) :
    newLevel2Steps base (p :: rest) =
      (runsBy (·.leaf.blockSlot) (p :: rest)).flatMap childSteps ++
        Step.zero p.t2 :: (runsBy (·.leaf.blockSlot) (p :: rest)).flatMap (level2Entry base) ++
        [Step.fence, Step.store 0 (index1 p.leaf.va) (tableAt base p.t2)] := by
  simp only [newLevel2Steps]; congr 2; congr 1; funext slot; cases slot <;> rfl

/-- The link of the new level 3 table of a page into its level 2 table. -/
def link3 (base : UInt64) (q : Placed) : Step := .store q.t2 (index2 q.leaf.va) (tableAt base q.t3)

theorem mem_writesOf {base : UInt64} {q : Placed} {x : Step} :
    x ∈ writesOf base q ↔ (q.new2 = true ∧ x = .store 0 (index1 q.leaf.va) (tableAt base q.t2)) ∨
      (q.leaf.form = .page ∧ q.new3 = true ∧ x = link3 base q) ∨ x = q.store := by
  simp only [writesOf, List.mem_append, link3]
  constructor
  · rintro ((h | h) | h)
    · split at h <;> simp_all
    · split at h <;> simp_all
    · simp_all
  · rintro (⟨h1, rfl⟩ | ⟨h1, h2, rfl⟩ | rfl)
    · simp [h1]
    · simp [h1, h2]
    · simp

theorem gib_run {placed : List Placed} (hp : PlacedOk placed) {R : List Placed}
    (hR : R ∈ runsBy (·.leaf.gibSlot) placed) :
    ∃ p rest, R = p :: rest ∧ ∀ q ∈ R, q ∈ placed ∧ q.leaf.gibSlot = p.leaf.gibSlot ∧
      q.new2 = p.new2 ∧ q.t2 = p.t2 ∧ index1 q.leaf.va = index1 p.leaf.va := by
  obtain ⟨p, rest, rfl, hk⟩ := runsBy_key _ placed R hR
  have hmem : ∀ q ∈ p :: rest, q ∈ placed := fun q hq => (mem_runsBy _).2 ⟨_, hR, hq⟩
  refine ⟨p, rest, rfl, fun q hq => ?_⟩
  have hg := hk q hq
  obtain ⟨a, b⟩ := hp.gib q (hmem q hq) p (hmem p List.mem_cons_self) hg
  exact ⟨hmem q hq, hg, a, b, index1_of_gib hg⟩

theorem block_run {placed : List Placed} (hp : PlacedOk placed) {R S : List Placed}
    (hR : ∀ q ∈ R, q ∈ placed) (hS : S ∈ runsBy (·.leaf.blockSlot) R) :
    ∃ q0 rest, S = q0 :: rest ∧ ∀ q ∈ S, q ∈ R ∧ q.leaf.blockSlot = q0.leaf.blockSlot ∧
      q.leaf.form = q0.leaf.form ∧ q.new3 = q0.new3 ∧ q.t3 = q0.t3 ∧ q.new2 = q0.new2 ∧
      q.t2 = q0.t2 ∧ index1 q.leaf.va = index1 q0.leaf.va ∧ index2 q.leaf.va = index2 q0.leaf.va := by
  obtain ⟨q0, rest, rfl, hk⟩ := runsBy_key _ R S hS
  have hmem : ∀ q ∈ q0 :: rest, q ∈ R := fun q hq => (mem_runsBy _).2 ⟨_, hS, hq⟩
  refine ⟨q0, rest, rfl, fun q hq => ?_⟩
  have hb := hk q hq
  have hq' := hR q (hmem q hq)
  have hq0 := hR q0 (hmem q0 List.mem_cons_self)
  obtain ⟨a, b, c⟩ := hp.block q hq' q0 hq0 hb
  obtain ⟨d, e⟩ := hp.gib q hq' q0 hq0 (gib_of_block hb)
  exact ⟨hmem q hq, hb, a, b, c, d, e, index1_of_gib (gib_of_block hb), index2_of_block hb⟩

theorem mem_map_store {S : List Placed} {x : Step} :
    x ∈ S.map Placed.store ↔ ∃ q ∈ S, x = q.store := by
  simp only [List.mem_map]; exact ⟨fun ⟨q, h, e⟩ => ⟨q, h, e.symm⟩, fun ⟨q, h, e⟩ => ⟨q, h, e.symm⟩⟩

theorem mem_childSteps {q0 : Placed} {rest : List Placed} {x : Step} :
    x ∈ childSteps (q0 :: rest) ↔ q0.leaf.form = .page ∧ (x = .zero q0.t3 ∨ ∃ q ∈ q0 :: rest, x = q.store) := by
  simp only [childSteps]
  cases hf : q0.leaf.form <;> simp [mem_map_store]

theorem mem_level2Entry {base : UInt64} {q0 : Placed} {rest : List Placed} {x : Step} :
    x ∈ level2Entry base (q0 :: rest) ↔
      (q0.leaf.form = .block ∧ x = q0.store) ∨ (q0.leaf.form = .page ∧ x = link3 base q0) := by
  simp only [level2Entry, link3]
  cases hf : q0.leaf.form <;> simp

theorem mem_newLevel2Steps {base : UInt64} {p : Placed} {rest : List Placed} {x : Step} :
    x ∈ newLevel2Steps base (p :: rest) ↔
      (∃ S ∈ runsBy (·.leaf.blockSlot) (p :: rest), x ∈ childSteps S) ∨ x = .zero p.t2 ∨
      (∃ S ∈ runsBy (·.leaf.blockSlot) (p :: rest), x ∈ level2Entry base S) ∨ x = .fence ∨
      x = .store 0 (index1 p.leaf.va) (tableAt base p.t2) := by
  rw [newLevel2Steps_eq]
  simp only [List.mem_append, List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false]
  constructor
  · intro h; rcases h with (h | h | h) | h | h <;> simp_all
  · intro h; rcases h with h | h | h | h | h <;> simp_all

theorem mem_heldLevel2Steps {base : UInt64} {q0 : Placed} {rest : List Placed} {x : Step} :
    x ∈ heldLevel2Steps base (q0 :: rest) ↔ (∃ q ∈ q0 :: rest, x = q.store) ∨
      (q0.leaf.form = .page ∧ q0.new3 = true ∧ (x = .zero q0.t3 ∨ x = .fence ∨ x = link3 base q0)) := by
  simp only [heldLevel2Steps]
  cases hf : q0.leaf.form
  · cases h3 : q0.new3
    · simp [mem_map_store]
    · have hl : level2Entry base (q0 :: rest) = [link3 base q0] := by
        simp only [level2Entry, link3, hf]
      simp only [ite_true, List.mem_cons, List.mem_append, mem_map_store, hl,
        List.not_mem_nil, or_false, true_and]
      constructor
      · rintro ((h | h) | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
      · rintro (h | h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
  · simp [mem_map_store]

/-- The stores of the steps of one 1 GiB slot are those that its leaves need. -/
theorem mem_runSteps {placed : List Placed} (hp : PlacedOk placed) {base : UInt64} {R : List Placed}
    (hR : R ∈ runsBy (·.leaf.gibSlot) placed) {t i : Nat} {d : UInt64} :
    Step.store t i d ∈ runSteps base R ↔ ∃ q ∈ R, Step.store t i d ∈ writesOf base q := by
  obtain ⟨p, rest, rfl, hRf⟩ := gib_run hp hR
  have hRp : ∀ q ∈ p :: rest, q ∈ placed := fun q hq => (hRf q hq).1
  have hslot : ∀ q ∈ p :: rest, ∃ S ∈ runsBy (·.leaf.blockSlot) (p :: rest), q ∈ S :=
    fun q hq => (mem_runsBy _).1 hq
  simp only [runSteps]
  by_cases hn : p.new2 = true
  · rw [ite_of_pos hn, mem_newLevel2Steps]
    constructor
    · rintro (⟨S, hS, hx⟩ | hx | ⟨S, hS, hx⟩ | hx | hx)
      · obtain ⟨q0, rest', rfl, hSf⟩ := block_run hp hRp hS
        obtain ⟨-, hz | ⟨q, hq, hq'⟩⟩ := mem_childSteps.1 hx
        · cases hz
        · exact ⟨q, (hSf q hq).1, mem_writesOf.2 (Or.inr (Or.inr hq'))⟩
      · cases hx
      · obtain ⟨q0, rest', rfl, hSf⟩ := block_run hp hRp hS
        have hq0 := (hSf q0 List.mem_cons_self).1
        rcases mem_level2Entry.1 hx with ⟨-, hx⟩ | ⟨hpg, hx⟩
        · exact ⟨q0, hq0, mem_writesOf.2 (Or.inr (Or.inr hx))⟩
        · have h2 : q0.new2 = true := by rw [(hRf q0 hq0).2.2.1]; exact hn
          exact ⟨q0, hq0, mem_writesOf.2 (Or.inr (Or.inl ⟨hpg, hp.new3 q0 (hRp q0 hq0) h2 hpg, hx⟩))⟩
      · cases hx
      · exact ⟨p, List.mem_cons_self, mem_writesOf.2 (Or.inl ⟨hn, hx⟩)⟩
    · rintro ⟨q, hq, hx⟩
      obtain ⟨-, -, -, ht2, hi1⟩ := hRf q hq
      obtain ⟨S, hS, hqS⟩ := hslot q hq
      obtain ⟨q0, rest', rfl, hSf⟩ := block_run hp hRp hS
      obtain ⟨-, -, hf, h3, ht3, -, ht2', -, hi2⟩ := hSf q hqS
      rcases mem_writesOf.1 hx with ⟨-, hx⟩ | ⟨hpg, -, hx⟩ | hx
      · right; right; right; right; rw [hx, hi1, ht2]
      · right; right; left
        refine ⟨_, hS, mem_level2Entry.2 (Or.inr ⟨hf ▸ hpg, ?_⟩)⟩
        rw [hx]; simp only [link3, hi2, ht2', ht3]
      · cases hfq : q.leaf.form
        · left
          exact ⟨_, hS, mem_childSteps.2 ⟨hf ▸ hfq, Or.inr ⟨q, hqS, hx⟩⟩⟩
        · right; right; left
          have := hp.blockOne q (hRp q (hSf q hqS).1) q0 (hRp q0 (hSf q0 List.mem_cons_self).1)
            (hSf q hqS).2.1 hfq
          subst this
          exact ⟨_, hS, mem_level2Entry.2 (Or.inl ⟨hfq, hx⟩)⟩
  · rw [ite_of_neg hn, List.mem_flatMap]
    constructor
    · rintro ⟨S, hS, hx⟩
      obtain ⟨q0, rest', rfl, hSf⟩ := block_run hp hRp hS
      rcases mem_heldLevel2Steps.1 hx with ⟨q, hq, hx⟩ | ⟨hpg, h3, hx | hx | hx⟩
      · exact ⟨q, (hSf q hq).1, mem_writesOf.2 (Or.inr (Or.inr hx))⟩
      · cases hx
      · cases hx
      · exact ⟨q0, (hSf q0 List.mem_cons_self).1, mem_writesOf.2 (Or.inr (Or.inl ⟨hpg, h3, hx⟩))⟩
    · rintro ⟨q, hq, hx⟩
      obtain ⟨-, -, hn2, -, -⟩ := hRf q hq
      obtain ⟨S, hS, hqS⟩ := hslot q hq
      obtain ⟨q0, rest', rfl, hSf⟩ := block_run hp hRp hS
      obtain ⟨-, -, hf, h3, ht3, -, ht2', -, hi2⟩ := hSf q hqS
      refine ⟨_, hS, mem_heldLevel2Steps.2 ?_⟩
      rcases mem_writesOf.1 hx with ⟨h2, -⟩ | ⟨hpg, h3q, hx⟩ | hx
      · exact absurd (hn2 ▸ h2) hn
      · right; refine ⟨hf ▸ hpg, h3 ▸ h3q, Or.inr (Or.inr ?_)⟩
        rw [hx]; simp only [link3, hi2, ht2', ht3]
      · exact Or.inl ⟨q, hqS, hx⟩

theorem mem_mapPlan {placed : List Placed} (hp : PlacedOk placed) {base : UInt64} {t i : Nat}
    {d : UInt64} :
    Step.store t i d ∈ mapPlan base placed ↔ ∃ q ∈ placed, Step.store t i d ∈ writesOf base q := by
  rw [mapPlan_eq]
  simp only [List.mem_append, List.mem_flatMap, List.mem_singleton, reduceCtorEq, or_false]
  constructor
  · rintro ⟨R, hR, hx⟩
    obtain ⟨q, hq, hx⟩ := (mem_runSteps hp hR).1 hx
    exact ⟨q, (mem_runsBy _).2 ⟨R, hR, hq⟩, hx⟩
  · rintro ⟨q, hq, hx⟩
    obtain ⟨R, hR, hqR⟩ := (mem_runsBy (·.leaf.gibSlot)).1 hq
    exact ⟨R, hR, (mem_runSteps hp hR).2 ⟨q, hqR, hx⟩⟩

theorem pairwise_of_no_zero {l : Plan} (h : ∀ t, Step.zero t ∉ l) : l.Pairwise ZeroFirst := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x rest ih =>
    refine List.pairwise_cons.2 ⟨fun y hy t i d _ hyz => ?_, ih fun t ht => h t (List.mem_cons_of_mem _ ht)⟩
    subst hyz; exact h t (List.mem_cons_of_mem _ hy)

theorem store_ne_zero (q : Placed) (t : Nat) : q.store ≠ .zero t := by
  simp only [Placed.store]; split <;> simp

theorem zero_not_mem_map_store {S : List Placed} {t : Nat} : Step.zero t ∉ S.map Placed.store := by
  rw [mem_map_store]; rintro ⟨q, -, h⟩; exact store_ne_zero q t h.symm

theorem zero_not_mem_level2Entry {base : UInt64} {S : List Placed} {t : Nat} :
    Step.zero t ∉ level2Entry base S := by
  cases S with
  | nil => simp [level2Entry]
  | cons q0 rest =>
    rw [mem_level2Entry]; rintro (⟨-, h⟩ | ⟨-, h⟩)
    · exact store_ne_zero q0 t h.symm
    · simp [link3] at h

/-- The zeroes of the steps of one 1 GiB slot are of new tables of its leaves. -/
theorem zero_runSteps {placed : List Placed} (hp : PlacedOk placed) {base : UInt64} {R : List Placed}
    (hR : R ∈ runsBy (·.leaf.gibSlot) placed) {t : Nat} (h : Step.zero t ∈ runSteps base R) :
    ∃ q ∈ R, NewTable q t := by
  obtain ⟨p, rest, rfl, hRf⟩ := gib_run hp hR
  have hRp : ∀ q ∈ p :: rest, q ∈ placed := fun q hq => (hRf q hq).1
  simp only [runSteps] at h
  by_cases hn : p.new2 = true
  · rw [ite_of_pos hn, mem_newLevel2Steps] at h
    rcases h with ⟨S, hS, hx⟩ | hx | ⟨S, hS, hx⟩ | hx | hx
    · obtain ⟨q0, rest', rfl, hSf⟩ := block_run hp hRp hS
      obtain ⟨hpg, hz | ⟨q, -, hq⟩⟩ := mem_childSteps.1 hx
      · have hq0 := (hSf q0 List.mem_cons_self).1
        have h2 : q0.new2 = true := by rw [(hRf q0 hq0).2.2.1]; exact hn
        cases hz
        exact ⟨q0, hq0, Or.inr ⟨hpg, hp.new3 q0 (hRp q0 hq0) h2 hpg, rfl⟩⟩
      · exact absurd hq.symm (store_ne_zero q t)
    · cases hx; exact ⟨p, List.mem_cons_self, Or.inl ⟨hn, rfl⟩⟩
    · exact absurd hx zero_not_mem_level2Entry
    · cases hx
    · cases hx
  · rw [ite_of_neg hn, List.mem_flatMap] at h
    obtain ⟨S, hS, hx⟩ := h
    obtain ⟨q0, rest', rfl, hSf⟩ := block_run hp hRp hS
    rcases mem_heldLevel2Steps.1 hx with ⟨q, -, hq⟩ | ⟨hpg, h3, hz | hz | hz⟩
    · exact absurd hq.symm (store_ne_zero q t)
    · cases hz; exact ⟨q0, (hSf q0 List.mem_cons_self).1, Or.inr ⟨hpg, h3, rfl⟩⟩
    · cases hz
    · simp [link3] at hz

theorem zero_mapPlan {placed : List Placed} (hp : PlacedOk placed) {base : UInt64} {t : Nat}
    (h : Step.zero t ∈ mapPlan base placed) : ∃ q ∈ placed, NewTable q t := by
  rw [mapPlan_eq] at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_singleton, reduceCtorEq, or_false] at h
  obtain ⟨R, hR, hx⟩ := h
  obtain ⟨q, hq, hn⟩ := zero_runSteps hp hR hx
  exact ⟨q, (mem_runsBy _).2 ⟨R, hR, hq⟩, hn⟩

theorem pairwise_runsBy_lt {placed : List Placed} (hp : PlacedOk placed) :
    (runsBy (·.leaf.gibSlot) placed).Pairwise
      (fun R R' => ∀ x ∈ R, ∀ y ∈ R', x.leaf.gibSlot < y.leaf.gibSlot) := by
  apply runsBy_pairwise
  refine hp.mono.imp fun h => ?_
  simp only [MapLeaf.gibSlot]; exact Nat.div_le_div_right h

theorem pairwise_block_runs {placed : List Placed} (hp : PlacedOk placed) {R : List Placed}
    (hR : R ∈ runsBy (·.leaf.gibSlot) placed) :
    (runsBy (·.leaf.blockSlot) R).Pairwise
      (fun S S' => ∀ x ∈ S, ∀ y ∈ S', x.leaf.blockSlot < y.leaf.blockSlot) := by
  apply runsBy_pairwise
  have hsub : R.Sublist placed := by
    rw [← runsBy_flatten (·.leaf.gibSlot) placed]
    exact List.sublist_flatten_of_mem hR
  refine (hp.mono.sublist hsub).imp fun h => ?_
  simp only [MapLeaf.blockSlot]; exact Nat.div_le_div_right h

/-- The plan of a map zeroes each new table before any step stores into it. -/
theorem pairwise_mapPlan {placed : List Placed} (hp : PlacedOk placed) (base : UInt64) :
    (mapPlan base placed).Pairwise ZeroFirst := by
  rw [mapPlan_eq, List.pairwise_append, List.pairwise_flatMap]
  refine ⟨⟨fun R hR => ?_, ?_⟩, List.pairwise_singleton _ _, fun _ _ y hy => ?_⟩
  rotate_left
  · refine (pairwise_runsBy_lt hp).imp_of_mem fun {R R'} hR hR' hlt => ?_
    intro x hx y hy t i d hxs hyz
    subst hxs hyz
    obtain ⟨q, hq, hxq⟩ := (mem_runSteps hp hR).1 hx
    obtain ⟨q', hq', hn⟩ := zero_runSteps hp hR' hy
    have hqp := (mem_runsBy _).2 ⟨R, hR, hq⟩
    have hqp' := (mem_runsBy _).2 ⟨R', hR', hq'⟩
    exact absurd (conflict hp hqp hqp' hxq hn).1 (Nat.ne_of_lt (hlt q hq q' hq'))
  · intro t i d _; rw [List.mem_singleton] at hy; rw [hy]; simp
  obtain ⟨p, rest, rfl, hRf⟩ := gib_run hp hR
  have hRp : ∀ q ∈ p :: rest, q ∈ placed := fun q hq => (hRf q hq).1
  have hbl := pairwise_block_runs hp hR
  simp only [runSteps]
  by_cases hn : p.new2 = true
  · rw [ite_of_pos hn, newLevel2Steps_eq, List.pairwise_append, List.pairwise_append,
      List.pairwise_flatMap]
    refine ⟨⟨⟨fun S hS => ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
    · obtain ⟨q0, rest', rfl, -⟩ := block_run hp hRp hS
      simp only [childSteps]
      split
      · rw [List.pairwise_cons]
        refine ⟨(fun y _ t i d h => by cases h), ?_⟩
        refine List.Pairwise.imp_of_mem (R := fun _ _ => True) ?_ (List.pairwise_of_forall (fun _ _ => trivial))
        intro x y _ hy _ t i d _ hyz; subst hyz; exact zero_not_mem_map_store hy
      · exact List.Pairwise.nil
    · refine hbl.imp_of_mem fun {S S'} hS hS' hlt => ?_
      intro x hx y hy t i d hxs hyz
      subst hxs hyz
      obtain ⟨q0, rest', rfl, hSf⟩ := block_run hp hRp hS
      obtain ⟨q0', rest'', rfl, hSf'⟩ := block_run hp hRp hS'
      obtain ⟨-, hz | ⟨q, hqS, hq⟩⟩ := mem_childSteps.1 hx
      · cases hz
      obtain ⟨hpg', hz | ⟨q', -, hq'⟩⟩ := mem_childSteps.1 hy
      · cases hz
        have hq0' := hRp q0' (hSf' q0' List.mem_cons_self).1
        have h2 : q0'.new2 = true := by rw [(hRf q0' (hSf' q0' List.mem_cons_self).1).2.2.1]; exact hn
        have hqp := hRp q (hSf q hqS).1
        have := (conflict hp hqp hq0' ((mem_writesOf (base := base)).2 (Or.inr (Or.inr hq)))
          (Or.inr ⟨hpg', hp.new3 q0' hq0' h2 hpg', rfl⟩)).2.1 ⟨hpg', hp.new3 q0' hq0' h2 hpg', rfl⟩
        exact absurd this (Nat.ne_of_lt (hlt q hqS q0' List.mem_cons_self))
      · exact absurd hq'.symm (store_ne_zero q' _)
    · refine List.pairwise_cons.2 ⟨(fun y _ t i d h => by cases h), pairwise_of_no_zero ?_⟩
      intro t ht
      obtain ⟨S, -, hS⟩ := List.mem_flatMap.1 ht
      exact zero_not_mem_level2Entry hS
    · intro x hx y hy t i d hxs hyz
      subst hxs hyz
      obtain ⟨S, hS, hx⟩ := List.mem_flatMap.1 hx
      obtain ⟨q0, rest', rfl, hSf⟩ := block_run hp hRp hS
      obtain ⟨hpg, hz | ⟨q, hqS, hq⟩⟩ := mem_childSteps.1 hx
      · cases hz
      rcases List.mem_cons.1 hy with hy | hy
      · injection hy with hy
        have hqp := hRp q (hSf q hqS).1
        have hpq : q.leaf.form = .page := (hSf q hqS).2.2.1.trans hpg
        have : q.store = .store q.t3 (index3 q.leaf.va) q.leaf.desc := by
          simp only [Placed.store, hpq]
        rw [this] at hq; injection hq with hq
        exact (hp.t2new q hqp p (hRp p List.mem_cons_self) hn).2.2 hpq (hy.symm.trans hq)
      · obtain ⟨S', -, hS'⟩ := List.mem_flatMap.1 hy
        exact zero_not_mem_level2Entry hS'
    · exact pairwise_of_no_zero (by simp)
    · intro x _ y hy t i d _ hyz; subst hyz; simp at hy
  · rw [ite_of_neg hn, List.pairwise_flatMap]
    refine ⟨fun S hS => ?_, ?_⟩
    · obtain ⟨q0, rest', rfl, -⟩ := block_run hp hRp hS
      simp only [heldLevel2Steps]
      split
      · exact pairwise_of_no_zero fun t => zero_not_mem_map_store
      · split
        · refine List.pairwise_cons.2 ⟨(fun y _ t i d h => by cases h), pairwise_of_no_zero ?_⟩
          intro t ht
          rcases List.mem_append.1 ht with ht | ht
          · exact zero_not_mem_map_store ht
          · rcases List.mem_cons.1 ht with ht | ht
            · cases ht
            · exact zero_not_mem_level2Entry ht
        · exact pairwise_of_no_zero fun t => zero_not_mem_map_store
    · refine hbl.imp_of_mem fun {S S'} hS hS' hlt => ?_
      intro x hx y hy t i d hxs hyz
      subst hxs hyz
      obtain ⟨q0, rest', rfl, hSf⟩ := block_run hp hRp hS
      obtain ⟨q0', rest'', rfl, hSf'⟩ := block_run hp hRp hS'
      have hq0 := hRp q0 (hSf q0 List.mem_cons_self).1
      have hq0' := hRp q0' (hSf' q0' List.mem_cons_self).1
      obtain ⟨q, hqS, hw⟩ : ∃ q ∈ q0 :: rest', Step.store t i d ∈ writesOf base q := by
        rcases mem_heldLevel2Steps.1 hx with ⟨q, hqS, hq⟩ | ⟨hpg, h3, hz | hz | hz⟩
        · exact ⟨q, hqS, mem_writesOf.2 (Or.inr (Or.inr hq))⟩
        · cases hz
        · cases hz
        · exact ⟨q0, List.mem_cons_self, mem_writesOf.2 (Or.inr (Or.inl ⟨hpg, h3, hz⟩))⟩
      rcases mem_heldLevel2Steps.1 hy with ⟨q', -, hq'⟩ | ⟨hpg', h3', hz | hz | hz⟩
      · exact absurd hq'.symm (store_ne_zero q' _)
      · cases hz
        have hqp := hRp q (hSf q hqS).1
        have := (conflict hp hqp hq0' hw (Or.inr ⟨hpg', h3', rfl⟩)).2.1 ⟨hpg', h3', rfl⟩
        exact absurd this (Nat.ne_of_lt (hlt q hqS q0' List.mem_cons_self))
      · cases hz
      · simp [link3] at hz

end Krepi.Proofs.PageTables
