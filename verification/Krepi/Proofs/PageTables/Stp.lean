module

public import Krepi.SpecTests.PageTables.Stp
import Mathlib.Util.CountHeartbeats
import Mathlib.Tactic.SplitIfs
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.Fdt.StpLemmas
import Krepi.Proofs.PageTables.BitLemmas
import Krepi.Proofs.PageTables.CountLemmas
import Krepi.Proofs.PageTables.EntryLemmas
import Krepi.Proofs.PageTables.LeavesLemmas
import Krepi.Proofs.PageTables.PoolLemmas
import Krepi.Proofs.PageTables.WalkLemmas

/-!
# Page tables: proofs of the specification tests

One theorem for each specification test of `Krepi.SpecTests.PageTables`,
whose type is exactly that test: for each requirement of the component,
PGT-R01 to PGT-R12, the input that the specification accepts with its result
and the input that it rejects with its error.

The tests of PGT-R01 to PGT-R07 and PGT-R12 are proved, and
`verification/statements.json` registers each as `proved`. The tests on
small inputs are decided by the kernel on their concrete inputs once their
proposition is unfolded, with the equality of `Except` values of
`Krepi.Proofs.Fdt.decEqExcept` as a local instance. The two tests whose
results are tuples of six and ten values, `unmapAndResetFollowContract` and
`copyIsPrivateAndOrdered`, raise `synthInstance.maxSize` so that the instance
of their equality is found. The tests of PGT-R03 and the accepting test of
PGT-R05, whose inputs are too large to evaluate, are proved from closed
forms: the set after the first `n` of the 4,096 blocks, by induction on `n`,
and the counts of the direct maps of the Pi 5 models from the runs of their
leaves (`Krepi.Proofs.PageTables.CountLemmas`). The other theorems are
planned: their proof is `sorry` until a proof pull request proves them, and
`verification/statements.json` registers each as `planned`. They are the
tests of PGT-R08 to PGT-R11. Mathlib is imported so that the gate counts the
heartbeats of each theorem.
-/

namespace Krepi.Proofs.PageTables.Stp

open Krepi.Spec Krepi.Spec.PageTables Krepi.SpecTests.PageTables Krepi.Proofs.PageTables
open Krepi.Proofs.Fdt (except_ok_bind)

attribute [local instance] Krepi.Proofs.Fdt.decEqExcept

variable {r : Region} {N : Nat}

/-! ## PGT-R01 -/

public theorem descriptorsFollowKindRows : DescriptorsFollowKindRows := by
  unfold DescriptorsFollowKindRows; decide +kernel

public theorem descriptorKeepsOnlyItsBits : DescriptorKeepsOnlyItsBits := by
  unfold DescriptorKeepsOnlyItsBits; decide +kernel

/-! ## PGT-R02 -/

public theorem mapPageThenLookup : MapPageThenLookup := by
  unfold MapPageThenLookup; decide +kernel

public theorem mapPageRefusesMappedPage : MapPageRefusesMappedPage := by
  unfold MapPageRefusesMappedPage; decide +kernel

/-! ## PGT-R03 -/

/-! The set after the first `n` blocks of `blocksFromZero`: the root holds
the table descriptors of the tables 1 to $\lceil n / 512 \rceil$, and entry
`i` of table `t` the block descriptor of block $512 (t - 1) + i$ when that is
below `n`. -/

private theorem block_va {n : Nat} (hn : n ≤ 4096) :
    (DIRECT_BASE ||| UInt64.ofNat (n * BLOCK_SIZE)).toNat = DIRECT_BASE.toNat + n * BLOCK_SIZE ∧
      Region.holds .upper (DIRECT_BASE ||| UInt64.ofNat (n * BLOCK_SIZE)) = true ∧
      index1 (DIRECT_BASE ||| UInt64.ofNat (n * BLOCK_SIZE)) = n / 512 ∧
      index2 (DIRECT_BASE ||| UInt64.ofNat (n * BLOCK_SIZE)) = n % 512 := by
  have hx : (UInt64.ofNat (n * BLOCK_SIZE)).toNat = n * BLOCK_SIZE := by
    rw [UInt64.toNat_ofNat']; apply Nat.mod_eq_of_lt; simp only [BLOCK_SIZE]; omega
  have h := direct_or (a := UInt64.ofNat (n * BLOCK_SIZE))
    (by rw [hx]; simp only [VA_LIMIT, BLOCK_SIZE]; omega)
  rw [hx] at h
  refine ⟨h, ?_⟩
  simp only [Region.holds, index1, index2, decide_eq_true_eq]
  rw [h, direct_base_toNat]
  simp only [GIB_SIZE, BLOCK_SIZE, ENTRIES]
  omega

private theorem block_checks {n : Nat} (hn : n ≤ 4096) :
    checkEntry .upper 9 (DIRECT_BASE ||| UInt64.ofNat (n * BLOCK_SIZE)) BLOCK_SIZE BASE BITS =
        .ok () ∧
      checkPhysical (UInt64.ofNat (n * BLOCK_SIZE)) BLOCK_SIZE BITS = .ok () := by
  obtain ⟨h1, h2, -, -⟩ := block_va hn
  have hp : (UInt64.ofNat (n * BLOCK_SIZE)).toNat = n * BLOCK_SIZE := by
    rw [UInt64.toNat_ofNat']; apply Nat.mod_eq_of_lt; simp only [BLOCK_SIZE]; omega
  refine ⟨checkEntry_ok.2 ⟨?_, by decide, h2, by decide, by decide⟩, checkPhysical_ok.2 ⟨?_, ?_⟩⟩
  · rw [h1, direct_base_toNat]; simp only [BLOCK_SIZE]; omega
  · rw [hp]; simp only [BLOCK_SIZE]; omega
  · rw [hp]; simp only [BITS, BLOCK_SIZE]
    show n * 2097152 < 2 ^ 40
    omega

private theorem mapBlock_root {s : Tables r N} {v p base : UInt64} {bits : UInt8}
    (hc : checkEntry r N v BLOCK_SIZE base bits = .ok ())
    (hp : checkPhysical p BLOCK_SIZE bits = .ok ()) (hw : s.walk2 base v = .ok none)
    (hn : s.used < N) :
    s.mapBlock v p base bits = .ok ({ s with used := s.used + 1 },
      [.zero s.used, .store s.used (index2 v) (blockDescriptor p),
        .fence, .store 0 (index1 v) (tableDescriptor (tableAddress base s.used)), .sync]) := by
  unfold Tables.mapBlock
  rw [hc, hp, hw]
  simp only [bind, Except.bind, show ¬ (N - s.used < 1) by omega, ite_false]
  rfl

private theorem mapBlock_level2 {s : Tables r N} {v p base : UInt64} {bits : UInt8} {t2 : Nat}
    {e2 : UInt64} (hc : checkEntry r N v BLOCK_SIZE base bits = .ok ())
    (hp : checkPhysical p BLOCK_SIZE bits = .ok ()) (hw : s.walk2 base v = .ok (some (t2, e2)))
    (he : isValid e2 = false) :
    s.mapBlock v p base bits = .ok (s, [.store t2 (index2 v) (blockDescriptor p), .sync]) := by
  unfold Tables.mapBlock
  rw [hc, hp, hw]
  simp only [bind, Except.bind, he, Bool.false_and]
  rfl

private def rootE (n i : Nat) : UInt64 := if i < (n + 511) / 512 then tableAt BASE (i + 1) else 0

private def blkE (n t i : Nat) : UInt64 :=
  if 0 < t ∧ i < 512 ∧ (t - 1) * 512 + i < n then
    blockDescriptor (UInt64.ofNat (((t - 1) * 512 + i) * BLOCK_SIZE))
  else 0

private def E (n t i : Nat) : UInt64 := if t = 0 then rootE n i else blkE n t i

private structure Inv (n : Nat) (s : Tables .upper 9) : Prop where
  used : s.used = 1 + (n + 511) / 512
  entry : ∀ t i, s.entry t i = E n t i

private theorem poolOk9 : PoolOk 9 BASE BITS := ⟨by decide, by decide, by decide⟩

private theorem inv_zero : Inv 0 (newSet .upper 9) := by
  refine ⟨rfl, fun t i => ?_⟩
  rw [entry_eq_get]
  simp only [newSet, Tables.new, E, rootE, blkE]
  by_cases ht : t < 9
  · by_cases hi : i < ENTRIES
    · simp [Pool.get, Pool.zero, ht, hi, Table.zero]
    · simp [Pool.get, ht, hi]
  · simp [Pool.get, ht]

private theorem E_out {n t i : Nat} (hn : n ≤ 4096) (h : 9 ≤ t ∨ ENTRIES ≤ i) : E n t i = 0 := by
  simp only [ENTRIES] at h
  unfold E rootE blkE
  split_ifs <;> first | rfl | omega

private theorem E_succ {n t i : Nat} :
    E (n + 1) t i =
      if t = n / 512 + 1 ∧ i = n % 512 then blockDescriptor (UInt64.ofNat (n * BLOCK_SIZE))
      else if t = 0 ∧ i = n / 512 then tableAt BASE (n / 512 + 1) else E n t i := by
  unfold E rootE blkE
  split_ifs <;> first | omega | (rw [show i + 1 = n / 512 + 1 by omega]) |
    (rw [show (t - 1) * 512 + i = n by omega]) | rfl

private theorem E_succ2 {n t i : Nat} (hm : n % 512 ≠ 0) :
    E (n + 1) t i =
      if t = n / 512 + 1 ∧ i = n % 512 then blockDescriptor (UInt64.ofNat (n * BLOCK_SIZE))
      else E n t i := by
  unfold E rootE blkE
  split_ifs <;> first | omega | (rw [show (t - 1) * 512 + i = n by omega]) | rfl

private theorem entry_apply {s : Tables r N} {plan : Plan} {t i : Nat} (ht : t < N)
    (hi : i < ENTRIES) : (s.apply plan).entry t i = (lastAt t i plan).getD (s.entry t i) := by
  rw [entry_eq_get, entry_eq_get]
  exact get_exec plan s.pool ht hi

/-- One more block: block `n` takes a new level 2 table when `n` is a multiple
of 512 and goes into the last one otherwise. -/
private theorem inv_step {n : Nat} {s : Tables .upper 9} (hn : n < 4096) (h : Inv n s) :
    ∃ s', withBlock s (DIRECT_BASE ||| UInt64.ofNat (n * BLOCK_SIZE))
      (UInt64.ofNat (n * BLOCK_SIZE)) = .ok s' ∧ Inv (n + 1) s' := by
  obtain ⟨-, -, hi1, hi2⟩ := block_va (Nat.le_of_lt hn)
  obtain ⟨hc, hp⟩ := block_checks (Nat.le_of_lt hn)
  have hout : ∀ (s' : Tables .upper 9) t i, (9 ≤ t ∨ ENTRIES ≤ i) →
      s'.entry t i = E (n + 1) t i := by
    intro s' t i hti
    rw [E_out (by omega) hti, entry_eq_get]
    rcases hti with hti | hti
    · exact get_of_ge _ _ hti
    · exact get_of_ge_entries _ _ hti
  by_cases hm : n % 512 = 0
  · have he1 : s.entry 0 (index1 (DIRECT_BASE ||| UInt64.ofNat (n * BLOCK_SIZE))) = 0 := by
      rw [h.entry, hi1]; unfold E rootE
      split_ifs <;> first | rfl | omega
    have hw : s.walk2 BASE (DIRECT_BASE ||| UInt64.ofNat (n * BLOCK_SIZE)) = .ok none :=
      walk2_ok.2 (Or.inl ⟨by rw [he1]; rfl, rfl⟩)
    have hu : s.used < 9 := by rw [h.used]; omega
    refine ⟨_, by unfold withBlock; rw [mapBlock_root hc hp hw hu]; rfl, ⟨?_, fun t i => ?_⟩⟩
    · show s.used + 1 = _; rw [h.used]; omega
    · by_cases hti : t < 9 ∧ i < ENTRIES
      · rw [entry_apply hti.1 hti.2, E_succ, hi1, hi2]
        have hU : s.used = n / 512 + 1 := by rw [h.used]; omega
        simp only [lastAt, stepAt, hU]
        rw [show ({ pool := s.pool, used := n / 512 + 1 + 1 } : Tables .upper 9).entry t i =
          s.entry t i from rfl, h.entry]
        split_ifs <;> simp only [Option.or, Option.getD] <;>
          first | omega | rfl | (unfold E blkE; split_ifs <;> first | omega | rfl)
      · exact hout _ t i (by omega)
  · have hU : s.used = n / 512 + 2 := by rw [h.used]; omega
    have he1 : s.entry 0 (index1 (DIRECT_BASE ||| UInt64.ofNat (n * BLOCK_SIZE))) =
        tableAt BASE (n / 512 + 1) := by
      rw [h.entry, hi1]; unfold E rootE
      split_ifs <;> first | omega | rfl
    have hch : s.child? BASE (tableAt BASE (n / 512 + 1)) = some (n / 512 + 1) :=
      child?_tableAt poolOk9 (by omega) (by omega)
    have he2 :
        s.entry (n / 512 + 1) (index2 (DIRECT_BASE ||| UInt64.ofNat (n * BLOCK_SIZE))) = 0 := by
      rw [h.entry, hi2]; unfold E blkE
      split_ifs <;> first | contradiction | omega | rfl
    have hw : s.walk2 BASE (DIRECT_BASE ||| UInt64.ofNat (n * BLOCK_SIZE)) =
        .ok (some (n / 512 + 1, 0)) :=
      walk2_ok.2 (Or.inr ⟨_, by rw [he1]; exact isValid_tableDescriptor _, by rw [he1, hch],
        by rw [he2]⟩)
    refine ⟨_, by unfold withBlock; rw [mapBlock_level2 hc hp hw isValid_zero]; rfl,
      ⟨by show s.used = _; rw [hU]; omega, fun t i => ?_⟩⟩
    by_cases hti : t < 9 ∧ i < ENTRIES
    · rw [entry_apply hti.1 hti.2, E_succ2 hm, hi2, h.entry]
      simp only [lastAt, stepAt]
      split_ifs <;> simp only [Option.or, Option.getD] <;> omega
    · exact hout _ t i (by omega)

private theorem blocks_succ (n : Nat) : blocksFromZero (n + 1) = (blocksFromZero n).bind fun s =>
    withBlock s (DIRECT_BASE ||| UInt64.ofNat (n * BLOCK_SIZE)) (UInt64.ofNat (n * BLOCK_SIZE)) := by
  unfold blocksFromZero
  rw [List.range_succ, List.foldlM_append]
  simp only [List.foldlM_cons, List.foldlM_nil, bind_pure]
  rfl

private theorem blocks_inv : ∀ n, n ≤ 4096 → ∃ s, blocksFromZero n = .ok s ∧ Inv n s
  | 0, _ => ⟨newSet .upper 9, rfl, inv_zero⟩
  | n + 1, hn => by
    obtain ⟨s, hs, hi⟩ := blocks_inv n (by omega)
    obtain ⟨s', h1, h2⟩ := inv_step (by omega) hi
    refine ⟨s', ?_, h2⟩
    rw [blocks_succ, hs, ok_bind_eq]
    exact h1

private theorem walk2_full {s : Tables .upper 9} (hi : Inv 4096 s) {b : Nat} (hb : b < 4096) :
    s.walk2 BASE (DIRECT_BASE ||| UInt64.ofNat (b * BLOCK_SIZE)) =
      .ok (some (b / 512 + 1, blockDescriptor (UInt64.ofNat (b * BLOCK_SIZE)))) := by
  obtain ⟨-, -, hi1, hi2⟩ := block_va (Nat.le_of_lt hb)
  have he1 : s.entry 0 (index1 (DIRECT_BASE ||| UInt64.ofNat (b * BLOCK_SIZE))) =
      tableAt BASE (b / 512 + 1) := by
    rw [hi.entry, hi1]; unfold E rootE
    split_ifs <;> first | omega | rfl
  have hch : s.child? BASE (tableAt BASE (b / 512 + 1)) = some (b / 512 + 1) :=
    child?_tableAt poolOk9 (by rw [hi.used]; omega) (by omega)
  have he2 : s.entry (b / 512 + 1) (index2 (DIRECT_BASE ||| UInt64.ofNat (b * BLOCK_SIZE))) =
      blockDescriptor (UInt64.ofNat (b * BLOCK_SIZE)) := by
    rw [hi.entry, hi2]; unfold E blkE
    split_ifs <;> first | contradiction | omega |
      (rw [show (b / 512 + 1 - 1) * 512 + b % 512 = b by omega])
  exact walk2_ok.2 (Or.inr ⟨_, by rw [he1]; exact isValid_tableDescriptor _, by rw [he1, hch],
    by rw [he2]⟩)

private theorem lookup_at {s : Tables .upper 9} (hi : Inv 4096 s) (pa : UInt64) {b : Nat}
    (hb : b < 4096) (hpa : pa = UInt64.ofNat (b * BLOCK_SIZE)) :
    s.lookupBlock (DIRECT_BASE ||| pa) BASE BITS = .ok (blockDescriptor pa) := by
  subst hpa
  unfold Tables.lookupBlock
  rw [(block_checks (Nat.le_of_lt hb)).1, walk2_full hi hb, except_ok_bind, except_ok_bind]
  dsimp only
  rw [typeBits_blockDescriptor]
  rfl

private theorem beyond_full {s : Tables .upper 9} (hi : Inv 4096 s) :
    s.mapBlock (DIRECT_BASE ||| 0x2_0000_0000) 0x2_0000_0000 BASE BITS = .error .outOfTables := by
  obtain ⟨-, -, hi1, -⟩ := block_va (n := 4096) (Nat.le_refl _)
  obtain ⟨hc, hp⟩ := block_checks (n := 4096) (Nat.le_refl _)
  have he1 : s.entry 0 (index1 (DIRECT_BASE ||| UInt64.ofNat (4096 * BLOCK_SIZE))) = 0 := by
    rw [hi.entry, hi1]; unfold E rootE; split_ifs <;> first | omega | rfl
  have hw : s.walk2 BASE (DIRECT_BASE ||| UInt64.ofNat (4096 * BLOCK_SIZE)) = .ok none :=
    walk2_ok.2 (Or.inl ⟨by rw [he1]; rfl, rfl⟩)
  rw [show (0x2_0000_0000 : UInt64) = UInt64.ofNat (4096 * BLOCK_SIZE) from rfl]
  unfold Tables.mapBlock
  rw [hc, hp, except_ok_bind, except_ok_bind]
  dsimp only
  rw [hw, except_ok_bind]
  dsimp only
  rw [hi.used, ite_of_pos (by decide)]
  rfl

public theorem eightGibOfBlocksInNineTables : EightGibOfBlocksInNineTables := by
  obtain ⟨s, hs, hi⟩ := blocks_inv 4096 (Nat.le_refl _)
  unfold EightGibOfBlocksInNineTables
  rw [hs, ok_bind_eq]
  simp only [pt17Lookups, List.mapM_cons, List.mapM_nil]
  rw [lookup_at hi 0x0 (b := 0) (by decide) rfl,
    lookup_at hi 0x3fe0_0000 (b := 511) (by decide) rfl,
    lookup_at hi 0x4000_0000 (b := 512) (by decide) rfl,
    lookup_at hi 0x1_0000_0000 (b := 2048) (by decide) rfl,
    lookup_at hi 0x1_ffe0_0000 (b := 4095) (by decide) rfl]
  simp only [except_ok_bind]
  show Except.ok (s.used, _) = _
  rw [hi.used]
  decide

public theorem blockBeyondNineTablesRefused : BlockBeyondNineTablesRefused := by
  obtain ⟨s, hs, hi⟩ := blocks_inv 4096 (Nat.le_refl _)
  unfold BlockBeyondNineTablesRefused
  rw [hs, ok_map_eq, beyond_full hi]

/-! ## PGT-R04 -/

set_option synthInstance.maxSize 4096 in
public theorem unmapAndResetFollowContract : UnmapAndResetFollowContract := by
  unfold UnmapAndResetFollowContract; decide +kernel

public theorem unmapRefusesUnmappedPage : UnmapRefusesUnmappedPage := by
  unfold UnmapRefusesUnmappedPage; decide +kernel

/-! ## PGT-R05 -/

/-! The direct maps of the Pi 5 models, counted from the closed forms of
`Krepi.Proofs.PageTables.CountLemmas`: the usable ranges of each model are
two ranges below 1 GiB, whose leaves are 89 pages, then 492 pages and 508
blocks, and one or two ranges of blocks above it. -/

private theorem pool80 : PoolOk DIRECT_MAP_TABLES DM_BASE BITS := ⟨by decide, by decide, by decide⟩

private theorem zero80 : ∀ t i, (newSet .upper DIRECT_MAP_TABLES).pool.get t i = 0 := by
  intro t i
  simp only [newSet, Tables.new, Pool.get]
  by_cases ht : t < DIRECT_MAP_TABLES
  · by_cases hi : i < ENTRIES
    · simp [Pool.zero, ht, hi, Table.zero]
    · simp [ht, hi]
  · simp [ht]

private theorem pi5_of {ram : List Fdt.Span} {t b p : Nat}
    {G : Fdt.MemoryPlan → Except TableError (Nat × Nat × Nat)}
    (hG : ∀ M s₁ plan, (newSet .upper DIRECT_MAP_TABLES).directMap M DM_BASE BITS = .ok (s₁, plan) →
      G M = .ok (s₁.used, plan.counts.blocks, plan.counts.pages))
    {us : List Fdt.Span}
    (hM : (pi5Memory ram).map (fun M => sortByKey (·.start.toNat) M.availableRanges) = .ok us)
    (hok : ∀ u ∈ us, UsableOk BITS u) (hpw : us.Pairwise (fun a b => a.endNat ≤ b.start.toNat))
    (hN : t ≤ DIRECT_MAP_TABLES)
    (hres : (((us.flatMap usableLeaves).foldl tick (1, none, none)).1,
        (us.flatMap usableLeaves).countP (·.form == .block),
        (us.flatMap usableLeaves).countP (·.form == .page)) = (t, b, p)) :
    (pi5Memory ram).toOption.map G = some (.ok (t, b, p)) := by
  cases h : pi5Memory ram with
  | error e => rw [h] at hM; cases hM
  | ok M =>
    rw [h, ok_map_eq] at hM
    obtain ⟨s₁, plan, hd, h1, h2, h3⟩ := directMap_counts pool80 zero80 rfl (Except.ok.inj hM)
      hok hpw (by rw [congrArg (·.1) hres]; exact hN)
    show some (G M) = _
    rw [hG M s₁ plan hd, h1, h2, h3, hres]

private def uA : Fdt.Span := ⟨0x1a_7000, 0x5_9000⟩
private def uB : Fdt.Span := ⟨0x21_4000, 0x3f9e_c000⟩
private def u2 : Fdt.Span := ⟨0x4000_0000, 0x4000_0000⟩
private def u4 : Fdt.Span := ⟨0x4000_0000, 0xc000_0000⟩
private def u8 : Fdt.Span := ⟨0x1_0000_0000, 0x1_0000_0000⟩
private def u16 : Fdt.Span := ⟨0x1_0000_0000, 0x3_0000_0000⟩

private theorem leavesA : usableLeaves uA = pageRun 0x1a_7000 89 := by
  have := usableLeaves_eq (u := uA) 0x1a_7000 0x20_0000 89 0 0 rfl rfl
    (fun j hj => by simp only [PAGE_SIZE, BLOCK_SIZE]; omega) (by decide) (fun j hj => by omega)
    (by decide) (by decide)
  rw [this, blockRun_zero, pageRun_zero, List.append_nil, List.append_nil]

private theorem leavesB : usableLeaves uB = pageRun 0x21_4000 492 ++ blockRun 0x40_0000 508 := by
  have := usableLeaves_eq (u := uB) 0x21_4000 0x3fc0_0000 492 508 0 rfl rfl
    (fun j hj => by simp only [PAGE_SIZE, BLOCK_SIZE]; omega) (by decide) (fun j hj => by omega)
    (by decide) (by decide)
  rw [this, pageRun_zero, List.append_nil]
  rfl

private theorem leavesBlocks {u : Fdt.Span} (a k : Nat) (hs : u.start.toNat = a)
    (he : u.endNat = a + k * BLOCK_SIZE) (ha : a % BLOCK_SIZE = 0) :
    usableLeaves u = blockRun a k := by
  have := usableLeaves_eq a (a + k * BLOCK_SIZE) 0 k 0 hs he (fun j hj => by omega)
    (by rw [Nat.zero_mul, Nat.add_zero]; exact ha) (fun j hj => by omega) (by omega)
    (by simp only [directFuel, BLOCK_SIZE, ENTRIES]; omega)
  rw [this, pageRun_zero, pageRun_zero, List.append_nil, List.nil_append, Nat.zero_mul,
    Nat.add_zero]

private theorem leaves2 : usableLeaves u2 = blockRun 0x4000_0000 512 :=
  leavesBlocks _ _ rfl rfl (by decide)
private theorem leaves4 : usableLeaves u4 = blockRun 0x4000_0000 1536 :=
  leavesBlocks _ _ rfl rfl (by decide)
private theorem leaves8 : usableLeaves u8 = blockRun 0x1_0000_0000 2048 :=
  leavesBlocks _ _ rfl rfl (by decide)
private theorem leaves16 : usableLeaves u16 = blockRun 0x1_0000_0000 6144 :=
  leavesBlocks _ _ rfl rfl (by decide)

private theorem model1 : ((([uA, uB].flatMap usableLeaves).foldl tick (1, none, none)).1,
    ([uA, uB].flatMap usableLeaves).countP (·.form == .block),
    ([uA, uB].flatMap usableLeaves).countP (·.form == .page)) = (4, 508, 581) := by
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.countP_append, leavesA, leavesB,
    pageRun_blocks, pageRun_pages, blockRun_blocks, blockRun_pages, List.foldl_append]
  rw [tick_pageRun 88 0x1a_7000 1 none none (by decide) (by decide),
    tick_pageRun 491 0x21_4000 _ _ _ (by decide) (by decide),
    tick_blockRun 507 0x40_0000 _ _ _ (by decide)]
  decide

private theorem model2 : ((([uA, uB, u2].flatMap usableLeaves).foldl tick (1, none, none)).1,
    ([uA, uB, u2].flatMap usableLeaves).countP (·.form == .block),
    ([uA, uB, u2].flatMap usableLeaves).countP (·.form == .page)) = (5, 1020, 581) := by
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.countP_append, leavesA, leavesB, leaves2,
    pageRun_blocks, pageRun_pages, blockRun_blocks, blockRun_pages, List.foldl_append]
  rw [tick_pageRun 88 0x1a_7000 1 none none (by decide) (by decide),
    tick_pageRun 491 0x21_4000 _ _ _ (by decide) (by decide),
    tick_blockRun 507 0x40_0000 _ _ _ (by decide),
    tick_blockRun 511 0x4000_0000 _ _ _ (by decide)]
  decide

private theorem model4 : ((([uA, uB, u4].flatMap usableLeaves).foldl tick (1, none, none)).1,
    ([uA, uB, u4].flatMap usableLeaves).countP (·.form == .block),
    ([uA, uB, u4].flatMap usableLeaves).countP (·.form == .page)) = (7, 2044, 581) := by
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.countP_append, leavesA, leavesB, leaves4,
    pageRun_blocks, pageRun_pages, blockRun_blocks, blockRun_pages, List.foldl_append]
  rw [tick_pageRun 88 0x1a_7000 1 none none (by decide) (by decide),
    tick_pageRun 491 0x21_4000 _ _ _ (by decide) (by decide),
    tick_blockRun 507 0x40_0000 _ _ _ (by decide),
    tick_blockRun 1535 0x4000_0000 _ _ _ (by decide)]
  decide

private theorem model8 : ((([uA, uB, u4, u8].flatMap usableLeaves).foldl tick (1, none, none)).1,
    ([uA, uB, u4, u8].flatMap usableLeaves).countP (·.form == .block),
    ([uA, uB, u4, u8].flatMap usableLeaves).countP (·.form == .page)) = (11, 4092, 581) := by
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.countP_append, leavesA, leavesB, leaves4, leaves8,
    pageRun_blocks, pageRun_pages, blockRun_blocks, blockRun_pages, List.foldl_append]
  rw [tick_pageRun 88 0x1a_7000 1 none none (by decide) (by decide),
    tick_pageRun 491 0x21_4000 _ _ _ (by decide) (by decide),
    tick_blockRun 507 0x40_0000 _ _ _ (by decide),
    tick_blockRun 1535 0x4000_0000 _ _ _ (by decide),
    tick_blockRun 2047 0x1_0000_0000 _ _ _ (by decide)]
  decide

private theorem model16 : ((([uA, uB, u4, u16].flatMap usableLeaves).foldl tick (1, none, none)).1,
    ([uA, uB, u4, u16].flatMap usableLeaves).countP (·.form == .block),
    ([uA, uB, u4, u16].flatMap usableLeaves).countP (·.form == .page)) = (19, 8188, 581) := by
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.countP_append, leavesA, leavesB, leaves4, leaves16,
    pageRun_blocks, pageRun_pages, blockRun_blocks, blockRun_pages, List.foldl_append]
  rw [tick_pageRun 88 0x1a_7000 1 none none (by decide) (by decide),
    tick_pageRun 491 0x21_4000 _ _ _ (by decide) (by decide),
    tick_blockRun 507 0x40_0000 _ _ _ (by decide),
    tick_blockRun 1535 0x4000_0000 _ _ _ (by decide),
    tick_blockRun 6143 0x1_0000_0000 _ _ _ (by decide)]
  decide

public theorem directMapCountsOfPi5Models : DirectMapCountsOfPi5Models := by
  unfold DirectMapCountsOfPi5Models
  intro m hm
  have hG : ∀ (G : Fdt.MemoryPlan → Except TableError (Nat × Nat × Nat)), G = (fun memory =>
      ((newSet .upper DIRECT_MAP_TABLES).directMap memory DM_BASE BITS).map
        (fun (s, plan) => (s.usedTables, plan.counts.blocks, plan.counts.pages))) →
      ∀ M s₁ plan, (newSet .upper DIRECT_MAP_TABLES).directMap M DM_BASE BITS = .ok (s₁, plan) →
        G M = .ok (s₁.used, plan.counts.blocks, plan.counts.pages) := by
    intro G hG M s₁ plan hd
    rw [hG]; dsimp only; rw [hd]; rfl
  simp only [pi5Models, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  · exact pi5_of (hG _ rfl) (us := [uA, uB]) (by decide) (by unfold UsableOk; decide) (by decide)
      (by decide) model1
  · exact pi5_of (hG _ rfl) (us := [uA, uB, u2]) (by decide) (by unfold UsableOk; decide)
      (by decide) (by decide) model2
  · exact pi5_of (hG _ rfl) (us := [uA, uB, u4]) (by decide) (by unfold UsableOk; decide)
      (by decide) (by decide) model4
  · exact pi5_of (hG _ rfl) (us := [uA, uB, u4, u8]) (by decide) (by unfold UsableOk; decide)
      (by decide) (by decide) model8
  · exact pi5_of (hG _ rfl) (us := [uA, uB, u4, u16]) (by decide) (by unfold UsableOk; decide)
      (by decide) (by decide) model16

public theorem directMapOmitsExcludedPages : DirectMapOmitsExcludedPages := by
  unfold DirectMapOmitsExcludedPages; decide +kernel

/-! ## PGT-R06 -/

public theorem kernelMapGivesKindsAndGuard : KernelMapGivesKindsAndGuard := by
  unfold KernelMapGivesKindsAndGuard; decide +kernel

public theorem kernelMapRefusesSharedPage : KernelMapRefusesSharedPage := by
  unfold KernelMapRefusesSharedPage; decide +kernel

/-! ## PGT-R07 -/

public theorem plansFollowContractOrder : PlansFollowContractOrder := by
  unfold PlansFollowContractOrder; decide +kernel

public theorem kernelFillRefusesValidEntry : KernelFillRefusesValidEntry := by
  unfold KernelFillRefusesValidEntry; decide +kernel

/-! ## PGT-R08 -/

public theorem ownershipOfBoardShapes : OwnershipOfBoardShapes := by
  sorry

public theorem ownershipRefusesOverlappingBanks : OwnershipRefusesOverlappingBanks := by
  sorry

/-! ## PGT-R09 -/

public theorem allocationTakesWindowAndGeneration : AllocationTakesWindowAndGeneration := by
  sorry

public theorem releaseRefusesStaleReceipt : ReleaseRefusesStaleReceipt := by
  sorry

/-! ## PGT-R10 -/

public theorem reservationPublishesAfterZeroing : ReservationPublishesAfterZeroing := by
  sorry

public theorem cancelRefusesAttemptedReservation : CancelRefusesAttemptedReservation := by
  sorry

/-! ## PGT-R11 -/

public theorem capacitiesAtTheirLimits : CapacitiesAtTheirLimits := by
  sorry

public theorem capacitiesRefuseOneMore : CapacitiesRefuseOneMore := by
  sorry

/-! ## PGT-R12 -/

set_option synthInstance.maxSize 4096 in
public theorem copyIsPrivateAndOrdered : CopyIsPrivateAndOrdered := by
  unfold CopyIsPrivateAndOrdered; decide +kernel

public theorem copyRefusesPrivateLeaf : CopyRefusesPrivateLeaf := by
  unfold CopyRefusesPrivateLeaf; decide +kernel

end Krepi.Proofs.PageTables.Stp
