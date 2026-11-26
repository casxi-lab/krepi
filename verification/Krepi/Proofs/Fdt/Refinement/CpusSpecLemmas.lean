module

public import Krepi.Proofs.Fdt.Refinement.NodePropertySpecLemmas
public import Krepi.Proofs.Fdt.DiscoveryLemmas

/-!
# Device tree: lemmas about the specification of the CPU nodes

Lemmas about `Krepi.Spec.Fdt.Cpus`, for the refinement proofs of the CPU
discovery, the CPU profile and the CPU topology. The module imports no
generated definitions, so it is built once and not again for every mutant of
the code.

- The steps of the specification as the code takes them: `cpuOfChild_eq` (one
  child of `/cpus`), `discoverCpus_eq` (the discovery), `timerRecords`,
  `timerFlags` and `validateTimers_eq` (the timer interrupts),
  `timerFlags_toNat` (the flags of 1 to 4 CPUs), `foldlM_filter_cons` (the
  children of `/cpus` one node at a time), and `ite_or_same`, `ite_and_same`
  (two tests of the code that lead to one block).
- The logical IDs: `affinityShift_cases` (the four shifts), `beq_shift`,
  `idOf_toNat` (the ID of an affinity as the code computes it, by a shift
  right and back), `idOf_lt` (an ID is below 4) and `map_word_iff`.
- The set of IDs as a mask: `IdsRepr` (distinct IDs below 4, the bit of each
  set, and their number), `idsRepr_nil`, `idsRepr_snoc`, `idsRepr_mem`,
  `idsRepr_and_eq_zero` (the test of an ID in the mask), `idsRepr_length_le`,
  `idsRepr_complete` (the mask of `0` to `count - 1`), `testBit_eq_mod` and
  `idsComplete_eq` (`idsComplete` as the code tests it).
- The timer interrupts: `beL` (a big-endian word of a list of bytes),
  `be32_length`, `foldl_be32`, `eq_be32`, `beL_drop`, `beL_append_left`,
  `beL_append`, `beL_record`, `timerRecords_nil`, `timerRecords_cons`,
  `records_iff` (the bytes of the records are those of the private
  interrupts exactly when every record reads as one), `beNat_eq_beL`,
  `records_iff_bytes` (the same with the words of `beNat`) and `RecordAt`.
- Tests of the code on machine words: `u64_bne_iff`, `u32_bne_iff'`,
  `word32_bne_zero` and `cells_test` (the test of the address cells).
- Names, lists and paths that the code writes as arrays: `toUTF8_inj'`,
  `bytes_device_type`, `bytes_cpu`, `bytes_compatible`, `bytes_cortex_a76`,
  `bytes_enable_method`, `bytes_psci`, `bytes_method`, `bytes_hvc`,
  `bytes_smc`, `psci_compatible_eq` (the lists of `PSCI_COMPATIBLE` as the
  bytes of the three arrays of the code), and the paths `path_cpus`,
  `path_psci`, `valid_cpus` and `valid_psci`.
-/

@[expose] public section

open Aeneas Aeneas.Std
open Krepi.Statements Krepi.Spec.Fdt Krepi.Proofs.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## The steps of the specification -/

/-- `cpuOfChild` with its steps as the code takes them. -/
theorem cpuOfChild_eq (p : CpuProfile) (cells : UInt32) (ids : List UInt64) (n : Node) :
    cpuOfChild p cells ids n =
      n.stringProperty "device_type" >>= fun dt =>
      if dt != some "cpu" then .ok ids else
      n.enabled >>= fun en =>
      if !en then .error .badProperty else
      n.stringProperty "compatible" >>= fun c =>
      if c != some "arm,cortex-a76" then .error .badProperty else
      match n.property "reg" with
      | some reg =>
        cellsU64 reg cells >>= fun aff =>
        match p.idOf aff with
        | some id =>
          if ids.contains id then .error .badProperty else
          if (id != 0 || p.cpu0EnableMethod) = true then
            n.stringProperty "enable-method" >>= fun m =>
            if m != some "psci" then .error .badProperty else .ok (ids ++ [id])
          else .ok (ids ++ [id])
        | _ => .error .badProperty
      | _ => .error .missingProperty := rfl

/-- `Fdt.discoverCpus` with its steps as the code takes them. -/
theorem discoverCpus_eq (t : Fdt) (p : CpuProfile) :
    t.discoverCpus p =
      t.findNode "/cpus" >>= fun o =>
      match o with
      | some cpus =>
        cpus.enabled >>= fun en =>
        if !en then .error .badProperty else
        cpus.sizeCells >>= fun sc =>
        if sc != 0 then .error .badProperty else
        cpus.addressCells >>= fun cells =>
        if !(cells == 1 || cells == 2) then .error .unsupportedCells else
        (t.nodes.filter (·.isChildOf cpus)).foldlM (cpuOfChild p cells) [] >>= fun ids =>
        if !idsComplete p ids then .error .badProperty else
        t.findNode "/psci" >>= fun o =>
        match o with
        | some psci =>
          psci.enabled >>= fun en =>
          if !en then .error .badProperty else
          psci.stringProperty "method" >>= fun m =>
          if m != some p.conduit.name then .error .badProperty else
          if !PSCI_COMPATIBLE.any (some · == (psci.property "compatible").map (·.toList)) then
            .error .badProperty
          else .ok { profile := p, count := UInt64.ofNat ids.length }
        | _ => .error .missingProperty
      | _ => .error .missingProperty := rfl

/-- The bytes of the records of the private interrupts `ppis` with the flags
`flags`, as `CpuTopology.validateTimers` builds them. -/
def timerRecords (flags : UInt32) (ppis : List UInt32) : List UInt8 :=
  ppis.flatMap fun ppi => be32 1 ++ be32 ppi.toNat ++ be32 flags.toNat

/-- The flags cell of the timer records of a topology with `count` CPUs. -/
def timerFlags (count : UInt64) : UInt32 := (((1 : UInt32) <<< count.toUInt32) - 1) <<< 8 ||| 4

/-- `CpuTopology.validateTimers` by the timer interrupts of its profile. -/
theorem validateTimers_eq (t : CpuTopology) (b : ByteArray) :
    t.validateTimers b =
      match t.profile.timerInterrupts with
      | some timer =>
        if b.toList = timerRecords (timerFlags t.count) timer.list then .ok () else .error .badProperty
      | none => .error .badProperty := by
  unfold CpuTopology.validateTimers
  cases t.profile.timerInterrupts with
  | none => rfl
  | some timer =>
    simp only [timerRecords, timerFlags]
    by_cases h : b.toList = List.flatMap (fun ppi => be32 1 ++ be32 ppi.toNat ++
      be32 ((((1 : UInt32) <<< t.count.toUInt32) - 1) <<< 8 ||| 4).toNat) timer.list
    · simp only [h, bne_self_eq_false, ↓reduceIte]; rfl
    · simp only [h, ↓reduceIte, bne_iff_ne, ne_eq, not_false_eq_true]; rfl

/-- The flags of a topology of 1 to 4 CPUs. -/
theorem timerFlags_toNat {c : UInt64} (h1 : 1 ≤ c.toNat) (h4 : c.toNat ≤ 4) :
    (timerFlags c).toNat = (2 ^ c.toNat - 1) * 2 ^ 8 + 4 := by
  have : c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 := by
    have : c.toNat = 1 ∨ c.toNat = 2 ∨ c.toNat = 3 ∨ c.toNat = 4 := by omega
    rcases this with h | h | h | h
    · exact Or.inl (UInt64.toNat_inj.1 h)
    · exact Or.inr (Or.inl (UInt64.toNat_inj.1 h))
    · exact Or.inr (Or.inr (Or.inl (UInt64.toNat_inj.1 h)))
    · exact Or.inr (Or.inr (Or.inr (UInt64.toNat_inj.1 h)))
  rcases this with rfl | rfl | rfl | rfl <;> decide

/-- A fold over the nodes that a test keeps, one node at a time. -/
theorem foldlM_filter_cons {α : Type} (q : Node → Bool) (f : α → Node → Except Krepi.Spec.Fdt.Error α)
    (n : Node) (l : List Node) (acc : α) :
    ((n :: l).filter q).foldlM f acc =
      if q n then f acc n >>= fun acc' => (l.filter q).foldlM f acc' else (l.filter q).foldlM f acc := by
  by_cases h : q n
  · simp only [List.filter_cons, h, ↓reduceIte, List.foldlM_cons]
  · simp only [List.filter_cons, h, Bool.false_eq_true, ↓reduceIte]

/-- Two tests that lead to the same block, as the code writes the
`enable-method` check of CPU 0. -/
theorem ite_or_same {α : Type} (a b : Bool) (x y : α) :
    (if a = true then x else if b = true then x else y) = if (a || b) = true then x else y := by
  cases a <;> cases b <;> rfl

/-- Two tests that lead to the same block, as the code writes the check of the
address cells. -/
theorem ite_and_same {α : Type} (a b : Bool) (x y : α) :
    (if a = true then (if b = true then x else y) else y) = if (a && b) = true then x else y := by
  cases a <;> cases b <;> rfl

/-! ## The logical IDs -/

/-- The four shifts of the affinity levels. -/
theorem affinityShift_cases (p : CpuProfile) :
    p.affinityShift = 0 ∨ p.affinityShift = 8 ∨ p.affinityShift = 16 ∨ p.affinityShift = 32 := by
  unfold CpuProfile.affinityShift
  cases p.affinityLevel <;> simp [AffinityLevel.shift]

/-- The test of an ID of `idOf` at a shift of a level, as numbers. -/
theorem beq_shift {x i sh : UInt64} (hi : i.toNat < 4) (hs : sh.toNat ≤ 32) :
    (x == i <<< sh) = decide (x.toNat = i.toNat * 2 ^ sh.toNat) := by
  have hlt : i.toNat * 2 ^ sh.toNat < 2 ^ 64 := by
    calc i.toNat * 2 ^ sh.toNat < 4 * 2 ^ 32 :=
          Nat.mul_lt_mul_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) hs) (by positivity)
      _ ≤ 2 ^ 64 := by norm_num
  have e : (i <<< sh).toNat = i.toNat * 2 ^ sh.toNat := by
    rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt (show sh.toNat < 64 by omega), Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt hlt]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← e, UInt64.toNat_inj]

/-- `CpuProfile.idOf` as the code computes it: the affinity shifted right by the
shift of the level, when it is below 4 and gives the affinity back shifted
left. -/
theorem idOf_toNat (p : CpuProfile) (x : UInt64) :
    (p.idOf x).map UInt64.toNat =
      if x.toNat >>> p.affinityShift.toNat < 4 ∧
          (x.toNat >>> p.affinityShift.toNat) <<< p.affinityShift.toNat = x.toNat
      then some (x.toNat >>> p.affinityShift.toNat) else none := by
  have hs : p.affinityShift.toNat ≤ 32 := by
    rcases affinityShift_cases p with h | h | h | h <;> rw [h] <;> decide
  unfold CpuProfile.idOf CPU_IDS
  simp only [List.find?_cons, List.find?_nil, beq_shift (show (0 : UInt64).toNat < 4 by decide) hs,
    beq_shift (show (1 : UInt64).toNat < 4 by decide) hs,
    beq_shift (show (2 : UInt64).toNat < 4 by decide) hs,
    beq_shift (show (3 : UInt64).toNat < 4 by decide) hs, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq, UInt64.reduceToNat]
  generalize x.toNat = a
  rcases affinityShift_cases p with h | h | h | h <;> rw [h] <;>
    (try simp only [UInt64.reduceToNat, Nat.reducePow]) <;>
    repeat' split
  all_goals
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, Option.map_some, Option.map_none,
      Option.some.injEq, reduceCtorEq, UInt64.reduceToNat] at *
    try omega

/-- An ID of `idOf` is below 4. -/
theorem idOf_lt {p : CpuProfile} {x id : UInt64} (h : p.idOf x = some id) : id.toNat < 4 := by
  have hm := List.mem_of_find?_eq_some h
  simp only [CPU_IDS, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl <;> decide

/-- An option of words of the code as an option of the specification, read as
numbers. -/
theorem map_word_iff {o : Option U64} {q : Option UInt64} :
    o.map word64 = q ↔ o.map (·.val) = q.map UInt64.toNat := by
  cases o <;> cases q <;> simp [word64_eq_iff]

/-! ## The set of IDs as a mask -/

/-- The IDs `ids` of the CPU nodes so far as the code keeps them: distinct IDs
below 4, the bit of each set in `mask` and no other bit, and their number
`count`. -/
def IdsRepr (mask count : Nat) (ids : List UInt64) : Prop :=
  ids.Nodup ∧ (∀ x ∈ ids, x.toNat < 4) ∧
    (∀ j, mask.testBit j = decide (∃ x ∈ ids, x.toNat = j)) ∧ count = ids.length

theorem idsRepr_nil : IdsRepr 0 0 [] := by
  refine ⟨List.nodup_nil, by simp, fun j => ?_, rfl⟩
  simp [Nat.zero_testBit]

/-- A new ID below 4 sets its bit and counts one more. -/
theorem idsRepr_snoc {m c : Nat} {ids : List UInt64} {x : UInt64} (h : IdsRepr m c ids)
    (hx : x.toNat < 4) (hn : x ∉ ids) : IdsRepr (m ||| 2 ^ x.toNat) (c + 1) (ids ++ [x]) := by
  obtain ⟨hd, hl, hb, hc⟩ := h
  refine ⟨List.nodup_append.2 ⟨hd, List.nodup_singleton x, ?_⟩, ?_, fun j => ?_, by simp [hc]⟩
  · intro a ha b hb' e
    simp only [List.mem_singleton] at hb'
    subst hb'; subst e; exact hn ha
  · intro y hy
    rcases List.mem_append.1 hy with hy | hy
    · exact hl y hy
    · simp only [List.mem_singleton] at hy; subst hy; exact hx
  · rw [Nat.testBit_or, hb j, Nat.testBit_two_pow]
    by_cases h1 : ∃ y ∈ ids, y.toNat = j
    · have : ∃ y ∈ ids ++ [x], y.toNat = j := by
        obtain ⟨y, hy, e⟩ := h1; exact ⟨y, List.mem_append_left _ hy, e⟩
      simp only [h1, this, decide_true, Bool.true_or]
    · by_cases h2 : x.toNat = j
      · simp only [h2, decide_true, Bool.or_true, eq_comm (a := true), decide_eq_true_iff]
        exact ⟨x, by simp, h2⟩
      · have : ¬ ∃ y ∈ ids ++ [x], y.toNat = j := by
          rintro ⟨y, hy, e⟩
          rcases List.mem_append.1 hy with hy | hy
          · exact h1 ⟨y, hy, e⟩
          · simp only [List.mem_singleton] at hy; subst hy; exact h2 e
        simp only [h1, h2, decide_false, Bool.or_false, eq_comm (a := false),
          decide_eq_false_iff_not]
        exact this

/-- An ID below 4 is in the set exactly when its bit is set. -/
theorem idsRepr_mem {m c : Nat} {ids : List UInt64} {x : UInt64} (h : IdsRepr m c ids) :
    m.testBit x.toNat = true ↔ x ∈ ids := by
  rw [h.2.2.1, decide_eq_true_iff]
  constructor
  · rintro ⟨y, hy, e⟩; rwa [← UInt64.toNat_inj.1 e]
  · intro hx; exact ⟨x, hx, rfl⟩

/-- The test of the code of an ID in the mask. -/
theorem idsRepr_and_eq_zero {m c : Nat} {ids : List UInt64} {x : UInt64} (h : IdsRepr m c ids) :
    m &&& 2 ^ x.toNat = 0 ↔ x ∉ ids := by
  rw [← idsRepr_mem h]
  constructor
  · intro h0 hb
    have := congrArg (fun n => n.testBit x.toNat) h0
    simp only [Nat.testBit_and, hb, Nat.testBit_two_pow_self, Bool.and_self, Nat.zero_testBit] at this
    cases this
  · intro hb
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases e : x.toNat = j
    · subst e; simpa using hb
    · simp [e]

/-- At most four IDs. -/
theorem idsRepr_length_le {m c : Nat} {ids : List UInt64} (h : IdsRepr m c ids) : c ≤ 4 := by
  obtain ⟨hd, hl, -, hc⟩ := h
  have hd' : (ids.map UInt64.toNat).Nodup := hd.map (fun a b e => UInt64.toNat_inj.1 e)
  have hs : ids.map UInt64.toNat ⊆ List.range 4 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
    exact List.mem_range.2 (hl x hx)
  have := (hd'.subperm hs).length_le
  simp only [List.length_map, List.length_range] at this
  omega

/-- The mask of `count` IDs is that of `0` to `count - 1` exactly when each of
them is in the set. -/
theorem idsRepr_complete {m c : Nat} {ids : List UInt64} (h : IdsRepr m c ids) :
    m = 2 ^ c - 1 ↔ ∀ i < c, UInt64.ofNat i ∈ ids := by
  have h4 := idsRepr_length_le h
  obtain ⟨hd, hl, hb, hc⟩ := h
  constructor
  · rintro rfl i hi
    have := hb i
    rw [Nat.testBit_two_pow_sub_one, decide_eq_decide] at this
    obtain ⟨y, hy, e⟩ := this.1 hi
    have : y = UInt64.ofNat i := by
      rw [← e]; exact (UInt64.ofNat_toNat).symm
    rwa [← this]
  · intro hall
    have hd' : (ids.map UInt64.toNat).Nodup := hd.map (fun a b e => UInt64.toNat_inj.1 e)
    have hs : List.range c ⊆ ids.map UInt64.toNat := by
      intro i hi
      have hi := List.mem_range.1 hi
      refine List.mem_map.2 ⟨UInt64.ofNat i, hall i hi, ?_⟩
      rw [UInt64.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (show i < 4 by omega) (by decide))]
    have hp := (List.nodup_range.subperm hs).perm_of_length_le (by simp [hc])
    apply Nat.eq_of_testBit_eq
    intro j
    rw [hb j, Nat.testBit_two_pow_sub_one, decide_eq_decide]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact List.mem_range.1 (hp.mem_iff.2 (List.mem_map.2 ⟨y, hy, rfl⟩))
    · intro hj
      obtain ⟨y, hy, e⟩ := List.mem_map.1 (hp.mem_iff.1 (List.mem_range.2 hj))
      exact ⟨y, hy, e⟩

/-- `idsComplete` of a set of IDs that a mask stands for, as the code tests it:
a count from 1 to 4 whose bit of `cpu_counts` is set, and the mask of `0` to
`count - 1`. -/
theorem idsComplete_eq {m c : Nat} {ids : List UInt64} (h : IdsRepr m c ids) (p : CpuProfile) :
    idsComplete p ids =
      (c != 0 && c ≤ 4 && p.cpuCounts.toNat.testBit c && decide (m = 2 ^ c - 1)) := by
  simp only [idsRepr_complete h]
  unfold idsComplete CpuProfile.allows
  rw [← h.2.2.2]
  dsimp only
  congr 1
  rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff]
  constructor
  · intro ha i hi
    have := ha i (List.mem_range.2 hi)
    rwa [List.contains_iff_mem] at this
  · intro ha i hi
    rw [List.contains_iff_mem]
    exact ha i (List.mem_range.1 hi)

/-! ## The timer interrupts -/

/-- The big-endian 32-bit word of a list of bytes at `i`. -/
def beL (l : List UInt8) (i : Nat) : Nat :=
  ((l.drop i).take 4).foldl (fun acc x => acc * 256 + x.toNat) 0

theorem be32_length (n : Nat) : (be32 n).length = 4 := rfl

/-- The four bytes of a word read back. -/
theorem foldl_be32 (n : Nat) :
    (be32 n).foldl (fun acc x => acc * 256 + x.toNat) 0 = n % 2 ^ 32 := by
  simp only [be32, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, UInt8.toNat_ofNat']
  omega

/-- Four bytes that read as a word are its bytes. -/
theorem eq_be32 {bs : List UInt8} {n : Nat} (hl : bs.length = 4)
    (hv : bs.foldl (fun acc x => acc * 256 + x.toNat) 0 = n) : bs = be32 n := by
  match bs, hl with
  | [b0, b1, b2, b3], _ =>
    simp only [List.foldl_cons, List.foldl_nil] at hv
    have h0 := UInt8.toNat_lt b0
    have h1 := UInt8.toNat_lt b1
    have h2 := UInt8.toNat_lt b2
    have h3 := UInt8.toNat_lt b3
    simp only [be32, List.map_cons, List.map_nil, List.cons.injEq, ← UInt8.toNat_inj,
      UInt8.toNat_ofNat', and_true]
    omega

theorem beL_drop (l : List UInt8) (a i : Nat) : beL (l.drop a) i = beL l (a + i) := by
  simp only [beL, List.drop_drop]

theorem beL_append_left (A B : List UInt8) {i : Nat} (h : i + 4 ≤ A.length) :
    beL (A ++ B) i = beL A i := by
  simp only [beL, List.drop_append_of_le_length (show i ≤ A.length by omega)]
  rw [List.take_append_of_le_length (by simp; omega)]

theorem beL_append (A B : List UInt8) (i : Nat) : beL (A ++ B) (A.length + i) = beL B i := by
  rw [beL, beL, List.drop_append, List.drop_of_length_le (by omega), List.nil_append,
    Nat.add_sub_cancel_left]

/-- The three words of a record. -/
theorem beL_record (a b c : Nat) :
    beL (be32 a ++ be32 b ++ be32 c) 0 = a % 2 ^ 32 ∧
      beL (be32 a ++ be32 b ++ be32 c) 4 = b % 2 ^ 32 ∧
      beL (be32 a ++ be32 b ++ be32 c) 8 = c % 2 ^ 32 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.append_assoc, beL_append_left _ _ (by rfl)]
    simp only [beL, List.drop_zero, List.take_of_length_le (le_of_eq (be32_length a)), foldl_be32]
  · rw [List.append_assoc, show 4 = (be32 a).length + 0 from rfl, beL_append,
      beL_append_left _ _ (by rfl)]
    simp only [beL, List.drop_zero, List.take_of_length_le (le_of_eq (be32_length b)), foldl_be32]
  · rw [show 8 = (be32 a ++ be32 b).length + 0 from rfl, beL_append]
    simp only [beL, List.drop_zero, List.take_of_length_le (le_of_eq (be32_length c)), foldl_be32]

theorem timerRecords_nil (f : UInt32) : timerRecords f [] = [] := rfl

theorem timerRecords_cons (f : UInt32) (p : UInt32) (ps : List UInt32) :
    timerRecords f (p :: ps) = (be32 1 ++ be32 p.toNat ++ be32 f.toNat) ++ timerRecords f ps :=
  List.flatMap_cons

/-- The bytes are the records of the private interrupts `ppis` exactly when
they are twelve bytes for each and every record reads as type 1, its number
and the flags. -/
theorem records_iff (f : UInt32) : ∀ (ppis : List UInt32) (l : List UInt8),
    l = timerRecords f ppis ↔ l.length = 12 * ppis.length ∧
      ∀ j (hj : j < ppis.length), beL l (12 * j) = 1 ∧ beL l (12 * j + 4) = ppis[j].toNat ∧
        beL l (12 * j + 8) = f.toNat
  | [], l => by
    simp only [timerRecords_nil, List.length_nil, Nat.mul_zero, List.length_eq_zero_iff,
      Nat.not_lt_zero, IsEmpty.forall_iff, implies_true, and_true]
  | p :: ps, l => by
    have ih := records_iff f ps
    have hG : (be32 1 ++ be32 p.toNat ++ be32 f.toNat).length = 12 := rfl
    have hp := UInt32.toNat_lt p
    have hf := UInt32.toNat_lt f
    obtain ⟨r0, r4, r8⟩ := beL_record 1 p.toNat f.toNat
    rw [timerRecords_cons]
    constructor
    · rintro rfl
      obtain ⟨hlen, hall⟩ := (ih _).1 rfl
      refine ⟨by simp only [List.length_append, hG, hlen, List.length_cons]; omega, fun j hj => ?_⟩
      cases j with
      | zero =>
        have hl : ∀ i, i + 4 ≤ 12 → beL ((be32 1 ++ be32 p.toNat ++ be32 f.toNat) ++
            timerRecords f ps) i = beL (be32 1 ++ be32 p.toNat ++ be32 f.toNat) i :=
          fun i h => beL_append_left _ _ (by rw [hG]; exact h)
        simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
        rw [hl 0 (by omega), hl 4 (by omega), hl 8 (by omega), r0, r4, r8]
        exact ⟨by decide, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hf⟩
      | succ j =>
        have hj' : j < ps.length := by simp at hj; omega
        obtain ⟨a0, a4, a8⟩ := hall j hj'
        simp only [List.getElem_cons_succ]
        rw [show 12 * (j + 1) = (be32 1 ++ be32 p.toNat ++ be32 f.toNat).length + 12 * j by
            rw [hG]; omega,
          show (be32 1 ++ be32 p.toNat ++ be32 f.toNat).length + 12 * j + 4 =
            (be32 1 ++ be32 p.toNat ++ be32 f.toNat).length + (12 * j + 4) by omega,
          show (be32 1 ++ be32 p.toNat ++ be32 f.toNat).length + 12 * j + 8 =
            (be32 1 ++ be32 p.toNat ++ be32 f.toNat).length + (12 * j + 8) by omega,
          beL_append, beL_append, beL_append]
        exact ⟨a0, a4, a8⟩
    · rintro ⟨hlen, hall⟩
      simp only [List.length_cons] at hlen
      have h12 : 12 ≤ l.length := by omega
      rw [← List.take_append_drop 12 l]
      congr 1
      · obtain ⟨a0, a4, a8⟩ := hall 0 (by simp)
        simp only [Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero] at a0 a4 a8
        have e : l.take 12 = l.take 4 ++ (l.drop 4).take 4 ++ (l.drop 8).take 4 := by
          rw [show 12 = 8 + 4 from rfl, List.take_add, show 8 = 4 + 4 from rfl, List.take_add]
        rw [e, eq_be32 (bs := l.take 4) (by simp; omega) (by simpa [beL] using a0),
          eq_be32 (bs := (l.drop 4).take 4) (by simp; omega) (by simpa [beL] using a4),
          eq_be32 (bs := (l.drop 8).take 4) (by simp; omega) (by simpa [beL] using a8)]
      · refine (ih _).2 ⟨by simp; omega, fun j hj => ?_⟩
        obtain ⟨a0, a4, a8⟩ := hall (j + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at a4
        rw [beL_drop, beL_drop, beL_drop]
        refine ⟨?_, ?_, ?_⟩
        · rw [show 12 + 12 * j = 12 * (j + 1) by omega]; exact a0
        · rw [show 12 + (12 * j + 4) = 12 * (j + 1) + 4 by omega]; exact a4
        · rw [show 12 + (12 * j + 8) = 12 * (j + 1) + 8 by omega]; exact a8

/-- A word of `beNat` of the bytes of a slice as a word of the list. -/
theorem beNat_eq_beL (s : Slice U8) (i : Nat) : beNat (bytesOf s) i 4 = beL (bytesOf s).toList i := by
  rw [beNat, bytesOf_extract, bytesOf_toList, beL, Nat.add_sub_cancel_left, List.map_take,
    List.map_drop]

/-- `records_iff` for the bytes of a slice, with the words of `beNat`. -/
theorem records_iff_bytes (f : UInt32) (ppis : List UInt32) (s : Slice U8) :
    (bytesOf s).toList = timerRecords f ppis ↔ s.length = 12 * ppis.length ∧
      ∀ j (hj : j < ppis.length), beNat (bytesOf s) (12 * j) 4 = 1 ∧
        beNat (bytesOf s) (12 * j + 4) 4 = ppis[j].toNat ∧ beNat (bytesOf s) (12 * j + 8) 4 = f.toNat := by
  rw [records_iff, bytesOf_toList, List.length_map]
  simp only [beNat_eq_beL, bytesOf_toList]

/-- Two strings with the same bytes are equal. -/
theorem toUTF8_inj' {a b : String} : a.toUTF8 = b.toUTF8 ↔ a = b := by
  rw [String.toUTF8_eq_toByteArray, String.toUTF8_eq_toByteArray]
  exact String.toByteArray_inj

/-- A bit as the code tests it. -/
theorem testBit_eq_mod (m n : Nat) : m.testBit n = decide ((m >>> n) % 2 ≠ 0) := by
  rw [Nat.testBit, Nat.one_and_eq_mod_two]
  by_cases h : (m >>> n) % 2 = 0
  · simp [h]
  · simp [h]; omega

/-! ## Tests of the code on machine words -/

/-- A record of the timer interrupts at index `j` reads as type 1, the number
`n` and the flags `f`. -/
abbrev RecordAt (s : Slice U8) (j : Nat) (n f : UInt32) : Prop :=
  beNat (bytesOf s) (12 * j) 4 = 1 ∧ beNat (bytesOf s) (12 * j + 4) 4 = n.toNat ∧
    beNat (bytesOf s) (12 * j + 8) 4 = f.toNat

theorem u64_bne_iff {x y : U64} : (x != y) = true ↔ x.val ≠ y.val := by
  rw [bne_iff_ne, ne_eq, UScalar.eq_equiv]

theorem u32_bne_iff' {x y : U32} : (x != y) = true ↔ x.val ≠ y.val := by
  rw [bne_iff_ne, ne_eq, UScalar.eq_equiv]

theorem word32_bne_zero (x : U32) : (word32 x != 0) = (x != 0#u32) := by
  rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, ne_eq, ne_eq, word32_eq_iff, UScalar.eq_equiv]
  rfl

/-- The test of the code of the address cells of `/cpus`. -/
theorem cells_test (x : U32) :
    ((x != 1#u32) && (x != 2#u32)) = !(word32 x == 1 || word32 x == 2) := by
  have e1 : (word32 x == 1) = decide (x.val = 1) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, word32_eq_iff, decide_eq_true_iff]; rfl
  have e2 : (word32 x == 2) = decide (x.val = 2) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, word32_eq_iff, decide_eq_true_iff]; rfl
  have f1 : (x != 1#u32) = !decide (x.val = 1) := by
    rw [Bool.eq_iff_iff, u32_bne_iff', Bool.not_eq_true', decide_eq_false_iff_not]; rfl
  have f2 : (x != 2#u32) = !decide (x.val = 2) := by
    rw [Bool.eq_iff_iff, u32_bne_iff', Bool.not_eq_true', decide_eq_false_iff_not]; rfl
  rw [e1, e2, f1, f2, Bool.not_or]

/-! ## The names, lists and paths that the code writes -/

theorem bytes_device_type :
    bytesOf (Array.to_slice (Array.make 11#usize [100#u8, 101#u8, 118#u8, 105#u8, 99#u8, 101#u8,
      95#u8, 116#u8, 121#u8, 112#u8, 101#u8])) = "device_type".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

theorem bytes_cpu :
    bytesOf (Array.to_slice (Array.make 3#usize [99#u8, 112#u8, 117#u8])) = "cpu".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

theorem bytes_compatible :
    bytesOf (Array.to_slice (Array.make 10#usize [99#u8, 111#u8, 109#u8, 112#u8, 97#u8, 116#u8,
      105#u8, 98#u8, 108#u8, 101#u8])) = "compatible".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

theorem bytes_cortex_a76 :
    bytesOf (Array.to_slice (Array.make 14#usize [97#u8, 114#u8, 109#u8, 44#u8, 99#u8, 111#u8,
      114#u8, 116#u8, 101#u8, 120#u8, 45#u8, 97#u8, 55#u8, 54#u8])) = "arm,cortex-a76".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

theorem bytes_enable_method :
    bytesOf (Array.to_slice (Array.make 13#usize [101#u8, 110#u8, 97#u8, 98#u8, 108#u8, 101#u8,
      45#u8, 109#u8, 101#u8, 116#u8, 104#u8, 111#u8, 100#u8])) = "enable-method".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

theorem bytes_psci :
    bytesOf (Array.to_slice (Array.make 4#usize [112#u8, 115#u8, 99#u8, 105#u8])) =
      "psci".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

theorem bytes_method :
    bytesOf (Array.to_slice (Array.make 6#usize [109#u8, 101#u8, 116#u8, 104#u8, 111#u8, 100#u8])) =
      "method".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

theorem bytes_hvc :
    bytesOf (Array.to_slice (Array.make 3#usize [104#u8, 118#u8, 99#u8])) = "hvc".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

theorem bytes_smc :
    bytesOf (Array.to_slice (Array.make 3#usize [115#u8, 109#u8, 99#u8])) = "smc".toUTF8 := by
  rw [byteArray_eq_iff, toUTF8_toList, bytesOf_toList]; rfl

/-- The `compatible` lists of `/psci` as the bytes of the three arrays of the
code. -/
theorem psci_compatible_eq : PSCI_COMPATIBLE =
    [(bytesOf (Array.to_slice (Array.make 13#usize [97#u8, 114#u8, 109#u8, 44#u8, 112#u8, 115#u8,
        99#u8, 105#u8, 45#u8, 48#u8, 46#u8, 50#u8, 0#u8]))).toList,
     (bytesOf (Array.to_slice (Array.make 26#usize [97#u8, 114#u8, 109#u8, 44#u8, 112#u8, 115#u8,
        99#u8, 105#u8, 45#u8, 49#u8, 46#u8, 48#u8, 0#u8, 97#u8, 114#u8, 109#u8, 44#u8, 112#u8,
        115#u8, 99#u8, 105#u8, 45#u8, 48#u8, 46#u8, 50#u8, 0#u8]))).toList,
     (bytesOf (Array.to_slice (Array.make 35#usize [97#u8, 114#u8, 109#u8, 44#u8, 112#u8, 115#u8,
        99#u8, 105#u8, 45#u8, 49#u8, 46#u8, 48#u8, 0#u8, 97#u8, 114#u8, 109#u8, 44#u8, 112#u8,
        115#u8, 99#u8, 105#u8, 45#u8, 48#u8, 46#u8, 50#u8, 0#u8, 97#u8, 114#u8, 109#u8, 44#u8,
        112#u8, 115#u8, 99#u8, 105#u8, 0#u8]))).toList] := by
  simp only [PSCI_COMPATIBLE, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    ← String.toUTF8_eq_toByteArray, toUTF8_toList, bytesOf_toList]
  rfl

theorem path_cpus :
    (Array.to_slice (Array.make 5#usize [47#u8, 99#u8, 112#u8, 117#u8, 115#u8])).val.map byte =
      utf8Bytes "/cpus".toList := rfl

theorem path_psci :
    (Array.to_slice (Array.make 5#usize [47#u8, 112#u8, 115#u8, 99#u8, 105#u8])).val.map byte =
      utf8Bytes "/psci".toList := rfl

theorem valid_cpus : pathValidB (utf8Bytes "/cpus".toList) = true := by
  rw [show utf8Bytes "/cpus".toList = [47, 99, 112, 117, 115] from rfl]; decide

theorem valid_psci : pathValidB (utf8Bytes "/psci".toList) = true := by
  rw [show utf8Bytes "/psci".toList = [47, 112, 115, 99, 105] from rfl]; decide

end Krepi.Proofs.Fdt.Refinement
