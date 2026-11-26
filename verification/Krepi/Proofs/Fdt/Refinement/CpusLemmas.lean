module

public import Krepi.Proofs.Fdt.Refinement.NodePropertyLemmas
public import Krepi.Proofs.Fdt.Refinement.CpusSpecLemmas

/-!
# Device tree: refinement of the CPU nodes

The triples of the generated functions of `fdt::cpus` and of
`fdt::nodes::string_is`, stated against the specification of
`Krepi.Spec.Fdt.Cpus`, so that the proof of a caller steps over the call with
the triple of the callee and a mutant of a callee fails the proof of the
callee alone. The lemmas that need no generated code are in
`Krepi.Proofs.Fdt.Refinement.CpusSpecLemmas`.

- The profile and the topology: `cpu_profile_affinity_shift_spec`,
  `cpu_profile_conduit_spec`, `cpu_topology_count_spec`,
  `cpu_topology_profile_spec`, `affinityShift_val` (the shift as a number of
  at most 32), `id_of_spec` (`CpuProfile.idOf`),
  `cpu_profile_logical_id_spec` and `cpu_topology_affinity_spec`.
- Strings: `string_is_spec` (whether a string property is a given string),
  `method_is_spec` (the `method` of `/psci` against a conduit) and
  `psci_compatible_spec` (the `compatible` of `/psci` against
  `PSCI_COMPATIBLE`).
- The set of IDs: `ids_complete_spec` (`idsComplete` of the IDs that a mask
  and a count stand for, `IdsRepr`).
- The timer interrupts: `u32_at_ok` (a word read within the bytes),
  `timer_records_loop_spec`, `timer_records_spec`,
  `timersOf_list` and `validate_timers_spec` (`CpuTopology.validateTimers`).
- The children of `/cpus`: `cpu_of_child_spec` (`cpuOfChild`
  with the mask of the IDs before), `cpu_children_loop_spec` and
  `cpu_children_spec` (the fold of `cpuOfChild` over the children in tree
  order).
- The discovery: `find_path_valid_spec` (`Fdt.findNode` of a valid path, here
  `/cpus` and `/psci`, whose five bytes leave room for the index after the
  last) and `discover_cpus_spec` (`Fdt.discoverCpus`).
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Result
open KrepiGen.Fdt Krepi.Spec.Fdt Krepi.Statements Krepi.Statements.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## The profile and the topology -/

/-- `CpuProfile::affinity_shift()`: the shift of the affinity level. -/
@[step] theorem cpu_profile_affinity_shift_spec (p : fdt.CpuProfile) :
    fdt.cpus.CpuProfile.affinity_shift p ⦃ n => word64 n = (profileOf p).affinityShift ⦄ := by
  unfold fdt.cpus.CpuProfile.affinity_shift
  simp only [profileOf, CpuProfile.affinityShift]
  cases p.affinity_level <;> simp only [spec_ok] <;> rfl

/-- `CpuProfile::conduit()`: the PSCI conduit. -/
@[step] theorem cpu_profile_conduit_spec (p : fdt.CpuProfile) :
    fdt.cpus.CpuProfile.conduit p ⦃ c => conduitOf c = (profileOf p).conduit ⦄ := by
  unfold fdt.cpus.CpuProfile.conduit
  simp only [spec_ok]; rfl

/-- `CpuTopology::count()`: the number of CPUs. -/
@[step] theorem cpu_topology_count_spec (t : fdt.CpuTopology) :
    fdt.cpus.CpuTopology.count t ⦃ n => word64 n = (topologyOf t).count ⦄ := by
  unfold fdt.cpus.CpuTopology.count
  simp only [spec_ok]; rfl

/-- `CpuTopology::profile()`: the profile. -/
@[step] theorem cpu_topology_profile_spec (t : fdt.CpuTopology) :
    fdt.cpus.CpuTopology.profile t ⦃ p => profileOf p = (topologyOf t).profile ⦄ := by
  unfold fdt.cpus.CpuTopology.profile
  simp only [spec_ok]; rfl

/-- The shift of a profile as a number of at most 32. -/
theorem affinityShift_val {p : fdt.CpuProfile} {n : U64}
    (h : word64 n = (profileOf p).affinityShift) :
    n.val = (profileOf p).affinityShift.toNat ∧ n.val ≤ 32 := by
  have e := word64_eq_iff.1 h
  refine ⟨e, ?_⟩
  rw [e]
  rcases affinityShift_cases (profileOf p) with h | h | h | h <;> rw [h] <;> decide

/-- `id_of(profile, affinity)`: the logical ID of `CpuProfile.idOf`. -/
@[step] theorem id_of_spec (p : fdt.CpuProfile) (a : U64) :
    fdt.cpus.id_of p a ⦃ o => o.map word64 = (profileOf p).idOf (word64 a) ⦄ := by
  unfold fdt.cpus.id_of
  step as ⟨sh, hsh⟩
  obtain ⟨hs, h32⟩ := affinityShift_val hsh
  simp only [map_word_iff, idOf_toNat, word64_toNat, ← hs]
  step as ⟨id, hid, hid1⟩
  have hb : ∀ k : Nat, k < 4 → k * 2 ^ sh.val < 2 ^ 64 := fun k hk =>
    calc k * 2 ^ sh.val < 4 * 2 ^ 32 :=
          Nat.mul_lt_mul_of_lt_of_le hk (Nat.pow_le_pow_right (by omega) h32) (by positivity)
      _ ≤ 2 ^ 64 := by norm_num
  split
  · rename_i hlt
    have hlt' : id.val < 4 := by scalar_tac
    step as ⟨i, hi, hi1⟩
    have hiv : i.val = id.val * 2 ^ sh.val := by
      rw [hi, u64_size, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (hb _ hlt')]
    split
    · rename_i he
      have hc : a.val >>> sh.val < 4 ∧ (a.val >>> sh.val) <<< sh.val = a.val := by
        rw [← hid, Nat.shiftLeft_eq, ← hiv, he]; exact ⟨hlt', rfl⟩
      simp only [spec_ok, Option.map_some, hc, and_self, ↓reduceIte, hid]
    · rename_i hne
      have hc : ¬ (a.val >>> sh.val < 4 ∧ (a.val >>> sh.val) <<< sh.val = a.val) := by
        rintro ⟨-, he⟩
        apply hne
        apply UScalar.eq_of_val_eq
        rw [hiv, ← he, hid, Nat.shiftLeft_eq]
      simp only [spec_ok, Option.map_none, hc, ↓reduceIte]
  · rename_i hge
    have hc : ¬ (a.val >>> sh.val < 4 ∧ (a.val >>> sh.val) <<< sh.val = a.val) := by
      rintro ⟨h4, -⟩
      apply hge
      scalar_tac
    simp only [spec_ok, Option.map_none, hc, ↓reduceIte]

/-- `CpuProfile::logical_id(mpidr)`: the logical ID of the affinity fields. -/
@[step] theorem cpu_profile_logical_id_spec (p : fdt.CpuProfile) (mpidr : U64) :
    fdt.cpus.CpuProfile.logical_id p mpidr ⦃ o =>
      o.map word64 = (profileOf p).logicalId (word64 mpidr) ⦄ := by
  unfold fdt.cpus.CpuProfile.logical_id
  simp only [lift, bind_ok]
  have e : word64 (mpidr &&& fdt.cpus.AFFINITY_MASK) = word64 mpidr &&& AFFINITY_MASK := by
    rw [word64_eq_iff, UInt64.toNat_and, word64_toNat, UScalar.val_and, fdt.cpus.AFFINITY_MASK]
    rfl
  unfold CpuProfile.logicalId
  rw [← e]
  exact id_of_spec p _

/-- `CpuTopology::affinity(index)`: the affinity of an index below the count. -/
@[step] theorem cpu_topology_affinity_spec (t : fdt.CpuTopology) (index : U64) :
    fdt.cpus.CpuTopology.affinity t index ⦃ o =>
      o.map word64 = (topologyOf t).affinity (word64 index) ⦄ := by
  unfold fdt.cpus.CpuTopology.affinity
  simp only [topologyOf, CpuTopology.affinity]
  split
  · rename_i hlt
    step as ⟨sh, hsh⟩
    obtain ⟨hs, h32⟩ := affinityShift_val hsh
    step as ⟨i1, hi1, hi1'⟩
    have hc : word64 index < word64 t.count := by
      rw [UInt64.lt_iff_toNat_lt, word64_toNat, word64_toNat]; scalar_tac
    simp only [Option.map_some, hc, ↓reduceIte, Option.some.injEq]
    rw [word64_eq_iff, UInt64.toNat_shiftLeft, word64_toNat, ← hsh, word64_toNat,
      Nat.mod_eq_of_lt (show sh.val < 64 by omega), hi1, u64_size]
  · rename_i hge
    have hc : ¬ word64 index < word64 t.count := by
      rw [UInt64.lt_iff_toNat_lt, word64_toNat, word64_toNat]; scalar_tac
    simp only [spec_ok, Option.map_none, hc, ↓reduceIte]

/-! ## Strings, the conduit and the `compatible` of `/psci` -/

/-- `string_is(structure, strings, node, name, expected)`: whether the string
property of the node named as the bytes of `s` is the string `e`, or the error
of `Node.stringProperty`. -/
theorem string_is_spec (hu : Usize64) {t : fdt.Fdt} {a : fdt.NodeAt} {N : Node}
    (h : NodeRepr ⟨t, a⟩ N) («name» expected : Slice U8) (s e : String)
    (hk : bytesOf «name» = s.toUTF8) (he : bytesOf expected = e.toUTF8) :
    fdt.nodes.string_is t.structure t.strings a «name» expected ⦃ r =>
      Agrees (fun b o => b = (o == some e)) errorOf r (N.stringProperty s) ⦄ := by
  unfold fdt.nodes.string_is
  step with string_at_spec hu h «name» s hk as ⟨r, r_post⟩
  rw [← bind_pure (N.stringProperty s)]
  refine try_spec r_post (fun e => from_residual_spec e) fun o v hov _ => ?_
  rcases o with _ | ⟨st, en⟩ <;> rcases v with _ | str
  · exact spec_of_eq rfl rfl
  · exact hov.elim
  · exact hov.elim
  · obtain ⟨h1, h2, h3⟩ := hov
    dsimp only at h1 h2 h3
    simp only
    step as ⟨b, b_post⟩
    show b = (some str == some e)
    rw [b_post, h3, he]
    simp only [h1, h2, true_and, toUTF8_inj', Option.some_beq_some]
    rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq]

/-- `method_is(structure, strings, psci, conduit)`: whether the `method` of the
node names the conduit, or the error of `Node.stringProperty`. -/
theorem method_is_spec (hu : Usize64) {t : fdt.Fdt} {a : fdt.NodeAt} {N : Node}
    (h : NodeRepr ⟨t, a⟩ N) (c : fdt.PsciConduit) :
    fdt.cpus.method_is t.structure t.strings a c ⦃ r =>
      Agrees (fun b o => b = (o == some (conduitOf c).name)) errorOf r
        (N.stringProperty "method") ⦄ := by
  unfold fdt.cpus.method_is
  cases c <;> simp only [lift, bind_ok]
  · exact string_is_spec hu h _ _ "method" "hvc" bytes_method bytes_hvc
  · exact string_is_spec hu h _ _ "method" "smc" bytes_method bytes_smc

/-- `psci_compatible(structure, value)`: whether the value is one of the
`compatible` lists of `PSCI_COMPATIBLE`. -/
theorem psci_compatible_spec (s : Slice U8) (o : Option (Usize × Usize)) (v : Option ByteArray)
    (ho : OptionRel (RangeRepr s) o v) :
    fdt.cpus.psci_compatible s o ⦃ b => b = PSCI_COMPATIBLE.any (some · == v.map (·.toList)) ⦄ := by
  unfold fdt.cpus.psci_compatible
  rw [psci_compatible_eq]
  rcases o with _ | ⟨st, en⟩ <;> rcases v with _ | w
  · simp only [spec_ok, List.any_cons, List.any_nil]
    rfl
  · exact ho.elim
  · exact ho.elim
  · obtain ⟨h1, h2, h3⟩ := ho
    dsimp only at h1 h2 h3
    have key : ∀ (x : Slice U8) (bx : Bool), bx = decide (st.val ≤ en.val ∧ en.val ≤ s.length ∧
        (bytesOf s).extract st.val en.val = bytesOf x) →
        bx = (some (bytesOf x).toList == (some w).map (·.toList)) := by
      intro x bx hx
      rw [hx, h3, Option.map_some, Option.some_beq_some]
      simp only [h1, h2, true_and, byteArray_eq_iff]
      rw [Bool.eq_iff_iff, decide_eq_true_iff, beq_iff_eq, eq_comm]
    simp only [lift, bind_ok, List.any_cons, List.any_nil, Bool.or_false]
    step as ⟨b, b_post⟩
    split
    · simp only [spec_ok, ← key _ b b_post, ‹b = true›, Bool.true_or]
    · step as ⟨b1, b1_post⟩
      split
      · simp only [spec_ok, ← key _ b b_post, ← key _ b1 b1_post, ‹b1 = true›, Bool.true_or,
          Bool.or_true]
      · step as ⟨b2, b2_post⟩
        simp only [← key _ b b_post, ← key _ b1 b1_post, ← key _ b2 b2_post]
        simp only [‹¬b = true›, ‹¬b1 = true›, Bool.false_or]

/-- `ids_complete(profile, ids, count)`: `idsComplete` of the set of IDs that
the mask and the count stand for. -/
@[step] theorem ids_complete_spec (p : fdt.CpuProfile) (ids count : U64) (L : List UInt64)
    (h : IdsRepr ids.val count.val L) :
    fdt.cpus.ids_complete p ids count ⦃ b => b = idsComplete (profileOf p) L ⦄ := by
  have h4 := idsRepr_length_le h
  simp only [idsComplete_eq h, profileOf, byte_toNat, testBit_eq_mod]
  unfold fdt.cpus.ids_complete
  split
  · rename_i h0
    have : count.val = 0 := by scalar_tac
    simp only [spec_ok, this, bne_self_eq_false, Bool.false_and]
  · rename_i h0
    have hc0 : (count.val != 0) = true := by simp only [bne_iff_ne]; scalar_tac
    split
    · scalar_tac
    · simp only [lift, bind_ok]
      step as ⟨i1, hi1, hi1'⟩
      have hcv : (UScalar.cast UScalarTy.U64 p.cpu_counts).val = p.cpu_counts.val := by
        rw [UScalar.cast_val_eq]
        exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (u8_lt p.cpu_counts) (by decide))
      have hbit : (i1 &&& 1#u64).val = (p.cpu_counts.val >>> count.val) % 2 := by
        rw [UScalar.val_and, hi1, hcv]; exact Nat.and_one_is_mod _
      have h4' : decide (count.val ≤ 4) = true := decide_eq_true h4
      simp only [hc0, h4', Bool.true_and]
      split
      · rename_i hz
        have : (p.cpu_counts.val >>> count.val) % 2 = 0 := by rw [← hbit, hz]; rfl
        simp only [spec_ok, this, ne_eq, not_true_eq_false, decide_false, Bool.false_and]
      · rename_i hz
        have hne : (p.cpu_counts.val >>> count.val) % 2 ≠ 0 := fun e =>
          hz (UScalar.eq_of_val_eq (by rw [hbit, e]; rfl))
        step as ⟨i3, hi3, hi3'⟩
        have hi3v : i3.val = 2 ^ count.val := by
          rw [hi3, Nat.shiftLeft_eq, Nat.one_mul, u64_size]
          exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
        have h1 : 1 ≤ i3.val := hi3v ▸ Nat.one_le_two_pow
        step as ⟨i4, hi4⟩
        have hi4v : i4.val = 2 ^ count.val - 1 := by rw [hi4, hi3v]
        simp only [hne, ne_eq, not_false_eq_true, decide_true, Bool.true_and]
        rw [decide_eq_decide]
        exact ⟨fun e => by rw [e, hi4v], fun e => UScalar.eq_of_val_eq (by rw [e, hi4v])⟩

/-! ## The timer interrupts -/

/-- A word read by `u32_at` within the bytes. -/
theorem u32_at_ok {s : Slice U8} {off : Usize} {r : core.result.Result U32 fdt.Error}
    (h : off.val + 4 ≤ s.length)
    (hr : Agrees (fun n N => word32 n = N) errorOf r (u32At (bytesOf s) off.val)) :
    ∃ v, r = .Ok v ∧ v.val = beNat (bytesOf s) off.val 4 := by
  rw [u32At_bytesOf_ok h] at hr
  rcases r with v | e
  · exact ⟨v, rfl, word32_beNat_iff.1 hr⟩
  · exact hr.elim

/-- The loop of `timer_records`: whether every record from `index` on reads as
the private interrupt of its index. -/
theorem timer_records_loop_spec (interrupts : Slice U8) (numbers : Array U32 5#usize)
    (records : Usize) (flags : U32) (ppis : List UInt32) (hlen : ppis.length = records.val)
    (hr : records.val ≤ 5) (hnum : ∀ j < ppis.length, ppis[j]! = word32 numbers.val[j]!)
    (hl : interrupts.length = 12 * records.val) (index : Usize) (hi : index.val ≤ records.val)
    (hpre : ∀ j < index.val, RecordAt interrupts j ppis[j]! (word32 flags)) :
    fdt.cpus.timer_records_loop interrupts numbers records flags index ⦃ b =>
      b = decide (∀ j < ppis.length, RecordAt interrupts j ppis[j]! (word32 flags)) ⦄ := by
  unfold fdt.cpus.timer_records_loop
  apply loop.spec_decr_nat (measure := fun (i : Usize) => records.val - i.val)
    (inv := fun (i : Usize) => i.val ≤ records.val ∧
      ∀ j < i.val, RecordAt interrupts j ppis[j]! (word32 flags))
  · rintro index ⟨hi, hpre⟩
    unfold fdt.cpus.timer_records_loop.body
    split
    · rename_i hlt
      have hlt' : index.val < records.val := (UScalar.lt_equiv _ _).1 hlt
      step as ⟨at_, hat⟩
      have h12 : at_.val = 12 * index.val := by rw [hat, Nat.mul_comm]
      step as ⟨r, r_post⟩
      obtain ⟨kind, rfl, hkind⟩ := u32_at_ok (by omega) r_post
      step as ⟨i, hi4⟩
      step as ⟨r1, r1_post⟩
      obtain ⟨number, rfl, hnumber⟩ := u32_at_ok (by omega) r1_post
      step as ⟨i1, hi8⟩
      step as ⟨r2, r2_post⟩
      obtain ⟨cell, rfl, hcell⟩ := u32_at_ok (by omega) r2_post
      rw [h12] at hkind
      rw [hi4, h12] at hnumber
      rw [hi8, h12] at hcell
      have hj : index.val < ppis.length := by omega
      have hrec : RecordAt interrupts index.val ppis[index.val]! (word32 flags) ↔
          kind.val = 1 ∧ number = numbers.val[index.val]! ∧ cell = flags := by
        rw [RecordAt, ← hkind, ← hnumber, ← hcell, hnum _ hj, word32_toNat, word32_toNat]
        exact and_congr Iff.rfl (and_congr ⟨UScalar.eq_of_val_eq, fun e => e ▸ rfl⟩
          ⟨UScalar.eq_of_val_eq, fun e => e ▸ rfl⟩)
      have hfalse : ¬ RecordAt interrupts index.val ppis[index.val]! (word32 flags) →
          false = decide (∀ j < ppis.length, RecordAt interrupts j ppis[j]! (word32 flags)) := by
        intro hn; symm; rw [decide_eq_false_iff_not]; intro ha; exact hn (ha _ hj)
      simp only
      split
      · rename_i hk1
        step as ⟨i2, hi2⟩
        have hi2' : i2 = numbers.val[index.val]! := by
          rw [hi2]; exact (getElem!_pos _ _ _).symm
        split
        · rename_i hn
          by_cases hc : cell = flags
          · rw [show decide (cell = flags) = true from decide_eq_true hc]
            simp only [bind_ok, ↓reduceIte]
            step as ⟨index1, hidx⟩
            have hr1 : RecordAt interrupts index.val ppis[index.val]! (word32 flags) :=
              hrec.2 ⟨by rw [hk1]; rfl, by rw [hn, hi2'], hc⟩
            refine ⟨by omega, fun j hj' => ?_, by omega⟩
            rcases Nat.lt_or_ge j index.val with h' | h'
            · exact hpre j h'
            · rw [show j = index.val by omega]; exact hr1
          · rw [show decide (cell = flags) = false from decide_eq_false hc]
            simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, spec_ok]
            exact hfalse fun h => hc (hrec.1 h).2.2
        · rename_i hn
          simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, spec_ok]
          exact hfalse fun h => hn (by rw [(hrec.1 h).2.1, hi2'])
      · rename_i hk1
        simp only [bind_ok, Bool.false_eq_true, ↓reduceIte, spec_ok]
        exact hfalse fun h => hk1 (UScalar.eq_of_val_eq (by rw [(hrec.1 h).1]; rfl))
    · rename_i hge
      have : index.val = records.val := by
        have := (UScalar.lt_equiv _ _).not.1 hge; omega
      simp only [spec_ok]
      exact (decide_eq_true (fun j hj => hpre j (by omega))).symm
  · exact ⟨hi, hpre⟩

/-- `timer_records(interrupts, numbers, records, flags)`: whether the bytes are
the records of the private interrupts `ppis`, the first `records` numbers, with
the flags. -/
theorem timer_records_spec (interrupts : Slice U8) (numbers : Array U32 5#usize)
    (records : Usize) (flags : U32) (ppis : List UInt32) (hlen : ppis.length = records.val)
    (hr : records.val ≤ 5) (hnum : ∀ j < ppis.length, ppis[j]! = word32 numbers.val[j]!) :
    fdt.cpus.timer_records interrupts numbers records flags ⦃ b =>
      b = decide ((bytesOf interrupts).toList = timerRecords (word32 flags) ppis) ⦄ := by
  have e : ((bytesOf interrupts).toList = timerRecords (word32 flags) ppis) ↔
      interrupts.length = 12 * records.val ∧
        ∀ j < ppis.length, RecordAt interrupts j ppis[j]! (word32 flags) := by
    rw [records_iff_bytes]
    refine and_congr (by rw [hlen]) ⟨fun h j hj => ?_, fun h j hj => ?_⟩
    · rw [getElem!_pos ppis j hj]; exact h j hj
    · have := h j hj; rwa [getElem!_pos ppis j hj] at this
  simp only [e]
  unfold fdt.cpus.timer_records
  step as ⟨i1, hi1⟩
  split
  · rename_i hne
    have : interrupts.length ≠ 12 * records.val := by
      have := usize_bne_iff.1 hne; rw [Slice.len_val, hi1] at this; omega
    simp only [spec_ok, this, false_and, decide_false]
  · rename_i heq
    have hl : interrupts.length = 12 * records.val := by
      have := (Bool.not_eq_true _).mp heq
      rw [bne_eq_false_iff_eq] at this
      have h' := congrArg (·.val) this
      simp only [Slice.len_val, hi1] at h'
      omega
    simp only [hl, true_and]
    exact timer_records_loop_spec interrupts numbers records flags ppis hlen hr hnum hl 0#usize
      (by simp) (fun j hj => by simp at hj)

/-- The private interrupts of the timer: the first `count` numbers, at most
five. -/
theorem timersOf_list (timer : fdt.TimerInterrupts) :
    (timersOf timer).list.length = min timer.count.val 5 ∧
      ∀ j < (timersOf timer).list.length,
        (timersOf timer).list[j]! = word32 timer.numbers.val[j]! := by
  have hl : (timersOf timer).list.length = min timer.count.val 5 := by
    simp only [TimerInterrupts.list, timersOf, Vector.toList_ofFn, List.length_take,
      List.length_ofFn, byte_toNat]
  refine ⟨hl, fun j hj => ?_⟩
  rw [getElem!_pos _ j hj]
  simp only [TimerInterrupts.list, timersOf, Vector.toList_ofFn, List.getElem_take,
    List.getElem_ofFn]

/-- `CpuTopology::validate_timers(interrupts)`: success exactly when the bytes
are the records of the timer interrupts of the profile, for a supported
topology. -/
theorem validate_timers_spec (t : fdt.CpuTopology) (interrupts : Slice U8)
    (hs : (topologyOf t).Supported) :
    fdt.cpus.CpuTopology.validate_timers t interrupts ⦃ r =>
      Agrees (fun _ _ => True) errorOf r ((topologyOf t).validateTimers (bytesOf interrupts)) ⦄ := by
  obtain ⟨h1, h4, -⟩ := hs
  have hc1 : 1 ≤ t.count.val := by
    have := UInt64.le_iff_toNat_le.1 h1
    simp only [topologyOf, word64_toNat, UInt64.reduceToNat] at this; exact this
  have hc4 : t.count.val ≤ 4 := by
    have := UInt64.le_iff_toNat_le.1 h4
    simp only [topologyOf, word64_toNat, UInt64.reduceToNat] at this; exact this
  have hflags := timerFlags_toNat (c := word64 t.count) (by rw [word64_toNat]; exact hc1)
    (by rw [word64_toNat]; exact hc4)
  rw [word64_toNat] at hflags
  simp only [validateTimers_eq]
  unfold fdt.cpus.CpuTopology.validate_timers
  simp only [topologyOf, profileOf, lift, bind_ok]
  cases ht : t.profile.timer_interrupts with
  | none => simp only [Option.map_none, spec_ok]; rfl
  | some timer =>
    simp only [Option.map_some]
    obtain ⟨hlen, hnum⟩ := timersOf_list timer
    have hrec : (if timer.count > 5#u8 then ok 5#usize else ok (UScalar.cast .Usize timer.count))
        ⦃ r => r.val = min timer.count.val 5 ⦄ := by
      split
      · rename_i hgt
        have := (UScalar.lt_equiv _ _).1 hgt
        simp only [spec_ok, show (5#usize : Usize).val = 5 from rfl,
          show (5#u8 : U8).val = 5 from rfl] at this ⊢
        omega
      · rename_i hle
        have := (UScalar.lt_equiv _ _).not.1 hle
        simp only [spec_ok, U8.cast_Usize_val_eq, show (5#u8 : U8).val = 5 from rfl] at this ⊢
        omega
    step with hrec as ⟨records, hrv⟩
    have hi1 : (UScalar.cast .U32 t.count &&& 31#u32).val = t.count.val := by
      rw [UScalar.val_and, UScalar.cast_val_eq, show (31#u32 : U32).val = 2 ^ 5 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod, show UScalarTy.U32.numBits = 32 from rfl]
      omega
    step as ⟨i2, hi2, hi2'⟩
    have hi2v : i2.val = 2 ^ t.count.val := by
      rw [hi2, hi1, Nat.shiftLeft_eq, Nat.one_mul, u32_size]
      exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
    have h1 : 1 ≤ i2.val := hi2v ▸ Nat.one_le_two_pow
    step as ⟨cpus, hcpus⟩
    step as ⟨i3, hi3, hi3'⟩
    have hp : 2 ^ t.count.val ≤ 2 ^ 4 := Nat.pow_le_pow_right (by omega) hc4
    have hfv : word32 (i3 ||| 4#u32) = timerFlags (word64 t.count) := by
      rw [word32_eq_iff, hflags, UScalar.val_or, hi3, hcpus, hi2v, u32_size, Nat.shiftLeft_eq]
      rw [Nat.mod_eq_of_lt (by
        have : (2 ^ t.count.val - 1) * 2 ^ 8 < 2 ^ 32 := by
          calc (2 ^ t.count.val - 1) * 2 ^ 8 < 2 ^ 4 * 2 ^ 8 :=
                Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
            _ ≤ 2 ^ 32 := by norm_num
        exact this)]
      exact or_add 8 (by norm_num)
    step with timer_records_spec interrupts timer.numbers records (i3 ||| 4#u32)
      (timersOf timer).list (by rw [hlen, hrv]) (by rw [hrv]; omega) hnum as ⟨b, hb⟩
    rw [hfv] at hb
    split
    · rename_i hbt
      have : (bytesOf interrupts).toList = timerRecords (timerFlags (word64 t.count))
          (timersOf timer).list := of_decide_eq_true (hb ▸ hbt)
      simp only [spec_ok, this, ↓reduceIte, agrees_ok_ok]
    · rename_i hbf
      have : ¬ (bytesOf interrupts).toList = timerRecords (timerFlags (word64 t.count))
          (timersOf timer).list := fun h => hbf (hb ▸ decide_eq_true h)
      simp only [spec_ok, this, ↓reduceIte, agrees_err_error]
      rfl

/-! ## One child of `/cpus` -/

/-- `cpu_of_child(structure, strings, node, profile, cells, ids)`: the ID of a
CPU node, none for another child, or the error of `cpuOfChild`, for the IDs
`L` of the CPU nodes before it, which the mask `ids` stands for. -/
theorem cpu_of_child_spec (hu : Usize64) {t : fdt.Fdt} {a : fdt.NodeAt} {N : Node}
    (h : NodeRepr ⟨t, a⟩ N) (p : fdt.CpuProfile) (ids : U64) {m : Nat} {L : List UInt64}
    (hids : IdsRepr ids.val m L) (c : U32) :
    fdt.cpus.cpu_of_child t.structure t.strings a p c ids ⦃ r =>
      Agrees (fun o L' => L' = L ++ o.toList.map word64 ∧
          ∀ id, o = some id → id.val < 4 ∧ word64 id ∉ L) errorOf r
        (cpuOfChild (profileOf p) (word32 c) L N) ⦄ := by
  unfold fdt.cpus.cpu_of_child
  simp only [lift, bind_ok, cpuOfChild_eq]
  step with string_is_spec hu h _ _ "device_type" "cpu" bytes_device_type bytes_cpu as ⟨r, r_post⟩
  refine try_spec r_post (fun e => from_residual_spec e) fun val dt hval _ => ?_
  subst hval
  simp only
  by_cases hdt : dt = some "cpu"
  · subst hdt
    simp only [beq_self_eq_true, bne_self_eq_false, ↓reduceIte, Bool.false_eq_true]
    step with enabled_at_spec hu h as ⟨r1, r1_post⟩
    refine try_spec r1_post (fun e => from_residual_spec e) fun val1 en hval1 _ => ?_
    subst hval1
    simp only
    cases val1
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, spec_ok, agrees_err_error]
      rfl
    · simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true]
      step with string_is_spec hu h _ _ "compatible" "arm,cortex-a76" bytes_compatible
        bytes_cortex_a76 as ⟨r2, r2_post⟩
      refine try_spec r2_post (fun e => from_residual_spec e) fun val2 cp hval2 _ => ?_
      subst hval2
      simp only
      by_cases hcp : cp = some "arm,cortex-a76"
      · subst hcp
        simp only [beq_self_eq_true, bne_self_eq_false, ↓reduceIte, Bool.false_eq_true]
        step with value_at_spec hu h _ "reg" bytes_reg as ⟨o, ho⟩
        rcases o with _ | ⟨st, en⟩ <;> rcases hreg : N.property "reg" with _ | reg <;>
          rw [hreg] at ho
        · simp only [spec_ok, agrees_err_error]; rfl
        · exact ho.elim
        · exact ho.elim
        · obtain ⟨h1, h2, h3⟩ := ho
          dsimp only at h1 h2 h3
          simp only
          step as ⟨s5, hs5⟩
          have hb5 : bytesOf s5 = reg := by rw [bytesOf_of_slice hs5, h3]
          step with cells_u64_spec s5 c as ⟨r3, r3_post⟩
          rw [hb5] at r3_post
          refine try_spec r3_post (fun e => from_residual_spec e) fun val3 aff hval3 _ => ?_
          simp only
          step with id_of_spec p val3 as ⟨o1, ho1⟩
          rw [hval3] at ho1
          rcases o1 with _ | id <;> rcases hid : (profileOf p).idOf aff with _ | x <;>
            rw [hid] at ho1
          · simp only [spec_ok, agrees_err_error]; rfl
          · cases ho1
          · cases ho1
          · simp only [Option.map_some, Option.some.injEq] at ho1
            subst ho1
            have hx4 := idOf_lt hid
            rw [word64_toNat] at hx4
            simp only
            step as ⟨i, hi, hi'⟩
            have hiv : i.val = 2 ^ id.val := by
              rw [hi, Nat.shiftLeft_eq, Nat.one_mul, u64_size]
              exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
            have hand : (ids &&& i).val = ids.val &&& 2 ^ (word64 id).toNat := by
              rw [UScalar.val_and, hiv, word64_toNat]
            split
            · rename_i hne
              have hmem : word64 id ∈ L := by
                by_contra hn
                exact (u64_bne_iff.1 hne) (by rw [hand]; exact (idsRepr_and_eq_zero hids).2 hn)
              simp only [spec_ok, List.contains_iff_mem.2 hmem, ↓reduceIte, agrees_err_error]
              rfl
            · rename_i heq
              have hnmem : word64 id ∉ L := by
                apply (idsRepr_and_eq_zero hids).1
                rw [← hand]
                have := (Bool.not_eq_true _).mp heq
                rw [bne_eq_false_iff_eq] at this
                rw [this]; rfl
              have hc' : L.contains (word64 id) = false := by
                rw [Bool.eq_false_iff, ne_eq, List.contains_iff_mem]; exact hnmem
              simp only [hc', Bool.false_eq_true, ↓reduceIte, ite_or_same, word64_bne_zero]
              have hcpu0 : (profileOf p).cpu0EnableMethod = p.cpu0_enable_method := rfl
              rw [hcpu0]
              split
              · step with string_is_spec hu h _ _ "enable-method" "psci" bytes_enable_method
                  bytes_psci as ⟨r4, r4_post⟩
                refine try_spec r4_post (fun e => from_residual_spec e) fun val4 me hval4 _ => ?_
                subst hval4
                simp only
                by_cases hme : me = some "psci"
                · subst hme
                  simp only [beq_self_eq_true, bne_self_eq_false, ↓reduceIte, Bool.false_eq_true,
                    spec_ok, agrees_ok_ok]
                  exact ⟨by simp, fun id' e => by cases e; exact ⟨hx4, hnmem⟩⟩
                · have e1 : (me == some "psci") = false := by simpa using hme
                  have e2 : (me != some "psci") = true := by simpa using hme
                  simp only [e1, e2, Bool.false_eq_true, ↓reduceIte, spec_ok, agrees_err_error]
                  rfl
              · simp only [spec_ok, agrees_ok_ok]
                exact ⟨by simp, fun id' e => by cases e; exact ⟨hx4, hnmem⟩⟩
      · have e1 : (cp == some "arm,cortex-a76") = false := by simpa using hcp
        have e2 : (cp != some "arm,cortex-a76") = true := by simpa using hcp
        simp only [e1, e2, Bool.false_eq_true, ↓reduceIte, spec_ok, agrees_err_error]
        rfl
  · have e1 : (dt == some "cpu") = false := by simpa using hdt
    have e2 : (dt != some "cpu") = true := by simpa using hdt
    simp only [e1, e2, Bool.false_eq_true, ↓reduceIte, spec_ok, agrees_ok_ok]
    exact ⟨by simp, fun _ e => by cases e⟩

/-! ## The children of `/cpus` -/

/-- The loop of `cpu_children`: from a walker whose walk gives the begin-node
tokens from index `read` on, and a mask and a count that stand for the IDs
`acc` of the CPU nodes before, the IDs of `cpuOfChild` over the children of
`/cpus` from index `read` on. -/
theorem cpu_children_loop_spec (hu : Usize64) {t : fdt.Fdt} {T : Fdt} {L : List Begin}
    (ht : TreeNodes t T L) {k0 : Nat} (hp : k0 < T.records.size) {pa : fdt.NodeAt}
    (hpa : AtRepr pa (L[k0]'(ht.length ▸ hp))) (p : fdt.CpuProfile) (c : U32)
    (ids count : U64) (w : fdt.Walker) (read : Usize) (acc : List UInt64) (f : Nat)
    (st : List Nat) (hacc : IdsRepr ids.val count.val acc) (hk : read.val ≤ L.length)
    (hf : f ≤ MAX_TOKENS.toNat) (hw : WalkerRepr w st)
    (hL : nodesFrom (bytesOf t.structure) (bytesOf t.strings) f w.cursor.val st =
      some (L.drop read.val)) :
    fdt.cpus.cpu_children_loop t.structure t.strings pa p c ids count w read ⦃ r =>
      Agrees (fun (x : U64 × U64) ids' => IdsRepr x.1.val x.2.val ids') errorOf r
        (((T.nodes.drop read.val).filter (·.isChildOf ⟨T, ⟨k0, hp⟩⟩)).foldlM
          (cpuOfChild (profileOf p) (word32 c)) acc) ⦄ := by
  have hLt : L.length < MAX_TOKENS.toNat := (nodesFrom_sorted ht.walk).2.2
  have hnl : T.nodes.length = L.length := by rw [nodes_length, ht.length]
  unfold fdt.cpus.cpu_children_loop
  apply loop.spec_decr_nat
    (measure := fun (x : U64 × U64 × fdt.Walker × Usize) => MAX_TOKENS.toNat - x.2.2.2.val)
    (inv := fun (x : U64 × U64 × fdt.Walker × Usize) => ∃ acc' f' st',
      IdsRepr x.1.val x.2.1.val acc' ∧ x.2.2.2.val ≤ L.length ∧ f' ≤ MAX_TOKENS.toNat ∧
      WalkerRepr x.2.2.1 st' ∧
      nodesFrom (bytesOf t.structure) (bytesOf t.strings) f' x.2.2.1.cursor.val st' =
        some (L.drop x.2.2.2.val) ∧
      ((T.nodes.drop x.2.2.2.val).filter (·.isChildOf ⟨T, ⟨k0, hp⟩⟩)).foldlM
          (cpuOfChild (profileOf p) (word32 c)) acc' =
        ((T.nodes.drop read.val).filter (·.isChildOf ⟨T, ⟨k0, hp⟩⟩)).foldlM
          (cpuOfChild (profileOf p) (word32 c)) acc)
  · rintro ⟨ids, count, w, read⟩ ⟨acc', f', st', hacc, hk, hf, hw, hL, hans⟩
    dsimp only at hacc hk hf hw hL hans
    unfold fdt.cpus.cpu_children_loop.body
    step as ⟨i, hi⟩
    split
    · rename_i hlt
      step with node_step_spec t.structure (bytesOf t.strings) w f' st' _ ht.size hw hf hL
        as ⟨next, found, hpost⟩
      obtain ⟨⟨f2, st2, hf2, hw2, hL2⟩, hend⟩ := hpost
      dsimp only at hw2 hL2 hend
      rw [List.tail_drop] at hL2
      rcases hdrop : L.drop read.val with _ | ⟨b, rest⟩
      · rw [hdrop] at hend
        obtain ⟨rfl, -⟩ := hend
        simp only [spec_ok]
        have : T.nodes.drop read.val = [] := by
          apply List.drop_of_length_le
          have := congrArg List.length hdrop
          simp only [List.length_drop, List.length_nil] at this
          omega
        rw [← hans, this]
        exact hacc
      · rw [hdrop] at hend
        obtain ⟨a, rfl, hat⟩ := hend
        have hkL : read.val < L.length := by
          rcases Nat.lt_or_ge read.val L.length with h' | h'
          · exact h'
          · rw [List.drop_of_length_le h'] at hdrop; cases hdrop
        have hkT : read.val < T.records.size := by rw [← ht.length]; exact hkL
        have hb : b = L[read.val] := by
          rw [List.drop_eq_getElem_cons hkL] at hdrop
          exact (List.cons.inj hdrop).1.symm
        subst hb
        have hrep := (ht.nodeRepr_iff a read.val hkT).2 hat
        have hdT : T.nodes.drop read.val = ⟨T, ⟨read.val, hkT⟩⟩ :: T.nodes.drop (read.val + 1) := by
          rw [List.drop_eq_getElem_cons (by rw [hnl]; exact hkL), nodes_getElem]
        rw [hdT, foldlM_filter_cons] at hans
        simp only
        step as ⟨bc, hbc⟩
        rw [ht.child_iff hkT hp hat hpa] at hbc
        subst hbc
        split
        · rename_i hch
          simp only [hch, ↓reduceIte] at hans
          refine WP.spec_bind (cpu_of_child_spec hu hrep p ids hacc c) fun r r_post => ?_
          rcases r with val | e
          · obtain ⟨acc2, hE, hrel, hnew⟩ := agrees_ok_iff.1 r_post
            rw [hE, except_ok_bind] at hans
            rcases val with _ | id
            · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
              step as ⟨read1, hread1⟩
              simp only [Option.toList_none, List.map_nil, List.append_nil] at hrel
              subst acc2
              refine ⟨⟨acc', f2, st2, by simpa using hacc, by omega, hf2, hw2,
                by rw [hread1]; exact hL2, by rw [hread1]; simpa using hans⟩, by omega⟩
            · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
              obtain ⟨hid4, hnot⟩ := hnew id rfl
              have h4 := idsRepr_length_le hacc
              step as ⟨i1, hi1, hi1'⟩
              step as ⟨ids2, hids2⟩
              step as ⟨count2, hcount2⟩
              step as ⟨read1, hread1⟩
              subst hrel
              have hi1v : i1.val = 2 ^ id.val := by
                rw [hi1, Nat.shiftLeft_eq, Nat.one_mul, u64_size]
                exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))
              have hnew' := idsRepr_snoc hacc (x := word64 id) (by rw [word64_toNat]; exact hid4) hnot
              rw [word64_toNat, ← hi1v, ← UScalar.val_or] at hnew'
              refine ⟨⟨acc' ++ [word64 id], f2, st2, ?_, by omega, hf2, hw2,
                by rw [hread1]; exact hL2, by rw [hread1]; simpa using hans⟩, by omega⟩
              rw [hcount2, hids2]; simpa using hnew'
          · have hE := agrees_err_iff.1 r_post
            rw [hE] at hans
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            step with from_residual_spec e as ⟨r1, hr1⟩
            subst hr1
            rw [← hans]
            rfl
        · rename_i hch
          simp only [hch, Bool.false_eq_true, ↓reduceIte] at hans
          step as ⟨read1, hread1⟩
          refine ⟨⟨acc', f2, st2, hacc, by omega, hf2, hw2, by rw [hread1]; exact hL2,
            by rw [hread1]; exact hans⟩, by omega⟩
    · rename_i hge
      exact absurd ((UScalar.lt_equiv _ _).2 (by omega)) hge
  · exact ⟨acc, f, st, hacc, hk, hf, hw, hL, rfl⟩

/-- `cpu_children(structure, strings, cpus, profile, cells)`: the IDs of
`cpuOfChild` over the children of the node, in tree order, as a mask and a
count. -/
theorem cpu_children_spec (hu : Usize64) {t : fdt.Fdt} {T : Fdt} (hT : FdtRepr t T)
    {a : fdt.NodeAt} {C : Node} (h : NodeRepr ⟨t, a⟩ C) (p : fdt.CpuProfile) (c : U32) :
    fdt.cpus.cpu_children t.structure t.strings a p c ⦃ r =>
      Agrees (fun (x : U64 × U64) ids' => IdsRepr x.1.val x.2.val ids') errorOf r
        ((T.nodes.filter (·.isChildOf C)).foldlM (cpuOfChild (profileOf p) (word32 c)) []) ⦄ := by
  obtain ⟨L, ht⟩ := treeNodes_of_repr hu hT
  obtain ⟨k, hk, rfl, hat⟩ := ht.of_nodeRepr h
  unfold fdt.cpus.cpu_children
  have := cpu_children_loop_spec hu ht hk hat p c 0#u64 0#u64 fdt.nodes.START 0#usize [] MAX_TOKENS.toNat
    [] idsRepr_nil (by simp) (Nat.le_refl _) start_repr.1 (by rw [start_repr.2]; simpa using ht.walk)
  simpa using this

/-! ## The discovery -/

/-- `find_path(structure, path)` for the bytes of a valid path: the node of
`Fdt.findNode`. -/
theorem find_path_valid_spec {t : fdt.Fdt} {T : Fdt} {L : List Begin} (ht : TreeNodes t T L)
    (path : Slice U8) (s : String) (hb : path.val.map byte = utf8Bytes s.toList)
    (hv : pathValidB (utf8Bytes s.toList) = true) (hl : path.length < Usize.max) :
    fdt.nodes.find_path t.structure path ⦃ r =>
      Agrees (OptionRel (fun a N => NodeRepr ⟨t, a⟩ N)) errorOf r (T.findNode s) ⦄ := by
  have hne : 1 ≤ path.length := by
    have h0 := hv
    rw [← hb] at h0
    simp only [pathValidB, Bool.and_eq_true, beq_iff_eq] at h0
    show 1 ≤ path.val.length
    cases hq : path.val with
    | nil => rw [hq] at h0; simp at h0
    | cons x xs => simp
  have := find_path_spec ht path hl hne
  rw [findNode_eq, hv, ← hb]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.length_map]
  exact this

/-- `Fdt::discover_cpus(profile)`: the statement `FdtDiscoverCpus`. -/
theorem discover_cpus_spec (hu : Usize64) (t : fdt.Fdt) (T : Fdt) (profile : fdt.CpuProfile)
    (h : FdtRepr t T) :
    fdt.cpus.Fdt.discover_cpus t profile ⦃ r =>
      Agrees (fun c C => topologyOf c = C) errorOf r (T.discoverCpus (profileOf profile)) ⦄ := by
  obtain ⟨L, ht⟩ := treeNodes_of_repr hu h
  have hl5 : ∀ s : Slice U8, s.length = 5 → s.length < Usize.max := fun s hs => by
    rw [hs, usize_max hu]; norm_num
  unfold fdt.cpus.Fdt.discover_cpus
  simp only [lift, bind_ok, discoverCpus_eq]
  step with find_path_valid_spec ht _ "/cpus" path_cpus valid_cpus (hl5 _ rfl) as ⟨r, r_post⟩
  refine try_spec r_post (fun e => from_residual_spec e) fun val o hval _ => ?_
  simp only
  rcases val with _ | cpus <;> rcases o with _ | C
  · simp only [spec_ok, agrees_err_error]; rfl
  · exact hval.elim
  · exact hval.elim
  simp only [optionRel_some_some] at hval
  step with enabled_at_spec hu hval as ⟨r1, r1_post⟩
  refine try_spec r1_post (fun e => from_residual_spec e) fun val1 en hval1 _ => ?_
  subst hval1
  simp only
  cases val1
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, spec_ok, agrees_err_error]; rfl
  simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true]
  step with size_cells_at_spec hu hval as ⟨r2, r2_post⟩
  refine try_spec r2_post (fun e => from_residual_spec e) fun val2 sc hval2 _ => ?_
  subst hval2
  simp only [word32_bne_zero]
  split
  · simp only [spec_ok, agrees_err_error]; rfl
  step with address_cells_at_spec hu hval as ⟨r3, r3_post⟩
  refine try_spec r3_post (fun e => from_residual_spec e) fun val3 cells hval3 _ => ?_
  subst hval3
  simp only [ite_and_same, ← cells_test]
  split
  · simp only [spec_ok, agrees_err_error]; rfl
  step with cpu_children_spec hu h hval profile val3 as ⟨r4, r4_post⟩
  refine try_spec r4_post (fun e => from_residual_spec e) fun val4 ids hval4 _ => ?_
  rcases val4 with ⟨mask, count⟩
  simp only [uncurry_apply_pair]
  step with ids_complete_spec profile mask count ids hval4 as ⟨b, hb⟩
  subst hb
  split
  rotate_left
  · rename_i hn
    simp only [(Bool.not_eq_true _).mp hn, Bool.not_false, ↓reduceIte, spec_ok, agrees_err_error]
    rfl
  rename_i hcomp
  simp only [hcomp, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  step with find_path_valid_spec ht _ "/psci" path_psci valid_psci (hl5 _ rfl) as ⟨r5, r5_post⟩
  refine try_spec r5_post (fun e => from_residual_spec e) fun val5 o5 hval5 _ => ?_
  simp only
  rcases val5 with _ | psci <;> rcases o5 with _ | P
  · simp only [spec_ok, agrees_err_error]; rfl
  · exact hval5.elim
  · exact hval5.elim
  simp only [optionRel_some_some] at hval5
  step with enabled_at_spec hu hval5 as ⟨r6, r6_post⟩
  refine try_spec r6_post (fun e => from_residual_spec e) fun val6 en6 hval6 _ => ?_
  subst hval6
  simp only
  cases val6
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, spec_ok, agrees_err_error]; rfl
  simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true]
  step as ⟨pc, hpc⟩
  step with method_is_spec hu hval5 pc as ⟨r7, r7_post⟩
  rw [hpc] at r7_post
  refine try_spec r7_post (fun e => from_residual_spec e) fun val7 m hval7 _ => ?_
  subst hval7
  simp only
  split
  rotate_left
  · rename_i hm
    have : (m != some (profileOf profile).conduit.name) = true := by
      rw [bne_iff_ne]; intro e; apply hm; rw [e]; exact beq_self_eq_true _
    simp only [this, ↓reduceIte, spec_ok, agrees_err_error]; rfl
  rename_i hm
  have : (m != some (profileOf profile).conduit.name) = false := by
    rw [bne_eq_false_iff_eq]; exact beq_iff_eq.1 hm
  simp only [this, Bool.false_eq_true, ↓reduceIte]
  step with value_at_spec hu hval5 _ "compatible" bytes_compatible as ⟨o, ho⟩
  step with psci_compatible_spec t.structure o _ ho as ⟨b1, hb1⟩
  subst hb1
  split
  · rename_i hy
    simp only [hy, Bool.not_true, Bool.false_eq_true, ↓reduceIte, spec_ok, agrees_ok_ok]
    simp only [topologyOf, CpuTopology.mk.injEq, true_and]
    rw [word64_eq_iff, hval4.2.2.2, UInt64.toNat_ofNat_of_lt']
    have := idsRepr_length_le hval4
    exact Nat.lt_of_le_of_lt (hval4.2.2.2 ▸ this) (by decide)
  · rename_i hy
    simp only [(Bool.not_eq_true _).mp hy, Bool.not_false, ↓reduceIte, spec_ok, agrees_err_error]
    rfl

end Krepi.Proofs.Fdt.Refinement
