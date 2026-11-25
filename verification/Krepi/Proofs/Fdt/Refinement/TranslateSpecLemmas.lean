module

public import Krepi.Proofs.Fdt.Refinement.BasicLemmas

/-!
# Device tree: lemmas about the specification of the address translation

Lemmas about `Krepi.Spec.Fdt.Translate` and about the `?` operator of the
code, for the refinement proofs of the regions and address maps. The module
imports no generated definitions, so it is built once and not again for every
mutant of the code.

- The `?` operator as one step of a proof: `try_spec` (a call whose result
  agrees with a step of the specification continues on a related value, and
  its failure agrees with the failure of the block that starts with that
  step) with `from_residual_spec`, the result of `from_residual` on a
  failure; `agrees_ok_eq`, `except_ok_bind`, `except_error_bind` and
  `bind_ite_ok`.
- Results whose value is not compared: `agrees_true_map` and
  `agrees_true_mapM_cons`, the agreement with a `mapM` after an entry that
  succeeds.
- Lists and entries: `mapM_cons_ok`, `mapM_cons_error`, `mapM_cons_eq_ok`,
  `mapM_ok_length`, `chunks_length`, `chunks_cons` and `chunks_nil` (the
  entries from an offset), `add_stride_le` (an offset that is a multiple of
  the stride below a length that is one leaves room for a whole entry),
  `slice_lt_len` and `slice_len_le` (a loop index against the length of a
  slice), and `bytesOf_slice` (the bytes of a range of a slice).
- Cells: `word32_beq_iff`.
- Entries: `regEntry_extract` and `window_extract`, one entry of a value read
  from its own bytes.
- `Reg.new`: `regNew_word32` (its checks on the numbers of the cells),
  `regNew_unsupported`, `regNew_badProperty`, `regNew_entries` and
  `regNew_ok` (what a success gives).
- `AddressMap.new`: `addressMapNew_word32`, `addressMapNew_unsupported`,
  `addressMapNew_none`, `addressMapNew_empty`, `addressMapNew_badProperty`,
  `addressMapNew_windows`, `addressMapNew_ok` (what a success gives),
  `mapM_chunks_ne_nil` and `addressMapNew_kind`.
- `AddressMap.translate`: `translate_eq`.
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP
open Krepi.Statements Krepi.Spec.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## The `?` operator -/

/-- `from_residual` of a failure returns the failure. -/
theorem from_residual_spec {γ ε : Type} (e : ε) :
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual γ
      (core.convert.FromSame ε) (.Err e) ⦃ out => out = .Err e ⦄ := by
  simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- The `?` operator as one step of a proof: the code `branch r >>= C` of
`f(..)?`, whose result `r` agrees with the step `E` of the specification,
agrees with the block `E >>= k` when the continuation on a success agrees
with `k` of the related value, and `C` returns the failure on a failure (the
`from_residual` of the code, `from_residual_spec`). -/
theorem try_spec {α β γ δ ε ε' : Type} {rel : α → β → Prop} {rel' : γ → δ → Prop}
    {err : ε → ε'} {r : core.result.Result α ε} {E : Except ε' β} {k : β → Except ε' δ}
    {C : core.ops.control_flow.ControlFlow (core.result.Result Never ε) α →
      Result (core.result.Result γ ε)}
    (hr : Agrees rel err r E)
    (he : ∀ e, C (.Break (.Err e)) ⦃ out => out = .Err e ⦄)
    (hk : ∀ a b, rel a b → E = .ok b → C (.Continue a) ⦃ out => Agrees rel' err out (k b) ⦄) :
    (core.result.Result.Insts.CoreOpsTry.branch r >>= C) ⦃ out =>
      Agrees rel' err out (E >>= k) ⦄ := by
  cases r with
  | Ok a =>
    obtain ⟨b, hE, hab⟩ := agrees_ok_iff.mp hr
    subst hE
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
    exact hk a b hab rfl
  | Err e =>
    rw [agrees_err_iff] at hr; subst hr
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
    exact spec_mono (he e) (fun out h => by subst h; rfl)

/-- A success that agrees through a function is the success of its image. -/
theorem agrees_ok_eq {α β ε ε' : Type} {f : α → β} {err : ε → ε'} {a : α} {E : Except ε' β}
    (h : Agrees (fun a b => f a = b) err (.Ok a) E) : E = .ok (f a) := by
  obtain ⟨b, hE, hb⟩ := agrees_ok_iff.mp h; rw [hE, hb]

theorem except_ok_bind {ε α β : Type} (a : α) (k : α → Except ε β) :
    ((.ok a : Except ε α) >>= k) = k a := rfl

theorem except_error_bind {ε α β : Type} (e : ε) (k : α → Except ε β) :
    ((.error e : Except ε α) >>= k) = .error e := rfl

/-- A bind on a choice of two values. -/
theorem bind_ite_ok {α β : Type} (c : Bool) (a b : α) (f : α → Result β) :
    Std.bind (if c then Result.ok a else Result.ok b) f = f (if c then a else b) := by
  cases c <;> simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]

/-! ## Results whose value is not compared -/

/-- The agreement of a result whose value is not compared does not see a map
of the specification's value. -/
theorem agrees_true_map {α β γ ε ε' : Type} {err : ε → ε'} {r : core.result.Result α ε}
    {E : Except ε' β} {g : β → γ} :
    Agrees (fun _ _ => True) err r (g <$> E) ↔ Agrees (fun _ _ => True) err r E := by
  cases r <;> cases E <;> rfl

/-- After an entry that succeeds, the agreement with a `mapM` is that with the
`mapM` of the rest. -/
theorem agrees_true_mapM_cons {α β δ ε ε' : Type} {err : ε → ε'} {f : α → Except ε' β}
    {a : α} {l : List α} {b : β} (h : f a = .ok b) {r : core.result.Result δ ε} :
    Agrees (fun _ (_ : List β) => True) err r ((a :: l).mapM f) ↔
      Agrees (fun _ (_ : List β) => True) err r (l.mapM f) := by
  rw [List.mapM_cons, h, except_ok_bind]
  cases r <;> cases l.mapM f <;> rfl

/-! ## Lists and entries -/

theorem mapM_cons_ok {α β ε : Type} {f : α → Except ε β} {a : α} {l : List α} {b : β}
    {m : List β} : (a :: l).mapM f = .ok (b :: m) ↔ f a = .ok b ∧ l.mapM f = .ok m := by
  rw [List.mapM_cons]
  cases f a <;> cases l.mapM f <;> simp [except_ok_bind, except_error_bind, pure, Except.pure]

theorem mapM_cons_error {α β ε : Type} {f : α → Except ε β} {a : α} {l : List α} {e : ε}
    (h : f a = .error e) : (a :: l).mapM f = .error e := by
  rw [List.mapM_cons, h, except_error_bind]

/-- A `mapM` that succeeds on a nonempty list. -/
theorem mapM_cons_eq_ok {α β ε : Type} {f : α → Except ε β} {a : α} {l : List α}
    {m : List β} (h : (a :: l).mapM f = .ok m) :
    ∃ b m', m = b :: m' ∧ f a = .ok b ∧ l.mapM f = .ok m' := by
  rw [List.mapM_cons] at h
  cases ha : f a <;> cases hl : l.mapM f <;> rw [ha, hl] at h <;> cases h
  exact ⟨_, _, rfl, rfl, rfl⟩

theorem mapM_ok_length {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {m : List β}, l.mapM f = .ok m → m.length = l.length
  | [], m, h => by simp [pure, Except.pure] at h; subst h; rfl
  | a :: l, m, h => by
    rw [List.mapM_cons] at h
    cases ha : f a <;> cases hl : l.mapM f <;>
      simp [ha, hl, except_ok_bind, except_error_bind, pure, Except.pure] at h
    subst h; simp [mapM_ok_length hl]

theorem chunks_length (b : ByteArray) (stride : Nat) :
    ∀ n pos, (chunks b stride n pos).length = n
  | 0, _ => rfl
  | n + 1, pos => by simp only [chunks, List.length_cons, chunks_length b stride n]

/-- The entries of `stride` bytes from `pos` to a length `len`: the entry at
`pos` and those after it, when a whole entry fits. -/
theorem chunks_cons {b : ByteArray} {len stride pos : Nat} (hs : 0 < stride)
    (h : pos + stride ≤ len) :
    chunks b stride ((len - pos) / stride) pos =
      b.extract pos (pos + stride) ::
        chunks b stride ((len - (pos + stride)) / stride) (pos + stride) := by
  rw [show len - pos = (len - (pos + stride)) + stride by omega, Nat.add_div_right _ hs]
  rfl

/-- No entries from `pos` when a whole entry does not fit. -/
theorem chunks_nil {b : ByteArray} {len stride pos : Nat} (hs : 0 < stride)
    (h : len < pos + stride) : chunks b stride ((len - pos) / stride) pos = [] := by
  rw [Nat.div_eq_of_lt (by omega)]; rfl

/-- An offset that is a multiple of `s`, below a length that is one, leaves
room for `s` bytes. -/
theorem add_stride_le {a b s : Nat} (ha : a % s = 0) (hb : b % s = 0) (h : a < b) :
    a + s ≤ b := by
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mod_eq_zero ha
  obtain ⟨m, rfl⟩ := Nat.dvd_of_mod_eq_zero hb
  have : k < m := Nat.lt_of_mul_lt_mul_left h
  calc s * k + s = s * (k + 1) := by rw [Nat.mul_succ]
    _ ≤ s * m := Nat.mul_le_mul_left _ this

/-- An index below the length of a slice, read as numbers. -/
theorem slice_lt_len {α : Type} {s : Slice α} {i : Usize} (h : i < s.len) : i.val < s.length := by
  rw [UScalar.lt_equiv, Slice.len_val] at h; exact h

/-- An index not below the length of a slice, read as numbers. -/
theorem slice_len_le {α : Type} {s : Slice α} {i : Usize} (h : ¬ i < s.len) :
    s.length ≤ i.val := by
  rw [UScalar.lt_equiv, Slice.len_val] at h; omega

/-- The bytes of the range `[i, j)` of a slice. -/
theorem bytesOf_slice {s b : Slice U8} {i j : Nat} (h : s.val = b.val.slice i j) :
    bytesOf s = (bytesOf b).extract i j := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_extract, Array.toList_extract, bytesOf_data_toList, bytesOf_data_toList, h,
    List.slice, List.extract_eq_take_drop, List.map_take, List.map_drop]

/-! ## Cells -/

theorem word32_beq_iff (x : U32) (n : UInt32) : (word32 x == n) = decide (x.val = n.toNat) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, word32_eq_iff]

/-! ## Entries -/

/-- One entry of a `reg` within bytes `b`, read from the bytes of its two
numbers. -/
theorem regEntry_extract {b : ByteArray} {ac sc : UInt32} {p q r : Nat}
    (hq : q = p + ac.toNat * 4) (hr : r = q + sc.toNat * 4) (hb : r ≤ b.size) :
    regEntry ac sc (b.extract p r) = (do
      let start ← cellsU64 (b.extract p q) ac
      let size ← cellsU64 (b.extract q r) sc
      let span ← Span.new start size
      checkWidth span ac
      pure span) := by
  simp only [regEntry, ByteArray.extract_extract, ByteArray.size_extract, Nat.add_zero]
  rw [Nat.min_eq_left hb, Nat.min_eq_left (by omega), Nat.add_sub_cancel' (by omega),
    Nat.min_eq_left (by omega), ← hq]

/-- One window of a map within bytes `b`, read from the bytes of its three
numbers. -/
theorem window_extract {b : ByteArray} {cc pc sc : UInt32} {p q r t : Nat}
    (hq : q = p + cc.toNat * 4) (hr : r = q + pc.toNat * 4) (ht : t = r + sc.toNat * 4)
    (hb : t ≤ b.size) :
    window cc pc sc (b.extract p t) = (do
      let child ← cellsU64 (b.extract p q) cc
      let parent ← cellsU64 (b.extract q r) pc
      let size ← cellsU64 (b.extract r t) sc
      if size = 0 then .error .emptyRegion else do
        let childSpan ← Span.new child size
        let parentSpan ← Span.new parent size
        checkWidth childSpan cc
        checkWidth parentSpan pc
        pure ⟨childSpan, parentSpan⟩) := by
  simp only [window, ByteArray.extract_extract, ByteArray.size_extract, Nat.add_zero]
  rw [Nat.min_eq_left hb, Nat.min_eq_left (by omega), Nat.min_eq_left (by omega),
    Nat.add_sub_cancel' (by omega), Nat.min_eq_left (by omega), ← hq,
    show p + (cc.toNat * 4 + pc.toNat * 4) = r by omega]
  rfl

/-! ## `Reg.new` -/

/-- `Reg.new` of cells of the code: the checks of the cells and of the length,
then the entries. -/
theorem regNew_word32 (b : ByteArray) (ac sc : U32) :
    Reg.new b (word32 ac) (word32 sc) =
      if ¬ ((ac.val = 1 ∨ ac.val = 2) ∧ sc.val ≤ 2) then .error .unsupportedCells
      else if b.size = 0 ∨ b.size % ((ac.val + sc.val) * 4) ≠ 0 then .error .badProperty
      else (fun e => ⟨e⟩) <$> (chunks b ((ac.val + sc.val) * 4)
        (b.size / ((ac.val + sc.val) * 4)) 0).mapM (regEntry (word32 ac) (word32 sc)) := by
  unfold Reg.new
  simp only [word32_beq_iff, word32_toNat, UInt32.reduceToNat]
  by_cases h1 : (ac.val = 1 ∨ ac.val = 2) ∧ sc.val ≤ 2
  · have h1' : ¬ (!(decide (ac.val = 1) || decide (ac.val = 2)) || decide (2 < sc.val)) =
        true := by
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
        decide_eq_false_iff_not, decide_eq_true_eq, not_or, not_and, not_lt]; omega
    simp only [h1', h1, ↓reduceIte, Bool.false_eq_true]
    by_cases h2 : b.size = 0 ∨ b.size % ((ac.val + sc.val) * 4) ≠ 0
    · have h2' : (b.size == 0 || b.size % ((ac.val + sc.val) * 4) != 0) = true := by
        simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]; exact h2
      simp only [h2', h2, ↓reduceIte]; rfl
    · have h2' : ¬ (b.size == 0 || b.size % ((ac.val + sc.val) * 4) != 0) = true := by
        simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]; exact h2
      simp only [h2', h2, ↓reduceIte, Bool.false_eq_true, and_self, not_true_eq_false,
        map_eq_pure_bind]
  · have h1' : (!(decide (ac.val = 1) || decide (ac.val = 2)) || decide (2 < sc.val)) =
        true := by
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
        decide_eq_false_iff_not, decide_eq_true_eq]; omega
    simp only [h1', h1, not_false_eq_true, ↓reduceIte]; rfl

theorem regNew_unsupported (b : Slice U8) {ac sc : U32}
    (h : ¬ ((ac.val = 1 ∨ ac.val = 2) ∧ sc.val ≤ 2)) :
    Reg.new (bytesOf b) (word32 ac) (word32 sc) = .error .unsupportedCells := by
  rw [regNew_word32]; simp only [h, not_false_eq_true, ↓reduceIte]

theorem regNew_badProperty {b : Slice U8} {ac sc : U32}
    (h1 : (ac.val = 1 ∨ ac.val = 2) ∧ sc.val ≤ 2)
    (h2 : b.length = 0 ∨ b.length % ((ac.val + sc.val) * 4) ≠ 0) :
    Reg.new (bytesOf b) (word32 ac) (word32 sc) = .error .badProperty := by
  rw [regNew_word32, bytesOf_size]; simp only [h1, h2, and_self, not_true_eq_false, ↓reduceIte]

theorem regNew_entries {b : Slice U8} {ac sc : U32}
    (h1 : (ac.val = 1 ∨ ac.val = 2) ∧ sc.val ≤ 2)
    (h2 : ¬ (b.length = 0 ∨ b.length % ((ac.val + sc.val) * 4) ≠ 0)) :
    Reg.new (bytesOf b) (word32 ac) (word32 sc) = (fun e => ⟨e⟩) <$>
      (chunks (bytesOf b) ((ac.val + sc.val) * 4) (b.length / ((ac.val + sc.val) * 4)) 0).mapM
        (regEntry (word32 ac) (word32 sc)) := by
  rw [regNew_word32, bytesOf_size]; simp only [h1, h2, and_self, not_true_eq_false, ↓reduceIte]

/-- A success of `Reg.new`: cells of 1 or 2 addresses and at most 2 sizes, a
nonempty value of whole entries, and the entries that every entry gave. -/
theorem regNew_ok {b : ByteArray} {ac sc : U32} {R : Reg}
    (h : Reg.new b (word32 ac) (word32 sc) = .ok R) :
    (ac.val = 1 ∨ ac.val = 2) ∧ sc.val ≤ 2 ∧ b.size ≠ 0 ∧ b.size % ((ac.val + sc.val) * 4) = 0 ∧
      (chunks b ((ac.val + sc.val) * 4) (b.size / ((ac.val + sc.val) * 4)) 0).mapM
        (regEntry (word32 ac) (word32 sc)) = .ok R.entries := by
  rw [regNew_word32] at h
  split at h
  · cases h
  split at h
  · cases h
  rename_i h1 h2
  simp only [not_not] at h1
  simp only [not_or, not_not] at h2
  refine ⟨h1.1, h1.2, h2.1, h2.2, ?_⟩
  cases hm : (chunks b ((ac.val + sc.val) * 4) (b.size / ((ac.val + sc.val) * 4)) 0).mapM
    (regEntry (word32 ac) (word32 sc)) with
  | error e => rw [hm] at h; cases h
  | ok l => rw [hm] at h; cases h; rfl

/-! ## `AddressMap.new` -/

/-- `AddressMap.new` of cells of the code: the checks of the cells, then the
windows of a value that is present and not empty. -/
theorem addressMapNew_word32 (b : Option ByteArray) (cc pc sc : U32) :
    AddressMap.new b (word32 cc) (word32 pc) (word32 sc) =
      if ¬ ((cc.val = 1 ∨ cc.val = 2) ∧ (pc.val = 1 ∨ pc.val = 2) ∧ sc.val ≤ 2) then
        .error .unsupportedCells
      else (fun w => AddressMap.mk w (word32 cc) (word32 pc) (word32 sc)) <$>
        match b with
        | none => .ok none
        | some v =>
          if v.size = 0 then .ok (some [])
          else if sc.val = 0 ∨ v.size % ((cc.val + pc.val + sc.val) * 4) ≠ 0 then
            .error .badProperty
          else some <$> (chunks v ((cc.val + pc.val + sc.val) * 4)
            (v.size / ((cc.val + pc.val + sc.val) * 4)) 0).mapM
              (window (word32 cc) (word32 pc) (word32 sc)) := by
  unfold AddressMap.new
  simp only [word32_beq_iff, word32_toNat, UInt32.reduceToNat]
  by_cases h1 : (cc.val = 1 ∨ cc.val = 2) ∧ (pc.val = 1 ∨ pc.val = 2) ∧ sc.val ≤ 2
  · have h1' : ¬ (!(decide (cc.val = 1) || decide (cc.val = 2)) ||
        !(decide (pc.val = 1) || decide (pc.val = 2)) || decide (2 < sc.val)) = true := by
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
        decide_eq_false_iff_not, decide_eq_true_eq, not_or, not_and, not_lt]; omega
    simp only [h1', h1, ↓reduceIte, Bool.false_eq_true, and_self, not_true_eq_false]
    cases b with
    | none => rfl
    | some v =>
      by_cases h0 : v.size = 0
      · simp only [h0, ↓reduceIte]; rfl
      · by_cases h2 : sc.val = 0 ∨ v.size % ((cc.val + pc.val + sc.val) * 4) ≠ 0
        · have h2' : (decide (sc.val = 0) || v.size % ((cc.val + pc.val + sc.val) * 4) != 0) =
              true := by
            simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]; exact h2
          simp only [h0, h2', h2, ↓reduceIte]; rfl
        · have h2' : ¬ (decide (sc.val = 0) ||
              v.size % ((cc.val + pc.val + sc.val) * 4) != 0) = true := by
            simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]; exact h2
          simp only [h0, h2', h2, ↓reduceIte, Bool.false_eq_true]
          simp only [map_eq_pure_bind, bind_assoc, pure_bind]
  · have h1' : (!(decide (cc.val = 1) || decide (cc.val = 2)) ||
        !(decide (pc.val = 1) || decide (pc.val = 2)) || decide (2 < sc.val)) = true := by
      simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
        decide_eq_false_iff_not, decide_eq_true_eq]; omega
    simp only [h1', h1, not_false_eq_true, ↓reduceIte]; rfl

theorem addressMapNew_unsupported (b : Option ByteArray) {cc pc sc : U32}
    (h : ¬ ((cc.val = 1 ∨ cc.val = 2) ∧ (pc.val = 1 ∨ pc.val = 2) ∧ sc.val ≤ 2)) :
    AddressMap.new b (word32 cc) (word32 pc) (word32 sc) = .error .unsupportedCells := by
  rw [addressMapNew_word32]; simp only [h, not_false_eq_true, ↓reduceIte]

theorem addressMapNew_none {cc pc sc : U32}
    (h : (cc.val = 1 ∨ cc.val = 2) ∧ (pc.val = 1 ∨ pc.val = 2) ∧ sc.val ≤ 2) :
    AddressMap.new none (word32 cc) (word32 pc) (word32 sc) =
      .ok ⟨none, word32 cc, word32 pc, word32 sc⟩ := by
  rw [addressMapNew_word32]; simp only [h, and_self, not_true_eq_false, ↓reduceIte]; rfl

theorem addressMapNew_empty {v : ByteArray} {cc pc sc : U32}
    (h : (cc.val = 1 ∨ cc.val = 2) ∧ (pc.val = 1 ∨ pc.val = 2) ∧ sc.val ≤ 2) (h0 : v.size = 0) :
    AddressMap.new (some v) (word32 cc) (word32 pc) (word32 sc) =
      .ok ⟨some [], word32 cc, word32 pc, word32 sc⟩ := by
  rw [addressMapNew_word32]; simp only [h, h0, and_self, not_true_eq_false, ↓reduceIte]; rfl

theorem addressMapNew_badProperty {v : ByteArray} {cc pc sc : U32}
    (h : (cc.val = 1 ∨ cc.val = 2) ∧ (pc.val = 1 ∨ pc.val = 2) ∧ sc.val ≤ 2) (h0 : v.size ≠ 0)
    (h2 : sc.val = 0 ∨ v.size % ((cc.val + pc.val + sc.val) * 4) ≠ 0) :
    AddressMap.new (some v) (word32 cc) (word32 pc) (word32 sc) = .error .badProperty := by
  rw [addressMapNew_word32]; simp only [h, h0, h2, and_self, not_true_eq_false, ↓reduceIte]; rfl

theorem addressMapNew_windows {v : ByteArray} {cc pc sc : U32}
    (h : (cc.val = 1 ∨ cc.val = 2) ∧ (pc.val = 1 ∨ pc.val = 2) ∧ sc.val ≤ 2) (h0 : v.size ≠ 0)
    (h2 : ¬ (sc.val = 0 ∨ v.size % ((cc.val + pc.val + sc.val) * 4) ≠ 0)) :
    AddressMap.new (some v) (word32 cc) (word32 pc) (word32 sc) =
      (fun w => AddressMap.mk w (word32 cc) (word32 pc) (word32 sc)) <$> (some <$>
        (chunks v ((cc.val + pc.val + sc.val) * 4)
          (v.size / ((cc.val + pc.val + sc.val) * 4)) 0).mapM
            (window (word32 cc) (word32 pc) (word32 sc))) := by
  rw [addressMapNew_word32]; simp only [h, h0, h2, and_self, not_true_eq_false, ↓reduceIte]

/-- A success of `AddressMap.new`: the cells that it checked, and the windows
of the value: none when it is absent, the empty list when it is empty, and
otherwise the windows that every window of a value of whole windows gave. -/
theorem addressMapNew_ok {b : Option ByteArray} {cc pc sc : U32} {M : AddressMap}
    (h : AddressMap.new b (word32 cc) (word32 pc) (word32 sc) = .ok M) :
    (cc.val = 1 ∨ cc.val = 2) ∧ (pc.val = 1 ∨ pc.val = 2) ∧ sc.val ≤ 2 ∧
      M.childCells = word32 cc ∧ M.parentCells = word32 pc ∧ M.sizeCells = word32 sc ∧
      match (generalizing := false) b with
      | none => M.windows = none
      | some v =>
        if v.size = 0 then M.windows = some []
        else sc.val ≠ 0 ∧ v.size % ((cc.val + pc.val + sc.val) * 4) = 0 ∧
          ∃ ws, (chunks v ((cc.val + pc.val + sc.val) * 4)
            (v.size / ((cc.val + pc.val + sc.val) * 4)) 0).mapM
              (window (word32 cc) (word32 pc) (word32 sc)) = .ok ws ∧ M.windows = some ws := by
  rw [addressMapNew_word32] at h
  split at h
  · cases h
  rename_i h1
  rw [not_not] at h1
  refine ⟨h1.1, h1.2.1, h1.2.2, ?_⟩
  cases b with
  | none => cases h; exact ⟨rfl, rfl, rfl, rfl⟩
  | some v =>
    simp only at h
    split at h
    · cases h; rename_i h0; refine ⟨rfl, rfl, rfl, ?_⟩; simp only [h0, ↓reduceIte]
    rename_i h0
    split at h
    · cases h
    rename_i h2
    simp only [not_or, not_not] at h2
    simp only [h0, ↓reduceIte]
    cases hm : (chunks v ((cc.val + pc.val + sc.val) * 4)
        (v.size / ((cc.val + pc.val + sc.val) * 4)) 0).mapM
          (window (word32 cc) (word32 pc) (word32 sc)) with
    | error e => rw [hm] at h; cases h
    | ok ws => rw [hm] at h; cases h; exact ⟨rfl, rfl, rfl, h2.1, h2.2, ws, rfl, rfl⟩

/-- The windows of a nonempty value of whole windows are not empty. -/
theorem mapM_chunks_ne_nil {α ε : Type} {f : ByteArray → Except ε α} {v : ByteArray} {s : Nat}
    {ws : List α} (hs : 0 < s) (h0 : v.size ≠ 0) (hd : v.size % s = 0)
    (hm : (chunks v s (v.size / s) 0).mapM f = .ok ws) : ws ≠ [] := by
  have hl := mapM_ok_length hm
  rw [chunks_length] at hl
  have hpos : 0 < v.size / s :=
    Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero hd)) hs
  intro h; subst h; simp only [List.length_nil] at hl; omega

/-- The kind of a map that `AddressMap.new` gave: absent for an absent value,
the identity for an empty one, and windows otherwise. -/
theorem addressMapNew_kind {b : Option ByteArray} {cc pc sc : U32} {M : AddressMap}
    (h : AddressMap.new b (word32 cc) (word32 pc) (word32 sc) = .ok M) :
    M.kind = match (generalizing := false) b with
      | none => .absent
      | some v => if v.size = 0 then .identity else .windows := by
  obtain ⟨hc, hp, -, -, -, -, hw⟩ := addressMapNew_ok h
  unfold AddressMap.kind
  cases b with
  | none => simp only at hw; rw [hw]
  | some v =>
    simp only at hw ⊢
    split at hw
    · rename_i h0; simp only [hw, h0, ↓reduceIte]
    · rename_i h0
      obtain ⟨-, hd, ws, hm, hws⟩ := hw
      have hne := mapM_chunks_ne_nil (by omega) h0 hd hm
      rw [hws]
      cases ws with
      | nil => exact absurd rfl hne
      | cons w ws => simp only [h0, ↓reduceIte]

/-! ## Translation -/

/-- `AddressMap.translate` with the cells of each side and the windows of the
map: the request of size 0, its width on the source side, an absent map, an
identity map with the width on the target side, and the windows. -/
theorem translate_eq (m : AddressMap) (s : Span) (reverse : Bool) :
    m.translate s reverse =
      if s.size = 0 then .error .emptyRegion
      else checkWidth s (if reverse then m.parentCells else m.childCells) >>= fun _ =>
        match m.windows with
        | none => .error .unmapped
        | some [] =>
          checkWidth s (if reverse then m.childCells else m.parentCells) >>= fun _ => pure s
        | some (w :: ws) =>
          throughWindows s (fun w => if reverse then w.parent else w.child)
            (fun w => if reverse then w.child else w.parent) (w :: ws) none := by
  unfold AddressMap.translate
  by_cases hz : s.size = 0
  · simp only [hz, ↓reduceIte]; rfl
  · simp only [hz, ↓reduceIte]
    cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      cases m.windows with
      | none => rfl
      | some ws => cases ws <;> rfl

end Krepi.Proofs.Fdt.Refinement
