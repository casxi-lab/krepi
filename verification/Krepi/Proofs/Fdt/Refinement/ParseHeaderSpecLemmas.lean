module

public import Krepi.Proofs.Fdt.Refinement.BasicLemmas
import Krepi.Proofs.Fdt.ExceptLemmas

/-!
# Device tree: lemmas about the specification of the header and the reservations

Lemmas about `header` and `reservationMap` of `Krepi.Spec.Fdt.Parse`, and
about the shapes of the code of their checks, for the refinement proofs of
the header, the reservation map and its iterator. The module imports no
generated definitions, so it is built once and not again for every mutant of
the code.

- The shapes of the checks: `check_spec` (an `if` of the code that returns an
  error agrees with the join point of an `if c then throw e` of the
  specification, when the two conditions agree), `check_or_spec` (one test of
  a disjunction of the specification that the code tests one part at a
  time), `ite_agrees_spec` (an `if` of the code whose condition agrees with
  that of an `if` of the specification), `eq_ok_of_agrees` and
  `eq_err_of_agrees` (a result that agrees with a success or a failure),
  `branch_ok_spec` and `branch_err_spec` (the `?` operator on a success and on
  a failure), and `ite_merge` and `ite_merge2`, nested tests of the code that
  repeat a branch, as one test.
- Numbers and bytes: `checkedAdd_of_lt`, `checkedAdd_of_not_lt`,
  `u64At_ok_le`, `u64At_error_lt`, and `beNat_extract`, `u32At_extract` and
  `u64At_extract`, a word read from a range of a byte array read from the
  array itself.
- The header: `block_ok`, `HeaderFacts` (what a successful `header` gives:
  the magic, `totalsize`, the tree's bytes, the bounds and alignment of the
  blocks and their bytes) with `header_facts`; `headerTail` (the checks after
  `totalsize`) and `header_eq_tail`; `header_blob` (the header of the tree's
  bytes is the header of the input), `parse_blob` (so is the parse) and
  `parse_ok` (the parts of a successful parse); `jp_neg` and `bind_ok_eq`,
  the steps of `header_eq_tail`.
- The reservation map: `ReadsAt` (a list of spans is the list of entries that
  the words of a byte array give from an offset on), `readsAt_nil`,
  `readsAt_cons`, `readsAt_append` and `readsAt_extract`; `entryStep` (the
  checks of one entry) with `reservationsFrom_succ` (one entry of the map as
  one `entryStep`) and `entryStep_ok`; `reservationsFrom_reads` and
  `reservationMap_ok` (the entries of a successful map are read from the
  tree's bytes, and they and the terminator lie within the tree).
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP
open Krepi.Statements Krepi.Spec.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## The shapes of the checks -/

section Checks

variable {γ δ ε ε' : Type} {rel : γ → δ → Prop} {err : ε → ε'}

/-- An `if` of the code that returns an error agrees with the join point of an
`if c then throw e` of the specification: both fail with the same error when
their conditions agree and hold, and otherwise the rest of the code agrees
with the rest of the specification. -/
theorem check_spec {c c' : Prop} [Decidable c] [Decidable c'] (hc : c ↔ c') {e : ε} {e' : ε'}
    (he : err e = e') {rest : Result (core.result.Result γ ε)} {K : Unit → Except ε' δ}
    {S : Except ε' δ} (hrest : ¬ c → ¬ c' → rest ⦃ out => Agrees rel err out S ⦄) :
    (if c then Result.ok (.Err e) else rest) ⦃ out =>
      Agrees rel err out (if c' then (throw e' >>= K) else S) ⦄ := by
  by_cases h : c'
  · have : c := hc.mpr h
    simp only [this, h, ↓reduceIte, spec_ok]; rw [← he]; rfl
  · have : ¬ c := fun x => h (hc.mp x)
    simp only [this, h, ↓reduceIte]; exact hrest this h

/-- One part of a disjunction that the specification tests at once and the
code one part at a time: the test of the first part. -/
theorem check_or_spec {c : Prop} [Decidable c] {a b : Bool} (hc : c ↔ a = true) {e : ε}
    {e' : ε'} (he : err e = e') {rest : Result (core.result.Result γ ε)}
    {K : Unit → Except ε' δ} {S : Except ε' δ}
    (hrest : ¬ c → rest ⦃ out =>
      Agrees rel err out (if b = true then (throw e' >>= K) else S) ⦄) :
    (if c then Result.ok (.Err e) else rest) ⦃ out =>
      Agrees rel err out (if (a || b) = true then (throw e' >>= K) else S) ⦄ := by
  by_cases h : c
  · have : (a || b) = true := by rw [hc.mp h]; rfl
    simp only [h, this, ↓reduceIte, spec_ok]; rw [← he]; rfl
  · have : a = false := by simpa [hc] using h
    simp only [h, this, Bool.false_or, ↓reduceIte]; exact hrest h

/-- An `if` of the code whose condition agrees with that of an `if` of the
specification: each branch agrees with the branch of the same condition. -/
theorem ite_agrees_spec {c c' : Prop} [Decidable c] [Decidable c'] (hc : c ↔ c')
    {x y : Result (core.result.Result γ ε)} {X Y : Except ε' δ}
    (hx : c → x ⦃ out => Agrees rel err out X ⦄)
    (hy : ¬ c → y ⦃ out => Agrees rel err out Y ⦄) :
    (if c then x else y) ⦃ out => Agrees rel err out (if c' then X else Y) ⦄ := by
  by_cases h : c
  · simp only [h, hc.mp h, ↓reduceIte]; exact hx h
  · simp only [h, (not_congr hc).mp h, ↓reduceIte]; exact hy h

end Checks

/-- A result that agrees with a success of the specification is a success. -/
theorem eq_ok_of_agrees {α β ε ε' : Type} {rel : α → β → Prop} {err : ε → ε'}
    {r : core.result.Result α ε} {b : β} (h : Agrees rel err r (.ok b)) :
    ∃ a, r = .Ok a ∧ rel a b := by
  cases r with
  | Ok a => exact ⟨a, rfl, h⟩
  | Err x => exact absurd h (by simp)

/-- A result that agrees with a failure of the specification is a failure. -/
theorem eq_err_of_agrees {α β ε ε' : Type} {rel : α → β → Prop} {err : ε → ε'}
    {r : core.result.Result α ε} {e : ε'} (h : Agrees rel err r (.error e)) :
    ∃ x, r = .Err x ∧ err x = e := by
  cases r with
  | Ok a => exact absurd h (by simp)
  | Err x => exact ⟨x, rfl, h⟩

/-- The `?` operator on a success continues on its value. -/
theorem branch_ok_spec {α β ε : Type} {v : α}
    {C : core.ops.control_flow.ControlFlow (core.result.Result Never ε) α → Result β}
    {p : β → Prop} (h : C (.Continue v) ⦃ p ⦄) :
    (core.result.Result.Insts.CoreOpsTry.branch (.Ok v : core.result.Result α ε) >>= C)
      ⦃ p ⦄ := by
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]; exact h

/-- The `?` operator on a failure takes the branch of the failure. -/
theorem branch_err_spec {α β ε : Type} {x : ε}
    {C : core.ops.control_flow.ControlFlow (core.result.Result Never ε) α → Result β}
    {p : β → Prop} (h : C (.Break (.Err x)) ⦃ p ⦄) :
    (core.result.Result.Insts.CoreOpsTry.branch (.Err x : core.result.Result α ε) >>= C)
      ⦃ p ⦄ := by
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]; exact h

/-- Three tests of the code that repeat their branches, as one test. -/
theorem ite_merge {α : Type} (a b c d : Prop) [Decidable a] [Decidable b] [Decidable c]
    [Decidable d] (e t : α) :
    (if a then e else if b then (if c then e else (if d then e else t))
      else (if d then e else t)) = (if a ∨ (b ∧ c) ∨ d then e else t) := by
  by_cases a <;> by_cases b <;> by_cases c <;> by_cases d <;> simp_all

/-- Two nested tests of the code that repeat their other branch, as one test.
-/
theorem ite_merge2 {α : Type} (a b : Prop) [Decidable a] [Decidable b] (x t : α) :
    (if a then (if b then x else t) else t) = (if a ∧ b then x else t) := by
  by_cases a <;> by_cases b <;> simp_all

/-! ## Bytes -/

theorem checkedAdd_of_lt {a b : Nat} (h : a + b < 2 ^ 64) : checkedAdd a b = .ok (a + b) := by
  simp only [checkedAdd, h, ↓reduceIte]

theorem checkedAdd_of_not_lt {a b : Nat} (h : ¬ a + b < 2 ^ 64) :
    checkedAdd a b = .error .overflow := by
  simp only [checkedAdd, h, ↓reduceIte]

/-- A 64-bit word that is read lies within the bytes. -/
theorem u64At_ok_le {b : ByteArray} {i : Nat} {v : UInt64} (h : u64At b i = .ok v) :
    i + 8 ≤ b.size := by
  unfold u64At at h
  split at h
  · assumption
  · cases h

/-- A 64-bit word that is not read runs past the end of the bytes. -/
theorem u64At_error_lt {b : ByteArray} {i : Nat} {e : Krepi.Spec.Fdt.Error}
    (h : u64At b i = .error e) : b.size < i + 8 := by
  unfold u64At at h
  split at h
  · cases h
  · omega

/-- The big-endian number of bytes of a range of a byte array. -/
theorem beNat_extract {b : ByteArray} {s e j n : Nat} (h : s + j + n ≤ e) :
    beNat (b.extract s e) j n = beNat b (s + j) n := by
  unfold beNat
  rw [ByteArray.extract_extract, Nat.min_eq_left (by omega), Nat.add_assoc]

/-- A 32-bit word of a range of a byte array within the array. -/
theorem u32At_extract {b : ByteArray} {s e j : Nat} (h : j + 4 ≤ e - s) (he : e ≤ b.size) :
    u32At (b.extract s e) j = u32At b (s + j) := by
  unfold u32At
  rw [ByteArray.size_extract, beNat_extract (by omega), Nat.min_eq_left he]
  simp only [show j + 4 ≤ e - s from h, show s + j + 4 ≤ b.size by omega, ↓reduceIte]

/-- A 64-bit word of a range of a byte array within the array. -/
theorem u64At_extract {b : ByteArray} {s e j : Nat} (h : j + 8 ≤ e - s) (he : e ≤ b.size) :
    u64At (b.extract s e) j = u64At b (s + j) := by
  unfold u64At
  rw [ByteArray.size_extract, beNat_extract (by omega), Nat.min_eq_left he]
  simp only [show j + 8 ≤ e - s from h, show s + j + 8 ≤ b.size by omega, ↓reduceIte]

/-! ## The header -/

/-- A failure of a check of a join point that does not hold: the rest. -/
theorem jp_neg {ε β : Type} {c : Prop} [Decidable c] {e : ε} {k : Unit → Except ε β}
    (h : ¬ c) :
    (if c then (throw e >>= k) else k ()) = k () := by
  simp only [h, ↓reduceIte]

/-- A bind on a step that succeeds. -/
theorem bind_ok_eq {ε α β : Type} {x : Except ε α} {a : α} {f : α → Except ε β}
    (h : x = .ok a) : x >>= f = f a := by
  rw [h]; rfl

theorem block_ok {blob B : ByteArray} {start size : Nat} (h : block blob start size = .ok B) :
    HEADER_SIZE ≤ start ∧ start + size ≤ blob.size ∧
      B = blob.extract start (start + size) := by
  unfold block at h
  obtain ⟨h1, h⟩ := Krepi.Proofs.Fdt.except_jp_ok h
  obtain ⟨e, he, h⟩ := Krepi.Proofs.Fdt.except_bind_ok.1 h
  obtain ⟨h2, h⟩ := Krepi.Proofs.Fdt.except_jp_ok h
  have h := Krepi.Proofs.Fdt.except_pure_ok.1 h
  unfold checkedAdd at he
  split at he
  · cases he; exact ⟨Nat.le_of_not_lt h1, Nat.le_of_not_lt h2, h.symm⟩
  · cases he

/-- What a successful `header` gives about the input and the header: the
tree's bytes, the bounds and alignment of its blocks, and their bytes. -/
structure HeaderFacts (input : ByteArray) (h : Header) : Prop where
  magic : u32At input 0 = .ok FDT_MAGIC
  total_read : ∃ v, u32At input 4 = .ok v ∧ v.toNat = h.layout.total
  blob : h.blob = input.extract 0 h.layout.total
  total_le : h.layout.total ≤ input.size
  header_le : HEADER_SIZE ≤ h.layout.total
  total_max : h.layout.total ≤ MAX_BLOB_SIZE.toNat
  blob_size : h.blob.size = h.layout.total
  structure_eq : h.structure_ = h.blob.extract h.layout.structStart h.layout.structEnd
  strings_eq : h.strings = h.blob.extract h.layout.stringsStart h.layout.stringsEnd
  struct_start : HEADER_SIZE ≤ h.layout.structStart
  struct_end_le : h.layout.structEnd ≤ h.layout.total
  strings_start : HEADER_SIZE ≤ h.layout.stringsStart
  strings_end_le : h.layout.stringsEnd ≤ h.layout.total
  struct_size : 12 ≤ h.layout.structSize
  reserve_start : HEADER_SIZE ≤ h.layout.reserveStart
  reserve_lt : h.layout.reserveStart < 2 ^ 32
  struct_align : h.layout.structStart % 4 = 0
  struct_size_align : h.layout.structSize % 4 = 0
  reserve_align : h.layout.reserveStart % 8 = 0
  disjoint : intersects h.layout.structStart h.layout.structEnd h.layout.stringsStart
    h.layout.stringsEnd = false

/-- `header_facts`: a successful `header` gives `HeaderFacts`. -/
theorem header_facts {input : ByteArray} {h : Header} (hh : header input = .ok h) :
    HeaderFacts input h := by
  unfold header at hh
  obtain ⟨-, hh⟩ := Krepi.Proofs.Fdt.except_jp_ok hh
  obtain ⟨m, hm, hh⟩ := Krepi.Proofs.Fdt.except_bind_ok.1 hh
  obtain ⟨h2, hh⟩ := Krepi.Proofs.Fdt.except_jp_ok hh
  obtain ⟨v, hv, hh⟩ := Krepi.Proofs.Fdt.except_bind_ok.1 hh
  obtain ⟨h3, hh⟩ := Krepi.Proofs.Fdt.except_jp_ok hh
  obtain ⟨h4, hh⟩ := Krepi.Proofs.Fdt.except_jp_ok hh
  obtain ⟨h5, hh⟩ := Krepi.Proofs.Fdt.except_jp_ok hh
  obtain ⟨_, -, hh⟩ := Krepi.Proofs.Fdt.except_bind_ok.1 hh
  obtain ⟨_, -, hh⟩ := Krepi.Proofs.Fdt.except_bind_ok.1 hh
  obtain ⟨-, hh⟩ := Krepi.Proofs.Fdt.except_jp_ok hh
  obtain ⟨a8, -, hh⟩ := Krepi.Proofs.Fdt.except_bind_ok.1 hh
  obtain ⟨a12, -, hh⟩ := Krepi.Proofs.Fdt.except_bind_ok.1 hh
  obtain ⟨a16, -, hh⟩ := Krepi.Proofs.Fdt.except_bind_ok.1 hh
  obtain ⟨a32, -, hh⟩ := Krepi.Proofs.Fdt.except_bind_ok.1 hh
  obtain ⟨a36, -, hh⟩ := Krepi.Proofs.Fdt.except_bind_ok.1 hh
  obtain ⟨h6, hh⟩ := Krepi.Proofs.Fdt.except_jp_ok hh
  obtain ⟨st, hst, hh⟩ := Krepi.Proofs.Fdt.except_bind_ok.1 hh
  obtain ⟨sg, hsg, hh⟩ := Krepi.Proofs.Fdt.except_bind_ok.1 hh
  obtain ⟨h7, hh⟩ := Krepi.Proofs.Fdt.except_jp_ok hh
  obtain ⟨h8, hh⟩ := Krepi.Proofs.Fdt.except_jp_ok hh
  have hh := Krepi.Proofs.Fdt.except_pure_ok.1 hh
  subst hh
  have hs : (input.extract 0 v.toNat).size = v.toNat := by
    rw [ByteArray.size_extract]; omega
  obtain ⟨b1, b2, b3⟩ := block_ok hst
  obtain ⟨c1, c2, c3⟩ := block_ok hsg
  rw [hs] at b2 c2
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not, decide_eq_true_eq]
    at h6 h7
  exact ⟨by rw [hm, Decidable.not_not.1 h2], ⟨v, hv, rfl⟩, rfl, Nat.le_of_not_lt h5,
    Nat.le_of_not_lt h3, Nat.le_of_not_lt h4, hs, b3, c3, b1, b2, c1, c2, Nat.le_of_not_lt h7.1,
    Nat.le_of_not_lt h7.2, a16.toNat_lt, h6.1.1, h6.1.2, h6.2, Bool.eq_false_iff.mpr h8⟩

/-- The checks of `header` after `totalsize`, on the tree's bytes `blob` and
`totalsize` `total`: the versions, the reads of the layout, the alignment,
the blocks and their places. -/
def headerTail (blob : ByteArray) (total : Nat) : Except Krepi.Spec.Fdt.Error Header := do
  let version := (← u32At blob 20).toNat
  let compatible := (← u32At blob 24).toNat
  if version < 17 || !(compatible == 16 || compatible == 17) || version < compatible then
    throw .unsupportedVersion
  let structStart := (← u32At blob 8).toNat
  let stringsStart := (← u32At blob 12).toNat
  let reserveStart := (← u32At blob 16).toNat
  let stringsSize := (← u32At blob 32).toNat
  let structSize := (← u32At blob 36).toNat
  if structStart % 4 != 0 || structSize % 4 != 0 || reserveStart % 8 != 0 then
    throw .badAlignment
  let structure_ ← block blob structStart structSize
  let strings ← block blob stringsStart stringsSize
  if structSize < 12 || reserveStart < HEADER_SIZE then throw .badLayout
  let layout : Layout :=
    { total, structStart, structSize, stringsStart, stringsSize, reserveStart }
  if intersects structStart layout.structEnd stringsStart layout.stringsEnd then
    throw .badLayout
  pure { blob, layout, structure_, strings }

/-- `header` of an input that passes the checks up to `totalsize`: the checks
after it on the first `totalsize` bytes. -/
theorem header_eq_tail {input : ByteArray} {v : UInt32} (h40 : HEADER_SIZE ≤ input.size)
    (hm : u32At input 0 = .ok FDT_MAGIC) (hv : u32At input 4 = .ok v)
    (c1 : HEADER_SIZE ≤ v.toNat) (c2 : v.toNat ≤ MAX_BLOB_SIZE.toNat)
    (c3 : v.toNat ≤ input.size) :
    header input = headerTail (input.extract 0 v.toNat) v.toNat := by
  unfold header
  refine (jp_neg (by omega)).trans ?_
  refine (bind_ok_eq hm).trans ?_
  refine (jp_neg (by simp)).trans ?_
  refine (bind_ok_eq hv).trans ?_
  refine (jp_neg (by omega)).trans ?_
  refine (jp_neg (by omega)).trans ?_
  refine (jp_neg (by omega)).trans ?_
  rfl

/-- The header of the tree's bytes of a header is that header. -/
theorem header_blob {input : ByteArray} {h : Header} (hh : header input = .ok h) :
    header h.blob = .ok h := by
  have F := header_facts hh
  have h40 : HEADER_SIZE ≤ input.size := Nat.le_trans F.header_le F.total_le
  have hm := F.magic
  obtain ⟨v, hv, hvt⟩ := F.total_read
  have hb := F.blob
  rw [← hvt] at hb
  have hsz : (input.extract 0 v.toNat).size = v.toNat := by
    rw [ByteArray.size_extract]; have := F.total_le; omega
  have h40v : 40 ≤ v.toNat := by have := F.header_le; rw [← hvt] at this; exact this
  have ht :=
    header_eq_tail h40 hm hv (hvt ▸ F.header_le) (hvt ▸ F.total_max) (hvt ▸ F.total_le)
  rw [hb, header_eq_tail (v := v) (by rw [hsz]; exact hvt ▸ F.header_le)
    (by rw [u32At_extract (by omega) (by rw [hvt]; exact F.total_le)]; exact hm)
    (by rw [u32At_extract (by omega) (by rw [hvt]; exact F.total_le)]; exact hv)
    (hvt ▸ F.header_le) (hvt ▸ F.total_max) (by rw [hsz]),
    ByteArray.extract_extract, Nat.zero_add, Nat.zero_add, Nat.min_self, ← ht, hh]

/-- The parse of the tree's bytes of a header is the parse of the input. -/
theorem parse_blob {input : ByteArray} {h : Header} (hh : header input = .ok h) :
    Fdt.parse h.blob = Fdt.parse input := by
  unfold Fdt.parse
  rw [header_blob hh, hh]

/-- The parts of a successful parse: its reservation map, its `totalsize` and
its nodes. -/
theorem parse_ok {input : ByteArray} {T : Fdt} {h : Header} (hp : Fdt.parse input = .ok T)
    (hh : header input = .ok h) :
    reservationMap h = .ok T.reservations ∧ T.totalSize = UInt64.ofNat h.layout.total ∧
      structureNodes h = .ok T.records := by
  unfold Fdt.parse at hp
  rw [hh, Krepi.Proofs.Fdt.except_ok_bind] at hp
  obtain ⟨l, hl, hp⟩ := Krepi.Proofs.Fdt.except_bind_ok.1 hp
  obtain ⟨r, hr, hp⟩ := Krepi.Proofs.Fdt.except_bind_ok.1 hp
  have hp := Krepi.Proofs.Fdt.except_pure_ok.1 hp
  subst hp
  exact ⟨hl, rfl, hr⟩

/-! ## The reservation map -/

/-- The list of spans `l` is the list of entries that the 64-bit words of `b`
give from the offset `first` on: the entry `k` is the start at
`first + 16 * k` and the size 8 bytes after it. -/
def ReadsAt (b : ByteArray) (first : Nat) (l : List Span) : Prop :=
  ∀ k (hk : k < l.length), u64At b (first + 16 * k) = .ok l[k].start ∧
    u64At b (first + 16 * k + 8) = .ok l[k].size

theorem readsAt_nil (b : ByteArray) (first : Nat) : ReadsAt b first [] :=
  fun k hk => absurd hk (Nat.not_lt_zero k)

theorem readsAt_cons {b : ByteArray} {first : Nat} {s : Span} {l : List Span} :
    ReadsAt b first (s :: l) ↔
      (u64At b first = .ok s.start ∧ u64At b (first + 8) = .ok s.size) ∧
        ReadsAt b (first + 16) l := by
  constructor
  · intro h
    refine ⟨h 0 (by simp), fun k hk => ?_⟩
    have := h (k + 1) (by simp; omega)
    simp only [List.getElem_cons_succ] at this
    rw [show first + 16 + 16 * k = first + 16 * (k + 1) by omega]
    exact this
  · rintro ⟨h0, h⟩ k hk
    cases k with
    | zero => simpa using h0
    | succ k =>
      have := h k (by simp at hk; omega)
      simp only [List.getElem_cons_succ]
      rw [show first + 16 * (k + 1) = first + 16 + 16 * k by omega]
      exact this

theorem readsAt_append {b : ByteArray} {first : Nat} {l : List Span} {s : Span}
    (h : ReadsAt b first l)
    (h1 : u64At b (first + 16 * l.length) = .ok s.start)
    (h2 : u64At b (first + 16 * l.length + 8) = .ok s.size) : ReadsAt b first (l ++ [s]) := by
  intro k hk
  rw [List.length_append, List.length_singleton] at hk
  by_cases hkl : k < l.length
  · rw [List.getElem_append_left hkl]; exact h k hkl
  · have : k = l.length := by omega
    subst this
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton]
    exact ⟨h1, h2⟩

/-- The entries read from a range of the bytes are those read from the bytes
at the offset of the range. -/
theorem readsAt_extract {b : ByteArray} {s e : Nat} {l : List Span} (h : ReadsAt b s l)
    (hl : s + 16 * l.length ≤ e) (he : e ≤ b.size) : ReadsAt (b.extract s e) 0 l := by
  intro k hk
  rw [Nat.zero_add, u64At_extract (by omega) he, u64At_extract (by omega) he]
  rw [← Nat.add_assoc]
  exact h k hk

/-- The checks of one entry of the reservation map at `cursor` after the
entries `earlier`: none for the terminator, the entry otherwise, or the error
of the first broken rule. -/
def entryStep (h : Header) (cursor : Nat) (earlier : List Span) :
    Except Krepi.Spec.Fdt.Error (Option Span) := do
  let e ← checkedAdd cursor 16
  if h.layout.total < e then throw .truncated
  if intersects cursor e h.layout.structStart h.layout.structEnd ||
      intersects cursor e h.layout.stringsStart h.layout.stringsEnd then
    throw .badLayout
  let start ← u64At h.blob cursor
  let size ← u64At h.blob (cursor + 8)
  if start == 0 && size == 0 then return none
  if MAX_RESERVATIONS.toNat < earlier.length + 1 then throw .limitExceeded
  let span ← Span.new start size
  if size = 0 then throw .emptyRegion
  if earlier.any (·.overlaps span) then throw .overlap
  return some span

theorem throw_bind {ε α β : Type} (e : ε) (k : α → Except ε β) :
    (throw e >>= k : Except ε β) = throw e := rfl

/-- One entry of the reservation map: the checks of `entryStep`, then the
end of the map or the entries after it. -/
theorem reservationsFrom_succ (h : Header) (fuel cursor : Nat) (earlier : List Span) :
    reservationsFrom h (fuel + 1) cursor earlier =
      entryStep h cursor earlier >>= fun o => match o with
        | none => .ok earlier
        | some span => reservationsFrom h fuel (cursor + 16) (earlier ++ [span]) := by
  rw [reservationsFrom.eq_2, entryStep]
  unfold checkedAdd
  by_cases hc : cursor + 16 < 2 ^ 64
  · simp only [hc, ↓reduceIte, Krepi.Proofs.Fdt.except_ok_bind]
    by_cases h1 : h.layout.total < cursor + 16
    · simp only [h1, ↓reduceIte, throw_bind]
    simp only [h1, ↓reduceIte]
    split
    · simp only [throw_bind]
    cases u64At h.blob cursor with
    | error e => rfl
    | ok start =>
      simp only [Krepi.Proofs.Fdt.except_ok_bind]
      cases u64At h.blob (cursor + 8) with
      | error e => rfl
      | ok size =>
        simp only [Krepi.Proofs.Fdt.except_ok_bind]
        split
        · rfl
        split
        · rfl
        cases Span.new start size with
        | error e => rfl
        | ok span =>
          simp only [Krepi.Proofs.Fdt.except_ok_bind]
          split
          · rfl
          split
          · rfl
          · rfl
  · simp only [hc, ↓reduceIte]; rfl

/-- A successful `entryStep`: the entry and its terminator lie within the
tree, and an entry is the two words at the cursor. -/
theorem entryStep_ok {h : Header} {cursor : Nat} {earlier : List Span} {o : Option Span}
    (hs : entryStep h cursor earlier = .ok o) :
    cursor + 16 ≤ h.layout.total ∧ ∀ s, o = some s →
      u64At h.blob cursor = .ok s.start ∧ u64At h.blob (cursor + 8) = .ok s.size := by
  unfold entryStep at hs
  obtain ⟨e, he, hs⟩ := Krepi.Proofs.Fdt.except_bind_ok.1 hs
  obtain ⟨h1, hs⟩ := Krepi.Proofs.Fdt.except_jp_ok hs
  obtain ⟨-, hs⟩ := Krepi.Proofs.Fdt.except_jp_ok hs
  obtain ⟨st, hst, hs⟩ := Krepi.Proofs.Fdt.except_bind_ok.1 hs
  obtain ⟨sz, hsz, hs⟩ := Krepi.Proofs.Fdt.except_bind_ok.1 hs
  have hec : e = cursor + 16 := by
    unfold checkedAdd at he; split at he
    · cases he; rfl
    · cases he
  refine ⟨by rw [hec] at h1; exact Nat.le_of_not_lt h1, fun s hos => ?_⟩
  rw [hos] at hs
  dsimp only at hs
  split at hs
  · cases Krepi.Proofs.Fdt.except_pure_ok.1 hs
  obtain ⟨-, hs⟩ := Krepi.Proofs.Fdt.except_jp_ok hs
  obtain ⟨span, hspan, hs⟩ := Krepi.Proofs.Fdt.except_bind_ok.1 hs
  obtain ⟨-, hs⟩ := Krepi.Proofs.Fdt.except_jp_ok hs
  obtain ⟨-, hs⟩ := Krepi.Proofs.Fdt.except_jp_ok hs
  have hs := Krepi.Proofs.Fdt.except_pure_ok.1 hs
  cases hs
  unfold Span.new at hspan
  split at hspan
  · cases hspan; exact ⟨hst, hsz⟩
  · cases hspan

/-- The entries of a successful map from `cursor` on, after `earlier`, are
read from the tree's bytes at `cursor`, and they and the terminator lie
within the tree. -/
theorem reservationsFrom_reads {h : Header} : ∀ {fuel cursor : Nat} {earlier l : List Span},
    reservationsFrom h fuel cursor earlier = .ok l →
      ∃ rest, l = earlier ++ rest ∧ ReadsAt h.blob cursor rest ∧
        cursor + 16 * rest.length + 16 ≤ h.layout.total
  | 0, _, _, _, hl => by cases hl
  | fuel + 1, cursor, earlier, l, hl => by
    rw [reservationsFrom_succ] at hl
    obtain ⟨o, ho, hl⟩ := Krepi.Proofs.Fdt.except_bind_ok.1 hl
    obtain ⟨hle, hs⟩ := entryStep_ok ho
    cases o with
    | none =>
      cases hl
      exact ⟨[], by simp, readsAt_nil _ _, by simpa using hle⟩
    | some s =>
      obtain ⟨rest, hr, hread, hlen⟩ := reservationsFrom_reads hl
      obtain ⟨h1, h2⟩ := hs s rfl
      refine ⟨s :: rest, by simp [hr], readsAt_cons.2 ⟨⟨h1, h2⟩, hread⟩, ?_⟩
      simp only [List.length_cons]; omega

/-- The entries of a successful reservation map are read from the tree's
bytes at `reserveStart`, and they and the terminator lie within the tree. -/
theorem reservationMap_ok {h : Header} {l : List Span} (hl : reservationMap h = .ok l) :
    ReadsAt h.blob h.layout.reserveStart l ∧
      h.layout.reserveStart + 16 * l.length + 16 ≤ h.layout.total := by
  obtain ⟨rest, hr, hread, hlen⟩ := reservationsFrom_reads hl
  simp only [List.nil_append] at hr
  subst hr
  exact ⟨hread, hlen⟩

end Krepi.Proofs.Fdt.Refinement
