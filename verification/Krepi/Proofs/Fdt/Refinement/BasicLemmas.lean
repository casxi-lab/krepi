module

public import Krepi.Statements.Basic
public import Krepi.Spec.Fdt.Translate

/-!
# Device tree: lemmas about the vocabulary of the refinement statements

Lemmas about the shared vocabulary of the refinement statements
(`Krepi.Statements.Basic`) and about the byte reads of the specification of
the `fdt` component, for the proofs below `Krepi.Proofs.Fdt.Refinement`. The
module imports no generated definitions, so it is built once and not again
for every mutant of the code.

- Triples: `spec_iff` (a triple holds exactly when the computation returns
  a value that satisfies the postcondition), `spec_of_eq` and `eq_of_spec`.
- Results: `agrees_ok_ok`, `agrees_err_error`, `agrees_ok_error`,
  `agrees_err_ok`, `agrees_ok_iff`, `agrees_err_iff`, `agrees_err_bind` (a
  failure of a step agrees with the failure of a block that starts with the
  step of the specification), `agrees_ok_bind`, `agrees_of_eq` and
  `agrees_ok_of_eq`.
- The `?` operator, read back from the hypotheses that `step*` leaves:
  `branch_ok`, `branch_err`, `agrees_of_branch_ok`, `agrees_err_of_branch`
  and `agrees_try_err`.
- Iterators: `fixed_iff` (the fixed-point clause of `Stands` as a triple),
  `stands_nil`, `stands_cons`, `stands_nil_iff` (the empty list in the form
  of triples alone), `stands_nil_of_eq`, `stands_cons_of_eq`, `stands_of_sim`
  (an iterator stands for a list when a relation between its states and
  lists is preserved by `next`), and `advances_of_stands` (an iterator that
  stands for a list advances on it, which proves the statement of each
  `next`).
- Options and lists: `optionRel_eq_iff`, `listRel_eq_iff`,
  `listRel_iff_forall₂`, `listRel_length`, and `any_drop_cons`, the step of
  a loop that looks for an item.
- Machine values: `byte_toNat`, `word32_toNat`, `word64_toNat`,
  `byte_eq_iff`, `word32_eq_iff`, `word64_eq_iff`, `word64_add`,
  `word64_ofNat_iff`, `word32_ofNat_iff`.
- Sizes, bounds and conditions: `u32_size`, `u64_size`, `u64_max_eq`,
  `u64_MAX_val`, `u8_lt`, `u32_lt`, `u64_lt` (bounds that `omega` reads
  without `scalar_tac`), `u64_eq_zero_iff`, `word64_bne_zero`, and
  `of_decide_post` and `of_decide_post_not`, the condition of a `decide`
  that a step returned.
- The platform: `usize_numBits`, `usize_max`, `usize_size`, `usize_lt`,
  `slice_length_lt` and `u64_max_eq_usize_max`, what `Usize64` gives about
  the bounds of `usize`.
- Bytes: `bytesOf_size`, `bytesOf_toList`, `bytesOf_extract`,
  `bytesOf_getElem?`, `beNat_bytesOf` (the big-endian number of the bytes of
  a slice), `beNat_bytesOf_four`, `beNat_bytesOf_eight`, `beNat_lt`,
  `beNat_zero`, `u32At_bytesOf`, `u64At_bytesOf`, `u32At_bytesOf_ok`,
  `u64At_bytesOf_ok`, `word32_beNat_iff`, `word64_beNat_iff` and
  `getElem_eq_getElem!`.
- Bit operations: `or_add` and `or_shift`, the `|||` of numbers whose bits
  do not overlap as their sum.
- Cells: `cellsU64_bytesOf` and `cellsU64_ok_of`.
-/

@[expose] public section

open Aeneas Aeneas.Std Aeneas.Std.WP Aeneas.Data.Coinductive
open Krepi.Statements Krepi.Spec.Fdt

namespace Krepi.Proofs.Fdt.Refinement

/-! ## Triples -/

unseal Result in
/-- A triple holds exactly when the computation returns a value, neither
failing nor diverging, that satisfies the postcondition. -/
theorem spec_iff {α : Type} {m : Result α} {p : α → Prop} :
    m ⦃ p ⦄ ↔ ∃ a, m = .ok a ∧ p a := by
  constructor
  · intro h
    unfold spec at h
    refine DWP.induction (P := fun (m : ITree RustEffect α) _ => ∃ a, m = Result.ok a ∧ p a)
      ?_ ?_ h
    · intro v s hv; exact ⟨v, rfl, hv⟩
    · intro e k s hw; cases e; exact hw.elim
  · rintro ⟨a, rfl, h⟩; simpa using h

/-- A computation that returns `a` satisfies a postcondition that `a` does. -/
theorem spec_of_eq {α : Type} {m : Result α} {p : α → Prop} {a : α} (h : m = .ok a)
    (hp : p a) : m ⦃ p ⦄ := by
  subst h; simpa using hp

/-- The value of a computation that returns `a` satisfies every postcondition
of a triple that holds. -/
theorem eq_of_spec {α : Type} {m : Result α} {p : α → Prop} {a : α} (h : m = .ok a)
    (hs : m ⦃ p ⦄) : p a := by
  subst h; simpa using hs

/-! ## Results -/

section Agrees

variable {α β ε ε' : Type} {rel : α → β → Prop} {err : ε → ε'}

@[simp] theorem agrees_ok_ok {a : α} {b : β} :
    Agrees rel err (.Ok a) (.ok b) ↔ rel a b := Iff.rfl

@[simp] theorem agrees_err_error {x : ε} {y : ε'} :
    Agrees rel err (.Err x) (.error y) ↔ err x = y := Iff.rfl

@[simp] theorem agrees_ok_error {a : α} {y : ε'} :
    Agrees rel err (.Ok a) (.error y) ↔ False := Iff.rfl

@[simp] theorem agrees_err_ok {x : ε} {b : β} :
    Agrees rel err (.Err x) (.ok b) ↔ False := Iff.rfl

/-- A success agrees exactly with a success of a related value. -/
theorem agrees_ok_iff {a : α} {e : Except ε' β} :
    Agrees rel err (.Ok a) e ↔ ∃ b, e = .ok b ∧ rel a b := by
  cases e <;> simp

/-- A failure agrees exactly with the failure of the mapped error. -/
theorem agrees_err_iff {x : ε} {e : Except ε' β} :
    Agrees rel err (.Err x) e ↔ e = .error (err x) := by
  cases e <;> simp [eq_comm]

/-- A failure that agrees with a step of the specification agrees with any
block that starts with that step: the error of the `?` operator. -/
theorem agrees_err_bind {γ δ : Type} {rel' : γ → δ → Prop} {x : ε} {e : Except ε' β}
    {k : β → Except ε' δ} (h : Agrees rel err (.Err x) e) :
    Agrees rel' err (.Err x) (e >>= k) := by
  rw [agrees_err_iff] at h; subst h; rfl

/-- A success that agrees with a step of the specification lets a block that
starts with that step continue on a related value. -/
theorem agrees_ok_bind {γ δ : Type} {rel' : γ → δ → Prop} {a : α} {e : Except ε' β}
    {k : β → Except ε' δ} {r : core.result.Result γ ε} (h : Agrees rel err (.Ok a) e)
    (hk : ∀ b, rel a b → Agrees rel' err r (k b)) :
    Agrees rel' err r (e >>= k) := by
  obtain ⟨b, rfl, hb⟩ := agrees_ok_iff.mp h; exact hk b hb

/-- Agreement through equal specification results. -/
theorem agrees_of_eq {r : core.result.Result α ε} {e e' : Except ε' β} (he : e = e')
    (h : Agrees rel err r e') : Agrees rel err r e := he ▸ h


/-! ## The `?` operator

The code of `f(..)?` binds the result `r` of `f`, takes it apart with
`branch` into `Continue v` for `Ok v` and `Break (Err e)` for `Err e`, and
returns `from_residual` of the residual on a break. After `step*` the
hypotheses are the postcondition of `branch`, a `match` on `r`, and the
branch taken; these lemmas read the result of `f` back from them. -/

theorem branch_ok {r : core.result.Result α ε}
    {cf : core.ops.control_flow.ControlFlow (core.result.Result Never ε) α} {v : α}
    (h : match r with
      | .Ok v => cf = .Continue v
      | .Err e => cf = .Break (.Err e)) (hc : cf = .Continue v) : r = .Ok v := by
  cases r <;> simp_all

theorem branch_err {r : core.result.Result α ε}
    {cf : core.ops.control_flow.ControlFlow (core.result.Result Never ε) α}
    {res : core.result.Result Never ε} {e : ε}
    (h : match r with
      | .Ok v => cf = .Continue v
      | .Err e => cf = .Break (.Err e)) (hc : cf = .Break res) (he : res = .Err e) :
    r = .Err e := by
  cases r <;> simp_all

/-- On the branch `Continue v`, the result `Ok v` agrees as `r` did. -/
theorem agrees_of_branch_ok {r : core.result.Result α ε} {E : Except ε' β}
    {cf : core.ops.control_flow.ControlFlow (core.result.Result Never ε) α} {v : α}
    (h : match r with
      | .Ok v => cf = .Continue v
      | .Err e => cf = .Break (.Err e)) (hc : cf = .Continue v)
    (hr : Agrees rel err r E) : Agrees rel err (.Ok v) E := by
  rw [branch_ok h hc] at hr; exact hr

/-- On the branch `Break (Err e)`, the step of the specification fails with
the error of `e`. -/
theorem agrees_err_of_branch {r : core.result.Result α ε} {E : Except ε' β}
    {cf : core.ops.control_flow.ControlFlow (core.result.Result Never ε) α}
    {res : core.result.Result Never ε} {e : ε}
    (h : match r with
      | .Ok v => cf = .Continue v
      | .Err e => cf = .Break (.Err e)) (hc : cf = .Break res) (he : res = .Err e)
    (hr : Agrees rel err r E) :
    E = .error (err e) := by
  rw [branch_err h hc he, agrees_err_iff] at hr; exact hr

/-- The error of the `?` operator agrees with a block of the specification
that starts with the step of the callee: the hypotheses are those that
`step*` leaves on the branch `Break`, `from_residual` included. -/
theorem agrees_try_err {γ δ : Type} {rel' : γ → δ → Prop} {r : core.result.Result α ε}
    {E : Except ε' β} {k : β → Except ε' δ}
    {cf : core.ops.control_flow.ControlFlow (core.result.Result Never ε) α}
    {res : core.result.Result Never ε} {e v : ε} {out : core.result.Result γ ε}
    (h : match r with
      | .Ok v => cf = .Continue v
      | .Err e => cf = .Break (.Err e)) (hc : cf = .Break res) (he : res = .Err e)
    (hv : e = v) (hout : out = .Err v) (hr : Agrees rel err r E) :
    Agrees rel' err out (E >>= k) := by
  rw [agrees_err_of_branch h hc he hr, hout, ← hv]; rfl

/-- A success that agrees with a specification result `.ok b` relates to `b`.
-/
theorem agrees_ok_of_eq {a : α} {e : Except ε' β} {b : β} (h : Agrees rel err (.Ok a) e)
    (he : e = .ok b) : rel a b := by
  subst he; exact h

end Agrees

/-! ## Options and lists -/

@[simp] theorem optionRel_none_none {α β : Type} {rel : α → β → Prop} :
    OptionRel rel none none ↔ True := Iff.rfl

@[simp] theorem optionRel_some_some {α β : Type} {rel : α → β → Prop} {a : α} {b : β} :
    OptionRel rel (some a) (some b) ↔ rel a b := Iff.rfl

@[simp] theorem optionRel_none_some {α β : Type} {rel : α → β → Prop} {b : β} :
    OptionRel rel none (some b) ↔ False := Iff.rfl

@[simp] theorem optionRel_some_none {α β : Type} {rel : α → β → Prop} {a : α} :
    OptionRel rel (some a) none ↔ False := Iff.rfl

/-- `OptionRel` of a function: the option mapped by it. -/
theorem optionRel_eq_iff {α β : Type} (f : α → β) (o : Option α) (p : Option β) :
    OptionRel (fun a b => f a = b) o p ↔ o.map f = p := by
  cases o <;> cases p <;> simp

@[simp] theorem listRel_nil_nil {α β : Type} {rel : α → β → Prop} :
    ListRel rel [] [] ↔ True := Iff.rfl

@[simp] theorem listRel_cons_cons {α β : Type} {rel : α → β → Prop} {a : α} {b : β}
    {l : List α} {m : List β} : ListRel rel (a :: l) (b :: m) ↔ rel a b ∧ ListRel rel l m :=
  Iff.rfl

@[simp] theorem listRel_nil_cons {α β : Type} {rel : α → β → Prop} {b : β} {m : List β} :
    ListRel rel [] (b :: m) ↔ False := Iff.rfl

@[simp] theorem listRel_cons_nil {α β : Type} {rel : α → β → Prop} {a : α} {l : List α} :
    ListRel rel (a :: l) [] ↔ False := Iff.rfl

/-- `ListRel` is `List.Forall₂`. -/
theorem listRel_iff_forall₂ {α β : Type} {rel : α → β → Prop} :
    ∀ (l : List α) (m : List β), ListRel rel l m ↔ List.Forall₂ rel l m
  | [], [] => by simp
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp
  | a :: l, b :: m => by simp [listRel_iff_forall₂ l m]

/-- Lists that `ListRel` relates have one length. -/
theorem listRel_length {α β : Type} {rel : α → β → Prop} {l : List α} {m : List β}
    (h : ListRel rel l m) : l.length = m.length :=
  ((listRel_iff_forall₂ l m).mp h).length_eq

/-- `List.any` of the suffix from an index within the list. -/
theorem any_drop_cons {α : Type} {l : List α} {p : α → Bool} {i : Nat} (h : i < l.length) :
    (l.drop i).any p = (p l[i] || (l.drop (i + 1)).any p) := by
  rw [List.drop_eq_getElem_cons h, List.any_cons]

/-- `ListRel` of a function: the list mapped by it. -/
theorem listRel_eq_iff {α β : Type} (f : α → β) :
    ∀ (l : List α) (m : List β), ListRel (fun a b => f a = b) l m ↔ l.map f = m
  | [], [] => by simp
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp
  | a :: l, b :: m => by simp [listRel_eq_iff f l m]

/-! ## Iterators -/

section Iterators

variable {σ α β : Type} {next : σ → Result (Option α × σ)} {rel : α → β → Prop}

/-- The fixed-point clause of `Stands` at the end of the list, as a triple:
a call returns none and the same state. -/
theorem fixed_iff (it : σ) :
    next it = .ok (none, it) ↔ next it ⦃ o s => o = none ∧ s = it ⦄ := by
  rw [spec_iff]
  constructor
  · intro h; exact ⟨_, h, rfl, rfl⟩
  · rintro ⟨⟨o, s⟩, h, ho, hs⟩
    subst ho hs; exact h

/-- `Stands` of the empty list, unfolded. -/
theorem stands_nil (it : σ) :
    Stands next rel it [] ↔ next it ⦃ o it' => o = none ∧ next it' = .ok (none, it') ⦄ := by
  simp only [Stands]

/-- `Stands` of a nonempty list, unfolded. -/
theorem stands_cons (it : σ) (b : β) (l : List β) :
    Stands next rel it (b :: l) ↔
      next it ⦃ o it' => ∃ a, o = some a ∧ rel a b ∧ Stands next rel it' l ⦄ := by
  simp only [Stands]

/-- `Stands` of the empty list with its fixed-point clause as a triple. -/
theorem stands_nil_iff (it : σ) :
    Stands next rel it [] ↔
      next it ⦃ o it' => o = none ∧ next it' ⦃ o' s => o' = none ∧ s = it' ⦄ ⦄ := by
  simp only [stands_nil, fixed_iff]

/-- An iterator stands for the empty list when a call returns none and a state
at which a call returns none and that state again. -/
theorem stands_nil_of_eq {it it' : σ} (h : next it = .ok (none, it'))
    (h' : next it' = .ok (none, it')) : Stands next rel it [] := by
  rw [stands_nil, h, spec_ok, uncurry'_pair]; exact ⟨rfl, h'⟩

/-- An iterator stands for `b :: l` when a call returns an item related to `b`
and a state that stands for `l`. -/
theorem stands_cons_of_eq {it it' : σ} {a : α} {b : β} {l : List β}
    (h : next it = .ok (some a, it')) (hr : rel a b) (hs : Stands next rel it' l) :
    Stands next rel it (b :: l) := by
  rw [stands_cons, h, spec_ok, uncurry'_pair]; exact ⟨a, rfl, hr, hs⟩

/-- A simulation proves `Stands`: if a relation `R` between the states of the
iterator and lists makes `next` give none and a fixed point at the empty
list, and at `b :: l` an item related to `b` and a state related to `l`, then
every state stands for each list that `R` relates it to. -/
theorem stands_of_sim (R : σ → List β → Prop)
    (hnil : ∀ s, R s [] → next s ⦃ o s' => o = none ∧ next s' = .ok (none, s') ⦄)
    (hcons : ∀ s b l, R s (b :: l) →
      next s ⦃ o s' => ∃ a, o = some a ∧ rel a b ∧ R s' l ⦄) :
    ∀ l s, R s l → Stands next rel s l := by
  intro l
  induction l with
  | nil => intro s hs; exact (stands_nil s).mpr (hnil s hs)
  | cons b l ih =>
    intro s hs
    rw [stands_cons]
    refine spec_mono (hcons s b l hs) ?_
    rintro ⟨o, s'⟩ ⟨a, ho, hr, hR⟩
    exact ⟨a, ho, hr, ih s' hR⟩

/-- An iterator that stands for a list advances on it: the statement of the
`next` of an iterator follows from `Stands` alone. -/
theorem advances_of_stands {it : σ} {l : List β} (h : Stands next rel it l) :
    Advances next rel it l := by
  unfold Advances
  cases l with
  | nil =>
    rw [stands_nil] at h
    refine spec_mono h ?_
    rintro ⟨o, it'⟩ ⟨ho, hfix⟩
    subst ho
    simp only [uncurry'_pair, List.head?_nil, List.tail_nil, optionRel_none_none, true_and]
    exact stands_nil_of_eq hfix hfix
  | cons b l =>
    rw [stands_cons] at h
    refine spec_mono h ?_
    rintro ⟨o, it'⟩ ⟨a, ho, hr, hs⟩
    subst ho
    simp only [uncurry'_pair, List.head?_cons, List.tail_cons, optionRel_some_some]
    exact ⟨hr, hs⟩

end Iterators

/-! ## Machine values -/

@[simp] theorem byte_toNat (x : U8) : (byte x).toNat = x.val := by
  simp only [byte, UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by scalar_tac)

@[simp] theorem word32_toNat (x : U32) : (word32 x).toNat = x.val := by
  simp only [word32, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by scalar_tac)

@[simp] theorem word64_toNat (x : U64) : (word64 x).toNat = x.val := by
  simp only [word64, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by scalar_tac)

theorem byte_eq_iff {x : U8} {n : UInt8} : byte x = n ↔ x.val = n.toNat := by
  rw [← UInt8.toNat_inj, byte_toNat]

theorem word32_eq_iff {x : U32} {n : UInt32} : word32 x = n ↔ x.val = n.toNat := by
  rw [← UInt32.toNat_inj, word32_toNat]

theorem word64_eq_iff {x : U64} {n : UInt64} : word64 x = n ↔ x.val = n.toNat := by
  rw [← UInt64.toNat_inj, word64_toNat]

/-- A word whose value is the exact sum of two others is their sum. -/
theorem word64_add {a b c : U64} (h : c.val = a.val + b.val) :
    word64 c = word64 a + word64 b := by
  rw [word64_eq_iff, UInt64.toNat_add, word64_toNat, word64_toNat, ← h]
  exact (Nat.mod_eq_of_lt (by scalar_tac)).symm

theorem word64_ofNat_iff {x : U64} {n : Nat} :
    word64 x = UInt64.ofNat n ↔ x.val = n % 2 ^ 64 := by
  rw [word64_eq_iff, UInt64.toNat_ofNat']

theorem word32_ofNat_iff {x : U32} {n : Nat} :
    word32 x = UInt32.ofNat n ↔ x.val = n % 2 ^ 32 := by
  rw [word32_eq_iff, UInt32.toNat_ofNat']

/-! ## Sizes of the machine types -/

theorem u32_size : U32.size = 2 ^ 32 := by rw [U32.size, U32.numBits]; rfl

theorem u64_size : U64.size = 2 ^ 64 := by rw [U64.size, U64.numBits]; rfl

theorem u64_max_eq : U64.max = 2 ^ 64 - 1 := by rw [U64.max, U64.numBits]; rfl

theorem u64_MAX_val : core.num.U64.MAX.val = 2 ^ 64 - 1 := rfl

theorem u8_lt (x : U8) : x.val < 2 ^ 8 := x.hmax

theorem u32_lt (x : U32) : x.val < 2 ^ 32 := x.hmax

theorem u64_lt (x : U64) : x.val < 2 ^ 64 := x.hmax

theorem u64_eq_zero_iff {x : U64} : x = 0#u64 ↔ x.val = 0 :=
  ⟨fun h => by rw [h]; rfl, fun h => UScalar.eq_of_val_eq (by rw [h]; rfl)⟩

theorem word64_bne_zero (x : U64) : (word64 x != 0) = (x != 0#u64) := by
  rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, ne_eq, ne_eq, word64_eq_iff, u64_eq_zero_iff]
  rfl

/-- The condition of a `decide` that a step returned as `true`. -/
theorem of_decide_post {p : Prop} [Decidable p] {b : Bool} (h : b = decide p) (hb : b = true) :
    p := of_decide_eq_true (h ▸ hb)

/-- The negated condition of a `decide` that a step returned as not `true`. -/
theorem of_decide_post_not {p : Prop} [Decidable p] {b : Bool} (h : b = decide p)
    (hb : ¬ b = true) : ¬ p := of_decide_eq_false (h ▸ (Bool.not_eq_true _).mp hb)

/-! ## The platform -/

section Platform

variable (h : Usize64)
include h

theorem usize_numBits : Usize.numBits = 64 := by
  rw [Usize.numBits]; exact h

theorem usize_max : Usize.max = 2 ^ 64 - 1 := by
  rw [Usize.max, usize_numBits h]

theorem usize_size : Usize.size = 2 ^ 64 := by
  rw [Usize.size, usize_numBits h]

theorem u64_max_eq_usize_max : U64.max = Usize.max := by
  rw [usize_max h, U64.max, U64.numBits]; rfl

theorem usize_lt (x : Usize) : x.val < 2 ^ 64 := by
  have hx := x.hmax
  have h' : System.Platform.numBits = 64 := h
  rw [UScalarTy.Usize_numBits_eq, h'] at hx; exact hx

theorem slice_length_lt {α : Type} (s : Slice α) : s.length < 2 ^ 64 := by
  have := s.property; rw [usize_max h] at this; show s.val.length < 2 ^ 64; omega

end Platform

/-! ## Bytes -/

/-- The loop of `ByteArray.toList` from the index `i`. -/
theorem toList_loop_eq (b : ByteArray) : ∀ (i : Nat) (r : List UInt8),
    ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
  intro i r
  fun_induction ByteArray.toList.loop b i r with
  | case1 i r hi ih =>
    rw [ih]
    have hl : i < b.data.toList.length := by simpa using hi
    have : b.data.toList.drop i = b.get! i :: b.data.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hl]
      congr 1
      simp [ByteArray.get!, hi]
    simp [this]
  | case2 i r hi =>
    have : b.data.toList.length ≤ i := by simp; exact Nat.le_of_not_lt hi
    simp [List.drop_eq_nil_of_le this]

@[simp] theorem bytesOf_size (s : Slice U8) : (bytesOf s).size = s.length := by
  simp [bytesOf, ByteArray.size]

@[simp] theorem bytesOf_data_toList (s : Slice U8) : (bytesOf s).data.toList = s.val.map byte := by
  simp [bytesOf]

@[simp] theorem bytesOf_toList (s : Slice U8) : (bytesOf s).toList = s.val.map byte := by
  simp [ByteArray.toList, toList_loop_eq]

/-- The bytes `[i, j)` of the bytes of a slice. -/
theorem bytesOf_extract (s : Slice U8) (i j : Nat) :
    ((bytesOf s).extract i j).toList = ((s.val.drop i).take (j - i)).map byte := by
  simp [ByteArray.toList, toList_loop_eq, ByteArray.data_extract, List.extract_eq_take_drop,
    List.map_take, List.map_drop]

@[simp] theorem bytesOf_getElem? (s : Slice U8) (i : Nat) :
    (bytesOf s)[i]? = (s.val[i]?).map byte := by
  by_cases hi : i < s.val.length
  · rw [getElem?_pos (bytesOf s) i (by simpa using hi), ByteArray.getElem_eq_getElem_data,
      List.getElem?_eq_getElem hi]
    simp [bytesOf]
  · rw [getElem?_neg (bytesOf s) i (by simpa using hi), List.getElem?_eq_none (by omega)]
    rfl

/-- The big-endian number of `n` bytes of a slice from `i`. -/
theorem beNat_bytesOf (s : Slice U8) (i n : Nat) :
    beNat (bytesOf s) i n = ((s.val.drop i).take n).foldl (fun acc x => acc * 256 + x.val) 0 := by
  rw [beNat, bytesOf_extract, Nat.add_sub_cancel_left, List.foldl_map]
  simp only [byte_toNat]

/-- The big-endian number of a list of bytes is below `256 ^ length`. -/
theorem foldl_be_lt (l : List U8) : ∀ acc : Nat,
    l.foldl (fun acc x => acc * 256 + x.val) acc < (acc + 1) * 256 ^ l.length := by
  induction l with
  | nil => intro acc; simp
  | cons x l ih =>
    intro acc
    simp only [List.foldl_cons, List.length_cons, Nat.pow_succ]
    have hx : x.val < 256 := by scalar_tac
    have := ih (acc * 256 + x.val)
    calc _ < _ := this
      _ ≤ (acc + 1) * (256 ^ l.length * 256) := by
        rw [Nat.mul_comm (256 ^ l.length) 256, ← Nat.mul_assoc]
        apply Nat.mul_le_mul_right
        omega

/-- The big-endian number of `n` bytes fits `8 * n` bits. -/
theorem beNat_lt (s : Slice U8) (i n : Nat) : beNat (bytesOf s) i n < 2 ^ (8 * n) := by
  rw [beNat_bytesOf]
  have := foldl_be_lt ((s.val.drop i).take n) 0
  have hl : ((s.val.drop i).take n).length ≤ n := List.length_take_le _ _
  calc _ < (0 + 1) * 256 ^ ((s.val.drop i).take n).length := this
    _ ≤ 256 ^ n := by rw [Nat.zero_add, Nat.one_mul]; exact Nat.pow_le_pow_right (by omega) hl
    _ = 2 ^ (8 * n) := by rw [Nat.pow_mul]

/-- Four bytes of a slice read big-endian. -/
theorem beNat_bytesOf_four (s : Slice U8) (i : Nat) (h : i + 4 ≤ s.length) :
    beNat (bytesOf s) i 4 = s.val[i]!.val * 2 ^ 24 + s.val[i + 1]!.val * 2 ^ 16 +
      s.val[i + 2]!.val * 2 ^ 8 + s.val[i + 3]!.val := by
  rw [beNat_bytesOf]
  have hl : i + 4 ≤ s.val.length := h
  have e : (s.val.drop i).take 4 = [s.val[i]!, s.val[i + 1]!, s.val[i + 2]!, s.val[i + 3]!] := by
    rw [List.drop_eq_getElem_cons (i := i) (by omega),
      List.drop_eq_getElem_cons (i := i + 1) (by omega),
      List.drop_eq_getElem_cons (i := i + 2) (by omega),
      List.drop_eq_getElem_cons (i := i + 3) (by omega)]
    simp only [List.take_succ_cons, List.take_zero, getElem!_pos s.val i (by omega),
      getElem!_pos s.val (i + 1) (by omega), getElem!_pos s.val (i + 2) (by omega),
      getElem!_pos s.val (i + 3) (by omega)]
  rw [e]; simp only [List.foldl_cons, List.foldl_nil]; omega

/-- The big-endian fold from an initial value: the value shifted past the
bytes, plus the number of the bytes. -/
theorem foldl_be_acc (l : List U8) : ∀ acc : Nat,
    l.foldl (fun acc x => acc * 256 + x.val) acc =
      acc * 256 ^ l.length + l.foldl (fun acc x => acc * 256 + x.val) 0 := by
  induction l with
  | nil => intro acc; simp
  | cons x l ih =>
    intro acc
    simp only [List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add]
    rw [ih (acc * 256 + x.val), ih x.val, Nat.pow_succ]
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256 (256 ^ l.length), Nat.add_assoc]

/-- Eight bytes of a slice read big-endian: the word at `i` and the word at
`i + 4`. -/
theorem beNat_bytesOf_eight (s : Slice U8) (i : Nat) (h : i + 8 ≤ s.length) :
    beNat (bytesOf s) i 8 = beNat (bytesOf s) i 4 * 2 ^ 32 + beNat (bytesOf s) (i + 4) 4 := by
  simp only [beNat_bytesOf]
  have hl : i + 8 ≤ s.val.length := h
  have e : (s.val.drop i).take 8 = (s.val.drop i).take 4 ++ (s.val.drop (i + 4)).take 4 := by
    rw [show 8 = 4 + 4 from rfl, List.take_add, List.drop_drop]
  have h4 : ((s.val.drop (i + 4)).take 4).length = 4 := by simp; omega
  rw [e, List.foldl_append, foldl_be_acc ((s.val.drop (i + 4)).take 4), h4]
  rfl

/-- The 32-bit word of the specification at `i` of the bytes of a slice. -/
theorem u32At_bytesOf (s : Slice U8) (i : Nat) :
    u32At (bytesOf s) i =
      if i + 4 ≤ s.length then .ok (UInt32.ofNat (beNat (bytesOf s) i 4)) else .error .truncated := by
  simp only [u32At, bytesOf_size]

/-- The 64-bit word of the specification at `i` of the bytes of a slice. -/
theorem u64At_bytesOf (s : Slice U8) (i : Nat) :
    u64At (bytesOf s) i =
      if i + 8 ≤ s.length then .ok (UInt64.ofNat (beNat (bytesOf s) i 8)) else .error .truncated := by
  simp only [u64At, bytesOf_size]

/-- The big-endian number of no bytes. -/
theorem beNat_zero (b : ByteArray) (i : Nat) : beNat b i 0 = 0 := by
  simp [beNat, ByteArray.extract_same]

/-- A 32-bit word within the bytes of a slice. -/
theorem u32At_bytesOf_ok {s : Slice U8} {i : Nat} (h : i + 4 ≤ s.length) :
    u32At (bytesOf s) i = .ok (UInt32.ofNat (beNat (bytesOf s) i 4)) := by
  simp [u32At, h]

/-- A 64-bit word within the bytes of a slice. -/
theorem u64At_bytesOf_ok {s : Slice U8} {i : Nat} (h : i + 8 ≤ s.length) :
    u64At (bytesOf s) i = .ok (UInt64.ofNat (beNat (bytesOf s) i 8)) := by
  simp [u64At, h]

theorem word32_beNat_iff {v : U32} {s : Slice U8} {i : Nat} :
    word32 v = UInt32.ofNat (beNat (bytesOf s) i 4) ↔ v.val = beNat (bytesOf s) i 4 := by
  rw [word32_ofNat_iff, Nat.mod_eq_of_lt (beNat_lt s i 4)]

theorem word64_beNat_iff {v : U64} {s : Slice U8} {i : Nat} :
    word64 v = UInt64.ofNat (beNat (bytesOf s) i 8) ↔ v.val = beNat (bytesOf s) i 8 := by
  rw [word64_ofNat_iff, Nat.mod_eq_of_lt (beNat_lt s i 8)]

/-- An item that `Slice.index_usize` returns, read with `!` at an equal index. -/
theorem getElem_eq_getElem! {α : Type} [Inhabited α] {l : List α} {i j : Nat} (hij : i = j)
    (h : i < l.length) : l[i] = l[j]! := by
  subst hij; exact (getElem!_pos l i h).symm

/-! ## Bit operations -/

/-- The `|||` of a number shifted past `k` bits and a number below `2 ^ k` is
their sum. -/
theorem or_add {a b : Nat} (k : Nat) (hb : b < 2 ^ k) : a * 2 ^ k ||| b = a * 2 ^ k + b := by
  rw [Nat.mul_comm a, ← Nat.two_pow_add_eq_or_of_lt hb]

/-- The `|||` of two numbers shifted by `n` bits, the first by `k` bits more,
the second below `2 ^ k`. -/
theorem or_shift {a b : Nat} (n k : Nat) (hb : b < 2 ^ k) :
    a * 2 ^ (k + n) ||| b * 2 ^ n = (a * 2 ^ k + b) * 2 ^ n := by
  have : a * 2 ^ (k + n) = (a * 2 ^ k) * 2 ^ n := by rw [Nat.pow_add, Nat.mul_assoc]
  rw [this, ← Nat.shiftLeft_eq (a * 2 ^ k) n, ← Nat.shiftLeft_eq b n, ← Nat.shiftLeft_or_distrib,
    or_add k hb, Nat.shiftLeft_eq]

/-! ## Cells -/

/-- `cellsU64` of the bytes of a slice and a 32-bit count. -/
theorem cellsU64_bytesOf (b : Slice U8) (c : U32) :
    cellsU64 (bytesOf b) (word32 c) =
      if 2 < c.val then .error .unsupportedCells
      else if b.length ≠ c.val * 4 then .error .badProperty
      else .ok (UInt64.ofNat (beNat (bytesOf b) 0 b.length)) := by
  simp only [cellsU64, word32_toNat, bytesOf_size]

/-- `cellsU64` of a count of at most 2 cells and bytes of exactly that many. -/
theorem cellsU64_ok_of {b : Slice U8} {c : U32} (hc : c.val ≤ 2) (hl : b.length = c.val * 4) :
    cellsU64 (bytesOf b) (word32 c) = .ok (UInt64.ofNat (beNat (bytesOf b) 0 b.length)) := by
  simp only [cellsU64_bytesOf, show ¬ 2 < c.val by omega, hl, ne_eq, not_true_eq_false,
    ↓reduceIte]

end Krepi.Proofs.Fdt.Refinement
