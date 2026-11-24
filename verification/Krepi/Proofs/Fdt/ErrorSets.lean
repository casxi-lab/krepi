module

public import Krepi.SpecProperties.Fdt.Properties
import Mathlib.Util.CountHeartbeats
import Krepi.Proofs.Fdt.ExceptLemmas
import Krepi.Proofs.Fdt.SpanLemmas
import Krepi.Proofs.Fdt.PathLemmas

/-!
# Device tree: the errors that an entry can give

`ErrsIn P x`: every error of the result `x` satisfies `P`. A proof that an
entry never takes an error branch shows `ErrsIn (· ≠ e) x` for its result,
one step of its `do` block at a time, without evaluating it:

- the steps: `errsIn_bind`, `errsIn_jp` (the join point of `if c then
  throw e`), `errsIn_ite`, `errsIn_foldlM`, `errsIn_mapM`, the results
  `errsIn_ok`, `errsIn_pure`, `errsIn_error`, `errsIn_throw`,
  `errsIn_throw_bind`, `errsIn_of_ok`, and `errsIn_sub` (a call whose errors
  are among a list, each of which satisfies `P`);
- the tactic `errs_auto`, which applies these steps until only calls are
  left, and closes a call with a lemma that lists its errors (`errs_leaf`,
  extended below by each such lemma);
- the lists of errors of the reads, cells, spans, regions, maps, the node
  access and the steps of the discoveries (`u32At_errs` to
  `compatibleEntries_errs`);
- the walks of the unreachable branches: the header and the tokens never fail
  with `Overflow` (`header_errs`, `walkTokens_errs`, with `header_bounds`),
  and the discoveries of a well-formed tree and the climb of a translation
  never fail with `BadTree` (`discoverMemory_errs`, `climbRanges_errs`,
  with `child_parent` and `findNode_root` for the nodes that they read).

Every step of `errs_auto` unifies at reducible transparency, and the calls
are tried last: a lemma about a call unified with a whole `do` block can
unfold it far.
-/

@[expose] public section

namespace Krepi.Proofs.Fdt

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt

/-! ## Errors of a result -/

/-- Every error of `x` satisfies `P`. -/
def ErrsIn {ε α : Type} (P : ε → Prop) (x : Except ε α) : Prop := ∀ e, x = .error e → P e

theorem errsIn_ok {ε α : Type} {P : ε → Prop} (a : α) : ErrsIn P (Except.ok a : Except ε α) :=
  fun _ h => by cases h

theorem errsIn_pure {ε α : Type} {P : ε → Prop} (a : α) : ErrsIn P (pure a : Except ε α) :=
  fun _ h => by cases h

theorem errsIn_error {ε α : Type} {P : ε → Prop} {e : ε} (h : P e) :
    ErrsIn P (Except.error e : Except ε α) :=
  fun _ he => by cases he; exact h

theorem errsIn_throw {ε α : Type} {P : ε → Prop} {e : ε} (h : P e) :
    ErrsIn P (throw e : Except ε α) :=
  fun _ he => by cases he; exact h

theorem errsIn_of_ok {ε α : Type} {P : ε → Prop} {x : Except ε α} {a : α} (h : x = .ok a) :
    ErrsIn P x := by
  rw [h]; exact errsIn_ok a

/-- The errors of a bind: those of its first step, and those of its
continuation on a value of that step. -/
theorem errsIn_bind {ε α β : Type} {P : ε → Prop} {x : Except ε α} {f : α → Except ε β}
    (hx : ErrsIn P x) (hf : ∀ a, x = .ok a → ErrsIn P (f a)) : ErrsIn P (x >>= f) := by
  intro e h
  cases hxe : x with
  | error e' =>
    rw [hxe] at h
    cases h
    exact hx _ hxe
  | ok a =>
    rw [hxe] at h
    exact hf a hxe e h

theorem errsIn_throw_bind {ε α β : Type} {P : ε → Prop} {e : ε} {f : α → Except ε β}
    (h : P e) : ErrsIn P (throw e >>= f) :=
  fun _ he => by cases he; exact h

/-- The join point that `do` writes for `if c then throw e` without `else`,
read through by unification. -/
theorem errsIn_jp {ε β : Type} {P : ε → Prop} {c : Prop} [Decidable c] {e : ε}
    {k : Unit → Except ε β} (he : c → P e) (hk : ¬ c → ErrsIn P (k ())) :
    ErrsIn P (if c then (throw e >>= k) else k ()) := by
  split
  · exact errsIn_throw_bind (he ‹_›)
  · exact hk ‹_›

theorem errsIn_ite {ε α : Type} {P : ε → Prop} {c : Prop} [Decidable c] {a b : Except ε α}
    (ha : c → ErrsIn P a) (hb : ¬ c → ErrsIn P b) : ErrsIn P (if c then a else b) := by
  split
  · exact ha ‹_›
  · exact hb ‹_›

/-- A call whose errors are among `L`, each of which satisfies `P`. -/
theorem errsIn_sub {ε α : Type} {P : ε → Prop} {L : List ε} {x : Except ε α}
    (h : ErrsIn (· ∈ L) x) (hL : ∀ e ∈ L, P e) : ErrsIn P x :=
  fun e he => hL e (h e he)

/-- The result of an entry never fails with an error outside `P`. -/
theorem ne_of_errsIn {ε α : Type} {P : ε → Prop} {x : Except ε α} {e : ε} (h : ErrsIn P x)
    (he : ¬ P e) : x ≠ .error e :=
  fun hx => he (h e hx)

theorem errsIn_foldlM {ε α β : Type} {P : ε → Prop} {f : β → α → Except ε β} :
    ∀ {l : List α}, (∀ b, ∀ x ∈ l, ErrsIn P (f b x)) → ∀ init, ErrsIn P (l.foldlM f init)
  | [], _, init => by simpa using errsIn_pure (P := P) init
  | x :: l, h, init => by
    rw [List.foldlM_cons]
    exact errsIn_bind (h init x List.mem_cons_self) fun b _ =>
      errsIn_foldlM (fun b y hy => h b y (List.mem_cons_of_mem _ hy)) b

theorem errsIn_mapM {ε α β : Type} {P : ε → Prop} {f : α → Except ε β} :
    ∀ {l : List α}, (∀ x ∈ l, ErrsIn P (f x)) → ErrsIn P (l.mapM f)
  | [], _ => by simpa using errsIn_pure (P := P) ([] : List β)
  | x :: l, h => by
    rw [List.mapM_cons]
    exact errsIn_bind (h x List.mem_cons_self) fun b _ =>
      errsIn_bind (errsIn_mapM fun y hy => h y (List.mem_cons_of_mem _ hy)) fun _ _ =>
        errsIn_pure _

/-! ## The tactic -/

/-- Closes `ErrsIn P (f ...)` for a call `f` with a lemma that lists its
errors; each lemma below adds itself. -/
syntax "errs_leaf" : tactic

/-- `ErrsIn P x` from a lemma `t : ErrsIn (· ∈ L) x` and `∀ e ∈ L, P e` by
`decide`. -/
macro "errs_by " t:term : tactic =>
  `(tactic| ((with_reducible refine errsIn_sub $t ?_) <;> decide))

/-- Takes `ErrsIn P x` apart step by step: results, join points, branches,
folds, binds and matches, and then calls (`errs_leaf`). Goals that it cannot
close are left. -/
macro "errs_auto" : tactic => `(tactic| (repeat' (first
  | with_reducible exact errsIn_pure _
  | with_reducible exact errsIn_ok _
  | with_reducible exact errsIn_throw (by decide)
  | with_reducible exact errsIn_error (by decide)
  | with_reducible exact errsIn_throw_bind (by decide)
  | with_reducible refine errsIn_jp (fun _ => by decide) fun _ => ?_
  | with_reducible refine errsIn_ite (fun _ => ?_) (fun _ => ?_)
  | with_reducible refine errsIn_mapM fun _ _ => ?_
  | with_reducible refine errsIn_foldlM (fun _ _ _ => ?_) _
  | with_reducible refine errsIn_bind ?_ fun _ _ => ?_
  | split
  | errs_leaf)))

/-! ## Reads and cells -/

theorem u32At_errs (b : ByteArray) (i : Nat) : ErrsIn (· ∈ [Error.truncated]) (u32At b i) := by
  unfold u32At
  errs_auto

theorem cString_errs (b : ByteArray) (s : Nat) : ErrsIn (· ∈ [Error.badString]) (cString b s) := by
  unfold cString
  errs_auto

theorem paddedEnd_errs (b : ByteArray) (e : Nat) (z : Bool) :
    ErrsIn (· ∈ [Error.truncated, .badPadding]) (paddedEnd b e z) := by
  unfold paddedEnd
  errs_auto

theorem checkedAdd_errs (a b : Nat) : ErrsIn (· ∈ [Error.overflow]) (checkedAdd a b) := by
  unfold checkedAdd
  errs_auto

theorem spanNew_errs (a b : UInt64) : ErrsIn (· ∈ [Error.overflow]) (Span.new a b) := by
  unfold Span.new
  errs_auto

theorem endAddr_errs (s : Span) : ErrsIn (· ∈ [Error.overflow]) s.endAddr := by
  unfold Span.endAddr
  errs_auto

theorem checkWidth_errs (s : Span) (c : UInt32) :
    ErrsIn (· ∈ [Error.overflow]) (checkWidth s c) := by
  unfold checkWidth
  errs_auto

theorem cellsU64_errs (b : ByteArray) (c : UInt32) :
    ErrsIn (· ∈ [Error.unsupportedCells, .badProperty]) (cellsU64 b c) := by
  unfold cellsU64
  errs_auto

/-- `cells_u64` of at most 2 cells fails only with `BadProperty`. -/
theorem cellsU64_small (b : ByteArray) {c : UInt32} (h : c.toNat ≤ 2) :
    ErrsIn (· ∈ [Error.badProperty]) (cellsU64 b c) := by
  unfold cellsU64
  exact errsIn_ite (fun h' => absurd h (by omega)) fun _ =>
    errsIn_ite (fun _ => errsIn_error (by decide)) fun _ => errsIn_ok _

theorem alignUp_errs (a b : Nat) : ErrsIn (· ∈ [Error.overflow]) (alignUp a b) := by
  unfold alignUp
  errs_auto

macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (u32At_errs _ _))
macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (cString_errs _ _))
macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (paddedEnd_errs _ _ _))
macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (checkedAdd_errs _ _))
macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (spanNew_errs _ _))
macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (endAddr_errs _))
macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (checkWidth_errs _ _))
macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (cellsU64_errs _ _))
macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (alignUp_errs _ _))

/-! ## The node access -/

theorem stringProperty_errs (n : Node) (name : String) :
    ErrsIn (· ∈ [Error.badString, .badProperty]) (n.stringProperty name) := by
  unfold Node.stringProperty
  errs_auto

macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (stringProperty_errs _ _))

theorem enabled_errs (n : Node) : ErrsIn (· ∈ [Error.badString, .badProperty]) n.enabled := by
  unfold Node.enabled
  errs_auto

theorem cellCount_errs (n : Node) (name : String) (d : UInt32) :
    ErrsIn (· ∈ [Error.badProperty, .truncated]) (n.cellCount name d) := by
  unfold Node.cellCount
  errs_auto

theorem addressCells_errs (n : Node) :
    ErrsIn (· ∈ [Error.badProperty, .truncated]) n.addressCells :=
  cellCount_errs _ _ _

theorem sizeCells_errs (n : Node) : ErrsIn (· ∈ [Error.badProperty, .truncated]) n.sizeCells :=
  cellCount_errs _ _ _

theorem flag_errs (n : Node) (name : String) :
    ErrsIn (· ∈ [Error.badProperty]) (n.flag name) := by
  unfold Node.flag
  errs_auto

theorem descend_errs (t : Fdt) :
    ∀ cs cur, ErrsIn (· ∈ [Error.ambiguousMapping]) (t.descend cs cur)
  | [], _ => by rw [Fdt.descend]; exact errsIn_ok _
  | _ :: _, none => by rw [Fdt.descend]; exact errsIn_ok _
  | c :: rest, some p => by
    rw [Fdt.descend]
    split
    · exact descend_errs t rest none
    · exact descend_errs t rest _
    · exact errsIn_error (by decide)

theorem findNode_errs (t : Fdt) (path : String) :
    ErrsIn (· ∈ [Error.badPath, .ambiguousMapping]) (t.findNode path) := by
  unfold Fdt.findNode
  exact errsIn_ite (fun _ => errsIn_error (by decide)) fun _ =>
    errsIn_ite (fun _ => errsIn_ok _) fun _ => errsIn_sub (descend_errs _ _ _) (by decide)

macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (enabled_errs _))
macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (addressCells_errs _))
macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (sizeCells_errs _))
macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (flag_errs _ _))
macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (findNode_errs _ _))

/-! ## Regions, maps and translation -/

theorem regEntry_errs (ac sc : UInt32) (e : ByteArray) :
    ErrsIn (· ∈ [Error.unsupportedCells, .badProperty, .overflow]) (regEntry ac sc e) := by
  unfold regEntry
  errs_auto

macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (regEntry_errs _ _ _))

theorem regNew_errs (b : ByteArray) (ac sc : UInt32) :
    ErrsIn (· ∈ [Error.unsupportedCells, .badProperty, .overflow]) (Reg.new b ac sc) := by
  unfold Reg.new
  errs_auto

theorem window_errs (cc pc sc : UInt32) (e : ByteArray) :
    ErrsIn (· ∈ [Error.unsupportedCells, .badProperty, .emptyRegion, .overflow])
      (window cc pc sc e) := by
  unfold window
  errs_auto

macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (regNew_errs _ _ _))
macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (window_errs _ _ _ _))

theorem addressMapNew_errs (b : Option ByteArray) (cc pc sc : UInt32) :
    ErrsIn (· ∈ [Error.unsupportedCells, .badProperty, .emptyRegion, .overflow])
      (AddressMap.new b cc pc sc) := by
  unfold AddressMap.new
  errs_auto

theorem throughWindows_errs (req : Span) (src tgt : Window → Span) :
    ∀ ws found, ErrsIn (· ∈ [Error.ambiguousMapping, .overflow, .unmapped])
      (throughWindows req src tgt ws found)
  | [], none => errsIn_error (by decide)
  | [], some _ => errsIn_ok _
  | w :: ws, found => by
    rw [throughWindows]
    errs_auto
    all_goals exact throughWindows_errs req src tgt ws _

macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (addressMapNew_errs _ _ _ _))
macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (throughWindows_errs _ _ _ _ _))

theorem translate_errs (m : AddressMap) (s : Span) (r : Bool) :
    ErrsIn (· ∈ [Error.emptyRegion, .overflow, .unmapped, .ambiguousMapping])
      (m.translate s r) := by
  unfold AddressMap.translate
  errs_auto

/-- The `reg` of a node that has a parent. -/
theorem reg_errs {n q : Node} (hp : n.parent = some q) :
    ErrsIn (· ∈ [Error.missingProperty, .badProperty, .truncated, .unsupportedCells, .overflow])
      n.reg := by
  unfold Node.reg
  rw [hp]
  errs_auto

/-- The `ranges` of a node that has a parent. -/
theorem ranges_errs {n q : Node} (hp : n.parent = some q) :
    ErrsIn (· ∈ [Error.badProperty, .truncated, .unsupportedCells, .emptyRegion, .overflow])
      n.ranges := by
  unfold Node.ranges Node.addressMap
  rw [hp]
  errs_auto

macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (translate_errs _ _ _))
macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (reg_errs (by assumption)))

/-- The climb of a translation never fails with `BadTree`: it reads the
`ranges` of a bus only when the bus has a parent. -/
theorem climbRanges_errs :
    ∀ fuel bus s, ErrsIn (· ≠ .badTree) (climbRanges fuel bus s)
  | 0, _, _ => errsIn_error (by decide)
  | fuel + 1, bus, s => by
    rw [climbRanges]
    split
    · exact errsIn_ok _
    · rename_i up hup
      refine errsIn_bind (errsIn_sub (ranges_errs hup) (by decide)) fun m _ => ?_
      refine errsIn_bind (errsIn_sub (translate_errs _ _ _) (by decide)) fun s' _ => ?_
      exact climbRanges_errs fuel up s'

/-! ## The parse -/

/-- A block whose end is within 64 bits never fails with `Overflow`. -/
theorem block_errs (blob : ByteArray) {s z : Nat} (h : s + z < 2 ^ 64) :
    ErrsIn (· ≠ .overflow) (block blob s z) := by
  unfold block
  refine errsIn_jp (fun _ => by decide) fun _ => ?_
  refine errsIn_bind (errsIn_of_ok (checkedAdd_ok.2 ⟨h, rfl⟩)) fun e _ => ?_
  exact errsIn_jp (fun _ => by decide) fun _ => errsIn_pure _

/-- Step 1 of the parse never fails with `Overflow`: each block starts and
ends at 32-bit words. -/
theorem header_errs (input : ByteArray) : ErrsIn (· ≠ .overflow) (header input) := by
  have hw : ∀ b i, ErrsIn (· ≠ Error.overflow) (u32At b i) := fun b i =>
    errsIn_sub (u32At_errs b i) (by decide)
  unfold header
  refine errsIn_jp (fun _ => by decide) fun _ => ?_
  refine errsIn_bind (hw _ _) fun _ _ => ?_
  refine errsIn_jp (fun _ => by decide) fun _ => ?_
  refine errsIn_bind (hw _ _) fun _ _ => ?_
  refine errsIn_jp (fun _ => by decide) fun _ => ?_
  refine errsIn_jp (fun _ => by decide) fun _ => ?_
  refine errsIn_jp (fun _ => by decide) fun _ => ?_
  refine errsIn_bind (hw _ _) fun _ _ => ?_
  refine errsIn_bind (hw _ _) fun _ _ => ?_
  refine errsIn_jp (fun _ => by decide) fun _ => ?_
  refine errsIn_bind (hw _ _) fun a _ => ?_
  refine errsIn_bind (hw _ _) fun b _ => ?_
  refine errsIn_bind (hw _ _) fun _ _ => ?_
  refine errsIn_bind (hw _ _) fun c _ => ?_
  refine errsIn_bind (hw _ _) fun d _ => ?_
  refine errsIn_jp (fun _ => by decide) fun _ => ?_
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  refine errsIn_bind (block_errs _ (by omega)) fun _ _ => ?_
  refine errsIn_bind (block_errs _ (by omega)) fun _ _ => ?_
  refine errsIn_jp (fun _ => by decide) fun _ => ?_
  exact errsIn_jp (fun _ => by decide) fun _ => errsIn_pure _

/-- A block has at most the size that the header gives it. -/
theorem block_size {blob : ByteArray} {s z : Nat} {b : ByteArray}
    (h : block blob s z = .ok b) : b.size ≤ z := by
  unfold block at h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨e, he, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  rw [except_pure_ok] at h
  subst h
  rw [ByteArray.size_extract]
  have := (checkedAdd_ok.1 he).2
  omega

/-- The reservation map of a header starts at a 32-bit offset, and its
structure block has fewer than `2 ^ 32` bytes. -/
theorem header_bounds {input : ByteArray} {hd : Header} (h : header input = .ok hd) :
    hd.layout.reserveStart < 2 ^ 32 ∧ hd.structure_.size < 2 ^ 32 := by
  unfold header at h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨_, -, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨_, -, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨_, -, h⟩ := except_bind_ok.1 h
  obtain ⟨_, -, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨_, -, h⟩ := except_bind_ok.1 h
  obtain ⟨_, -, h⟩ := except_bind_ok.1 h
  obtain ⟨r, -, h⟩ := except_bind_ok.1 h
  obtain ⟨_, -, h⟩ := except_bind_ok.1 h
  obtain ⟨d, -, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨st, hst, h⟩ := except_bind_ok.1 h
  obtain ⟨_, -, h⟩ := except_bind_ok.1 h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨-, h⟩ := except_jp_ok h
  have h := except_pure_ok.1 h
  subst h
  exact ⟨r.toNat_lt, Nat.lt_of_le_of_lt (block_size hst) d.toNat_lt⟩

theorem u32At_le {b : ByteArray} {i : Nat} {v : UInt32} (h : u32At b i = .ok v) :
    i + 4 ≤ b.size := by
  unfold u32At at h
  split at h
  · assumption
  · cases h

/-- A token of a block of fewer than `2 ^ 32` bytes never fails with
`Overflow`: a value starts within the block and its length is a 32-bit
word. -/
theorem decodeToken_errs {str : ByteArray} (strs : ByteArray) (hs : str.size < 2 ^ 32)
    (c : Nat) : ErrsIn (· ≠ .overflow) (decodeToken str strs c) := by
  unfold decodeToken
  refine errsIn_bind (errsIn_sub (u32At_errs _ _) (by decide)) fun tag _ => ?_
  split
  · errs_auto
  · exact errsIn_pure _
  · refine errsIn_bind (errsIn_sub (u32At_errs _ _) (by decide)) fun len _ => ?_
    refine errsIn_bind (errsIn_sub (u32At_errs _ _) (by decide)) fun off hoff => ?_
    have h1 := u32At_le hoff
    have h2 := len.toNat_lt
    refine errsIn_bind (errsIn_of_ok (checkedAdd_ok.2 ⟨by omega, rfl⟩)) fun _ _ => ?_
    errs_auto
  · exact errsIn_pure _
  · exact errsIn_pure _
  · exact errsIn_throw (by decide)

theorem place_errs (w : Walk) (tok : Token) : ErrsIn (· ≠ .overflow) (w.place tok) := by
  unfold Walk.place
  cases tok <;> errs_auto

/-- The walk of a structure block of fewer than `2 ^ 32` bytes never fails
with `Overflow`. -/
theorem walkTokens_errs {str : ByteArray} (strs : ByteArray) (hs : str.size < 2 ^ 32) :
    ∀ fuel c w, ErrsIn (· ≠ .overflow) (walkTokens str strs fuel c w)
  | 0, _, _ => errsIn_error (by decide)
  | fuel + 1, c, w => by
    rw [walkTokens]
    refine errsIn_bind (decodeToken_errs strs hs c) fun p _ => ?_
    split
    split
    · exact errsIn_jp (fun _ => by decide) fun _ => errsIn_pure _
    · exact errsIn_bind (place_errs _ _) fun w' _ => walkTokens_errs strs hs fuel _ w'

/-! ## The discoveries -/

theorem pushReserved_errs (l : List ReservedRegion) (r : ReservedRegion) :
    ErrsIn (· ∈ [Error.limitExceeded]) (pushReserved l r) := by
  unfold pushReserved
  errs_auto

theorem addRam_errs (l : List Span) (s : Span) :
    ErrsIn (· ∈ [Error.emptyRegion, .overlap, .limitExceeded]) (addRam l s) := by
  unfold addRam
  errs_auto

macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (pushReserved_errs _ _))
macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (addRam_errs _ _))

theorem addReservedSpan_errs (a b : Bool) (l : List ReservedRegion) (s : Span) :
    ErrsIn (· ∈ [Error.emptyRegion, .limitExceeded]) (addReservedSpan a b l s) := by
  unfold addReservedSpan
  errs_auto

theorem reservedMemoryBinding_errs (p r : Node) :
    ErrsIn (· ∈ [Error.badProperty, .truncated]) (reservedMemoryBinding p r) := by
  unfold reservedMemoryBinding
  errs_auto

theorem compatibleEntries_errs :
    ∀ l, ErrsIn (· ∈ [Error.badString, .badProperty]) (compatibleEntries l)
  | [] => errsIn_ok _
  | e :: rest => by
    rw [compatibleEntries]
    errs_auto
    all_goals exact compatibleEntries_errs rest

macro_rules | `(tactic| errs_leaf) => `(tactic| errs_by (addReservedSpan_errs _ _ _ _))

/-- A child of a node of a tree has a parent. -/
theorem child_parent {t : Fdt} {p c : Node} (hp : p ∈ t.nodes)
    (hc : c ∈ t.nodes.filter (·.isChildOf p)) : ∃ q, c.parent = some q := by
  obtain ⟨hcm, hch⟩ := List.mem_filter.1 hc
  simp only [Fdt.nodes, List.mem_map, List.mem_finRange, true_and] at hp hcm
  obtain ⟨i, rfl⟩ := hp
  obtain ⟨j, rfl⟩ := hcm
  unfold Node.isChildOf at hch
  have h : (⟨t, j⟩ : Node).record.parent = some i.val := by simpa using hch
  unfold Node.parent
  rw [h]
  simp [i.isLt]

theorem ramOfChild_errs {n q : Node} (hp : n.parent = some q) (acc : List Span) :
    ErrsIn (· ≠ .badTree) (ramOfChild acc n) := by
  unfold ramOfChild
  errs_auto

theorem reservedOfChild_errs {n q : Node} (hp : n.parent = some q)
    (acc : List ReservedRegion × Nat) : ErrsIn (· ≠ .badTree) (reservedOfChild acc n) := by
  unfold reservedOfChild
  errs_auto

theorem reservedMemory_errs {t : Fdt} (ht : t.WellFormed) (root : Node)
    (mapped : List ReservedRegion) : ErrsIn (· ≠ .badTree) (t.reservedMemory root mapped) := by
  unfold Fdt.reservedMemory
  refine errsIn_bind (errsIn_sub (findNode_errs _ _) (by decide)) fun x hx => ?_
  split
  · exact errsIn_pure _
  · rename_i parent
    have hpm : parent ∈ t.nodes :=
      (findNode_single ht (c := "reserved-memory".toList) (by decide) (by decide) (by decide)
        hx).1
    refine errsIn_bind (errsIn_sub (reservedMemoryBinding_errs _ _) (by decide)) fun _ _ => ?_
    refine errsIn_bind (errsIn_sub (enabled_errs _) (by decide)) fun _ _ => ?_
    refine errsIn_ite (fun _ => errsIn_pure _) fun _ => ?_
    refine errsIn_foldlM (fun acc c hc => ?_) _
    obtain ⟨q, hq⟩ := child_parent hpm hc
    exact reservedOfChild_errs hq acc

/-- The lookup of `/` in a well-formed tree gives its root, the node of
index 0. -/
theorem findNode_root {t : Fdt} (ht : t.WellFormed) {x : Option Node}
    (hx : t.findNode "/" = .ok x) : x = some ⟨t, ⟨0, ht.2.2.2.2.2.1⟩⟩ := by
  rw [findNode_slash (by decide)] at hx
  cases hx
  simp [Fdt.root, ht.2.2.2.2.2.1]

/-- The memory discovery of a well-formed tree never fails with `BadTree`. -/
theorem discoverMemory_errs {t : Fdt} (ht : t.WellFormed) :
    ErrsIn (· ≠ .badTree) t.discoverMemory := by
  unfold Fdt.discoverMemory
  refine errsIn_bind (errsIn_foldlM (fun _ _ _ => errsIn_sub (pushReserved_errs _ _)
    (by decide)) _) fun mapped _ => ?_
  refine errsIn_bind (errsIn_sub (findNode_errs _ _) (by decide)) fun x hx => ?_
  cases findNode_root ht hx
  refine errsIn_bind (errsIn_foldlM (fun acc c hc => ?_) _) fun ram _ => ?_
  · obtain ⟨q, hq⟩ := child_parent (node_mem t _) hc
    exact ramOfChild_errs hq acc
  · refine errsIn_jp (fun _ => by decide) fun _ => ?_
    exact errsIn_bind (reservedMemory_errs ht _ _) fun _ _ => errsIn_pure _

macro_rules | `(tactic| errs_leaf) => `(tactic| with_reducible exact discoverMemory_errs ‹_›)

end Krepi.Proofs.Fdt
