module

public import Krepi.Proofs.Fdt.Refinement.TreeSpecLemmas
import Krepi.Proofs.Fdt.ExceptLemmas

/-!
# Device tree: lemmas about the specification of the walk over the tokens

Lemmas about `walkTokens` and `decodeToken` of `Krepi.Spec.Fdt.Parse` for the
refinement proof of `Fdt::parse`, whose walk over the tokens of the structure
block checks each token as the specification does but builds no records. The
module imports no generated definitions, so it is built once and not again for
every mutant of the code.

- The names of the properties of a node so far: `NamesFrom` (the tokens from
  the token after a begin node up to a cursor are properties and
  no-operations, and these are the names of the properties), with
  `NamesFrom.le`, `NamesFrom.cases_lt`, `NamesFrom.eq_nil`,
  `NamesFrom.snoc_nop` and `NamesFrom.snoc_prop`: what `repeats_name` walks.
- The walk of the code on numbers: `MFrame` (an open node of the code: where
  its properties start, how many it has, whether a child has begun), `MWalk`
  (the table of frames, the number of open nodes, whether the root has
  begun), and the steps of the code on them, `MWalk.beginNode` (with
  `MWalk.push`, `markChild`, `MFrame.mark`), `MWalk.endNode`,
  `MWalk.property` (with `MFrame.bump`, the answer of `repeats_name` given)
  and `MWalk.endStructure`.
- The relation of the two walks: `MRel` (the first frames of the table stand
  for the open nodes of the specification, innermost last, with the same
  depth, root and children; every open node but the innermost has a child;
  and the innermost, while it has no child, counts its properties and starts
  them where `NamesFrom` reads their names up to the cursor), `mrel_start`,
  `mrel_open_cons`, `mrel_push`, and one lemma per token: `mrel_begin`,
  `mrel_property`, `mrel_endNode`, `mrel_nop` and `mrel_end`, with `Follows`
  (a step of the code and the place of the specification fail with the same
  error or succeed with related walks).
- One token of the walk: `stepOf` (the place of a token, none for the end
  token that ends the walk), `walkTokens_succ` (the walk as one `stepOf` after
  `decodeToken`), `Placed` (what a step of the code returns against
  `stepOf`), `follows_place`, `placed_end` and `placed_nop`; the closed forms
  `place_begin_nil`, `place_begin_cons`, `place_property_nil` and
  `place_property_cons` of `Walk.place`.
- Results of the code against the specification: `check_else_spec` (an `if`
  of the code that fails in its other branch, against an `if c then throw e`
  of the specification on the negated condition) and `agrees_true_of_map_eq`
  (a result whose value is not compared agrees with specifications that agree
  once their values are forgotten).
- The decoding of a token as the code tests its tag: `decodeBegin`,
  `decodeProperty`, `decodeTag` and `decodeToken_eq`.
- Lists: `rev_take_succ`, `take_set_self`, `take_set_succ`,
  `getElem!_set_self`, `getElem!_of_forall`, `forall_set` and
  `forall2_set_last`.
-/

@[expose] public section

open Krepi.Statements Krepi.Spec.Fdt Krepi.Proofs.Fdt

namespace Krepi.Proofs.Fdt.Refinement

variable {str strs : ByteArray}

/-! ## The names of the properties of a node so far -/

/-- `NamesFrom str strs a c names`: the tokens of the structure block `str`
from `a` up to `c`, as `decodeToken` reads them with the strings block
`strs`, are properties and no-operations, and `names` are the names of the
properties in their order. These are the tokens that `repeats_name` walks from
the token after the begin node of the innermost open node to the cursor. -/
inductive NamesFrom (str strs : ByteArray) : Nat → Nat → List String → Prop
  | nil (c : Nat) : NamesFrom str strs c c []
  | nop {a next c : Nat} {names : List String} :
      decodeToken str strs a = .ok (.nop, next) → NamesFrom str strs next c names →
      NamesFrom str strs a c names
  | prop {a next c : Nat} {nm : String} {v : ByteArray} {names : List String} :
      decodeToken str strs a = .ok (.property nm v, next) → NamesFrom str strs next c names →
      NamesFrom str strs a c (nm :: names)

/-- The tokens of `NamesFrom` end at or after their start. -/
theorem NamesFrom.le {a c : Nat} {names : List String} (h : NamesFrom str strs a c names) :
    a ≤ c := by
  induction h with
  | nil => exact Nat.le_refl _
  | nop hd _ ih => have := decodeToken_next_ge hd; omega
  | prop hd _ ih => have := decodeToken_next_ge hd; omega

/-- Tokens of `NamesFrom` before the cursor: a no-operation or a property,
and the rest after it. -/
theorem NamesFrom.cases_lt {a c : Nat} {names : List String} (h : NamesFrom str strs a c names)
    (hac : a < c) :
    (∃ next, decodeToken str strs a = .ok (.nop, next) ∧ NamesFrom str strs next c names) ∨
    (∃ nm v next rest, names = nm :: rest ∧
      decodeToken str strs a = .ok (.property nm v, next) ∧ NamesFrom str strs next c rest) := by
  cases h with
  | nil => omega
  | nop hd h => exact .inl ⟨_, hd, h⟩
  | prop hd h => exact .inr ⟨_, _, _, _, rfl, hd, h⟩

/-- No token of `NamesFrom` at or after the cursor: no names. -/
theorem NamesFrom.eq_nil {a c : Nat} {names : List String} (h : NamesFrom str strs a c names)
    (hac : ¬ a < c) : names = [] := by
  cases h with
  | nil => rfl
  | nop hd h => have := decodeToken_next_ge hd; have := h.le; omega
  | prop hd h => have := decodeToken_next_ge hd; have := h.le; omega

/-- A no-operation at the cursor: the same names up to the next token. -/
theorem NamesFrom.snoc_nop {a c next : Nat} {names : List String}
    (h : NamesFrom str strs a c names) (hd : decodeToken str strs c = .ok (.nop, next)) :
    NamesFrom str strs a next names := by
  induction h with
  | nil c => exact .nop hd (.nil next)
  | nop hd' _ ih => exact .nop hd' (ih hd)
  | prop hd' _ ih => exact .prop hd' (ih hd)

/-- A property at the cursor: its name after the names so far. -/
theorem NamesFrom.snoc_prop {a c next : Nat} {names : List String} {nm : String} {v : ByteArray}
    (h : NamesFrom str strs a c names) (hd : decodeToken str strs c = .ok (.property nm v, next)) :
    NamesFrom str strs a next (names ++ [nm]) := by
  induction h with
  | nil c => exact .prop hd (.nil next)
  | nop hd' _ ih => exact .nop hd' (ih hd)
  | prop hd' _ ih => exact .prop hd' (ih hd)

/-! ## The walk of the code -/

/-- An open node of the walk of the code: the offset of the token after its
begin node, the number of its properties so far, and whether a child has
begun in it. -/
structure MFrame where
  properties : Nat
  count : Nat
  children : Bool
  deriving Inhabited

/-- The walk of the code: its table of frames, the open nodes first, innermost
last; the number of open nodes; and whether the root has begun. -/
structure MWalk where
  frames : List MFrame
  open_ : Nat
  seenRoot : Bool

/-- A frame in which a child has begun. -/
def MFrame.mark (f : MFrame) : MFrame := { f with children := true }

/-- The table of frames after a child begins in the innermost of the `o` open
nodes. -/
def markChild (frames : List MFrame) (o : Nat) : List MFrame :=
  if 0 < o then frames.set (o - 1) (frames[o - 1]!).mark else frames

/-- A node that the code opens: `LimitExceeded` at the depth `MAX_DEPTH`,
otherwise a new innermost frame at `next`. -/
def MWalk.push (w : MWalk) (next : Nat) : Except Error MWalk :=
  if MAX_DEPTH.toNat ≤ w.open_ then .error .limitExceeded
  else .ok ⟨(markChild w.frames w.open_).set w.open_ ⟨next, 0, false⟩, w.open_ + 1, true⟩

/-- A begin node as the code places it: outside every node it must be the
first root and have an empty name, inside a node it must have a name. -/
def MWalk.beginNode (w : MWalk) (empty : Bool) (next : Nat) : Except Error MWalk :=
  if w.open_ = 0 then
    if w.seenRoot then .error .badTree else if empty then w.push next else .error .badTree
  else if empty then .error .badTree else w.push next

/-- An end node as the code places it: it closes the innermost open node. -/
def MWalk.endNode (w : MWalk) : Except Error MWalk :=
  if w.open_ = 0 then .error .badTree else .ok { w with open_ := w.open_ - 1 }

/-- A frame with one property more. -/
def MFrame.bump (f : MFrame) : MFrame := { f with count := f.count + 1 }

/-- A property as the code places it, with `dup` the answer of `repeats_name`:
it belongs to the innermost open node, before its children, within
`MAX_PROPERTIES`, with a new name. -/
def MWalk.property (w : MWalk) (dup : Bool) : Except Error MWalk :=
  if w.open_ = 0 then .error .badTree
  else if (w.frames[w.open_ - 1]!).children then .error .badTree
  else if MAX_PROPERTIES.toNat < (w.frames[w.open_ - 1]!).count + 1 then .error .limitExceeded
  else if dup then .error .duplicateProperty
  else .ok { w with frames := w.frames.set (w.open_ - 1) (w.frames[w.open_ - 1]!).bump }

/-- The end token as the code checks it: after the root, with no open node, at
the end of the block of `length` bytes. -/
def MWalk.endStructure (w : MWalk) (next length : Nat) : Except Error Bool :=
  if w.seenRoot then
    if w.open_ ≠ 0 then .error .badTree else if next ≠ length then .error .badTree else .ok true
  else .error .badTree

/-- `MRel str strs m W c`: the walk `m` of the code stands for the walk `W` of
the specification at the cursor `c` of the structure block `str` with the
strings block `strs`. -/
structure MRel (str strs : ByteArray) (m : MWalk) (W : Walk) (c : Nat) : Prop where
  length : m.frames.length = MAX_DEPTH.toNat
  depth : m.open_ = W.open_.length
  le : m.open_ ≤ MAX_DEPTH.toNat
  seen : m.seenRoot = W.seenRoot
  counts : ∀ f ∈ m.frames, f.count ≤ MAX_PROPERTIES.toNat
  children : List.Forall₂ (fun a b => a.children = b.children) (m.frames.take m.open_).reverse
    W.open_
  outer : ∀ f ∈ W.open_.tail, f.children = true
  inner : ∀ f rest, W.open_ = f :: rest → f.children = false →
    (m.frames[m.open_ - 1]!).count = f.names.length ∧
      NamesFrom str strs (m.frames[m.open_ - 1]!).properties c f.names

/-- A step of `MWalk` and the place of the specification: both fail with the
same error, or both succeed with walks that `MRel` relates at `next`. -/
def Follows (str strs : ByteArray) (next : Nat) : Except Error MWalk → Except Error Walk → Prop
  | .ok m, .ok W => MRel str strs m W next
  | .error e, .error e' => e = e'
  | _, _ => False

/-- What a step of the code returns, `b` whether the walk ends, against what
`stepOf` gives: the end, or a walk that the walk `m` of the code stands for
at `next`. -/
def Placed (str strs : ByteArray) (m : MWalk) (next : Nat) (b : Bool) : Option Walk → Prop
  | none => b = true
  | some W => b = false ∧ MRel str strs m W next

/-- One token of `walkTokens` after its decoding: the end token ends the walk
(none) or fails, any other token is placed (`Walk.place`). -/
def stepOf (W : Walk) (tok : Token) (next length : Nat) : Except Error (Option Walk) :=
  match tok with
  | .endStructure =>
    if !W.seenRoot || !W.open_.isEmpty || next ≠ length then .error .badTree else .ok none
  | tok => some <$> W.place tok

/-- `walkTokens` as one `stepOf` after `decodeToken`. -/
theorem walkTokens_succ (f c : Nat) (W : Walk) :
    walkTokens str strs (f + 1) c W = decodeToken str strs c >>= fun p =>
      stepOf W p.1 p.2 str.size >>= fun o => match o with
        | none => .ok W.records
        | some W' => walkTokens str strs f p.2 W' := by
  rw [walkTokens]
  cases decodeToken str strs c with
  | error e => rfl
  | ok p =>
    obtain ⟨tok, next⟩ := p
    simp only [except_ok_bind]
    cases tok with
    | endStructure =>
      simp only [stepOf]
      split <;> rfl
    | _ =>
      simp only [stepOf]
      cases W.place _ <;> rfl

/-- A step of the code that returns what a step of `MWalk` gives, which follows
the place of the specification, returns what `stepOf` gives. -/
theorem follows_place {ε : Type} {err : ε → Error} {r : Aeneas.Std.core.result.Result Bool ε}
    {m' : MWalk} {M : Except Error MWalk} {E : Except Error Walk} {next : Nat}
    (h1 : Agrees (fun b m => b = false ∧ m' = m) err r M)
    (h2 : Follows str strs next M E) :
    Agrees (Placed str strs m' next) err r (some <$> E) := by
  cases r <;> cases M <;> cases E <;>
    simp_all [Agrees, Follows, Placed, Functor.map, Except.map]


/-- `Walk.place` of a begin node outside every node. -/
theorem place_begin_nil (sr : Bool) (recs : Array NodeRecord) (nm : String) :
    ({ open_ := [], seenRoot := sr, records := recs } : Walk).place (.beginNode nm) =
      if sr = true ∨ nm ≠ "" then .error .badTree
      else .ok ⟨[⟨recs.size, [], false⟩], true, recs.push ⟨nm, none, []⟩⟩ := by
  by_cases h1 : sr = true <;> by_cases h2 : nm = "" <;>
    simp [Walk.place, h1, h2, MAX_DEPTH] <;> rfl

/-- `Walk.place` of a begin node inside a node. -/
theorem place_begin_cons (f : Frame) (rest : List Frame) (sr : Bool) (recs : Array NodeRecord)
    (nm : String) :
    ({ open_ := f :: rest, seenRoot := sr, records := recs } : Walk).place (.beginNode nm) =
      if nm = "" then .error .badTree
      else if MAX_DEPTH.toNat ≤ rest.length + 1 then .error .limitExceeded
      else .ok ⟨⟨recs.size, [], false⟩ :: { f with children := true } :: rest, true,
        recs.push ⟨nm, some f.index, []⟩⟩ := by
  by_cases h2 : nm = "" <;> by_cases h3 : MAX_DEPTH.toNat ≤ rest.length + 1 <;>
    simp [Walk.place, h2, h3] <;> rfl

/-- `Walk.place` of a property outside every node. -/
theorem place_property_nil (sr : Bool) (recs : Array NodeRecord) (nm : String) (v : ByteArray) :
    ({ open_ := [], seenRoot := sr, records := recs } : Walk).place (.property nm v) =
      .error .badTree := rfl

/-- `Walk.place` of a property inside a node. -/
theorem place_property_cons (f : Frame) (rest : List Frame) (sr : Bool) (recs : Array NodeRecord)
    (nm : String) (v : ByteArray) :
    ({ open_ := f :: rest, seenRoot := sr, records := recs } : Walk).place (.property nm v) =
      if f.children = true then .error .badTree
      else if MAX_PROPERTIES.toNat < f.names.length + 1 then .error .limitExceeded
      else if f.names.contains nm = true then .error .duplicateProperty
      else .ok ⟨{ f with names := f.names ++ [nm] } :: rest, sr,
        recs.modify f.index fun r => { r with properties := r.properties ++ [(nm, v)] }⟩ := by
  simp only [Walk.place]
  split_ifs <;> rfl


/-! ## Lists -/

theorem rev_take_succ {α : Type} [Inhabited α] (l : List α) {i : Nat} (h : i < l.length) :
    (l.take (i + 1)).reverse = l[i]! :: (l.take i).reverse := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, List.reverse_append]
  simp [h]

theorem take_set_self {α : Type} (l : List α) (i : Nat) (x : α) :
    (l.set i x).take i = l.take i := by
  rw [List.take_set, List.set_eq_of_length_le (by simp)]

theorem take_set_succ {α : Type} (l : List α) {i : Nat} (h : i < l.length) (x : α) :
    (l.set i x).take (i + 1) = l.take i ++ [x] := by
  rw [List.take_add_one, List.getElem?_set_self h]
  simp [List.take_set, List.set_eq_of_length_le]

theorem getElem!_set_self {α : Type} [Inhabited α] (l : List α) {i : Nat} (h : i < l.length)
    (x : α) : (l.set i x)[i]! = x := by simp [h]

theorem getElem!_of_forall {α : Type} [Inhabited α] {l : List α} {P : α → Prop} (hd : P default)
    (h : ∀ a ∈ l, P a) (i : Nat) : P l[i]! := by
  rw [List.getElem!_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => exact hd
  | some a => exact h a (List.mem_of_getElem? hi)

theorem forall_set {α : Type} {l : List α} {P : α → Prop} (h : ∀ a ∈ l, P a) {x : α} (hx : P x)
    (i : Nat) : ∀ a ∈ l.set i x, P a := fun a ha =>
  (List.mem_or_eq_of_mem_set ha).elim (h a) (fun e => e ▸ hx)

/-- The last of the first `i + 1` frames replaced: the relation of the frames
to the open nodes, innermost first, with the innermost replaced. -/
theorem forall2_set_last {α β : Type} [Inhabited α] {R : α → β → Prop} {l : List α} {i : Nat}
    (hi : i < l.length) {b : β} {rest : List β}
    (h : List.Forall₂ R (l.take (i + 1)).reverse (b :: rest))
    {x : α} {b' : β} (hx : R x b') :
    List.Forall₂ R ((l.set i x).take (i + 1)).reverse (b' :: rest) := by
  rw [rev_take_succ _ hi] at h
  rw [take_set_succ _ hi, List.reverse_append]
  exact List.Forall₂.cons hx (List.forall₂_cons.mp h).2

/-! ## The relation of the walk of the code to the walk of the specification -/

/-- The walks before the first token. -/
theorem mrel_start : MRel str strs ⟨List.replicate 32 ⟨0, 0, false⟩, 0, false⟩ Walk.start 0 where
  length := rfl
  depth := rfl
  le := by decide
  seen := rfl
  counts := fun f hf => by rw [List.eq_of_mem_replicate hf]; decide
  children := by simp [Walk.start]
  outer := fun f hf => by simp [Walk.start] at hf
  inner := fun f rest h => by simp [Walk.start] at h

/-- Some node is open: the innermost open node of the specification and its
frame. -/
theorem mrel_open_cons {m : MWalk} {W : Walk} {c : Nat} (h : MRel str strs m W c)
    (ho : m.open_ ≠ 0) : ∃ f rest, W.open_ = f :: rest ∧
      (m.frames[m.open_ - 1]!).children = f.children ∧
      List.Forall₂ (fun a b => a.children = b.children) (m.frames.take (m.open_ - 1)).reverse
        rest := by
  have hlt : m.open_ - 1 < m.frames.length := by have := h.le; have := h.length; omega
  have hc := h.children
  rw [show m.open_ = m.open_ - 1 + 1 by omega, rev_take_succ _ hlt] at hc
  cases hW : W.open_ with
  | nil => rw [hW] at hc; cases hc
  | cons f rest =>
    rw [hW] at hc
    exact ⟨f, rest, rfl, (List.forall₂_cons.mp hc).1, (List.forall₂_cons.mp hc).2⟩

/-- A node that both walks open. -/
theorem mrel_push {m : MWalk} {W W' : Walk} {c next : Nat} (h : MRel str strs m W c)
    (hd : m.open_ < MAX_DEPTH.toNat)
    (ho : W'.open_ = ⟨W.records.size, [], false⟩ ::
      W.open_.modifyHead (fun f => { f with children := true }))
    (hs : W'.seenRoot = true) :
    MRel str strs ⟨(markChild m.frames m.open_).set m.open_ ⟨next, 0, false⟩, m.open_ + 1, true⟩ W'
      next := by
  have hmk : (markChild m.frames m.open_).length = m.frames.length := by
    unfold markChild; split <;> simp
  have hlt : m.open_ < (markChild m.frames m.open_).length := by rw [hmk, h.length]; exact hd
  have hcm : ∀ f ∈ markChild m.frames m.open_, f.count ≤ MAX_PROPERTIES.toNat := by
    unfold markChild; split
    · exact forall_set h.counts (show (m.frames[m.open_ - 1]!).mark.count ≤ _ from
        getElem!_of_forall (P := fun f : MFrame => f.count ≤ _) (Nat.zero_le _) h.counts _) _
    · exact h.counts
  refine ⟨by simp [hmk, h.length], by simp [ho, h.depth], by show m.open_ + 1 ≤ _; omega,
    hs.symm, forall_set hcm (Nat.zero_le _) _, ?_, ?_, ?_⟩
  · rw [rev_take_succ _ (by simpa using hlt), getElem!_set_self _ hlt, take_set_self, ho]
    refine List.Forall₂.cons rfl ?_
    unfold markChild
    split
    · rename_i hpos
      obtain ⟨f, rest, hW, -, -⟩ := mrel_open_cons h (by omega)
      have hc := h.children
      rw [hW] at hc ⊢
      rw [show m.open_ = m.open_ - 1 + 1 by omega] at hc ⊢
      exact forall2_set_last (by have := h.length; have := h.le; omega) hc rfl
    · rename_i hpos
      have h0 : m.open_ = 0 := by omega
      have hW : W.open_ = [] := by
        have := h.depth; rw [h0] at this; exact List.eq_nil_of_length_eq_zero this.symm
      rw [hW, h0]; exact List.Forall₂.nil
  · rw [ho]
    intro f hf
    cases hW : W.open_ with
    | nil => rw [hW] at hf; cases hf
    | cons g rest =>
      rw [hW] at hf
      simp only [List.tail_cons, List.modifyHead_cons, List.mem_cons] at hf
      rcases hf with rfl | hf
      · rfl
      · exact h.outer f (by rw [hW]; exact hf)
  · intro f rest hW' _
    rw [ho] at hW'
    cases hW'
    rw [Nat.add_sub_cancel, getElem!_set_self _ hlt]
    exact ⟨rfl, .nil next⟩

/-- A begin node: the step of the code follows the place of the specification.
-/
theorem mrel_begin {m : MWalk} {W : Walk} {c next : Nat} {nm : String} (h : MRel str strs m W c) :
    Follows str strs next (m.beginNode (decide (nm = "")) next) (W.place (.beginNode nm)) := by
  obtain ⟨op, sr, recs⟩ := W
  have hseen := h.seen
  have hdep := h.depth
  simp only at hseen hdep
  cases op with
  | nil =>
    rw [place_begin_nil]
    simp only [List.length_nil] at hdep
    by_cases hs : sr = true
    · simp [MWalk.beginNode, hdep, hseen, hs, Follows]
    · by_cases hn : nm = ""
      · subst hn
        have hd : m.open_ < MAX_DEPTH.toNat := by rw [hdep]; decide
        have h32 : ¬ MAX_DEPTH.toNat ≤ 0 := by decide
        simp only [MWalk.beginNode, hdep, hseen, hs, ↓reduceIte, decide_true, MWalk.push,
          Bool.false_eq_true, ne_eq, not_true_eq_false, or_self, h32, Follows]
        have := mrel_push (next := next)
          (W' := ⟨[⟨recs.size, [], false⟩], true, recs.push ⟨"", none, []⟩⟩) h hd rfl rfl
        rw [hdep] at this
        exact this
      · simp [MWalk.beginNode, hdep, hseen, hs, hn, Follows]
  | cons f rest =>
    rw [place_begin_cons]
    simp only [List.length_cons] at hdep
    by_cases hn : nm = ""
    · simp [MWalk.beginNode, hdep, hn, Follows]
    · by_cases hd : MAX_DEPTH.toNat ≤ rest.length + 1
      · simp [MWalk.beginNode, MWalk.push, hdep, hn, hd, Follows]
      · simp only [MWalk.beginNode, MWalk.push, hdep, hn, hd, ↓reduceIte, decide_false,
          Nat.add_eq_zero_iff, one_ne_zero, and_false, Bool.false_eq_true, Follows]
        have := mrel_push (next := next)
          (W' := ⟨⟨recs.size, [], false⟩ :: { f with children := true } :: rest, true,
            recs.push ⟨nm, some f.index, []⟩⟩) h (by omega) rfl rfl
        rw [hdep] at this
        exact this


/-- A property: the step of the code follows the place of the specification
when `dup` tells whether the innermost open node, while it has no child,
already has the name. -/
theorem mrel_property {m : MWalk} {W : Walk} {c next : Nat} {nm : String} {v : ByteArray}
    {dup : Bool} (h : MRel str strs m W c)
    (hd : decodeToken str strs c = .ok (.property nm v, next))
    (hdup : ∀ f rest, W.open_ = f :: rest → f.children = false → dup = f.names.contains nm) :
    Follows str strs next (m.property dup) (W.place (.property nm v)) := by
  obtain ⟨op, sr, recs⟩ := W
  have hdep := h.depth
  simp only at hdep hdup
  cases op with
  | nil =>
    simp only [List.length_nil] at hdep
    simp only [MWalk.property, hdep, ↓reduceIte, place_property_nil, Follows]
  | cons f rest =>
    simp only [List.length_cons] at hdep
    have ho : m.open_ ≠ 0 := by omega
    obtain ⟨f', rest', hW, hch, hrest⟩ := mrel_open_cons h ho
    simp only [List.cons.injEq] at hW
    obtain ⟨hf, hr⟩ := hW
    subst hf hr
    have hin := h.inner f rest rfl
    have hlt : m.open_ - 1 < m.frames.length := by have := h.le; have := h.length; omega
    rw [place_property_cons]
    unfold MWalk.property
    generalize hfr : m.frames[m.open_ - 1]! = fr at hch hin
    simp only [ho, ↓reduceIte, hch]
    by_cases h1 : f.children = true
    · simp only [h1, ↓reduceIte, Follows]
    · have h1' : f.children = false := by simpa using h1
      obtain ⟨hcnt, hnames⟩ := hin h1'
      simp only [h1, Bool.false_eq_true, ↓reduceIte, hcnt]
      by_cases h2 : MAX_PROPERTIES.toNat < f.names.length + 1
      · simp only [h2, ↓reduceIte, Follows]
      · rw [hdup f rest rfl h1']
        by_cases h3 : f.names.contains nm = true
        · simp only [h2, h3, ↓reduceIte, Follows]
        · simp only [h2, h3, ↓reduceIte, Bool.false_eq_true, Follows]
          refine ⟨by simp [h.length], hdep, h.le, h.seen, forall_set h.counts ?_ _, ?_,
            h.outer, ?_⟩
          · show fr.count + 1 ≤ _
            omega
          · have hc := h.children
            rw [show m.open_ = m.open_ - 1 + 1 by omega] at hc ⊢
            exact forall2_set_last hlt hc (by simp only [MFrame.bump]; rw [hch, h1'])
          · intro g r hg hgc
            simp only [List.cons.injEq] at hg
            obtain ⟨rfl, rfl⟩ := hg
            rw [getElem!_set_self _ hlt]
            exact ⟨by simp [MFrame.bump, hcnt], hnames.snoc_prop hd⟩

/-- An end node: the step of the code follows the place of the specification.
-/
theorem mrel_endNode {m : MWalk} {W : Walk} {c next : Nat} (h : MRel str strs m W c) :
    Follows str strs next m.endNode (W.place .endNode) := by
  obtain ⟨op, sr, recs⟩ := W
  have hdep := h.depth
  simp only at hdep
  cases op with
  | nil =>
    simp only [List.length_nil] at hdep
    simp [MWalk.endNode, hdep, Walk.place, Follows]
  | cons f rest =>
    simp only [List.length_cons] at hdep
    have ho : m.open_ ≠ 0 := by omega
    obtain ⟨f', rest', hW, -, hrest⟩ := mrel_open_cons h ho
    simp only [List.cons.injEq] at hW
    obtain ⟨hf, hr⟩ := hW
    subst hf hr
    simp only [MWalk.endNode, ho, ↓reduceIte, Walk.place, Follows]
    refine ⟨h.length, by simp only; omega, by simp only; have := h.le; omega, h.seen, h.counts,
      hrest, fun g hg => h.outer g (List.mem_of_mem_tail hg), ?_⟩
    intro g r hg hgc
    simp only at hg
    have := h.outer g (by simp [hg])
    simp [hgc] at this

/-- A no-operation: the walks stand for each other at the next token. -/
theorem mrel_nop {m : MWalk} {W : Walk} {c next : Nat} (h : MRel str strs m W c)
    (hd : decodeToken str strs c = .ok (.nop, next)) : MRel str strs m W next :=
  ⟨h.length, h.depth, h.le, h.seen, h.counts, h.children, h.outer, fun f rest hW hc =>
    ⟨(h.inner f rest hW hc).1, (h.inner f rest hW hc).2.snoc_nop hd⟩⟩

/-- The end token: the checks of the code are those of `walkTokens`. -/
theorem mrel_end {m : MWalk} {W : Walk} {c next len : Nat} (h : MRel str strs m W c) :
    m.endStructure next len =
      (if !W.seenRoot || !W.open_.isEmpty || next ≠ len then .error .badTree else .ok true) := by
  have hs := h.seen
  have hd := h.depth
  unfold MWalk.endStructure
  rw [hs]
  cases hW : W.open_ with
  | nil =>
    rw [hW] at hd
    cases hsr : W.seenRoot <;> by_cases hn : next = len <;> simp [hd, hn]
  | cons f rest =>
    rw [hW] at hd
    cases hsr : W.seenRoot <;> simp [hd]

/-- The end token: what the code returns against `stepOf`. -/
theorem placed_end {ε : Type} {err : ε → Error} {r : Aeneas.Std.core.result.Result Bool ε}
    {m m' : MWalk} {W : Walk} {c next len : Nat} (h : MRel str strs m W c)
    (h1 : Agrees (· = ·) err r (m.endStructure next len)) :
    Agrees (Placed str strs m' next) err r (stepOf W .endStructure next len) := by
  rw [mrel_end h] at h1
  simp only [stepOf]
  by_cases hc : (!W.seenRoot || !W.open_.isEmpty || decide (next ≠ len)) = true
  · simp only [hc, ↓reduceIte] at h1 ⊢
    cases r with
    | Ok b => exact h1
    | Err x => exact h1
  · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h1 ⊢
    cases r with
    | Ok b => exact h1
    | Err x => exact h1

/-- A no-operation: what the code returns against `stepOf`. -/
theorem placed_nop {ε : Type} {err : ε → Error} {m : MWalk} {W : Walk} {c next len : Nat}
    (h : MRel str strs m W c) (hd : decodeToken str strs c = .ok (.nop, next)) :
    Agrees (Placed str strs m next) err (.Ok false) (stepOf W .nop next len) :=
  ⟨rfl, mrel_nop h hd⟩

/-! ## Results of the code against the specification -/

section Checks

open Aeneas Aeneas.Std Aeneas.Std.WP

/-- An `if` of the code that continues when its condition holds and returns an
error otherwise agrees with the join point of an `if c' then throw e` of the
specification whose condition is the negation. -/
theorem check_else_spec {γ δ ε ε' : Type} {rel : γ → δ → Prop} {err : ε → ε'} {c c' : Prop}
    [Decidable c] [Decidable c'] (hc : c ↔ ¬ c') {e : ε} {e' : ε'} (he : err e = e')
    {rest : Result (core.result.Result γ ε)} {K : Unit → Except ε' δ}
    {S : Except ε' δ} (hrest : c → ¬ c' → rest ⦃ out => Agrees rel err out S ⦄) :
    (if c then rest else Result.ok (.Err e)) ⦃ out =>
      Agrees rel err out (if c' then (throw e' >>= K) else S) ⦄ := by
  by_cases h : c
  · have : ¬ c' := hc.mp h
    simp only [h, this, ↓reduceIte]; exact hrest h this
  · have : c' := by by_contra h'; exact h (hc.mpr h')
    simp only [h, this, ↓reduceIte, spec_ok]; rw [← he]; rfl

end Checks

/-- Results whose value is not compared agree with the same specifications
once the values of the specifications are forgotten. -/
theorem agrees_true_of_map_eq {α β γ ε ε' : Type} {err : ε → ε'}
    {r : Aeneas.Std.core.result.Result α ε} {E : Except ε' β} {E' : Except ε' γ}
    (h : (fun _ => ()) <$> E = (fun _ => ()) <$> E') (hr : Agrees (fun _ _ => True) err r E) :
    Agrees (fun _ _ => True) err r E' := by
  cases r <;> cases E <;> cases E' <;> simp_all [Agrees, Functor.map, Except.map]

/-! ## The decoding of a token -/

/-- The begin-node branch of `decodeToken`, with the name at `start`. -/
def decodeBegin (str : ByteArray) (start : Nat) : Except Error (Token × Nat) := do
  let (nm, nameEnd) ← cString str start
  let after ← paddedEnd str nameEnd true
  if !nm.toList.all isNodeNameChar then throw .badString
  pure (.beginNode nm, after)

/-- The property branch of `decodeToken`, with the length of the value at
`next`. -/
def decodeProperty (str strs : ByteArray) (next : Nat) : Except Error (Token × Nat) := do
  let length ← u32At str next
  let nameOffset ← u32At str (next + 4)
  let valueStart := next + 8
  let valueEnd ← checkedAdd valueStart length.toNat
  if str.size < valueEnd then throw .truncated
  let (nm, _) ← cString strs nameOffset.toNat
  if nm.isEmpty || MAX_PROPERTY_NAME.toNat < nm.utf8ByteSize ||
      !nm.toList.all isPropertyNameChar then
    throw .badString
  let after ← paddedEnd str valueEnd false
  pure (.property nm (str.extract valueStart valueEnd), after)

/-- `decodeToken` after its tag, as the code tests the tag. -/
def decodeTag (str strs : ByteArray) (cursor t : Nat) : Except Error (Token × Nat) :=
  if t = 1 then decodeBegin str (cursor + 4)
  else if t = 2 then .ok (.endNode, cursor + 4)
  else if t = 3 then decodeProperty str strs (cursor + 4)
  else if t = 4 then .ok (.nop, cursor + 4)
  else if t = 9 then .ok (.endStructure, cursor + 4)
  else .error .badToken

/-- `decodeToken` as the read of its tag and `decodeTag`. -/
theorem decodeToken_eq (c : Nat) :
    decodeToken str strs c = u32At str c >>= fun tag => decodeTag str strs c tag.toNat := by
  unfold decodeToken
  congr 1
  funext tag
  unfold decodeTag
  split
  next h => simp only [h, ↓reduceIte]; rfl
  next h => simp only [h, Nat.reduceEqDiff, ↓reduceIte]; rfl
  next h => simp only [h, Nat.reduceEqDiff, ↓reduceIte]; rfl
  next h => simp only [h, Nat.reduceEqDiff, ↓reduceIte]; rfl
  next h => simp only [h, Nat.reduceEqDiff, ↓reduceIte]; rfl
  next h1 h2 h3 h4 h5 =>
    have h1' : ¬ tag.toNat = 1 := h1
    have h2' : ¬ tag.toNat = 2 := h2
    have h3' : ¬ tag.toNat = 3 := h3
    have h4' : ¬ tag.toNat = 4 := h4
    have h5' : ¬ tag.toNat = 9 := h5
    simp only [h1', h2', h3', h4', h5', ↓reduceIte]; rfl
end Krepi.Proofs.Fdt.Refinement
