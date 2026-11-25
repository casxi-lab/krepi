module

public import Aeneas

/-!
# Refinement statements: what the targets share

The vocabulary of the refinement statements of every target, which relate a
function of the code, as Aeneas translates it, to its function of the
specification:

- the machine values of the code read as the values of the specifications:
  a scalar as the `UInt` of its width, a slice of bytes as its `ByteArray`;
- `Agrees`, which relates the result of a function of the code to that of
  its specification: both succeed with values that the representation of
  their type relates, or both fail with the same error; and `Writes`, the
  same for a function that writes a state, whose state after a success
  stands for that of the specification and after a failure is unchanged;
- `Stands`, which represents an iterator by the list of the specification
  that its calls of `next` give, and `Advances`, the step of one call. The
  statement of the `next` of an iterator, that an iterator which stands for
  a list advances on it, follows from the definition of `Stands`; the list
  is stated by the statement of the function that gives the iterator.

A refinement statement states its function with the triple `⦃ ⦄` of the
Aeneas Lean library, so that the function returns, for a function with a
loop as for any other, neither failing nor diverging, and its result
satisfies the postcondition. This module imports no generated definitions:
each module of statements imports the generated definitions of one target
alone, whose enumerations and external declarations would clash with those
of another.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace Krepi.Statements

/-! ## Machine values -/

/-- A byte of the code as a byte of the specifications. -/
def byte (x : U8) : UInt8 := UInt8.ofNat x.val

/-- A 32-bit word of the code as one of the specifications. -/
def word32 (x : U32) : UInt32 := UInt32.ofNat x.val

/-- A 64-bit word of the code as one of the specifications. -/
def word64 (x : U64) : UInt64 := UInt64.ofNat x.val

/-- The bytes of a slice of the code, in their order. -/
def bytesOf (s : Slice U8) : ByteArray := ⟨(s.val.map byte).toArray⟩

/-! ## Results -/

/-- Whether the result `r` of a function of the code agrees with the result
`e` of its specification: both succeed with values that `rel` relates, or
both fail, the code with an error that `err` maps to the error of the
specification. A failure of one where the other succeeds disagrees, so the
error and its priority are those of the specification. -/
def Agrees {α β ε ε' : Type} (rel : α → β → Prop) (err : ε → ε') :
    core.result.Result α ε → Except ε' β → Prop
  | .Ok a, .ok b => rel a b
  | .Err x, .error y => err x = y
  | _, _ => False

/-- Whether the result `r` of a function of the code that writes a state,
and the state `s'` that it leaves, agree with the result `e` of its
specification, for a call on the state `s`: both succeed, with a value that
`rel` relates and a state that stands, by `repr`, for the state of the
specification; or both fail with errors that `err` relates, and the state is
`s`, unchanged. The modification set of a success is therefore exactly that
of the specification, and a failure writes nothing. -/
def Writes {σ τ α β ε ε' : Type} (repr : σ → τ → Prop) (rel : α → β → Prop)
    (err : ε → ε' → Prop) (s : σ) : core.result.Result α ε → σ → Except ε' (τ × β) → Prop
  | .Ok a, s', .ok (t, b) => rel a b ∧ repr s' t
  | .Err x, s', .error y => err x y ∧ s' = s
  | _, _, _ => False

/-- Whether two options agree under `rel`: both none, or both some with
values that `rel` relates. -/
def OptionRel {α β : Type} (rel : α → β → Prop) : Option α → Option β → Prop
  | none, none => True
  | some a, some b => rel a b
  | _, _ => False

/-- Whether two lists agree item by item under `rel`: of one length, each
item related to the item of the same index. -/
def ListRel {α β : Type} (rel : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: l, b :: m => rel a b ∧ ListRel rel l m
  | _, _ => False

/-! ## Iterators -/

/-- `Stands next rel it l`: the iterator `it` of the code stands for the
list `l` of the specification. Its calls of `next` give the items of `l` in
order, each related by `rel` to its item, and then none; each call returns
the next state of the iterator with its item. The call that gives none
returns a state at which the iterator stays: a call there gives none and
returns that state again. The state need not be the one of the call that
gave none, since the code may move its cursor while it finds the end. This
is the representation of an iterator by its list: the functions that give
an iterator state that it stands for the list of their specification, and
the functions that walk one rely on it. -/
def Stands {σ α β : Type} (next : σ → Result (Option α × σ)) (rel : α → β → Prop) :
    σ → List β → Prop
  | it, [] => next it ⦃ o it' => o = none ∧ next it' = .ok (none, it') ⦄
  | it, b :: l => next it ⦃ o it' => ∃ a, o = some a ∧ rel a b ∧ Stands next rel it' l ⦄

/-- `Advances next rel it l`: one call of `next` on an iterator that stands
for `l` gives the head of `l`, none for the empty list, and returns an
iterator that stands for the rest of `l`, the empty list again at the end,
so that a call at the end leaves the iterator at its end. An iterator that
stands for `l` advances on `l` by the definition of `Stands` alone, so the
statement of the `next` of an iterator adds nothing to the statement of the
function that gives it: that statement relates the calls of `next` from the
states that the iterator reaches to the list of the specification, and so
covers the code of `next`. -/
def Advances {σ α β : Type} (next : σ → Result (Option α × σ)) (rel : α → β → Prop)
    (it : σ) (l : List β) : Prop :=
  next it ⦃ o it' => OptionRel rel o l.head? ∧ Stands next rel it' l.tail ⦄

end Krepi.Statements
