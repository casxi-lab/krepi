module

public import Krepi.SpecTests.Fdt.Builder
import Mathlib.Util.CountHeartbeats
public import Krepi.Proofs.Fdt.ParseBuilt

/-!
# Device tree: lemmas of the specification tests

Lemmas with which the proofs of the specification tests evaluate their
inputs by kernel decisions in seconds:

- `parse_fast`, `parse_fast0`: the parse of a tree that `Builder` finishes is
  `fastParse`, which walks the structure block on the byte array of its list
  when the builder wrote over nothing and the tree passes the header and the
  reservation map (`fastOk`, by `Krepi.Proofs.Fdt.ParseBuilt`), and is the
  parse itself otherwise. Rewriting a test with it before deciding it skips
  the copy of the whole tree that the header makes, which the kernel performs
  in quadratic time.
- `decEqExcept`: equality of `Except` values, for the modules that decide
  such equations with it as a local instance.
- `okAnd`, `okAnd_spec`: a decision that a computation succeeds and that its
  value passes a check, turned into the value.
- `sameB`, `sameB_sound`: a check of `Fdt.SameExceptValues` on two trees.
-/

@[expose] public section

namespace Krepi.Proofs.Fdt

open Krepi.Spec.Fdt Krepi.SpecProperties.Fdt Krepi.SpecTests.Fdt

/-- Equality of two `Except` values, decided by their constructors and payloads; Lean core has
no such instance. -/
@[instance_reducible]
def decEqExcept {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α)
  | .ok a, .ok b => if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (Except.ok.inj e)
  | .error a, .error b =>
    if h : a = b then isTrue (h ▸ rfl) else isFalse fun e => h (Except.error.inj e)
  | .ok _, .error _ => isFalse nofun
  | .error _, .ok _ => isFalse nofun

/-! ## The parse of a finished tree -/

/-- A builder that wrote over nothing finishes the bytes of its tree. -/
theorem finishTo_eq (b : Builder) (size : Nat) (h : b.overwrites = []) :
    b.finishTo size = b.tree.bytes size := by
  simp only [Builder.finishTo, h, List.foldl_nil, bytesOf, Array.toArray_toList]

/-- Whether the tree of a builder can be parsed by its walk alone: the builder wrote over
nothing, and the tree passes the header and the reservation map by the conditions of
`header_built` and `reservationMap_built`. -/
def fastOk (b : Builder) (size : Nat) : Bool :=
  b.overwrites.isEmpty && decide (max (natural b.tree) size ≤ MAX_BLOB_SIZE.toNat) &&
    decide (12 ≤ (structBytes b.tree).length) &&
    decide (b.tree.reservations.length ≤ MAX_RESERVATIONS.toNat) &&
    decide (∀ e ∈ b.tree.reservations, 0 < e.2 ∧ e.1 + e.2 < 2 ^ 64) &&
    decide ((b.tree.reservations.map entrySpan).Pairwise (fun x y => x.overlaps y = false))

/-- The parse of the tree of a builder: the walk of its structure block when `fastOk` holds,
the parse of its bytes otherwise. -/
def fastParse (b : Builder) (size : Nat) : Except Error Fdt :=
  if fastOk b size then
    (walkTokens (ByteArray.mk (structBytes b.tree).toArray)
      (ByteArray.mk (Krepi.Proofs.Fdt.stringBytes b.tree).toArray) MAX_TOKENS.toNat 0
        Walk.start).bind fun records =>
      .ok { totalSize := UInt64.ofNat (max (natural b.tree) size),
            reservations := b.tree.reservations.map entrySpan, records }
  else Fdt.parse (b.finishTo size)

/-- The parse of a finished tree is `fastParse`. -/
theorem parse_fast (b : Builder) (size : Nat) :
    Fdt.parse (b.finishTo size) = fastParse b size := by
  unfold fastParse
  split
  · rename_i h
    simp only [fastOk, Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨h0, hmax⟩, h12⟩, hlen⟩, hgood⟩, hdisj⟩ := h
    rw [finishTo_eq b size h0, parse_built b.tree size hmax h12
      (reservationMap_built b.tree size hmax hlen hgood hdisj)]
    rfl
  · rfl

/-- `parse_fast` for a tree finished without zero bytes after it. -/
theorem parse_fast0 (b : Builder) : Fdt.parse b.finish = fastParse b 0 := parse_fast b 0

/-! ## Values of decisions -/

/-- Whether `x` succeeds with a value that passes `p`. -/
def okAnd {ε α : Type} (x : Except ε α) (p : α → Bool) : Bool :=
  match x with
  | .ok a => p a
  | .error _ => false

/-- The value of a computation that `okAnd` accepts. -/
theorem okAnd_spec {ε α : Type} {x : Except ε α} {p : α → Bool} (h : okAnd x p = true) :
    ∃ a, x = .ok a ∧ p a = true := by
  unfold okAnd at h
  split at h
  · exact ⟨_, rfl, h⟩
  · exact absurd h (by decide)

/-- `Fdt.SameExceptValues` checked node by node. -/
def sameB (free : Nat → String → Bool) (t t' : Fdt) : Bool :=
  decide (t.totalSize = t'.totalSize) && decide (t.reservations = t'.reservations) &&
  decide (t.records.size = t'.records.size) &&
  (List.range t.records.size).all fun i =>
    match t.records[i]?, t'.records[i]? with
    | some r, some r' => decide (r.name = r'.name) && decide (r.parent = r'.parent) &&
        decide (r.properties.map (·.1) = r'.properties.map (·.1)) &&
        (r.properties.zip r'.properties).all fun q => free i q.1.1 || decide (q.1.2 = q.2.2)
    | _, _ => true

/-- `sameB` implies `Fdt.SameExceptValues`. -/
theorem sameB_sound {free : Nat → String → Bool} {t t' : Fdt} (h : sameB free t t' = true) :
    t.SameExceptValues free t' := by
  simp only [sameB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, ?_⟩
  intro i r r' hr hr'
  have hi : i < t.records.size := by
    rcases Nat.lt_or_ge i t.records.size with hi | hi
    · exact hi
    · rw [Array.getElem?_eq_none hi] at hr; cases hr
  have h5 := h4 i hi
  rw [hr, hr'] at h5
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at h5
  obtain ⟨⟨⟨hn, hp⟩, hm⟩, hv⟩ := h5
  refine ⟨hn, hp, hm, fun q hq hf => ?_⟩
  rcases hv q hq with h | h
  · rw [hf] at h; exact absurd h (by decide)
  · exact h

end Krepi.Proofs.Fdt
