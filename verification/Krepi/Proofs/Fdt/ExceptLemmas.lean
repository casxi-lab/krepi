module

import Mathlib.Util.CountHeartbeats

/-!
# Device tree: lemmas about results

Lemmas about the monad `Except` in which the entries of the specification of
the `fdt` component are written: what a `do` block that succeeds tells about
each of its steps. They take apart a hypothesis `entry ... = .ok v` one step
at a time:

- `except_bind_ok`: a bind succeeds exactly when its first step succeeds and
  its continuation succeeds on that value;
- `except_ok_bind`: a bind on a success is its continuation;
- `except_throw_bind_ne` and `except_throw_ne`: a step that throws makes the
  block fail;
- `except_pure_ok`: `pure a` succeeds with `a` alone;
- `except_jp_ok`: the join point that `do` writes for `if c then throw e`
  without `else` succeeds only when `c` is false and the rest succeeds; the
  join point is a `have` that this lemma reads through by unification, so
  that the rest is never copied into both branches;
- `except_mapM_ok`: a `List.mapM` that succeeds gives one value for each
  entry, each a success of the function on an entry.
-/

namespace Krepi.Proofs.Fdt

/-- A bind succeeds exactly when its first step succeeds and its continuation
succeeds on that value. -/
public theorem except_bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp [bind, Except.bind]

/-- A bind on a success is its continuation on the value. -/
public theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f : Except ε β) = f a := rfl

/-- A block whose first step throws never succeeds. -/
public theorem except_throw_bind_ne {ε α β : Type} (e : ε) (f : α → Except ε β) (b : β) :
    (throw e >>= f : Except ε β) ≠ .ok b := by
  simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind]

/-- A throw never succeeds. -/
public theorem except_throw_ne {ε α : Type} (e : ε) (b : α) : (throw e : Except ε α) ≠ .ok b := by
  simp [throw, throwThe, MonadExceptOf.throw]

/-- `pure a` succeeds with `a` alone. -/
public theorem except_pure_ok {ε α : Type} {a b : α} : (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

/-- The join point of `if c then throw e` without `else`, followed by the rest
`k` of the block, succeeds only when `c` is false and the rest succeeds. -/
public theorem except_jp_ok {ε β : Type} {c : Prop} [Decidable c] {e : ε}
    {k : Unit → Except ε β} {b : β} (h : (if c then (throw e >>= k) else k ()) = .ok b) :
    ¬ c ∧ k () = .ok b := by
  split at h
  · exact absurd h (except_throw_bind_ne _ _ _)
  · exact ⟨‹_›, h⟩

/-- A `List.mapM` that succeeds gives as many values as the list has entries,
each the success of the function on an entry of the list. -/
public theorem except_mapM_ok {ε α β : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' →
      l'.length = l.length ∧ ∀ y ∈ l', ∃ x ∈ l, f x = .ok y
  | [], l', h => by
    simp [List.mapM_nil, pure, Except.pure] at h
    subst h
    simp
  | x :: xs, l', h => by
    rw [List.mapM_cons, except_bind_ok] at h
    obtain ⟨y, hy, h⟩ := h
    rw [except_bind_ok] at h
    obtain ⟨ys, hys, h⟩ := h
    rw [except_pure_ok] at h
    subst h
    obtain ⟨hl, hm⟩ := except_mapM_ok hys
    refine ⟨by simp [hl], ?_⟩
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨x, List.mem_cons_self, hy⟩
    · obtain ⟨w, hw, hfw⟩ := hm z hz
      exact ⟨w, List.mem_cons_of_mem _ hw, hfw⟩

end Krepi.Proofs.Fdt
