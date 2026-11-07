module

public import Aeneas

/-!
# `Arc` as a structure

Definitions that the reviewed external declarations of the qualification
cases `match-machine-arc` and `term-layout-cut` use. They serve only the type
checking of those cases: they are not models, `verification/models.json`
does not register them, and no proof target uses them.

The Rust standard library documents `Arc<T>` as a thread-safe
reference-counting pointer that provides shared ownership of a value of type
`T`. `Arc::clone` makes a new pointer to the same allocation, and `Deref`
gives the inner value. The structure holds that value alone: pointer
identity and the reference counts are not part of it. So `clone` returns the
same structure and `deref` its field, and neither fails; the abort of `clone`
when the reference count overflows is outside these definitions.
-/

@[expose] public section

/-- `alloc::sync::Arc<T>`: the shared value. -/
structure alloc.sync.Arc (T : Type) where
  val : T

namespace Krepi.Qualification.Models.Arc

/-- `Arc::clone`: a pointer to the same allocation, which holds the same
value. -/
def clone {T : Type} (a : alloc.sync.Arc T) : alloc.sync.Arc T := a

/-- `Deref::deref` of an `Arc`: the inner value. -/
def deref {T : Type} (a : alloc.sync.Arc T) : T := a.val

end Krepi.Qualification.Models.Arc

end
