module

public import Krepi.Spec.PageTables.Tables

/-!
# Page tables: write plans

`page_tables::WritePlan` of the contract's `Write plans and publication`: the
ordered steps that carry out a write of a set, which `krepi_arch::mmu::apply`
executes in order, each completing before the next.

| Step | Effect |
| --- | --- |
| `Zero(t)` | Writes 0 into the 512 entries of table `t` of the pool |
| `Store(t, i, d)` | Writes descriptor `d` into entry `i` of table `t` |
| `Fence` | `DMB ISHST` |
| `Sync` | `DSB ISH`, then `ISB` |
| `Invalidate(v)` | `DSB ISH`, `TLBI VAAE1IS` of `v`, `DSB ISH`, `ISB` |

The execution of a plan here is its effect on the pool: `Zero` and `Store`
write the pool, and `Fence`, `Sync` and `Invalidate` leave it as it is. What
the barriers and the invalidation do to the other observers of the tables, the
walks of the CPUs and their TLBs, belongs to the adapter and to the boot
component's maintenance, whose obligations the contract lists as open; this
specification states the order of the steps, not their effect on hardware.

A step names a table by its index in the pool and an entry by its index in the
table. The plans that the entries build name only tables below `N` and entries
below 512; the execution of any other step leaves the pool as it is, so that
it is total.
-/

@[expose] public section

namespace Krepi.Spec.PageTables

/-! ## Steps and plans -/

/-- A step of a write plan. -/
inductive Step where
  /-- `Zero(t)`: write 0 into the 512 entries of table `t`. -/
  | zero (t : Nat)
  /-- `Store(t, i, d)`: write descriptor `d` into entry `i` of table `t`. -/
  | store (t i : Nat) (d : UInt64)
  /-- `Fence`: `DMB ISHST`. -/
  | fence
  /-- `Sync`: `DSB ISH`, then `ISB`. -/
  | sync
  /-- `Invalidate(v)`: `DSB ISH`, `TLBI VAAE1IS` of `v`, `DSB ISH`, `ISB`. -/
  | invalidate (v : UInt64)
  deriving DecidableEq, Repr

/-- `page_tables::WritePlan`: the steps of a write, in the order of their
execution. -/
abbrev Plan := List Step

/-- Whether a step stores a valid descriptor, so that the entry that it writes
becomes valid. -/
def Step.storesValid : Step → Bool
  | .store _ _ d => isValid d
  | _ => false

/-! ## Execution on the pool -/

/-- Writes descriptor `d` into entry `i` of table `t` of a pool; a step outside
the pool or the table leaves the pool as it is. The table is taken out of the
pool while it is written, so that the write needs no copy of it. -/
def Pool.store (p : Pool N) (t i : Nat) (d : UInt64) : Pool N :=
  if h : t < N then
    if hi : i < ENTRIES then
      let table := p[t]
      let p := p.set t Table.zero
      p.set t (table.set i d hi) h
    else p
  else p

/-- Writes 0 into the 512 entries of table `t` of a pool; a table outside the
pool leaves it as it is. -/
def Pool.zeroTable (p : Pool N) (t : Nat) : Pool N :=
  if h : t < N then p.set t Table.zero h else p

/-- The effect of one step on the pool. `Fence`, `Sync` and `Invalidate` act
on no entry of the pool. -/
def Step.exec (step : Step) (p : Pool N) : Pool N :=
  match step with
  | .zero t => p.zeroTable t
  | .store t i d => p.store t i d
  | .fence => p
  | .sync => p
  | .invalidate _ => p

/-- The execution of a plan on the pool: its steps in order, each on the pool
that the steps before it left. -/
def Plan.exec (plan : Plan) (p : Pool N) : Pool N :=
  plan.foldl (fun p step => step.exec p) p

/-- A set once a plan has been executed on its pool: the pool changes and the
record of the tables in use, which the write phase of the entry set, does
not. -/
def Tables.apply (s : Tables r N) (plan : Plan) : Tables r N :=
  { s with pool := plan.exec s.pool }

end Krepi.Spec.PageTables
