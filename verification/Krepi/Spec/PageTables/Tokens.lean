module

public import Krepi.Spec.PageTables.Boot
public import Krepi.Spec.PageTables.Ownership

/-!
# Page tables: the shared fields as transactions that hold a token

The four shared fields of the contract's `State fields`: the descriptors of
the lower kernel set; the descriptors of the direct map's set, read-only
after boot; the tables in use of the pools of the kernel tables, which are
the records of the two sets; and the page ownership table, with its extents,
exclusion records, generation counter and arena. `Shared` holds them, with
whether the MMU is on, which ends the boot.

Every write of a shared field is a transaction that takes the evidence of
the owner that the field's row names, and runs one entry from its first
check to the end of the execution of its plan (`Terms`, Token):

- the boot CPU, before the MMU is on (`BootCpu`), builds the kernel tables
  with `kernel_map` and `direct_map` and turns the MMU on, which publishes
  the direct map's set: no transaction writes it after;
- after it, the token of the kernel tables (`KernelTablesToken`) fills
  invalid entries of the lower kernel set with `map_page`, whose plan is
  executed under the token, and lends the set as the source of a copy;
- the token of the page ownership table (`OwnershipToken`) runs every entry
  of the table, the read entries included, and the allocation of one step,
  `choose`, the caller's zeroing and `assign`, under one token, so that the
  choice that `assign` takes is that of `choose` on the same table.

A transaction that is not enabled gives none; one whose entry fails gives
the error of the entry and leaves the state as it was. With one CPU the
executing CPU holds each token, `KernelTablesToken.executing` and
`OwnershipToken.executing`, and is the boot CPU, `BootCpu.boot`. The hardware
effect of a plan, the stores, barriers and invalidations of the adapter, is
not modelled (`Krepi.Spec.PageTables.Plan`): `Tables.apply` gives the pool
once the plan has run.
-/

@[expose] public section

namespace Krepi.Spec.PageTables

/-! ## Tokens -/

/-- The boot CPU before the MMU is on: the owner of the descriptors of both
kernel sets and of their tables in use while it builds them. -/
structure BootCpu where
  deriving DecidableEq, Repr, Inhabited

/-- The executing CPU at boot, the boot CPU. -/
def BootCpu.boot : BootCpu := {}

/-- The token of the kernel tables: the right to fill an invalid entry of the
lower kernel set, and to change its tables in use, once the MMU is on. -/
structure KernelTablesToken where
  deriving DecidableEq, Repr, Inhabited

/-- The token of the kernel tables that the executing CPU holds with one CPU. -/
def KernelTablesToken.executing : KernelTablesToken := {}

/-- The token of the page ownership table: the right to run an entry on it,
held by one CPU at a time. -/
structure OwnershipToken where
  deriving DecidableEq, Repr, Inhabited

/-- The token of the page ownership table that the executing CPU holds with
one CPU. -/
def OwnershipToken.executing : OwnershipToken := {}

/-! ## The shared state -/

/-- The shared fields of the component: the lower kernel set and the direct
map's set, each with its descriptors and its tables in use, in the pools of
the kernel tables; the page ownership table of extent capacity `E` and
exclusion capacity `X`, none until it is built; and whether the MMU is on. -/
structure Shared (E X : Nat) where
  lowerKernel : Tables .lower KERNEL_TABLES
  directMap : Tables .upper DIRECT_MAP_TABLES
  ownership : Option (Ownership E X)
  mmuOn : Bool

/-- The state that the boot wiring starts from: both kernel sets made by
`Tables::new` on their pools, which are zero BSS of the image, no page
ownership table and the MMU off. -/
def Shared.boot (_ : BootCpu) (lower : Pool KERNEL_TABLES) (direct : Pool DIRECT_MAP_TABLES) :
    Shared E X :=
  ⟨Tables.new lower, Tables.new direct, none, false⟩

/-! ## The kernel tables -/

/-- `kernel_map` of a layout into the lower kernel set by the boot CPU,
enabled while the MMU is off: the set once its plan has run, and the plan. -/
def Shared.buildKernelMap (_ : BootCpu) (s : Shared E X) (layout : Layout) (base : UInt64)
    (bits : UInt8) : Option (Except TableError (Shared E X × Plan)) :=
  if s.mmuOn then none
  else some ((s.lowerKernel.kernelMap layout base bits).map fun (t, plan) =>
    ({ s with lowerKernel := t.apply plan }, plan))

/-- `direct_map` of the boot memory map into the direct map's set by the boot
CPU, enabled while the MMU is off: the set once its plan has run, and the
plan. -/
def Shared.buildDirectMap (_ : BootCpu) (s : Shared E X) (memory : Fdt.MemoryPlan) (base : UInt64)
    (bits : UInt8) : Option (Except TableError (Shared E X × Plan)) :=
  if s.mmuOn then none
  else some ((s.directMap.directMap memory base bits).map fun (t, plan) =>
    ({ s with directMap := t.apply plan }, plan))

/-- The end of the boot: `enable` on the boot CPU writes `TTBR1_EL1` and
turns the MMU on, and its `ISB` publishes the direct map's set, which no
transaction writes after it. Enabled once, while the MMU is off. -/
def Shared.enable (_ : BootCpu) (s : Shared E X) : Option (Shared E X) :=
  if s.mmuOn then none else some { s with mmuOn := true }

/-- A fill of an invalid entry of the lower kernel set under the token of the
kernel tables, enabled once the MMU is on: `map_page`, which refuses a slot
that is not free, and the execution of its plan, whose `Sync` is the
linearization point. The tables that the plan takes are recorded under the
same token. -/
def Shared.fillKernel (_ : KernelTablesToken) (s : Shared E X) (v p : UInt64) (k : Kind)
    (base : UInt64) (bits : UInt8) : Option (Except TableError (Shared E X × Plan)) :=
  if s.mmuOn then
    some ((s.lowerKernel.mapPage v p k base bits).map fun (t, plan) =>
      ({ s with lowerKernel := t.apply plan }, plan))
  else none

/-- The lower kernel set as the source of `clone_kernel_from` into the tables
of an address space, read under the token of the kernel tables once the MMU
is on; the copy writes only the target, a field of the address-space
component. -/
def Shared.withKernelSource (_ : KernelTablesToken) (s : Shared E X)
    (f : Tables .lower KERNEL_TABLES → α) : Option α :=
  if s.mmuOn then some (f s.lowerKernel) else none

/-! ## The page ownership table -/

/-- `Ownership::new` under the token of the page ownership table, enabled once,
while no table is built: the table, or the error with the state unchanged. -/
def Shared.newOwnership (_ : OwnershipToken) (s : Shared E X) (arena : UInt64)
    (banks : List PhysRange) (exclusions : List Exclusion) :
    Option (Except OwnershipError (Shared E X)) :=
  match s.ownership with
  | some _ => none
  | none => some ((Ownership.new arena banks exclusions).map fun t => { s with ownership := some t })

/-- A write entry of the page ownership table under its token, enabled once
the table is built: `entry` from its first check to the end of its write
phase, the linearization point, and its result; on an error the state is
unchanged. `assign`, `reserve`, `publish`, `cancel` and `release` are such
entries. -/
def Shared.withOwnership (_ : OwnershipToken) (s : Shared E X)
    (entry : Ownership E X → Except ε (Ownership E X × α)) : Option (Except ε (Shared E X × α)) :=
  s.ownership.map fun t =>
    (entry t).map fun (t', a) => ({ s with ownership := some t' }, a)

/-- A read entry of the page ownership table under its token, enabled once
the table is built: `choose`, `owner`, `validate` or `stats`. -/
def Shared.readOwnership (_ : OwnershipToken) (s : Shared E X) (entry : Ownership E X → α) :
    Option α :=
  s.ownership.map entry

/-- An allocation of one step under one token of the page ownership table:
`choose`, then the caller's zeroing of the chosen range through the direct
map, whose outcome `zeroed` gives, then `assign` of that choice with the
outcome. The choice that `assign` takes is that of `choose` on the same
table, as its requirement states. -/
def Shared.allocate (tok : OwnershipToken) (s : Shared E X) (owner pages alignment : UInt64)
    (p : Placement) (zeroed : PhysRange → Bool) :
    Option (Except OwnershipError (Shared E X × Allocation)) :=
  s.withOwnership tok fun t => do
    let c ← t.choose owner pages alignment p
    t.assign c (zeroed c.range)

end Krepi.Spec.PageTables
