module

public import Krepi.Spec.Fdt.Plan
public import Krepi.Spec.Fdt.Cpus

/-!
# Device tree: the shared results of the boot

The three shared fields of the contract's `State fields`: the bytes of the
hand-over tree, shared and read-only; the boot memory map, a `MemoryPlan`,
and the CPU topology, a `CpuTopology`, each shared and immutable once built.
The component writes no state of its own, so these fields are the state of
the boot that holds its results.

Each field is published once, by a transaction that holds the boot token:
the hand-over, at the cold entry; the boot memory map and the topology, at
the return of the entry that builds them, before the secondary CPUs start.
A transaction that is not enabled, because its field is published or the
secondary CPUs have started, gives none; one whose entry fails gives the
error of the entry and leaves the state as it was. Nothing writes a field
again once it is published, and reading a field needs no token.

In this release one executor, the boot CPU, runs every transaction before the
secondary CPUs start, so it holds the token: `BootToken.bootCpu`.
-/

@[expose] public section

namespace Krepi.Spec.Fdt

/-! ## The token -/

/-- The boot token: the right to publish a shared field of the boot state. -/
structure BootToken where
  deriving DecidableEq, Repr, Inhabited

/-- The token of the one executor of this release, the boot CPU. -/
def BootToken.bootCpu : BootToken := {}

/-! ## The state -/

/-- The shared fields of the boot: the bytes of the hand-over tree
(`handOver`); the boot memory map (`plan`) and the CPU topology (`topology`),
none until they are published; and whether the first secondary CPU has
started (`secondaries`). -/
structure BootState where
  handOver : ByteArray
  plan : Option MemoryPlan
  topology : Option CpuTopology
  secondaries : Bool
  deriving Inhabited

/-- The entry that builds a boot memory map, with its arguments:
`MemoryPlan::all_ram`, `new` or `from_boot_memory`. -/
inductive PlanBuild where
  | allRam (ram boot : List Span) (firmware : List ReservedRegion)
  | new (window : Span) (ram boot : List Span) (firmware : List ReservedRegion)
  | fromBootMemory (memory : BootMemory) (window : Span) (more : List Span)

/-- The result of the entry of a `PlanBuild`. -/
def PlanBuild.run : PlanBuild → Except PlanError MemoryPlan
  | .allRam ram boot firmware => MemoryPlan.allRam ram boot firmware
  | .new window ram boot firmware => MemoryPlan.new window ram boot firmware
  | .fromBootMemory memory window more => MemoryPlan.fromBootMemory memory window more

/-! ## Transactions -/

/-- The hand-over: the state at the cold entry, with the bytes of the
hand-over tree that the firmware or the loader wrote before it, and nothing
built yet. The bytes are published here, once, and no transaction writes
them again. -/
def BootState.coldEntry (_ : BootToken) (bytes : ByteArray) : BootState :=
  { handOver := bytes, plan := none, topology := none, secondaries := false }

/-- The tree of the hand-over bytes, as `Fdt::parse` gives it: a read, which
needs no token. -/
def BootState.tree (s : BootState) : Except Error Fdt := Fdt.parse s.handOver

/-- The publication of the boot memory map: enabled while no map is published
and no secondary CPU has started, and otherwise none. It runs the entry of
`build` and, at its return, publishes the map, or gives the error of the
entry with the state unchanged. -/
def BootState.publishPlan (_ : BootToken) (s : BootState) (build : PlanBuild) :
    Option (Except PlanError BootState) :=
  if s.secondaries || s.plan.isSome then none
  else some (build.run.map fun p => { s with plan := some p })

/-- The publication of the CPU topology: enabled while no topology is
published and no secondary CPU has started, and otherwise none. It parses
the hand-over bytes and runs `Fdt::discover_cpus` with `profile`, and at its
return publishes the topology, or gives the error of either with the state
unchanged. -/
def BootState.publishTopology (_ : BootToken) (s : BootState) (profile : CpuProfile) :
    Option (Except Error BootState) :=
  if s.secondaries || s.topology.isSome then none
  else some ((s.tree.bind (·.discoverCpus profile)).map fun t => { s with topology := some t })

/-- The start of the secondary CPUs: enabled once the boot memory map and the
topology are published and before the secondary CPUs have started, and
otherwise none. From then on every CPU reads the published fields, and no
publication is enabled. -/
def BootState.startSecondaries (_ : BootToken) (s : BootState) : Option BootState :=
  if s.secondaries || s.plan.isNone || s.topology.isNone then none
  else some { s with secondaries := true }

end Krepi.Spec.Fdt
