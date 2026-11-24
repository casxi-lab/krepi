module

public import Krepi.Spec.Fdt.Translate

/-!
# Device tree: the CPU nodes

`Fdt::discover_cpus` of the contract's `CPU nodes`, with step 6 of the error
order of the parse and the entries on a tree, and the functions of the CPU
profile and of the topology that it returns: `CpuProfile::logical_id`,
`affinity_shift` and `conduit`, and `CpuTopology::count`, `profile`,
`affinity` and `validate_timers`.

A CPU profile is a value that the board gives: the PSCI conduit, the
affinity level of the CPU IDs, the numbers of CPUs that the board allows,
whether CPU 0 needs an `enable-method`, and the timer interrupts that the
core checks, if any. The specification holds for every profile; which
values a board gives is not part of it. The discovery reads the children of
`/cpus` once each, in tree order, and `/psci`; the topology that it returns
holds the profile and the number of CPUs, whose IDs are `0` to `count - 1`.
-/

@[expose] public section

namespace Krepi.Spec.Fdt

/-! ## Profiles -/

/-- The PSCI conduit of a profile. -/
inductive PsciConduit where
  | hvc
  | smc
  deriving DecidableEq, Repr, Inhabited

/-- The `method` of `/psci` that names a conduit. -/
def PsciConduit.name : PsciConduit → String
  | .hvc => "hvc"
  | .smc => "smc"

/-- `AffinityLevel`: the affinity level of `MPIDR_EL1` that holds the CPU
IDs, one of its four levels. -/
inductive AffinityLevel where
  | aff0
  | aff1
  | aff2
  | aff3
  deriving DecidableEq, Repr, Inhabited

/-- The position of the field of a level in `MPIDR_EL1`: bits 0, 8, 16 and
32. -/
def AffinityLevel.shift : AffinityLevel → UInt64
  | .aff0 => 0
  | .aff1 => 8
  | .aff2 => 16
  | .aff3 => 32

/-- `TimerInterrupts`: the private interrupts of a timer, in their order, the
first `count` of the five `numbers`; a `count` above 5 stands for all five.
-/
structure TimerInterrupts where
  numbers : Vector UInt32 5
  count : UInt8
  deriving DecidableEq, Repr, Inhabited

/-- `CpuProfile`, the CPU profile that the board gives: the PSCI conduit
(`CpuProfile::conduit`); the affinity level of the CPU IDs
(`affinity_level`); the numbers of CPUs that the board allows
(`cpu_counts`), as a set whose bit `n` is set when `n` CPUs are allowed,
for `n` from 1 to 4, the other bits not read; whether CPU 0 needs the
`enable-method` `psci` as every other CPU does (`cpu0_enable_method`); and
the timer interrupts that `CpuTopology::validate_timers` checks
(`timer_interrupts`), none when the core does not check the timer of the
board. Every value is a profile, with the behaviour that these rules give
it. -/
structure CpuProfile where
  conduit : PsciConduit
  affinityLevel : AffinityLevel
  cpuCounts : UInt8
  cpu0EnableMethod : Bool
  timerInterrupts : Option TimerInterrupts
  deriving DecidableEq, Repr, Inhabited

/-- `CpuProfile::affinity_shift`: the position of the affinity level of the
profile in `MPIDR_EL1`. -/
def CpuProfile.affinityShift (p : CpuProfile) : UInt64 := p.affinityLevel.shift

/-- Whether the profile allows `count` CPUs: a count from 1 to 4 whose bit of
`cpu_counts` is set. -/
def CpuProfile.allows (p : CpuProfile) (count : Nat) : Bool :=
  count != 0 && count ≤ 4 && p.cpuCounts.toNat.testBit count

/-- The logical IDs, 0 to 3. -/
def CPU_IDS : List UInt64 := [0, 1, 2, 3]

/-- The affinity fields of `MPIDR_EL1`, `0xff_00ff_ffff`: bits 0 to 23 and 32
to 39, without the U, MT and other flag bits. -/
def AFFINITY_MASK : UInt64 := 0xff_00ff_ffff

/-- The logical ID whose affinity is `affinity`: the ID below 4 whose
`id << affinity_shift` equals it, or none. -/
def CpuProfile.idOf (p : CpuProfile) (affinity : UInt64) : Option UInt64 :=
  CPU_IDS.find? fun id => affinity == id <<< p.affinityShift

/-- `CpuProfile::logical_id(mpidr)`: the logical ID of the affinity fields of
`mpidr`, `mpidr & 0xff_00ff_ffff`, so that the flag bits do not change it; none
for an affinity that is not `id << affinity_shift` with an ID below 4. -/
def CpuProfile.logicalId (p : CpuProfile) (mpidr : UInt64) : Option UInt64 :=
  p.idOf (mpidr &&& AFFINITY_MASK)

/-! ## The topology -/

/-- `CpuTopology`, the result of `Fdt::discover_cpus`: the profile
(`CpuTopology::profile`) and the number of CPUs (`CpuTopology::count`). -/
structure CpuTopology where
  profile : CpuProfile
  count : UInt64
  deriving DecidableEq, Repr, Inhabited

/-- `CpuTopology::affinity(i)`: `i << affinity_shift` for `i` below `count`, and
none otherwise. -/
def CpuTopology.affinity (t : CpuTopology) (i : UInt64) : Option UInt64 :=
  if i < t.count then some (i <<< t.profile.affinityShift) else none

/-- A 32-bit word as its four big-endian bytes. -/
def be32 (n : Nat) : List UInt8 :=
  [n / 2 ^ 24, n / 2 ^ 16, n / 2 ^ 8, n].map UInt8.ofNat

/-- The private interrupts of a timer, in their order: the first `count` of
its numbers. -/
def TimerInterrupts.list (timer : TimerInterrupts) : List UInt32 :=
  timer.numbers.toList.take timer.count.toNat

/-- `CpuTopology::validate_timers(interrupts)`: for a profile without timer
interrupts, `BadProperty`; otherwise the `interrupts` of the timer node must
be the records of three cells, type 1 for a private interrupt, its number and
the flags `((1 << count) - 1) << 8 | 4`, the admitted CPUs and a level-high
trigger, for the private interrupts of the profile in their order, with
nothing else, or `BadProperty`. The flags are a 32-bit cell, computed at that
width; a topology of the discovery has 1 to 4 CPUs, so its shift is exact.
-/
def CpuTopology.validateTimers (t : CpuTopology) (interrupts : ByteArray) :
    Except Error Unit := do
  let some timer := t.profile.timerInterrupts | throw .badProperty
  let flags : UInt32 := (((1 : UInt32) <<< t.count.toUInt32) - 1) <<< 8 ||| 4
  let records := timer.list.flatMap fun ppi => be32 1 ++ be32 ppi.toNat ++ be32 flags.toNat
  if interrupts.toList != records then throw .badProperty

/-! ## The discovery -/

/-- The `compatible` lists of `/psci` that the discovery accepts, each the
bytes of its NUL-terminated strings: `arm,psci-0.2`; `arm,psci-1.0`,
`arm,psci-0.2`; and `arm,psci-1.0`, `arm,psci-0.2`, `arm,psci`. -/
def PSCI_COMPATIBLE : List (List UInt8) :=
  [["arm,psci-0.2"], ["arm,psci-1.0", "arm,psci-0.2"],
    ["arm,psci-1.0", "arm,psci-0.2", "arm,psci"]].map
    fun names => names.flatMap fun s => s.toByteArray.toList ++ [0]

/-- One child of `/cpus`, whose address cells are `cells`, after the IDs `ids`
of the CPU nodes before it. First its `device_type`, with the errors of
`Node::string_property`, and a child whose `device_type` is not `cpu` is
skipped. Then, for a CPU node: disabled, or a `compatible` other than exactly
`arm,cortex-a76`, `BadProperty`; no `reg`, `MissingProperty`; its value in
`cells` cells (`cellsU64`), `UnsupportedCells` or `BadProperty`; its ID: a
value that is not `id << affinity_shift` for an ID below 4, or the ID of an
earlier CPU node, `BadProperty`; then, for every CPU but ID 0, and for CPU 0
when the profile asks it of CPU 0, an `enable-method` other than `psci`,
`BadProperty`. The `enable-method` of CPU 0 is otherwise not read. -/
def cpuOfChild (profile : CpuProfile) (cells : UInt32) (ids : List UInt64) (n : Node) :
    Except Error (List UInt64) := do
  if (← n.stringProperty "device_type") != some "cpu" then return ids
  if !(← n.enabled) then throw .badProperty
  if (← n.stringProperty "compatible") != some "arm,cortex-a76" then throw .badProperty
  let some reg := n.property "reg" | throw .missingProperty
  let affinity ← cellsU64 reg cells
  let some id := profile.idOf affinity | throw .badProperty
  if ids.contains id then throw .badProperty
  if id != 0 || profile.cpu0EnableMethod then
    let method ← n.stringProperty "enable-method"
    if method != some "psci" then throw .badProperty
  pure (ids ++ [id])

/-- The set of the IDs of the CPU nodes, which are distinct: their number
`count` is one that the profile allows, and they are `0` to `count - 1`. -/
def idsComplete (profile : CpuProfile) (ids : List UInt64) : Bool :=
  let count := ids.length
  profile.allows count &&
    (List.range count).all fun i => ids.contains (UInt64.ofNat i)

/-- `Fdt::discover_cpus(profile)`: the CPU topology of the tree, or the error
of the first broken rule of step 6 of the error order. `/cpus` absent,
`MissingProperty`; disabled, then with size cells other than 0,
`BadProperty`; its address cells, a value that is not 4 bytes `BadProperty`,
then other than 1 or 2 `UnsupportedCells`; each child of `/cpus` in tree
order (`cpuOfChild`); then the set of IDs (`idsComplete`), `BadProperty`;
`/psci` absent, `MissingProperty`; its binding: disabled, a `method` other
than the conduit of the profile, or a `compatible` other than one of
`PSCI_COMPATIBLE`, `BadProperty`. The `status` and `method` of `/psci` fail as
`Node::string_property` does; its `compatible`, a list of strings, is
compared as bytes. -/
def Fdt.discoverCpus (t : Fdt) (profile : CpuProfile) : Except Error CpuTopology := do
  let some cpus ← t.findNode "/cpus" | throw .missingProperty
  if !(← cpus.enabled) then throw .badProperty
  if (← cpus.sizeCells) != 0 then throw .badProperty
  let cells ← cpus.addressCells
  if !(cells == 1 || cells == 2) then throw .unsupportedCells
  let ids ← (t.nodes.filter (·.isChildOf cpus)).foldlM (cpuOfChild profile cells) []
  if !idsComplete profile ids then throw .badProperty
  let some psci ← t.findNode "/psci" | throw .missingProperty
  if !(← psci.enabled) then throw .badProperty
  if (← psci.stringProperty "method") != some profile.conduit.name then throw .badProperty
  let compatible := (psci.property "compatible").map (·.toList)
  if !PSCI_COMPATIBLE.any (some · == compatible) then throw .badProperty
  pure { profile, count := UInt64.ofNat ids.length }

end Krepi.Spec.Fdt
