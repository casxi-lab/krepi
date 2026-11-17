module

public import Krepi.Spec.Fdt.Translate

/-!
# Device tree: the CPU nodes

`Fdt::discover_cpus` of the contract's `CPU nodes`, with step 6 of the error
order of the parse and the entries on a tree, and the functions of the CPU
profile and of the topology that it returns: `CpuProfile::logical_id`,
`affinity_shift` and `conduit`, and `CpuTopology::count`, `profile`,
`affinity` and `validate_qemu_timers`.

A CPU profile fixes the affinity level of the CPU IDs and the PSCI conduit:
QEMU virt with PSCI over HVC, QEMU virt with EL2 and PSCI over SMC, and the
Pi 5. The discovery reads the children of `/cpus` once each, in tree order,
and `/psci`; the topology that it returns holds the profile and the number of
CPUs, whose IDs are `0` to `count - 1`.
-/

@[expose] public section

namespace Krepi.Spec.Fdt

/-! ## Profiles -/

/-- `CpuProfile`: QEMU virt with PSCI over HVC, QEMU virt with EL2 and PSCI
over SMC, and the Pi 5. -/
inductive CpuProfile where
  | qemuHvc
  | qemuSmc
  | pi5
  deriving DecidableEq, Repr, Inhabited

/-- The PSCI conduit of a profile. -/
inductive PsciConduit where
  | hvc
  | smc
  deriving DecidableEq, Repr, Inhabited

/-- The `method` of `/psci` that names a conduit. -/
def PsciConduit.name : PsciConduit → String
  | .hvc => "hvc"
  | .smc => "smc"

/-- `CpuProfile::affinity_shift`: 8 on the Pi 5, whose CPU IDs are affinity
level 1 of `MPIDR_EL1`, and 0 on QEMU virt. -/
def CpuProfile.affinityShift : CpuProfile → UInt64
  | .pi5 => 8
  | _ => 0

/-- `CpuProfile::conduit`: HVC for QEMU virt without EL2, SMC for QEMU virt
with EL2 and for the Pi 5. -/
def CpuProfile.conduit : CpuProfile → PsciConduit
  | .qemuHvc => .hvc
  | _ => .smc

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

/-- The private interrupts of the timer of QEMU virt, in their order: 13, 14,
11 and 10, and with EL2 12 after them; none for the Pi 5, whose timer belongs
to its board support. -/
def CpuProfile.timerInterrupts : CpuProfile → Option (List Nat)
  | .qemuHvc => some [13, 14, 11, 10]
  | .qemuSmc => some [13, 14, 11, 10, 12]
  | .pi5 => none

/-- `CpuTopology::validate_qemu_timers(interrupts)`: for the Pi 5 profile,
`BadProperty`; otherwise the `interrupts` of the timer node of QEMU virt must
be the records of three cells, type 1 for a private interrupt, its number and
the flags `((1 << count) - 1) << 8 | 4`, the admitted CPUs and a level-high
trigger, for the private interrupts of the profile in their order, with
nothing else, or `BadProperty`. The flags are a 32-bit cell, computed at that
width; a topology of the discovery has 1, 2 or 4 CPUs, so its shift is exact.
-/
def CpuTopology.validateQemuTimers (t : CpuTopology) (interrupts : ByteArray) :
    Except Error Unit := do
  let some ppis := t.profile.timerInterrupts | throw .badProperty
  let flags : UInt32 := (((1 : UInt32) <<< t.count.toUInt32) - 1) <<< 8 ||| 4
  let records := ppis.flatMap fun ppi => be32 1 ++ be32 ppi ++ be32 flags.toNat
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
earlier CPU node, `BadProperty`; then, for every CPU but ID 0 and on the Pi 5
for every CPU, an `enable-method` other than `psci`, `BadProperty`. The
`enable-method` of CPU 0 on QEMU virt is not read. -/
def cpuOfChild (profile : CpuProfile) (cells : UInt32) (ids : List UInt64) (n : Node) :
    Except Error (List UInt64) := do
  if (← n.stringProperty "device_type") != some "cpu" then return ids
  if !(← n.enabled) then throw .badProperty
  if (← n.stringProperty "compatible") != some "arm,cortex-a76" then throw .badProperty
  let some reg := n.property "reg" | throw .missingProperty
  let affinity ← cellsU64 reg cells
  let some id := profile.idOf affinity | throw .badProperty
  if ids.contains id then throw .badProperty
  if id != 0 || profile == .pi5 then
    let method ← n.stringProperty "enable-method"
    if method != some "psci" then throw .badProperty
  pure (ids ++ [id])

/-- The set of the IDs of the CPU nodes, which are distinct: their number
`count` is 1, 2 or 4, and 4 on the Pi 5, and they are `0` to `count - 1`. -/
def idsComplete (profile : CpuProfile) (ids : List UInt64) : Bool :=
  let count := ids.length
  (count == 1 || count == 2 || count == 4) && (profile != .pi5 || count == 4) &&
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
