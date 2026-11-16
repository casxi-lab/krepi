module

public import Krepi.Spec.Fdt.Plan
public import Krepi.Spec.Fdt.Cpus
public meta import Krepi.Spec.Fdt.Plan
public meta import Krepi.Spec.Fdt.Cpus

/-!
# Replay of the device-tree vectors

`replay` answers one line of `verification/vectors/boot-platform/fdt.vectors`
through the specification: it reads the input in the notation of the
contract's `Legacy test vectors` section, calls the entries that the input
names and writes the output in the same notation, in its canonical form, so
that `cargo xtask formal vectors` compares it with the expected output as
text. The expected outputs are the literals of the vector file; nothing here
computes them.

An input is `entry=<entry>`, then `dtb=<bytes>` for an entry on a tree and
`node=<path>` for an entry on a node, then the other arguments of the entry,
and at the end `ask=` with the fields and queries that the case asks, joined
by `,`. A case that asks nothing gives `result=ok` or `result=err`; one that
asks `error` gives `result=ok`, or names the error of a rejection; one that
asks fields or queries gives each as `<field>=<value>` or
`<query>(<argument>)=<value>` in the order of the ask, or names the error of a
rejection, `Error::<variant>` or `PlanError::<variant>`. A query that fails
gives `Error::<variant>` as its value.

- `entry=parse` asks nothing, `error` or `total_size`; a case that asks
  entries on the tree, `discover_memory` once and `reg`, `ranges` and
  `dma_ranges` of every node, calls them on an accepted tree and gives
  `result=returned` once they have returned.
- `entry=string_property node=<path> name=<name>` asks `value`, the string or
  `-` for none; `entry=translate_reg node=<path> span=<span>` asks `span`.
- `entry=reg node=<path>`, and `entry=Reg::new bytes=<bytes>
  address_cells=<n> size_cells=<n>`, ask `entries`, the spans, and `end(<i>)`,
  `Span::end` of the entry `i`, counted from 0.
- `entry=ranges` and `dma_ranges` with `node=<path>`, and
  `entry=AddressMap::new bytes=<bytes> child_cells=<n> parent_cells=<n>
  size_cells=<n>`, where `bytes=-` is an absent property, ask `kind` and the
  queries `to_parent(<span>)` and `to_child(<span>)`.
- `entry=cells_u64 bytes=<bytes> cells=<n>` asks `value`.
- `entry=discover_memory` asks `ram`, `reserved` and `dynamic`.
- `entry=discover_pi5_boot_memory dtb_address=<address> image=<span>` asks
  `ram`, `reserved`, `dynamic`, `dtb`, `image`, `ram_bytes` and the query
  `is_available(<span>)`; `entry=find_available` with the same arguments and
  then `size`, `alignment`, `minimum` and `limit` asks `span`, `-` for none,
  and the same query of the Pi 5 boot memory.
- `entry=discover_cpus profile=<profile>` asks `count`, `profile` and
  `affinity(<i>)`, `-` for none; `entry=validate_qemu_timers` with the same
  argument and then `interrupts=<bytes>` asks nothing;
  `entry=logical_id profile=<profile> mpidr=<value>` asks `id`, `-` for none.
  A profile is `QemuHvc`, `QemuSmc` or `Pi5`.
- `entry=all_ram ram=<spans> boot=<spans> firmware=<regions>` and
  `entry=MemoryPlan::new` with `window=<span>` before them, and
  `entry=from_pi5` with the arguments of `discover_pi5_boot_memory` and then
  `window=<span> more=<spans>`, ask the fields `ram`, `managed`, `boot`,
  `firmware`, `reservations` and `available`, lists of spans;
  `described_bytes`, `managed_bytes` and `available_bytes`, the sum of the
  usable ranges, in hexadecimal; and the queries `contains_ram(<span>)`,
  `is_available(<span>)` and `permits_backing(<span>)`, `true` or `false`,
  and `available_count(<span>)`, the number of usable ranges that hold the
  span, in decimal. A firmware reservation is `<span>/<flag>`.

An entry on a tree first parses the bytes, and an entry on a node also finds
the node, and reports the error of either as the output.
-/

@[expose] public section

namespace Krepi.SpecTests.Fdt.Replay

open Krepi.Spec.Fdt

/-! ## Reading the input -/

/-- The pieces of `s` between the characters `c`. -/
def splitOnChar (c : Char) (s : String) : List String :=
  let rec go : List Char → List Char → List String
    | [], acc => [String.ofList acc.reverse]
    | x :: rest, acc => if x == c then String.ofList acc.reverse :: go rest [] else go rest (x :: acc)
  go s.toList []

/-- The fields `key=value` of an input, in their order. -/
def fields (input : String) : List (String × String) :=
  (splitOnChar ' ' input).filterMap fun f =>
    match f.toList.span (· != '=') with
    | (key, '=' :: value) => some (String.ofList key, String.ofList value)
    | _ => none

/-- The value of the field `key`. -/
def field (fs : List (String × String)) (key : String) : Option String :=
  (fs.find? (·.1 == key)).map (·.2)

/-- The value of a hexadecimal digit. -/
def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- The bytes of lowercase hexadecimal digits, two for each byte. -/
def hexBytes (s : String) : Option ByteArray :=
  let rec go : List Char → ByteArray → Option ByteArray
    | [], acc => some acc
    | [_], _ => none
    | h :: l :: rest, acc => do
      let a ← hexDigit h
      let b ← hexDigit l
      go rest (acc.push (UInt8.ofNat (a * 16 + b)))
  go s.toList ByteArray.empty

/-- A number written as `0x` and hexadecimal digits, or as decimal digits. -/
def number (s : String) : Option Nat :=
  match s.toList with
  | '0' :: 'x' :: digits@(_ :: _) =>
    digits.foldlM (fun acc c => (hexDigit c).map (acc * 16 + ·)) 0
  | digits@(_ :: _) =>
    digits.foldlM (fun acc c => if c.isDigit then some (acc * 10 + (c.toNat - '0'.toNat)) else none) 0
  | [] => none

/-- A 64-bit number. -/
def number64 (s : String) : Option UInt64 := do
  let n ← number s
  if n < 2 ^ 64 then some (UInt64.ofNat n) else none

/-- A 32-bit number. -/
def number32 (s : String) : Option UInt32 := do
  let n ← number s
  if n < 2 ^ 32 then some (UInt32.ofNat n) else none

/-- A span `<start>+<size>`. -/
def span (s : String) : Option Span :=
  match splitOnChar '+' s with
  | [start, size] => do pure ⟨← number64 start, ← number64 size⟩
  | _ => none

/-- A list of spans joined by `,`, or `-` for none. -/
def spans (s : String) : Option (List Span) :=
  if s == "-" then some [] else (splitOnChar ',' s).mapM span

/-- A reserved region `<span>/<flag>`, with the flag `no-map`, `reusable` or
`none`. -/
def region (s : String) : Option ReservedRegion :=
  match splitOnChar '/' s with
  | [sp, "no-map"] => (span sp).map (⟨·, true, false⟩)
  | [sp, "reusable"] => (span sp).map (⟨·, false, true⟩)
  | [sp, "none"] => (span sp).map (⟨·, false, false⟩)
  | _ => none

/-- A list of reserved regions joined by `,`, or `-` for none. -/
def regions (s : String) : Option (List ReservedRegion) :=
  if s == "-" then some [] else (splitOnChar ',' s).mapM region

/-- A query `<name>(<argument>)`: its name and its argument. -/
def query (s : String) : Option (String × String) :=
  match s.toList.span (· != '(') with
  | (name, '(' :: rest) =>
    match rest.reverse with
    | ')' :: arg => some (String.ofList name, String.ofList arg.reverse)
    | _ => none
  | _ => none

/-- A CPU profile by its name. -/
def profile : String → Option CpuProfile
  | "QemuHvc" => some .qemuHvc
  | "QemuSmc" => some .qemuSmc
  | "Pi5" => some .pi5
  | _ => none

/-! ## Writing the output -/

/-- A number as `0x` and lowercase hexadecimal digits. -/
def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- A span as `<start>+<size>`. -/
def spanText (s : Span) : String := hex s.start.toNat ++ "+" ++ hex s.size.toNat

/-- A list of spans joined by `,`, and `-` when empty. -/
def spansText (spans : List Span) : String :=
  if spans.isEmpty then "-" else ",".intercalate (spans.map spanText)

/-- A reserved region as its span, `/` and its flag. -/
def regionText (r : ReservedRegion) : String :=
  spanText r.span ++ "/" ++ if r.noMap then "no-map" else if r.reusable then "reusable" else "none"

/-- A list of reserved regions joined by `,`, and `-` when empty. -/
def regionsText (regions : List ReservedRegion) : String :=
  if regions.isEmpty then "-" else ",".intercalate (regions.map regionText)

/-- A truth value. -/
def boolText (b : Bool) : String := if b then "true" else "false"

/-- The name of a CPU profile. -/
def profileText : CpuProfile → String
  | .qemuHvc => "QemuHvc"
  | .qemuSmc => "QemuSmc"
  | .pi5 => "Pi5"

/-- The name of the kind of an address map. -/
def kindText : MappingKind → String
  | .absent => "Absent"
  | .identity => "Identity"
  | .windows => "Windows"

/-- The value of a query that may fail. -/
def queryText {α} (text : α → String) : Except Error α → String
  | .ok v => text v
  | .error e => "Error::" ++ e.name

/-- The output of a rejection that names its error. -/
def errorText (e : Error) : String := "result=err error=Error::" ++ e.name

/-- The output of a success with its fields. -/
def okText (fs : List String) : String := String.join ("result=ok" :: fs.map (" " ++ ·))

/-- The output of a case whose entry gave `result`, whose error `name` writes
as `<type>::<variant>`: a case that asks nothing gives `result=ok` or
`result=err`; one that asks `error` gives `result=ok` or the error; one that
asks fields and queries gives the error, or each of them with the value that
`answer` gives it. -/
def outcomeAs {ε α} (name : ε → String) (result : Except ε α) (ask : List String)
    (answer : α → String → Option String) : String :=
  match result with
  | .error e => if ask.isEmpty then "result=err" else "result=err error=" ++ name e
  | .ok v =>
    if ask.isEmpty || ask == ["error"] then "result=ok"
    else match ask.mapM fun a => (answer v a).map (a ++ "=" ++ ·) with
      | some answers => okText answers
      | none => "result=malformed ask"

/-- `outcomeAs` for an entry whose error is an `Error`. -/
def outcome {α} (result : Except Error α) (ask : List String) (answer : α → String → Option String) :
    String :=
  outcomeAs (fun e => "Error::" ++ e.name) result ask answer

/-! ## Answers -/

/-- The fields and queries of a `Reg`. -/
def regAnswer (r : Reg) : String → Option String
  | "entries" => some (spansText r.entries)
  | q => do
    let ("end", i) ← query q | none
    let i ← number i
    pure <| match r.entries[i]? with
      | none => "-"
      | some s => queryText (hex ·.toNat) s.endAddr

/-- The fields and queries of an address map. -/
def mapAnswer (m : AddressMap) : String → Option String
  | "kind" => some (kindText m.kind)
  | q => do
    let (name, arg) ← query q
    let s ← span arg
    match name with
    | "to_parent" => some (queryText spanText (m.toParent s))
    | "to_child" => some (queryText spanText (m.toChild s))
    | _ => none

/-- The fields of a memory map. -/
def memoryAnswer (m : MemoryMap) : String → Option String
  | "ram" => some (spansText m.ram)
  | "reserved" => some (regionsText m.reserved)
  | "dynamic" => some (toString m.dynamic.toNat)
  | _ => none

/-- The fields and queries of a Pi 5 boot memory. -/
def pi5Answer (m : Pi5BootMemory) : String → Option String
  | "dtb" => some (spanText m.dtb)
  | "image" => some (spanText m.image)
  | "ram_bytes" => some (hex m.ramBytes.toNat)
  | q => match query q with
    | some ("is_available", arg) => (span arg).map fun s => queryText boolText (m.isAvailable s)
    | _ => memoryAnswer m.memory q

/-- The fields and queries of a CPU topology. -/
def topologyAnswer (t : CpuTopology) : String → Option String
  | "count" => some (toString t.count.toNat)
  | "profile" => some (profileText t.profile)
  | q => do
    let ("affinity", i) ← query q | none
    let i ← number64 i
    pure ((t.affinity i).elim "-" (hex ·.toNat))

/-- The fields and queries of a boot memory map. -/
def planAnswer (p : MemoryPlan) : String → Option String
  | "ram" => some (spansText p.ram)
  | "managed" => some (spansText p.managedBanks)
  | "boot" => some (spansText p.bootRanges)
  | "firmware" => some (spansText p.firmwareRanges)
  | "reservations" => some (spansText p.reservations)
  | "available" => some (spansText p.availableRanges)
  | "described_bytes" => some (hex p.describedBytes.toNat)
  | "managed_bytes" => some (hex p.managedBytes.toNat)
  | "available_bytes" => some (hex (sumSizes p.availableRanges).toNat)
  | q => do
    let (name, arg) ← query q
    let s ← span arg
    match name with
    | "contains_ram" => some (boolText (p.containsRam s))
    | "is_available" => some (boolText (p.isAvailable s))
    | "permits_backing" => some (boolText (p.permitsBacking s))
    | "available_count" => some (toString (p.availableRanges.filter (·.holds s)).length)
    | _ => none

/-- The output of a case of a boot memory map, whose error is a `PlanError`. -/
def planOutcome (result : Except PlanError MemoryPlan) (ask : List String) : String :=
  outcomeAs (fun e => "PlanError::" ++ e.name) result ask planAnswer

/-! ## Cases -/

/-- The entries that a case of the parse may ask on an accepted tree. -/
def treeCalls : List String := ["discover_memory", "reg", "ranges", "dma_ranges"]

/-- `entry=parse`. -/
def parseCase (dtb : ByteArray) (ask : List String) : String :=
  if !ask.isEmpty && ask.all treeCalls.contains then
    match Fdt.parse dtb with
    | .error _ => "result=returned"
    | .ok t =>
      let calls := t.nodes.flatMap fun n =>
        (if ask.contains "reg" then [(n.reg.map fun _ => ()).toBool] else []) ++
        (if ask.contains "ranges" then [(n.ranges.map fun _ => ()).toBool] else []) ++
        (if ask.contains "dma_ranges" then [(n.dmaRanges.map fun _ => ()).toBool] else [])
      let memory := ask.contains "discover_memory" && (t.discoverMemory.map fun _ => ()).toBool
      -- The output depends on every result, so each is evaluated; neither condition holds.
      if (calls.filter id).length > 3 * t.records.size || (memory && t.records.size == 0) then
        "result=impossible"
      else "result=returned"
  else
    outcome (Fdt.parse dtb) ask fun t a =>
      if a == "total_size" then some (toString t.totalSize.toNat) else none

/-- The node `path` of the tree `t`, or the output of the failure. -/
def nodeOf (t : Fdt) (path : String) : Except String Node :=
  match t.findNode path with
  | .error e => .error (errorText e)
  | .ok none => .error "result=err node=-"
  | .ok (some n) => .ok n

/-- A case of an entry on a node of the tree `t`. -/
def nodeCase (t : Fdt) (entry : String) (fs : List (String × String)) (ask : List String) :
    String := Id.run do
  let some path := field fs "node" | return "result=malformed node"
  match nodeOf t path with
  | .error out => out
  | .ok n =>
    match entry with
    | "string_property" =>
      let some name := field fs "name" | return "result=malformed name"
      outcome (n.stringProperty name) ask fun v a => if a == "value" then some (v.getD "-") else none
    | "translate_reg" =>
      let some s := (field fs "span").bind span | return "result=malformed span"
      outcome (n.translateReg s) ask fun v a => if a == "span" then some (spanText v) else none
    | "reg" => outcome n.reg ask regAnswer
    | "ranges" => outcome n.ranges ask mapAnswer
    | "dma_ranges" => outcome n.dmaRanges ask mapAnswer
    | _ => "result=malformed entry"

/-- A case of an entry on the tree `t`. -/
def treeCase (t : Fdt) (entry : String) (fs : List (String × String)) (ask : List String) :
    String := Id.run do
  match entry with
  | "discover_memory" => return outcome t.discoverMemory ask memoryAnswer
  | "discover_pi5_boot_memory" | "find_available" | "from_pi5" =>
    let some dtbAddress := (field fs "dtb_address").bind number64 | return "result=malformed dtb_address"
    let some image := (field fs "image").bind span | return "result=malformed image"
    let memory := t.discoverPi5BootMemory dtbAddress image
    if entry == "discover_pi5_boot_memory" then return outcome memory ask pi5Answer
    if entry == "from_pi5" then
      let some window := (field fs "window").bind span | return "result=malformed window"
      let some more := (field fs "more").bind spans | return "result=malformed more"
      let plan : Except String MemoryPlan := match memory with
        | .error e => .error ("Error::" ++ e.name)
        | .ok m => (MemoryPlan.fromPi5 m window more).mapError ("PlanError::" ++ ·.name)
      return outcomeAs id plan ask planAnswer
    let some size := (field fs "size").bind number64 | return "result=malformed size"
    let some alignment := (field fs "alignment").bind number64 | return "result=malformed alignment"
    let some minimum := (field fs "minimum").bind number64 | return "result=malformed minimum"
    let some limit := (field fs "limit").bind number64 | return "result=malformed limit"
    let selected := do
      let m ← memory
      pure (m, ← m.findAvailable size alignment minimum limit)
    return outcome selected ask fun (m, s) a =>
      if a == "span" then some (s.elim "-" spanText) else pi5Answer m a
  | "discover_cpus" | "validate_qemu_timers" =>
    let some p := (field fs "profile").bind profile | return "result=malformed profile"
    let topology := t.discoverCpus p
    if entry == "discover_cpus" then return outcome topology ask topologyAnswer
    let some interrupts := (field fs "interrupts").bind hexBytes | return "result=malformed interrupts"
    return outcome (topology.bind (·.validateQemuTimers interrupts)) ask fun _ _ => none
  | _ => return nodeCase t entry fs ask

/-- The cells argument `key` of an entry without a tree. -/
def cellsField (fs : List (String × String)) (key : String) : Option UInt32 :=
  (field fs key).bind number32

/-- A case of an entry without a tree. -/
def valueCase (entry : String) (fs : List (String × String)) (ask : List String) : Option String := do
  match entry with
  | "cells_u64" =>
    let bytes ← (field fs "bytes").bind hexBytes
    let cells ← cellsField fs "cells"
    pure <| outcome (cellsU64 bytes cells) ask fun v a =>
      if a == "value" then some (hex v.toNat) else none
  | "Reg::new" =>
    let bytes ← (field fs "bytes").bind hexBytes
    pure <| outcome (Reg.new bytes (← cellsField fs "address_cells") (← cellsField fs "size_cells"))
      ask regAnswer
  | "AddressMap::new" =>
    let bytes ← match field fs "bytes" with
      | some "-" => some none
      | some text => (hexBytes text).map some
      | none => none
    let map := AddressMap.new bytes (← cellsField fs "child_cells") (← cellsField fs "parent_cells")
      (← cellsField fs "size_cells")
    pure <| outcome map ask mapAnswer
  | "logical_id" =>
    let p ← (field fs "profile").bind profile
    let mpidr ← (field fs "mpidr").bind number64
    pure <| outcome (.ok (p.logicalId mpidr) : Except Error _) ask fun v a =>
      if a == "id" then some (v.elim "-" (toString ·.toNat)) else none
  | "all_ram" =>
    let ram ← (field fs "ram").bind spans
    let boot ← (field fs "boot").bind spans
    let firmware ← (field fs "firmware").bind regions
    pure <| planOutcome (MemoryPlan.allRam ram boot firmware) ask
  | "MemoryPlan::new" =>
    let window ← (field fs "window").bind span
    let ram ← (field fs "ram").bind spans
    let boot ← (field fs "boot").bind spans
    let firmware ← (field fs "firmware").bind regions
    pure <| planOutcome (MemoryPlan.new window ram boot firmware) ask
  | _ => none

/-- The entries without a tree. -/
def valueEntries : List String :=
  ["cells_u64", "Reg::new", "AddressMap::new", "logical_id", "all_ram", "MemoryPlan::new"]

/-- One case. -/
def runCase (fs : List (String × String)) : String := Id.run do
  let some entry := field fs "entry" | return "result=malformed entry"
  let ask := match field fs "ask" with
    | some "" | none => []
    | some a => splitOnChar ',' a
  if valueEntries.contains entry then
    return (valueCase entry fs ask).getD "result=malformed input"
  let some dtbText := field fs "dtb" | return "result=malformed dtb"
  let some dtb := hexBytes dtbText | return "result=malformed dtb"
  if entry == "parse" then return parseCase dtb ask
  match Fdt.parse dtb with
  | .error e => errorText e
  | .ok t => treeCase t entry fs ask

/-- The output of the specification for the input of one vector. -/
def replay (input : String) : String := runCase (fields input)

/-! ## Representative cases

One case of each vector of the file, its input and expected output copied
from the vector file. The bytes of an input are written in pieces with string
gaps: a backslash at the end of a line, whose newline and the indentation
after it are not part of the string. -/

-- `fdt-parser-1.41`: the first 40 bytes of the minimal tree, its header alone, are rejected.
#guard replay
  "entry=parse \
  dtb=\
  d00dfeed000000df00000038000000b4000000280000001100000010000000000000002b\
  0000007c \
  ask=" ==
  "result=err"

-- `fdt-parser-2.1`: the minimal tree with the magic 0 fails with `BadMagic`.
#guard replay
  "entry=parse \
  dtb=\
  00000000000000df00000038000000b4000000280000001100000010000000000000002b\
  0000007c0000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f00000002000000016d656d6f72794031\
  30303030303030300000000000000003000000070000001b6d656d6f7279000000000003\
  000000100000002700000001000000000000000000200000000000020000000200000009\
  23616464726573732d63656c6c73002373697a652d63656c6c73006465766963655f7479\
  70650072656700 \
  ask=error" ==
  "result=err error=Error::BadMagic"

-- `fdt-parser-3.2`: the reservation entries `0x1000+0x2000` and `0x2000+0x2000` fail with
-- `Overlap`.
#guard replay
  "entry=parse \
  dtb=\
  d00dfeed000000ff00000058000000d4000000280000001100000010000000000000002b\
  0000007c0000000000001000000000000000200000000000000020000000000000002000\
  000000000000000000000000000000000000000100000000000000030000000400000000\
  0000000200000003000000040000000f00000002000000016d656d6f7279403130303030\
  303030300000000000000003000000070000001b6d656d6f727900000000000300000010\
  000000270000000100000000000000000020000000000002000000020000000923616464\
  726573732d63656c6c73002373697a652d63656c6c73006465766963655f747970650072\
  656700 \
  ask=error" ==
  "result=err error=Error::Overlap"

-- `fdt-parser-4.2`: `#address-cells` twice in the root fails with `DuplicateProperty`.
#guard replay
  "entry=parse \
  dtb=\
  d00dfeed000000a20000003800000078000000280000001100000010000000000000002a\
  000000400000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f0000000200000003000000040000001b\
  00000002000000020000000923616464726573732d63656c6c73002373697a652d63656c\
  6c730023616464726573732d63656c6c7300 \
  ask=error" ==
  "result=err error=Error::DuplicateProperty"

-- `fdt-parser-5.1`: a root without its end node fails with `BadTree`.
#guard replay
  "entry=parse \
  dtb=\
  d00dfeed0000007f0000003800000064000000280000001100000010000000000000001b\
  0000002c0000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f00000002000000092361646472657373\
  2d63656c6c73002373697a652d63656c6c7300 \
  ask=error" ==
  "result=err error=Error::BadTree"

-- `fdt-parser-6.1`: the minimal tree with its first byte inverted returns.
#guard replay
  "entry=parse \
  dtb=\
  2f0dfeed000000df00000038000000b4000000280000001100000010000000000000002b\
  0000007c0000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f00000002000000016d656d6f72794031\
  30303030303030300000000000000003000000070000001b6d656d6f7279000000000003\
  000000100000002700000001000000000000000000200000000000020000000200000009\
  23616464726573732d63656c6c73002373697a652d63656c6c73006465766963655f7479\
  70650072656700 \
  ask=discover_memory,reg,ranges,dma_ranges" ==
  "result=returned"

-- `fdt-parser-7.2`: the root `model` of the tree minimized from QEMU reads
-- `linux,dummy-virt`, with nonzero bytes in the padding after it.
#guard replay
  "entry=string_property \
  dtb=\
  d00dfeed0000010100000038000000d00000002800000011000000100000000000000031\
  000000980000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f0000000200000003000000110000001b\
  6c696e75782c64756d6d792d7669727400000002000000016d656d6f7279403430303030\
  303030000000000300000007000000216d656d6f7279007300000003000000100000002d\
  000000004000000000000000080000000000000200000002000000092361646472657373\
  2d63656c6c73002373697a652d63656c6c73006d6f64656c006465766963655f74797065\
  0072656700 \
  node=/ \
  name=model \
  ask=value" ==
  "result=ok value=linux,dummy-virt"

-- `fdt-parser-8.1`: the minimal tree of version 18, compatible with 17, is accepted.
#guard replay
  "entry=parse \
  dtb=\
  d00dfeed000000df00000038000000b4000000280000001200000011000000000000002b\
  0000007c0000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f00000002000000016d656d6f72794031\
  30303030303030300000000000000003000000070000001b6d656d6f7279000000000003\
  000000100000002700000001000000000000000000200000000000020000000200000009\
  23616464726573732d63656c6c73002373697a652d63656c6c73006465766963655f7479\
  70650072656700 \
  ask=" ==
  "result=ok"

-- `fdt-parser-9.6`: a root property name of 65 bytes fails with `BadString`.
#guard replay
  "entry=parse \
  dtb=\
  d00dfeed000000d10000003800000074000000280000001100000010000000000000005d\
  0000003c0000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f0000000200000003000000000000001b\
  000000020000000923616464726573732d63656c6c73002373697a652d63656c6c730078\
  787878787878787878787878787878787878787878787878787878787878787878787878\
  7878787878787878787878787878787878787878787878787878787800 \
  ask=error" ==
  "result=err error=Error::BadString"

-- `fdt-translation-1.1`: the `reg` `0x20+0x10` of `/bus/bridge/serial@20` translates to
-- `0x200001020+0x10` through the `ranges` of the bridge and of the bus.
#guard replay
  "entry=translate_reg \
  dtb=\
  d00dfeed000002060000003800000188000000280000001100000010000000000000007e\
  000001500000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f00000002000000016d656d6f72794031\
  30303030303030300000000000000003000000070000001b6d656d6f7279000000000003\
  000000100000002700000001000000000000000000200000000000020000000162757300\
  00000003000000040000002b0000000100000003000000040000003a0000000100000003\
  00000010000000460000000000000002000000000001000000000003000000100000004d\
  000000000000000300000000000100000000000162726964676500000000000300000004\
  000000580000000100000003000000040000006700000001000000030000000c00000073\
  0000000000001000000010000000000173657269616c4032300000000000000300000008\
  0000007a0000002000000010000000020000000200000002000000020000000923616464\
  726573732d63656c6c73002373697a652d63656c6c73006465766963655f747970650072\
  65670023616464726573732d63656c6c73002373697a652d63656c6c730072616e676573\
  00646d612d72616e6765730023616464726573732d63656c6c73002373697a652d63656c\
  6c730072616e6765730072656700 \
  node=/bus/bridge/serial@20 \
  span=0x20+0x10 \
  ask=span" ==
  "result=ok span=0x200001020+0x10"

-- `fdt-translation-2.1`: an absent map is of the kind `Absent` and fails `0x100000000+0x1000` with
-- `Unmapped`.
#guard replay
  "entry=AddressMap::new \
  bytes=- \
  child_cells=2 \
  parent_cells=2 \
  size_cells=2 \
  ask=kind,to_parent(0x100000000+0x1000)" ==
  "result=ok kind=Absent to_parent(0x100000000+0x1000)=Error::Unmapped"

-- `fdt-translation-3.2`: two windows that hold `0x4+0x4` fail with `AmbiguousMapping`.
#guard replay
  "entry=AddressMap::new \
  bytes=0000000000000001000000000000100000000000000000020000000000001000 \
  child_cells=1 \
  parent_cells=2 \
  size_cells=1 \
  ask=to_parent(0x4+0x4)" ==
  "result=ok to_parent(0x4+0x4)=Error::AmbiguousMapping"

-- `fdt-translation-4.1`: the cells `0x12`, `0x34567890` read as 2 cells give `0x1234567890`.
#guard replay
  "entry=cells_u64 \
  bytes=0000001234567890 \
  cells=2 \
  ask=value" ==
  "result=ok value=0x1234567890"

-- `fdt-translation-4.6`: a window to `0xffffffffffffffff` of size 2 fails with
-- `Overflow` at construction.
#guard replay
  "entry=AddressMap::new \
  bytes=00000000ffffffffffffffff00000002 \
  child_cells=1 \
  parent_cells=2 \
  size_cells=1 \
  ask=error" ==
  "result=err error=Error::Overflow"

-- `fdt-translation-5.2`: the one-cell `reg` `0xffffffff+0x1` is accepted and ends at `0x100000000`.
#guard replay
  "entry=Reg::new \
  bytes=ffffffff00000001 \
  address_cells=1 \
  size_cells=1 \
  ask=entries,end(0)" ==
  "result=ok entries=0xffffffff+0x1 end(0)=0x100000000"

-- `fdt-discovery-1.2`: the reservation entry and the `no-map` child of `/reserved-memory` are both
-- reserved regions, in that order, after the RAM range.
#guard replay
  "entry=discover_memory \
  dtb=\
  d00dfeed000001a4000000480000014c0000002800000011000000100000000000000058\
  000001040000000100000000000000000000100000000000000000000000000000000000\
  00000001000000000000000300000004000000000000000200000003000000040000000f\
  00000002000000016d656d6f727940313030303030303030000000000000000300000007\
  0000001b6d656d6f72790000000000030000001000000027000000010000000000000000\
  00200000000000020000000172657365727665642d6d656d6f7279000000000300000004\
  0000002b0000000200000003000000040000003a00000002000000030000000000000046\
  000000016669726d7761726540313030303031303030000000000003000000100000004d\
  000000010000100000000000000020000000000300000000000000510000000200000002\
  000000020000000923616464726573732d63656c6c73002373697a652d63656c6c730064\
  65766963655f74797065007265670023616464726573732d63656c6c73002373697a652d\
  63656c6c730072616e67657300726567006e6f2d6d617000 \
  ask=ram,reserved" ==
  "result=ok ram=0x100000000+0x200000 reserved=0x100000000+0x1000/no-map,\
  0x100001000+0x2000/no-map"

-- `fdt-discovery-2.2`: the `reg` of `/bus/dev@0` is read in the default 2 and 1 cells of `/bus`.
#guard replay
  "entry=reg \
  dtb=\
  d00dfeed000001a50000003800000158000000280000001100000010000000000000004d\
  000001200000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f00000002000000016d656d6f72794031\
  30303030303030300000000000000003000000070000001b6d656d6f7279000000000003\
  00000010000000270000000100000000000000000020000000000002000000016d656d6f\
  7279403230303030303030300000000000000003000000070000002b6d656d6f72790000\
  00000003000000090000003764697361626c65640000000000000003000000100000003e\
  000000020000000000000000000010000000000200000001627573000000000300000000\
  00000042000000016465764030000000000000030000000c000000490000000000000000\
  000010000000000200000002000000020000000923616464726573732d63656c6c730023\
  73697a652d63656c6c73006465766963655f7479706500726567006465766963655f7479\
  706500737461747573007265670072616e6765730072656700 \
  node=/bus/dev@0 \
  ask=entries" ==
  "result=ok entries=0x0+0x1000"

-- `fdt-discovery-3.1`: a disabled memory node under another name is skipped before its binding.
#guard replay
  "entry=discover_memory \
  dtb=\
  d00dfeed0000017800000038000001280000002800000011000000100000000000000050\
  000000f00000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f00000002000000016d656d6f72794031\
  30303030303030300000000000000003000000070000001b6d656d6f7279000000000003\
  000000100000002700000001000000000000000000200000000000020000000173656372\
  616d4065303030303030000000000003000000070000002b6d656d6f7279000000000003\
  000000090000003764697361626c65640000000000000003000000050000003e6f6b6179\
  0000000000000003000000100000004c000000000e000000000000000100000000000002\
  000000020000000923616464726573732d63656c6c73002373697a652d63656c6c730064\
  65766963655f7479706500726567006465766963655f7479706500737461747573007365\
  637572652d7374617475730072656700 \
  ask=ram" ==
  "result=ok ram=0x100000000+0x200000"

-- `fdt-discovery-4.2`: a child of `/reserved-memory` with `size` and no `reg` is one dynamic
-- reservation and no reserved region.
#guard replay
  "entry=discover_memory \
  dtb=\
  d00dfeed0000016e000000380000011c0000002800000011000000100000000000000052\
  000000e40000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f00000002000000016d656d6f72794031\
  30303030303030300000000000000003000000070000001b6d656d6f7279000000000003\
  000000100000002700000001000000000000000000200000000000020000000172657365\
  727665642d6d656d6f72790000000003000000040000002b000000020000000300000004\
  0000003a0000000200000003000000000000004600000001706f6f6c0000000000000003\
  000000080000004d00000000000010000000000200000002000000020000000923616464\
  726573732d63656c6c73002373697a652d63656c6c73006465766963655f747970650072\
  65670023616464726573732d63656c6c73002373697a652d63656c6c730072616e676573\
  0073697a6500 \
  ask=ram,reserved,dynamic" ==
  "result=ok ram=0x100000000+0x200000 reserved=- dynamic=1"

-- `fdt-discovery-5.2`: a tree without a memory node fails with `NoMemory`.
#guard replay
  "entry=discover_memory \
  dtb=\
  d00dfeed000000830000003800000068000000280000001100000010000000000000001b\
  000000300000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f00000002000000020000000923616464\
  726573732d63656c6c73002373697a652d63656c6c7300 \
  ask=error" ==
  "result=err error=Error::NoMemory"

-- `fdt-discovery-6.2`: a child of `/reserved-memory` with `no-map` and `reusable` fails
-- with `BadProperty`.
#guard replay
  "entry=discover_memory \
  dtb=\
  d00dfeed0000019d000000380000013c0000002800000011000000100000000000000061\
  000001040000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f00000002000000016d656d6f72794031\
  30303030303030300000000000000003000000070000001b6d656d6f7279000000000003\
  000000100000002700000001000000000000000000200000000000020000000172657365\
  727665642d6d656d6f72790000000003000000040000002b000000020000000300000004\
  0000003a0000000200000003000000000000004600000001706f6f6c0000000000000003\
  000000100000004d00000001000000000000000000001000000000030000000000000051\
  000000030000000000000058000000020000000200000002000000092361646472657373\
  2d63656c6c73002373697a652d63656c6c73006465766963655f74797065007265670023\
  616464726573732d63656c6c73002373697a652d63656c6c730072616e67657300726567\
  006e6f2d6d6170007265757361626c6500 \
  ask=error" ==
  "result=err error=Error::BadProperty"

-- `fdt-cpus-1.1`: the Pi 5 CPUs at affinity level 1 give 4 CPUs and `affinity(i)` of `i << 8`.
#guard replay
  "entry=discover_cpus \
  dtb=\
  d00dfeed00000364000000380000027800000028000000110000001000000000000000ec\
  000002400000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f00000002000000016370757300000000\
  00000003000000040000001b0000000200000003000000040000002a0000000000000001\
  637075403000000000000003000000040000003663707500000000030000000f00000042\
  61726d2c636f727465782d613736000000000003000000050000004d7073636900000000\
  00000003000000080000005b000000000000000000000002000000016370754031000000\
  00000003000000040000005f63707500000000030000000f0000006b61726d2c636f7274\
  65782d613736000000000003000000050000007670736369000000000000000300000008\
  000000840000000000000100000000020000000163707540320000000000000300000004\
  0000008863707500000000030000000f0000009461726d2c636f727465782d6137360000\
  00000003000000050000009f70736369000000000000000300000008000000ad00000000\
  00000200000000020000000163707540330000000000000300000004000000b163707500\
  000000030000000f000000bd61726d2c636f727465782d61373600000000000300000005\
  000000c870736369000000000000000300000008000000d6000000000000030000000002\
  000000020000000170736369000000000000000300000023000000da61726d2c70736369\
  2d312e300061726d2c707363692d302e320061726d2c7073636900000000000300000004\
  000000e5736d630000000002000000020000000923616464726573732d63656c6c730023\
  73697a652d63656c6c730023616464726573732d63656c6c73002373697a652d63656c6c\
  73006465766963655f7479706500636f6d70617469626c6500656e61626c652d6d657468\
  6f6400726567006465766963655f7479706500636f6d70617469626c6500656e61626c65\
  2d6d6574686f6400726567006465766963655f7479706500636f6d70617469626c650065\
  6e61626c652d6d6574686f6400726567006465766963655f7479706500636f6d70617469\
  626c6500656e61626c652d6d6574686f640072656700636f6d70617469626c65006d6574\
  686f6400 \
  profile=Pi5 \
  ask=count,profile,affinity(0),affinity(1),affinity(2),affinity(3),affinity(4)" ==
  "result=ok count=4 profile=Pi5 affinity(0)=0x0 affinity(1)=0x100 affinity(2)=0x200 \
  affinity(3)=0x300 affinity(4)=-"

-- `fdt-cpus-2.8`: the HVC profile rejects the ID `0x80000000`, a flag bit and no affinity.
#guard replay
  "entry=discover_cpus \
  dtb=\
  d00dfeed0000024a00000038000001b0000000280000001100000010000000000000009a\
  000001780000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f00000002000000016370757300000000\
  00000003000000040000001b0000000200000003000000040000002a0000000000000001\
  637075403000000000000003000000040000003663707500000000030000000f00000042\
  61726d2c636f727465782d613736000000000003000000050000004d7073636900000000\
  00000003000000080000005b000000000000000000000002000000016370754031000000\
  00000003000000040000005f63707500000000030000000f0000006b61726d2c636f7274\
  65782d613736000000000003000000050000007670736369000000000000000300000008\
  000000840000000080000000000000020000000200000001707363690000000000000003\
  000000230000008861726d2c707363692d312e300061726d2c707363692d302e32006172\
  6d2c70736369000000000003000000040000009368766300000000020000000200000009\
  23616464726573732d63656c6c73002373697a652d63656c6c730023616464726573732d\
  63656c6c73002373697a652d63656c6c73006465766963655f7479706500636f6d706174\
  69626c6500656e61626c652d6d6574686f6400726567006465766963655f747970650063\
  6f6d70617469626c6500656e61626c652d6d6574686f640072656700636f6d7061746962\
  6c65006d6574686f6400 \
  profile=QemuHvc \
  ask=" ==
  "result=err"

-- `fdt-cpus-3.2`: the Pi 5 tree with the `enable-method` `spin-table` is rejected.
#guard replay
  "entry=discover_cpus \
  dtb=\
  d00dfeed00000374000000380000028800000028000000110000001000000000000000ec\
  000002500000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f00000002000000016370757300000000\
  00000003000000040000001b0000000200000003000000040000002a0000000000000001\
  637075403000000000000003000000040000003663707500000000030000000f00000042\
  61726d2c636f727465782d6137360000000000030000000b0000004d7370696e2d746162\
  6c65000000000003000000080000005b0000000000000000000000020000000163707540\
  3100000000000003000000040000005f63707500000000030000000f0000006b61726d2c\
  636f727465782d6137360000000000030000000b000000767370696e2d7461626c650000\
  000000030000000800000084000000000000010000000002000000016370754032000000\
  00000003000000040000008863707500000000030000000f0000009461726d2c636f7274\
  65782d6137360000000000030000000b0000009f7370696e2d7461626c65000000000003\
  00000008000000ad00000000000002000000000200000001637075403300000000000003\
  00000004000000b163707500000000030000000f000000bd61726d2c636f727465782d61\
  37360000000000030000000b000000c87370696e2d7461626c6500000000000300000008\
  000000d60000000000000300000000020000000200000001707363690000000000000003\
  00000023000000da61726d2c707363692d312e300061726d2c707363692d302e32006172\
  6d2c7073636900000000000300000004000000e5736d6300000000020000000200000009\
  23616464726573732d63656c6c73002373697a652d63656c6c730023616464726573732d\
  63656c6c73002373697a652d63656c6c73006465766963655f7479706500636f6d706174\
  69626c6500656e61626c652d6d6574686f6400726567006465766963655f747970650063\
  6f6d70617469626c6500656e61626c652d6d6574686f6400726567006465766963655f74\
  79706500636f6d70617469626c6500656e61626c652d6d6574686f640072656700646576\
  6963655f7479706500636f6d70617469626c6500656e61626c652d6d6574686f64007265\
  6700636f6d70617469626c65006d6574686f6400 \
  profile=Pi5 \
  ask=" ==
  "result=err"

-- `fdt-cpus-4.1`: the Pi 5 tree with 1 address cell gives 4 CPUs.
#guard replay
  "entry=discover_cpus \
  dtb=\
  d00dfeed00000354000000380000026800000028000000110000001000000000000000ec\
  000002300000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f00000002000000016370757300000000\
  00000003000000040000001b0000000100000003000000040000002a0000000000000001\
  637075403000000000000003000000040000003663707500000000030000000f00000042\
  61726d2c636f727465782d613736000000000003000000050000004d7073636900000000\
  00000003000000040000005b000000000000000200000001637075403100000000000003\
  000000040000005f63707500000000030000000f0000006b61726d2c636f727465782d61\
  373600000000000300000005000000767073636900000000000000030000000400000084\
  000001000000000200000001637075403200000000000003000000040000008863707500\
  000000030000000f0000009461726d2c636f727465782d61373600000000000300000005\
  0000009f70736369000000000000000300000004000000ad000002000000000200000001\
  63707540330000000000000300000004000000b163707500000000030000000f000000bd\
  61726d2c636f727465782d61373600000000000300000005000000c87073636900000000\
  0000000300000004000000d6000003000000000200000002000000017073636900000000\
  0000000300000023000000da61726d2c707363692d312e300061726d2c707363692d302e\
  320061726d2c7073636900000000000300000004000000e5736d63000000000200000002\
  0000000923616464726573732d63656c6c73002373697a652d63656c6c73002361646472\
  6573732d63656c6c73002373697a652d63656c6c73006465766963655f7479706500636f\
  6d70617469626c6500656e61626c652d6d6574686f6400726567006465766963655f7479\
  706500636f6d70617469626c6500656e61626c652d6d6574686f64007265670064657669\
  63655f7479706500636f6d70617469626c6500656e61626c652d6d6574686f6400726567\
  006465766963655f7479706500636f6d70617469626c6500656e61626c652d6d6574686f\
  640072656700636f6d70617469626c65006d6574686f6400 \
  profile=Pi5 \
  ask=count" ==
  "result=ok count=4"

-- `fdt-cpus-5.39`: the flag bits `0xc1000000` do not change the Pi 5 logical ID 3.
#guard replay
  "entry=logical_id \
  profile=Pi5 \
  mpidr=0xc1000300 \
  ask=id" ==
  "result=ok id=3"

-- `fdt-cpus-5.45`: `0x100000000` is no Pi 5 affinity.
#guard replay
  "entry=logical_id \
  profile=Pi5 \
  mpidr=0x100000000 \
  ask=id" ==
  "result=ok id=-"

-- `fdt-cpus-6.1`: the four timer records of the HVC profile with one CPU are accepted.
#guard replay
  "entry=validate_qemu_timers \
  dtb=\
  d00dfeed000001bd000000380000014c0000002800000011000000100000000000000071\
  000001140000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f00000002000000016370757300000000\
  00000003000000040000001b0000000200000003000000040000002a0000000000000001\
  637075403000000000000003000000040000003663707500000000030000000f00000042\
  61726d2c636f727465782d613736000000000003000000050000004d7073636900000000\
  00000003000000080000005b000000000000000000000002000000020000000170736369\
  0000000000000003000000230000005f61726d2c707363692d312e300061726d2c707363\
  692d302e320061726d2c70736369000000000003000000040000006a6876630000000002\
  000000020000000923616464726573732d63656c6c73002373697a652d63656c6c730023\
  616464726573732d63656c6c73002373697a652d63656c6c73006465766963655f747970\
  6500636f6d70617469626c6500656e61626c652d6d6574686f640072656700636f6d7061\
  7469626c65006d6574686f6400 \
  profile=QemuHvc \
  interrupts=000000010000000d00000104000000010000000e00000104000000010000000b00000104\
  000000010000000a00000104 \
  ask=" ==
  "result=ok"

-- `fdt-pi5-1.1`: the three RAM ranges and three reserved regions of the hand-over tree and
-- the availability of eight spans.
#guard replay
  "entry=discover_pi5_boot_memory \
  dtb=\
  d00dfeed000002f2000000480000025c0000002800000011000000100000000000000096\
  000002140000000000200000000000000002000000000000000000000000000000000000\
  00000001000000000000000300000004000000000000000200000003000000040000000f\
  0000000200000003000000230000001b72617370626572727970692c352d6d6f64656c2d\
  62006272636d2c62636d323731320000000000016d656d6f727940300000000000000003\
  00000007000000266d656d6f727900000000000300000030000000320000000000000000\
  000000010000000000000001000000000000000100000000000000030000000000000000\
  00100000000000020000000172657365727665642d6d656d6f7279000000000300000004\
  000000360000000200000003000000040000004500000002000000030000000000000051\
  000000016174664030000000000000030000001000000058000000000000000000000000\
  0008000000000003000000000000005c0000000200000001706f6f6c4031303030303030\
  303000000000000300000010000000630000000100000000000000000001000000000003\
  000000000000006700000002000000020000000170636965403130303031323030303000\
  0000000300000004000000700000000300000003000000040000007f0000000200000003\
  0000001c0000008b0200000000000000000000000000001b000000000000000000100000\
  0000000165746865726e6574403000000000000300000014000000920000000000000000\
  000000000000000000001000000000020000000200000002000000092361646472657373\
  2d63656c6c73002373697a652d63656c6c7300636f6d70617469626c6500646576696365\
  5f74797065007265670023616464726573732d63656c6c73002373697a652d63656c6c73\
  0072616e67657300726567006e6f2d6d617000726567007265757361626c650023616464\
  726573732d63656c6c73002373697a652d63656c6c730072616e6765730072656700 \
  dtb_address=0x200000 \
  image=0x80000+0x20000 \
  ask=ram,ram_bytes,dtb,image,reserved,is_available(0x0+0x1000),is_available(0x80000+0x20000),\
  is_available(0x200000+0x8),is_available(0x100000000+0x1000),\
  is_available(0x200000000+0x1000),is_available(0xfffff000+0x2000),\
  is_available(0x1fffff000+0x100002000),is_available(0x100010000+0x1000)" ==
  "result=ok ram=0x0+0x100000000,0x100000000+0x100000000,0x300000000+0x100000 \
  ram_bytes=0x200100000 dtb=0x200000+0x2f2 image=0x80000+0x20000 \
  reserved=0x200000+0x20000/no-map,0x0+0x80000/no-map,0x100000000+0x10000/reusable \
  is_available(0x0+0x1000)=false is_available(0x80000+0x20000)=false \
  is_available(0x200000+0x8)=false is_available(0x100000000+0x1000)=false \
  is_available(0x200000000+0x1000)=false is_available(0xfffff000+0x2000)=false \
  is_available(0x1fffff000+0x100002000)=false is_available(0x100010000+0x1000)=true"

-- `fdt-pi5-2.1`: disabled RAM and a disabled `linux,cma` add nothing.
#guard replay
  "entry=discover_pi5_boot_memory \
  dtb=\
  d00dfeed0000024800000038000001c40000002800000011000000100000000000000084\
  0000018c0000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f0000000200000003000000230000001b\
  72617370626572727970692c352d6d6f64656c2d62006272636d2c62636d323731320000\
  000000016d656d6f72794030000000000000000300000007000000266d656d6f72790000\
  000000030000001000000032000000000000000000000002000000000000000200000001\
  6d656d6f72794030000000000000000300000007000000366d656d6f7279000000000003\
  000000090000004264697361626c65640000000000000003000000100000004900000000\
  000000000000000200000000000000020000000172657365727665642d6d656d6f727900\
  00000003000000040000004d0000000200000003000000040000005c0000000200000003\
  0000000000000068000000016c696e75782c636d6100000000000003000000040000006f\
  0400000000000003000000000000007400000003000000090000007d64697361626c6564\
  000000000000000200000002000000020000000923616464726573732d63656c6c730023\
  73697a652d63656c6c7300636f6d70617469626c65006465766963655f74797065007265\
  67006465766963655f7479706500737461747573007265670023616464726573732d6365\
  6c6c73002373697a652d63656c6c730072616e6765730073697a65007265757361626c65\
  0073746174757300 \
  dtb_address=0x200000 \
  image=0x80000+0x20000 \
  ask=ram_bytes,ram,reserved,dynamic" ==
  "result=ok ram_bytes=0x200000000 ram=0x0+0x200000000 reserved=- dynamic=0"

-- `fdt-pi5-3.1`: a root `compatible` with a further entry is accepted.
#guard replay
  "entry=discover_pi5_boot_memory \
  dtb=\
  d00dfeed00000158000000380000011c000000280000001100000010000000000000003c\
  000000e40000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f00000002000000030000001f0000001b\
  5261737062657272792050692035204d6f64656c20422052657620312e31000000000003\
  000000370000002176656e646f722c6e65772d7265766973696f6e007261737062657272\
  7970692c352d6d6f64656c2d62006272636d2c62636d323731320000000000016d656d6f\
  727940300000000000000003000000070000002c6d656d6f727900000000000300000010\
  000000380000000000000000000000020000000000000002000000020000000923616464\
  726573732d63656c6c73002373697a652d63656c6c73006d6f64656c00636f6d70617469\
  626c65006465766963655f747970650072656700 \
  dtb_address=0x200000 \
  image=0x80000+0x20000 \
  ask=ram_bytes" ==
  "result=ok ram_bytes=0x200000000"

-- `fdt-pi5-4.1`: a `reusable` pool with a `size` of one cell is one dynamic reservation.
#guard replay
  "entry=discover_pi5_boot_memory \
  dtb=\
  d00dfeed000001b2000000380000014c0000002800000011000000100000000000000066\
  000001140000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f0000000200000003000000230000001b\
  72617370626572727970692c352d6d6f64656c2d62006272636d2c62636d323731320000\
  000000016d656d6f72794030000000000000000300000007000000266d656d6f72790000\
  000000030000001000000032000000000000000000000002000000000000000200000001\
  72657365727665642d6d656d6f7279000000000300000004000000360000000200000003\
  00000004000000450000000200000003000000000000005100000001706f6f6c00000000\
  000000030000000000000058000000030000000400000061040000000000000200000002\
  000000020000000923616464726573732d63656c6c73002373697a652d63656c6c730063\
  6f6d70617469626c65006465766963655f74797065007265670023616464726573732d63\
  656c6c73002373697a652d63656c6c730072616e676573007265757361626c650073697a\
  6500 \
  dtb_address=0x200000 \
  image=0x80000+0x20000 \
  ask=ram_bytes,reserved,dynamic" ==
  "result=ok ram_bytes=0x200000000 reserved=- dynamic=1"

-- `fdt-pi5-boundaries-1.5`: a root `compatible` entry of the byte `0xff` is rejected.
#guard replay
  "entry=discover_pi5_boot_memory \
  dtb=\
  d00dfeed0000011600000038000000e00000002800000011000000100000000000000036\
  000000a80000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f0000000200000003000000250000001b\
  72617370626572727970692c352d6d6f64656c2d62006272636d2c62636d3237313200ff\
  00000000000000016d656d6f72794030000000000000000300000007000000266d656d6f\
  727900000000000300000010000000320000000000000000000000020000000000000002\
  000000020000000923616464726573732d63656c6c73002373697a652d63656c6c730063\
  6f6d70617469626c65006465766963655f747970650072656700 \
  dtb_address=0x200000 \
  image=0x80000+0x20000 \
  ask=" ==
  "result=err"

-- `fdt-pi5-boundaries-2.1`: a root with 1 and 1 cells fails with `UnsupportedCells`.
#guard replay
  "entry=discover_pi5_boot_memory \
  dtb=\
  d00dfeed000000be00000038000000980000002800000011000000100000000000000026\
  000000600000000000000000000000000000000000000001000000000000000300000004\
  000000000000000100000003000000040000000f0000000100000003000000230000001b\
  72617370626572727970692c352d6d6f64656c2d62006272636d2c62636d323731320000\
  000000020000000923616464726573732d63656c6c73002373697a652d63656c6c730063\
  6f6d70617469626c6500 \
  dtb_address=0x200000 \
  image=0x80000+0x20000 \
  ask=error" ==
  "result=err error=Error::UnsupportedCells"

-- `fdt-pi5-boundaries-3.9`: `is_available` of an empty span and of one that leaves 64 bits fails.
#guard replay
  "entry=discover_pi5_boot_memory \
  dtb=\
  d00dfeed0000011200000038000000dc0000002800000011000000100000000000000036\
  000000a40000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f0000000200000003000000230000001b\
  72617370626572727970692c352d6d6f64656c2d62006272636d2c62636d323731320000\
  000000016d656d6f72794030000000000000000300000007000000266d656d6f72790000\
  000000030000001000000032000000000000000000000000004000000000000200000002\
  0000000923616464726573732d63656c6c73002373697a652d63656c6c7300636f6d7061\
  7469626c65006465766963655f747970650072656700 \
  dtb_address=0x200000 \
  image=0x80000+0x20000 \
  ask=is_available(0x0+0x0),is_available(0xffffffffffffffff+0x1)" ==
  "result=ok is_available(0x0+0x0)=Error::EmptyRegion \
  is_available(0xffffffffffffffff+0x1)=Error::Overflow"

-- `fdt-pi5-boundaries-4.1`: RAM ranges that overlap fail with `Overlap`.
#guard replay
  "entry=discover_pi5_boot_memory \
  dtb=\
  d00dfeed0000012200000038000000ec0000002800000011000000100000000000000036\
  000000b40000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f0000000200000003000000230000001b\
  72617370626572727970692c352d6d6f64656c2d62006272636d2c62636d323731320000\
  000000016d656d6f72794030000000000000000300000007000000266d656d6f72790000\
  000000030000002000000032000000000000000000000002000000000000000100000000\
  000000010000000000000002000000020000000923616464726573732d63656c6c730023\
  73697a652d63656c6c7300636f6d70617469626c65006465766963655f74797065007265\
  6700 \
  dtb_address=0x200000 \
  image=0x80000+0x20000 \
  ask=error" ==
  "result=err error=Error::Overlap"

-- `fdt-pi5-boundaries-5.1`: one `reg` of 33 RAM ranges fails with `LimitExceeded`.
#guard replay
  "entry=discover_pi5_boot_memory \
  dtb=\
  d00dfeed0000031200000038000002dc0000002800000011000000100000000000000036\
  000002a40000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f0000000200000003000000230000001b\
  72617370626572727970692c352d6d6f64656c2d62006272636d2c62636d323731320000\
  000000016d656d6f72794030000000000000000300000007000000266d656d6f72790000\
  000000030000021000000032000000000000000000000001000000000000000100000000\
  000000010000000000000002000000000000000100000000000000030000000000000001\
  000000000000000400000000000000010000000000000005000000000000000100000000\
  000000060000000000000001000000000000000700000000000000010000000000000008\
  000000000000000100000000000000090000000000000001000000000000000a00000000\
  00000001000000000000000b0000000000000001000000000000000c0000000000000001\
  000000000000000d0000000000000001000000000000000e000000000000000100000000\
  0000000f0000000000000001000000000000001000000000000000010000000000000011\
  000000000000000100000000000000120000000000000001000000000000001300000000\
  000000010000000000000014000000000000000100000000000000150000000000000001\
  000000000000001600000000000000010000000000000017000000000000000100000000\
  00000018000000000000000100000000000000190000000000000001000000000000001a\
  0000000000000001000000000000001b0000000000000001000000000000001c00000000\
  00000001000000000000001d0000000000000001000000000000001e0000000000000001\
  000000000000001f00000000000000010000000000000020000000000000000100000000\
  00000002000000020000000923616464726573732d63656c6c73002373697a652d63656c\
  6c7300636f6d70617469626c65006465766963655f747970650072656700 \
  dtb_address=0x200000 \
  image=0x80000+0x20000 \
  ask=error" ==
  "result=err error=Error::LimitExceeded"

-- `fdt-pi5-selection-1.3`: above the tree, the lowest aligned start is the page after the tree,
-- `0x201000`, and `is_available` accepts the span.
#guard replay
  "entry=find_available \
  dtb=\
  d00dfeed00000152000000680000011c0000002800000011000000100000000000000036\
  000000b40000000000004000000000000000100100000000000000000000000000004000\
  000000010000000000000000000030000000000000000000000000000000000000000001\
  000000000000000300000004000000000000000200000003000000040000000f00000002\
  00000003000000230000001b72617370626572727970692c352d6d6f64656c2d62006272\
  636d2c62636d323731320000000000016d656d6f72794030000000000000000300000007\
  000000266d656d6f72790000000000030000002000000032000000000000000000000000\
  004000000000000100000000000000000001000000000002000000020000000923616464\
  726573732d63656c6c73002373697a652d63656c6c7300636f6d70617469626c65006465\
  766963655f747970650072656700 \
  dtb_address=0x200000 \
  image=0x80000+0x20000 \
  size=0x1000 \
  alignment=0x1000 \
  minimum=0x200000 \
  limit=0x400000 \
  ask=span,is_available(0x201000+0x1000)" ==
  "result=ok span=0x201000+0x1000 is_available(0x201000+0x1000)=true"

-- `fdt-pi5-selection-2.6`: the minimum `0xfffffffffffffffe` aligned up to `0x1000` fails
-- with `Overflow`.
#guard replay
  "entry=find_available \
  dtb=\
  d00dfeed0000011200000038000000dc0000002800000011000000100000000000000036\
  000000a40000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f0000000200000003000000230000001b\
  72617370626572727970692c352d6d6f64656c2d62006272636d2c62636d323731320000\
  000000016d656d6f72794030000000000000000300000007000000266d656d6f72790000\
  000000030000001000000032000000000000000000000002000000000000000200000002\
  0000000923616464726573732d63656c6c73002373697a652d63656c6c7300636f6d7061\
  7469626c65006465766963655f747970650072656700 \
  dtb_address=0x200000 \
  image=0x80000+0x20000 \
  size=0x1000 \
  alignment=0x1000 \
  minimum=0xfffffffffffffffe \
  limit=0xffffffffffffffff \
  ask=span" ==
  "result=err error=Error::Overflow"

-- `fdt-pi5-selection-3.1`: 128 `reusable` regions of one page from `0x400000` are accepted, and the
-- selection starts after them, at `0x480000`.
#guard replay
  "entry=find_available \
  dtb=\
  d00dfeed000023f80000003800001d2000000028000000110000001000000000000006d8\
  00001ce80000000000000000000000000000000000000001000000000000000300000004\
  000000000000000200000003000000040000000f0000000200000003000000230000001b\
  72617370626572727970692c352d6d6f64656c2d62006272636d2c62636d323731320000\
  000000016d656d6f72794030000000000000000300000007000000266d656d6f72790000\
  000000030000001000000032000000000000000000000002000000000000000200000001\
  72657365727665642d6d656d6f7279000000000300000004000000360000000200000003\
  00000004000000450000000200000003000000000000005100000001706f6f6c00000000\
  000000030000001000000058000000000040000000000000000010000000000300000000\
  0000005c0000000200000001706f6f6c0000000000000003000000100000006500000000\
  0040100000000000000010000000000300000000000000690000000200000001706f6f6c\
  000000000000000300000010000000720000000000402000000000000000100000000003\
  00000000000000760000000200000001706f6f6c0000000000000003000000100000007f\
  000000000040300000000000000010000000000300000000000000830000000200000001\
  706f6f6c0000000000000003000000100000008c00000000004040000000000000001000\
  0000000300000000000000900000000200000001706f6f6c000000000000000300000010\
  000000990000000000405000000000000000100000000003000000000000009d00000002\
  00000001706f6f6c000000000000000300000010000000a6000000000040600000000000\
  000010000000000300000000000000aa0000000200000001706f6f6c0000000000000003\
  00000010000000b3000000000040700000000000000010000000000300000000000000b7\
  0000000200000001706f6f6c000000000000000300000010000000c00000000000408000\
  00000000000010000000000300000000000000c40000000200000001706f6f6c00000000\
  0000000300000010000000cd000000000040900000000000000010000000000300000000\
  000000d10000000200000001706f6f6c000000000000000300000010000000da00000000\
  0040a00000000000000010000000000300000000000000de0000000200000001706f6f6c\
  000000000000000300000010000000e7000000000040b000000000000000100000000003\
  00000000000000eb0000000200000001706f6f6c000000000000000300000010000000f4\
  000000000040c00000000000000010000000000300000000000000f80000000200000001\
  706f6f6c00000000000000030000001000000101000000000040d0000000000000001000\
  0000000300000000000001050000000200000001706f6f6c000000000000000300000010\
  0000010e000000000040e000000000000000100000000003000000000000011200000002\
  00000001706f6f6c0000000000000003000000100000011b000000000040f00000000000\
  0000100000000003000000000000011f0000000200000001706f6f6c0000000000000003\
  00000010000001280000000000410000000000000000100000000003000000000000012c\
  0000000200000001706f6f6c000000000000000300000010000001350000000000411000\
  00000000000010000000000300000000000001390000000200000001706f6f6c00000000\
  000000030000001000000142000000000041200000000000000010000000000300000000\
  000001460000000200000001706f6f6c0000000000000003000000100000014f00000000\
  0041300000000000000010000000000300000000000001530000000200000001706f6f6c\
  0000000000000003000000100000015c0000000000414000000000000000100000000003\
  00000000000001600000000200000001706f6f6c00000000000000030000001000000169\
  0000000000415000000000000000100000000003000000000000016d0000000200000001\
  706f6f6c0000000000000003000000100000017600000000004160000000000000001000\
  00000003000000000000017a0000000200000001706f6f6c000000000000000300000010\
  000001830000000000417000000000000000100000000003000000000000018700000002\
  00000001706f6f6c00000000000000030000001000000190000000000041800000000000\
  000010000000000300000000000001940000000200000001706f6f6c0000000000000003\
  000000100000019d000000000041900000000000000010000000000300000000000001a1\
  0000000200000001706f6f6c000000000000000300000010000001aa000000000041a000\
  00000000000010000000000300000000000001ae0000000200000001706f6f6c00000000\
  0000000300000010000001b7000000000041b00000000000000010000000000300000000\
  000001bb0000000200000001706f6f6c000000000000000300000010000001c400000000\
  0041c00000000000000010000000000300000000000001c80000000200000001706f6f6c\
  000000000000000300000010000001d1000000000041d000000000000000100000000003\
  00000000000001d50000000200000001706f6f6c000000000000000300000010000001de\
  000000000041e00000000000000010000000000300000000000001e20000000200000001\
  706f6f6c000000000000000300000010000001eb000000000041f0000000000000001000\
  0000000300000000000001ef0000000200000001706f6f6c000000000000000300000010\
  000001f8000000000042000000000000000010000000000300000000000001fc00000002\
  00000001706f6f6c00000000000000030000001000000205000000000042100000000000\
  000010000000000300000000000002090000000200000001706f6f6c0000000000000003\
  000000100000021200000000004220000000000000001000000000030000000000000216\
  0000000200000001706f6f6c0000000000000003000000100000021f0000000000423000\
  00000000000010000000000300000000000002230000000200000001706f6f6c00000000\
  00000003000000100000022c000000000042400000000000000010000000000300000000\
  000002300000000200000001706f6f6c0000000000000003000000100000023900000000\
  00425000000000000000100000000003000000000000023d0000000200000001706f6f6c\
  000000000000000300000010000002460000000000426000000000000000100000000003\
  000000000000024a0000000200000001706f6f6c00000000000000030000001000000253\
  000000000042700000000000000010000000000300000000000002570000000200000001\
  706f6f6c0000000000000003000000100000026000000000004280000000000000001000\
  0000000300000000000002640000000200000001706f6f6c000000000000000300000010\
  0000026d0000000000429000000000000000100000000003000000000000027100000002\
  00000001706f6f6c0000000000000003000000100000027a000000000042a00000000000\
  0000100000000003000000000000027e0000000200000001706f6f6c0000000000000003\
  0000001000000287000000000042b000000000000000100000000003000000000000028b\
  0000000200000001706f6f6c00000000000000030000001000000294000000000042c000\
  00000000000010000000000300000000000002980000000200000001706f6f6c00000000\
  0000000300000010000002a1000000000042d00000000000000010000000000300000000\
  000002a50000000200000001706f6f6c000000000000000300000010000002ae00000000\
  0042e00000000000000010000000000300000000000002b20000000200000001706f6f6c\
  000000000000000300000010000002bb000000000042f000000000000000100000000003\
  00000000000002bf0000000200000001706f6f6c000000000000000300000010000002c8\
  000000000043000000000000000010000000000300000000000002cc0000000200000001\
  706f6f6c000000000000000300000010000002d500000000004310000000000000001000\
  0000000300000000000002d90000000200000001706f6f6c000000000000000300000010\
  000002e2000000000043200000000000000010000000000300000000000002e600000002\
  00000001706f6f6c000000000000000300000010000002ef000000000043300000000000\
  000010000000000300000000000002f30000000200000001706f6f6c0000000000000003\
  00000010000002fc00000000004340000000000000001000000000030000000000000300\
  0000000200000001706f6f6c000000000000000300000010000003090000000000435000\
  000000000000100000000003000000000000030d0000000200000001706f6f6c00000000\
  000000030000001000000316000000000043600000000000000010000000000300000000\
  0000031a0000000200000001706f6f6c0000000000000003000000100000032300000000\
  0043700000000000000010000000000300000000000003270000000200000001706f6f6c\
  000000000000000300000010000003300000000000438000000000000000100000000003\
  00000000000003340000000200000001706f6f6c0000000000000003000000100000033d\
  000000000043900000000000000010000000000300000000000003410000000200000001\
  706f6f6c0000000000000003000000100000034a000000000043a0000000000000001000\
  00000003000000000000034e0000000200000001706f6f6c000000000000000300000010\
  00000357000000000043b000000000000000100000000003000000000000035b00000002\
  00000001706f6f6c00000000000000030000001000000364000000000043c00000000000\
  000010000000000300000000000003680000000200000001706f6f6c0000000000000003\
  0000001000000371000000000043d0000000000000001000000000030000000000000375\
  0000000200000001706f6f6c0000000000000003000000100000037e000000000043e000\
  00000000000010000000000300000000000003820000000200000001706f6f6c00000000\
  00000003000000100000038b000000000043f00000000000000010000000000300000000\
  0000038f0000000200000001706f6f6c0000000000000003000000100000039800000000\
  00440000000000000000100000000003000000000000039c0000000200000001706f6f6c\
  000000000000000300000010000003a50000000000441000000000000000100000000003\
  00000000000003a90000000200000001706f6f6c000000000000000300000010000003b2\
  000000000044200000000000000010000000000300000000000003b60000000200000001\
  706f6f6c000000000000000300000010000003bf00000000004430000000000000001000\
  0000000300000000000003c30000000200000001706f6f6c000000000000000300000010\
  000003cc000000000044400000000000000010000000000300000000000003d000000002\
  00000001706f6f6c000000000000000300000010000003d9000000000044500000000000\
  000010000000000300000000000003dd0000000200000001706f6f6c0000000000000003\
  00000010000003e6000000000044600000000000000010000000000300000000000003ea\
  0000000200000001706f6f6c000000000000000300000010000003f30000000000447000\
  00000000000010000000000300000000000003f70000000200000001706f6f6c00000000\
  000000030000001000000400000000000044800000000000000010000000000300000000\
  000004040000000200000001706f6f6c0000000000000003000000100000040d00000000\
  0044900000000000000010000000000300000000000004110000000200000001706f6f6c\
  0000000000000003000000100000041a000000000044a000000000000000100000000003\
  000000000000041e0000000200000001706f6f6c00000000000000030000001000000427\
  000000000044b000000000000000100000000003000000000000042b0000000200000001\
  706f6f6c00000000000000030000001000000434000000000044c0000000000000001000\
  0000000300000000000004380000000200000001706f6f6c000000000000000300000010\
  00000441000000000044d000000000000000100000000003000000000000044500000002\
  00000001706f6f6c0000000000000003000000100000044e000000000044e00000000000\
  000010000000000300000000000004520000000200000001706f6f6c0000000000000003\
  000000100000045b000000000044f000000000000000100000000003000000000000045f\
  0000000200000001706f6f6c000000000000000300000010000004680000000000450000\
  000000000000100000000003000000000000046c0000000200000001706f6f6c00000000\
  000000030000001000000475000000000045100000000000000010000000000300000000\
  000004790000000200000001706f6f6c0000000000000003000000100000048200000000\
  0045200000000000000010000000000300000000000004860000000200000001706f6f6c\
  0000000000000003000000100000048f0000000000453000000000000000100000000003\
  00000000000004930000000200000001706f6f6c0000000000000003000000100000049c\
  000000000045400000000000000010000000000300000000000004a00000000200000001\
  706f6f6c000000000000000300000010000004a900000000004550000000000000001000\
  0000000300000000000004ad0000000200000001706f6f6c000000000000000300000010\
  000004b6000000000045600000000000000010000000000300000000000004ba00000002\
  00000001706f6f6c000000000000000300000010000004c3000000000045700000000000\
  000010000000000300000000000004c70000000200000001706f6f6c0000000000000003\
  00000010000004d0000000000045800000000000000010000000000300000000000004d4\
  0000000200000001706f6f6c000000000000000300000010000004dd0000000000459000\
  00000000000010000000000300000000000004e10000000200000001706f6f6c00000000\
  0000000300000010000004ea000000000045a00000000000000010000000000300000000\
  000004ee0000000200000001706f6f6c000000000000000300000010000004f700000000\
  0045b00000000000000010000000000300000000000004fb0000000200000001706f6f6c\
  00000000000000030000001000000504000000000045c000000000000000100000000003\
  00000000000005080000000200000001706f6f6c00000000000000030000001000000511\
  000000000045d00000000000000010000000000300000000000005150000000200000001\
  706f6f6c0000000000000003000000100000051e000000000045e0000000000000001000\
  0000000300000000000005220000000200000001706f6f6c000000000000000300000010\
  0000052b000000000045f000000000000000100000000003000000000000052f00000002\
  00000001706f6f6c00000000000000030000001000000538000000000046000000000000\
  0000100000000003000000000000053c0000000200000001706f6f6c0000000000000003\
  000000100000054500000000004610000000000000001000000000030000000000000549\
  0000000200000001706f6f6c000000000000000300000010000005520000000000462000\
  00000000000010000000000300000000000005560000000200000001706f6f6c00000000\
  00000003000000100000055f000000000046300000000000000010000000000300000000\
  000005630000000200000001706f6f6c0000000000000003000000100000056c00000000\
  0046400000000000000010000000000300000000000005700000000200000001706f6f6c\
  000000000000000300000010000005790000000000465000000000000000100000000003\
  000000000000057d0000000200000001706f6f6c00000000000000030000001000000586\
  0000000000466000000000000000100000000003000000000000058a0000000200000001\
  706f6f6c0000000000000003000000100000059300000000004670000000000000001000\
  0000000300000000000005970000000200000001706f6f6c000000000000000300000010\
  000005a0000000000046800000000000000010000000000300000000000005a400000002\
  00000001706f6f6c000000000000000300000010000005ad000000000046900000000000\
  000010000000000300000000000005b10000000200000001706f6f6c0000000000000003\
  00000010000005ba000000000046a00000000000000010000000000300000000000005be\
  0000000200000001706f6f6c000000000000000300000010000005c7000000000046b000\
  00000000000010000000000300000000000005cb0000000200000001706f6f6c00000000\
  0000000300000010000005d4000000000046c00000000000000010000000000300000000\
  000005d80000000200000001706f6f6c000000000000000300000010000005e100000000\
  0046d00000000000000010000000000300000000000005e50000000200000001706f6f6c\
  000000000000000300000010000005ee000000000046e000000000000000100000000003\
  00000000000005f20000000200000001706f6f6c000000000000000300000010000005fb\
  000000000046f00000000000000010000000000300000000000005ff0000000200000001\
  706f6f6c0000000000000003000000100000060800000000004700000000000000001000\
  00000003000000000000060c0000000200000001706f6f6c000000000000000300000010\
  000006150000000000471000000000000000100000000003000000000000061900000002\
  00000001706f6f6c00000000000000030000001000000622000000000047200000000000\
  000010000000000300000000000006260000000200000001706f6f6c0000000000000003\
  000000100000062f00000000004730000000000000001000000000030000000000000633\
  0000000200000001706f6f6c0000000000000003000000100000063c0000000000474000\
  00000000000010000000000300000000000006400000000200000001706f6f6c00000000\
  000000030000001000000649000000000047500000000000000010000000000300000000\
  0000064d0000000200000001706f6f6c0000000000000003000000100000065600000000\
  00476000000000000000100000000003000000000000065a0000000200000001706f6f6c\
  000000000000000300000010000006630000000000477000000000000000100000000003\
  00000000000006670000000200000001706f6f6c00000000000000030000001000000670\
  000000000047800000000000000010000000000300000000000006740000000200000001\
  706f6f6c0000000000000003000000100000067d00000000004790000000000000001000\
  0000000300000000000006810000000200000001706f6f6c000000000000000300000010\
  0000068a000000000047a000000000000000100000000003000000000000068e00000002\
  00000001706f6f6c00000000000000030000001000000697000000000047b00000000000\
  0000100000000003000000000000069b0000000200000001706f6f6c0000000000000003\
  00000010000006a4000000000047c00000000000000010000000000300000000000006a8\
  0000000200000001706f6f6c000000000000000300000010000006b1000000000047d000\
  00000000000010000000000300000000000006b50000000200000001706f6f6c00000000\
  0000000300000010000006be000000000047e00000000000000010000000000300000000\
  000006c20000000200000001706f6f6c000000000000000300000010000006cb00000000\
  0047f00000000000000010000000000300000000000006cf000000020000000200000002\
  0000000923616464726573732d63656c6c73002373697a652d63656c6c7300636f6d7061\
  7469626c65006465766963655f74797065007265670023616464726573732d63656c6c73\
  002373697a652d63656c6c730072616e67657300726567007265757361626c6500726567\
  007265757361626c6500726567007265757361626c6500726567007265757361626c6500\
  726567007265757361626c6500726567007265757361626c650072656700726575736162\
  6c6500726567007265757361626c6500726567007265757361626c650072656700726575\
  7361626c6500726567007265757361626c6500726567007265757361626c650072656700\
  7265757361626c6500726567007265757361626c6500726567007265757361626c650072\
  6567007265757361626c6500726567007265757361626c6500726567007265757361626c\
  6500726567007265757361626c6500726567007265757361626c65007265670072657573\
  61626c6500726567007265757361626c6500726567007265757361626c65007265670072\
  65757361626c6500726567007265757361626c6500726567007265757361626c65007265\
  67007265757361626c6500726567007265757361626c6500726567007265757361626c65\
  00726567007265757361626c6500726567007265757361626c6500726567007265757361\
  626c6500726567007265757361626c6500726567007265757361626c6500726567007265\
  757361626c6500726567007265757361626c6500726567007265757361626c6500726567\
  007265757361626c6500726567007265757361626c6500726567007265757361626c6500\
  726567007265757361626c6500726567007265757361626c650072656700726575736162\
  6c6500726567007265757361626c6500726567007265757361626c650072656700726575\
  7361626c6500726567007265757361626c6500726567007265757361626c650072656700\
  7265757361626c6500726567007265757361626c6500726567007265757361626c650072\
  6567007265757361626c6500726567007265757361626c6500726567007265757361626c\
  6500726567007265757361626c6500726567007265757361626c65007265670072657573\
  61626c6500726567007265757361626c6500726567007265757361626c65007265670072\
  65757361626c6500726567007265757361626c6500726567007265757361626c65007265\
  67007265757361626c6500726567007265757361626c6500726567007265757361626c65\
  00726567007265757361626c6500726567007265757361626c6500726567007265757361\
  626c6500726567007265757361626c6500726567007265757361626c6500726567007265\
  757361626c6500726567007265757361626c6500726567007265757361626c6500726567\
  007265757361626c6500726567007265757361626c6500726567007265757361626c6500\
  726567007265757361626c6500726567007265757361626c650072656700726575736162\
  6c6500726567007265757361626c6500726567007265757361626c650072656700726575\
  7361626c6500726567007265757361626c6500726567007265757361626c650072656700\
  7265757361626c6500726567007265757361626c6500726567007265757361626c650072\
  6567007265757361626c6500726567007265757361626c6500726567007265757361626c\
  6500726567007265757361626c6500726567007265757361626c65007265670072657573\
  61626c6500726567007265757361626c6500726567007265757361626c65007265670072\
  65757361626c6500726567007265757361626c6500726567007265757361626c65007265\
  67007265757361626c6500726567007265757361626c6500726567007265757361626c65\
  00726567007265757361626c6500726567007265757361626c6500726567007265757361\
  626c6500726567007265757361626c6500726567007265757361626c6500726567007265\
  757361626c6500726567007265757361626c6500726567007265757361626c6500726567\
  007265757361626c6500726567007265757361626c6500726567007265757361626c6500\
  726567007265757361626c6500726567007265757361626c650072656700726575736162\
  6c6500726567007265757361626c6500726567007265757361626c650072656700726575\
  7361626c6500726567007265757361626c6500726567007265757361626c650072656700\
  7265757361626c6500726567007265757361626c6500726567007265757361626c650072\
  6567007265757361626c6500726567007265757361626c6500726567007265757361626c\
  6500726567007265757361626c6500726567007265757361626c6500 \
  dtb_address=0x200000 \
  image=0x80000+0x20000 \
  size=0x8000 \
  alignment=0x1000 \
  minimum=0x400000 \
  limit=0x10000000 \
  ask=span,is_available(0x480000+0x8000)" ==
  "result=ok span=0x480000+0x8000 is_available(0x480000+0x8000)=true"


-- `fdt-pi5-platform-1.1`: the boot memory map of the 8 GB model through `from_pi5` keeps its
-- 3 banks, excludes the pages of the image and of the tree and manages no high page.
#guard replay
  "entry=from_pi5 \
  dtb=\
  d00dfeed00000142000000480000010c0000002800000011000000100000000000000036\
  000000c40000000000000000000000000008000000000000000000000000000000000000\
  00000001000000000000000300000004000000000000000200000003000000040000000f\
  0000000200000003000000230000001b72617370626572727970692c352d6d6f64656c2d\
  62006272636d2c62636d323731320000000000016d656d6f727940300000000000000003\
  00000007000000266d656d6f727900000000000300000030000000320000000000000000\
  000000003fc00000000000004000000000000000c0000000000000010000000000000001\
  0000000000000002000000020000000923616464726573732d63656c6c73002373697a65\
  2d63656c6c7300636f6d70617469626c65006465766963655f747970650072656700 \
  dtb_address=0x200000 \
  image=0x80000+0x20000 \
  window=0x0+0x8000000 \
  more=- \
  ask=ram,boot,permits_backing(0x0+0x1000),permits_backing(0x80000+0x1000),\
  permits_backing(0x200000+0x1000),permits_backing(0x400000+0x1000),\
  is_available(0x3fc00000+0x1000),is_available(0x100000000+0x1000),\
  permits_backing(0x100000000+0x1000)" ==
  "result=ok ram=0x0+0x3fc00000,0x40000000+0xc0000000,0x100000000+0x100000000 \
  boot=0x80000+0x20000,0x200000+0x1000 permits_backing(0x0+0x1000)=false \
  permits_backing(0x80000+0x1000)=false permits_backing(0x200000+0x1000)=false \
  permits_backing(0x400000+0x1000)=true is_available(0x3fc00000+0x1000)=false \
  is_available(0x100000000+0x1000)=true permits_backing(0x100000000+0x1000)=false"

-- `fdt-pi5-platform-2.1`: the discovery accepts a reservation entry on the tree, and `from_pi5`
-- fails with `PlanError::Overlap`.
#guard replay
  "entry=from_pi5 \
  dtb=\
  d00dfeed0000012200000048000000ec0000002800000011000000100000000000000036\
  000000a40000000000200000000000000002000000000000000000000000000000000000\
  00000001000000000000000300000004000000000000000200000003000000040000000f\
  0000000200000003000000230000001b72617370626572727970692c352d6d6f64656c2d\
  62006272636d2c62636d323731320000000000016d656d6f727940300000000000000003\
  00000007000000266d656d6f727900000000000300000010000000320000000000000000\
  000000020000000000000002000000020000000923616464726573732d63656c6c730023\
  73697a652d63656c6c7300636f6d70617469626c65006465766963655f74797065007265\
  6700 \
  dtb_address=0x200000 \
  image=0x80000+0x20000 \
  window=0x0+0x8000000 \
  more=- \
  ask=error" ==
  "result=err error=PlanError::Overlap"

-- `platform-1.1`: banks of the 8 GB shape keep their hole and their high RAM, and the pages of
-- the boot storage and of the firmware reservations are excluded.
#guard replay
  "entry=MemoryPlan::new \
  window=0x0+0x8000000 \
  ram=0x0+0x3fc00000,0x40000000+0xc0000000,0x100000000+0x100000000 \
  boot=0x80000+0x38000,0x200000+0x13ad4 \
  firmware=0x0+0x80000/no-map,0x3fd231e0+0x3e/no-map \
  ask=boot,firmware,is_available(0x213000+0x1000),permits_backing(0x213000+0x1000),\
  is_available(0x3fc00000+0x1000),permits_backing(0x3fc00000+0x1000),\
  is_available(0x80000+0x1000),permits_backing(0x80000+0x1000),\
  is_available(0x100000000+0x1000),permits_backing(0x100000000+0x1000),\
  permits_backing(0x214000+0x1000)" ==
  "result=ok boot=0x80000+0x38000,0x200000+0x14000 firmware=0x0+0x80000,0x3fd23000+0x1000 \
  is_available(0x213000+0x1000)=false permits_backing(0x213000+0x1000)=false \
  is_available(0x3fc00000+0x1000)=false permits_backing(0x3fc00000+0x1000)=false \
  is_available(0x80000+0x1000)=false permits_backing(0x80000+0x1000)=false \
  is_available(0x100000000+0x1000)=true permits_backing(0x100000000+0x1000)=false \
  permits_backing(0x214000+0x1000)=true"

-- `platform-2.1`: the managed window, the reservations by whole pages and the backing of the
-- two ranges that the page allocator of the test allocates.
#guard replay
  "entry=MemoryPlan::new \
  window=0x100000+0x5000 \
  ram=0x0+0x8000000 \
  boot=0x80000+0x38000 \
  firmware=0x101fff+0x2/no-map \
  ask=managed,reservations,permits_backing(0x100000+0x1000),permits_backing(0x103000+0x2000)" ==
  "result=ok managed=0x100000+0x5000 reservations=0x80000+0x38000,0x101000+0x2000 \
  permits_backing(0x100000+0x1000)=true permits_backing(0x103000+0x2000)=true"

-- `platform-3.1`: a QEMU prefix of boot storage is reserved, and RAM above 4 GiB stays described.
#guard replay
  "entry=MemoryPlan::new \
  window=0x40000000+0x8000000 \
  ram=0x40000000+0x100100000 \
  boot=0x40000000+0x300000 \
  firmware=- \
  ask=permits_backing(0x40000000+0x1000),permits_backing(0x40300000+0x1000),\
  is_available(0x100000000+0x1000),permits_backing(0x48000000+0x1000)" ==
  "result=ok permits_backing(0x40000000+0x1000)=false permits_backing(0x40300000+0x1000)=true \
  is_available(0x100000000+0x1000)=true permits_backing(0x48000000+0x1000)=false"

-- `platform-4.5`: a window of 128 MiB and one page fails with `ArenaTooLarge`.
#guard replay
  "entry=MemoryPlan::new \
  window=0x0+0x8001000 \
  ram=0x0+0x8000000 \
  boot=0x80000+0x38000 \
  firmware=- \
  ask=error" ==
  "result=err error=PlanError::ArenaTooLarge"

-- `platform-5.4`: banks that hold no page of the image fail with `OutsideRam`.
#guard replay
  "entry=MemoryPlan::new \
  window=0x0+0x8000000 \
  ram=0x0+0x1000,0x2000+0x1000 \
  boot=0x80000+0x38000 \
  firmware=- \
  ask=error" ==
  "result=err error=PlanError::OutsideRam"

-- `platform-6.1`: no range is held across two adjacent banks or across a hole.
#guard replay
  "entry=MemoryPlan::new \
  window=0x0+0x200000 \
  ram=0x0+0x200000,0x200000+0x200000,0x800000+0x100000 \
  boot=0x80000+0x38000 \
  firmware=- \
  ask=contains_ram(0x1ff000+0x2000),is_available(0x3ff000+0x402000)" ==
  "result=ok contains_ram(0x1ff000+0x2000)=false is_available(0x3ff000+0x402000)=false"

-- `platform-7.5`: boot storage whose pages end beyond 64 bits fails with `Overflow`.
#guard replay
  "entry=MemoryPlan::new \
  window=0x0+0x8000000 \
  ram=0x0+0x8000000 \
  boot=0x80000+0x38000,0xfffffffffffffffe+0x1 \
  firmware=- \
  ask=error" ==
  "result=err error=PlanError::Overflow"

-- `platform-8.1`: a firmware reservation on a page of boot storage fails with `Overlap`,
-- although they share no byte.
#guard replay
  "entry=MemoryPlan::new \
  window=0x0+0x8000000 \
  ram=0x0+0x8000000 \
  boot=0x80001+0x1 \
  firmware=0x80fff+0x1/no-map \
  ask=error" ==
  "result=err error=PlanError::Overlap"

-- `platform-9.1`: overlapping and `reusable` firmware reservations stay excluded by whole pages.
#guard replay
  "entry=MemoryPlan::new \
  window=0x0+0x8000000 \
  ram=0x0+0x8000000 \
  boot=0x80000+0x38000,0x200000+0x13ad4 \
  firmware=0x400001+0x1/reusable,0x400fff+0x2/no-map \
  ask=is_available(0x400000+0x2000),permits_backing(0x402000+0x1000)" ==
  "result=ok is_available(0x400000+0x2000)=false permits_backing(0x402000+0x1000)=true"

-- `platform-10.5`: three spans of boot storage that are all the image fail with `Overlap`,
-- where the prototype gave `Capacity`.
#guard replay
  "entry=MemoryPlan::new \
  window=0x0+0x8000000 \
  ram=0x0+0x8000000 \
  boot=0x80000+0x38000,0x80000+0x38000,0x80000+0x38000 \
  firmware=- \
  ask=error" ==
  "result=err error=PlanError::Overlap"

-- `platform-11.1`: unsorted banks of the 8 GB model: the managed bytes and the bytes of the
-- usable ranges, the managed bytes less the pages of the reservations.
#guard replay
  "entry=all_ram \
  ram=0x100000000+0x100000000,0x0+0x3fc00000,0x40000000+0xc0000000 \
  boot=0x80000+0x38000,0x200000+0x13ad4 \
  firmware=0x0+0x80000/no-map,0x40002001+0x1000/no-map,0x40003000+0x1/no-map \
  ask=managed_bytes,managed,permits_backing(0x1fffff000+0x1000),\
  permits_backing(0xfffff000+0x2000),available_bytes" ==
  "result=ok managed_bytes=0x1ffc00000 managed=0x0+0x3fc00000,0x40000000+0xc0000000,\
  0x100000000+0x100000000 permits_backing(0x1fffff000+0x1000)=true \
  permits_backing(0xfffff000+0x2000)=false available_bytes=0x1ffb32000"

-- `platform-12.1`: the partial pages of a bank are not managed.
#guard replay
  "entry=all_ram \
  ram=0x1+0x5000,0x10001+0x8 \
  boot=0x1000+0x1000 \
  firmware=- \
  ask=managed,available" ==
  "result=ok managed=0x1000+0x4000 available=0x2000+0x3000"

-- `platform-13.15`: page 14, past the reservations of pages 5 to 13, lies in one usable range.
#guard replay
  "entry=all_ram \
  ram=0x0+0x18000,0x20000+0x18000 \
  boot=0x0+0x1000 \
  firmware=0x9000+0x5000/no-map,0x5000+0x7000/no-map,0x16000+0xc000/no-map,0x28001+0x1/no-map \
  ask=available_count(0xe000+0x1000)" ==
  "result=ok available_count(0xe000+0x1000)=1"

-- `platform-13.41`: page 40, one byte of which is reserved, lies in no usable range.
#guard replay
  "entry=all_ram \
  ram=0x0+0x18000,0x20000+0x18000 \
  boot=0x0+0x1000 \
  firmware=0x9000+0x5000/no-map,0x5000+0x7000/no-map,0x16000+0xc000/no-map,0x28001+0x1/no-map \
  ask=available_count(0x28000+0x1000)" ==
  "result=ok available_count(0x28000+0x1000)=0"

end Krepi.SpecTests.Fdt.Replay
