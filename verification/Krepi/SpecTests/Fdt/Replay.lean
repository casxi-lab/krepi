module

public import Krepi.Spec.Fdt.Translate
public meta import Krepi.Spec.Fdt.Translate

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
by `,`:

- `entry=parse`: with nothing asked the output is `result=ok` or
  `result=err`; with `ask=error` a rejection also names its error; and a case
  that asks entries on the tree, `discover_memory` once and `reg`, `ranges`
  and `dma_ranges` of every node, calls them on an accepted tree and gives
  `result=returned` once they have returned.
- `entry=string_property node=<path> name=<name>` asks `value`, the string or
  `-` for none.
- `entry=translate_reg node=<path> span=<span>` asks `span`.
- `entry=reg`, `ranges` or `dma_ranges` with `node=<path>` asks queries of
  the value: `to_parent(<span>)` and `to_child(<span>)` of a map, each
  `<query>(<span>)=<span>`, or the error of the query.

An entry on a tree first parses the bytes and finds the node, and reports the
error of either as the output. `discover_memory` belongs to the memory
discovery, whose specification is not yet written; a case that needs it gives
`result=unsupported entry=discover_memory`, which matches no expected output.
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

/-- A span `<start>+<size>`. -/
def span (s : String) : Option Span :=
  match splitOnChar '+' s with
  | [start, size] => do pure ⟨← number64 start, ← number64 size⟩
  | _ => none

/-- A query `<name>(<argument>)`: its name and its argument. -/
def query (s : String) : Option (String × String) :=
  match s.toList.span (· != '(') with
  | (name, '(' :: rest) =>
    match rest.reverse with
    | ')' :: arg => some (String.ofList name, String.ofList arg.reverse)
    | _ => none
  | _ => none

/-! ## Writing the output -/

/-- A number as `0x` and lowercase hexadecimal digits. -/
def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- A span as `<start>+<size>`. -/
def spanText (s : Span) : String := hex s.start.toNat ++ "+" ++ hex s.size.toNat

/-- The output of a rejection that names its error. -/
def errorText (e : Error) : String := "result=err error=Error::" ++ e.name

/-- The output of a success with its fields. -/
def okText (fs : List String) : String := String.join ("result=ok" :: fs.map (" " ++ ·))

/-! ## Cases -/

/-- The entries that a case of the parse may ask on an accepted tree. -/
def treeCalls : List String := ["discover_memory", "reg", "ranges", "dma_ranges"]

/-- `entry=parse`. -/
def parseCase (dtb : ByteArray) (ask : List String) : String :=
  if ask.isEmpty then
    match Fdt.parse dtb with
    | .ok _ => "result=ok"
    | .error _ => "result=err"
  else if ask == ["error"] then
    match Fdt.parse dtb with
    | .ok _ => "result=ok"
    | .error e => errorText e
  else if ask.all treeCalls.contains then
    match Fdt.parse dtb with
    | .error _ => "result=returned"
    | .ok t =>
      let calls := t.nodes.map fun n =>
        (if ask.contains "reg" then [(n.reg.map fun _ => ()).toBool] else []) ++
        (if ask.contains "ranges" then [(n.ranges.map fun _ => ()).toBool] else []) ++
        (if ask.contains "dma_ranges" then [(n.dmaRanges.map fun _ => ()).toBool] else [])
      -- The count of the calls depends on every result, so each is evaluated.
      if calls.flatten.length > 3 * t.records.size then "result=impossible"
      else if ask.contains "discover_memory" then "result=unsupported entry=discover_memory"
      else "result=returned"
  else "result=malformed ask"

/-- The node `path` of the tree of `dtb`, or the output of the failure. -/
def nodeOf (dtb : ByteArray) (path : String) : Except String Node :=
  match Fdt.parse dtb with
  | .error e => .error (errorText e)
  | .ok t =>
    match t.findNode path with
    | .error e => .error (errorText e)
    | .ok none => .error "result=err node=-"
    | .ok (some n) => .ok n

/-- The answer of a query of an address map. -/
def mapQuery (m : AddressMap) (q : String) : Option String := do
  let (name, arg) ← query q
  let s ← span arg
  let result ← match name with
    | "to_parent" => some (m.toParent s)
    | "to_child" => some (m.toChild s)
    | _ => none
  pure <| q ++ "=" ++ match result with
    | .ok t => spanText t
    | .error e => "Error::" ++ e.name

/-- The output of an entry that returns an address map, with its queries. -/
def mapCase (result : Except Error AddressMap) (ask : List String) : String :=
  match result with
  | .error e => errorText e
  | .ok m =>
    match ask.mapM (mapQuery m) with
    | some answers => okText answers
    | none => "result=malformed ask"

/-- One case. -/
def runCase (fs : List (String × String)) : String := Id.run do
  let some entry := field fs "entry" | return "result=malformed entry"
  let ask := match field fs "ask" with
    | some "" | none => []
    | some a => splitOnChar ',' a
  if entry == "discover_memory" then return "result=unsupported entry=discover_memory"
  let some dtbText := field fs "dtb" | return "result=malformed dtb"
  let some dtb := hexBytes dtbText | return "result=malformed dtb"
  if entry == "parse" then return parseCase dtb ask
  let some path := field fs "node" | return "result=malformed node"
  match nodeOf dtb path with
  | .error out => out
  | .ok n =>
    match entry with
    | "string_property" =>
      let some name := field fs "name" | return "result=malformed name"
      if ask != ["value"] then return "result=malformed ask"
      match n.stringProperty name with
      | .ok v => okText ["value=" ++ v.getD "-"]
      | .error e => errorText e
    | "translate_reg" =>
      let some s := (field fs "span").bind span | return "result=malformed span"
      if ask != ["span"] then return "result=malformed ask"
      match n.translateReg s with
      | .ok t => okText ["span=" ++ spanText t]
      | .error e => errorText e
    | "ranges" => mapCase n.ranges ask
    | "dma_ranges" => mapCase n.dmaRanges ask
    | _ => "result=malformed entry"

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

end Krepi.SpecTests.Fdt.Replay
