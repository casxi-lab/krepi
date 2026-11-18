module

public import Krepi.Spec.PageTables.Boot
public meta import Krepi.Spec.PageTables.Boot

/-!
# Replay of the page-tables vectors

`replay` answers one line of `verification/vectors/memory/page-tables.vectors`
through the specification: it reads the input in the vector notation of the
component's `specification.md`, runs the calls that it names on the sets that
it declares and writes the output of the last call in the notation of the
contract's `Legacy test vectors` section, in its canonical form, so that
`cargo xtask formal vectors` compares it with the expected output as text.
The expected outputs are the literals of the vector file; nothing here
computes them.

An input is fields separated by single spaces:

- `sets=` the sets of the test, `-` for none, or `<name>:<region>:<N>`
  joined by `,`: a set of region `lower` or `upper` and capacity `N`, made by
  `Tables::new` from storage that is zero; `<name>:<region>:<N>:<record>` is
  a set on zero storage whose record of tables in use is `<record>`, as a
  test that writes the storage directly makes it;
- for a test of the direct map, `memory=` the boot memory map that the test
  builds with the fdt specification, `MemoryPlan::new` with the fields
  `window=`, `ram=`, `boot=` and `firmware=`, or `MemoryPlan::all_ram` with
  the last three: a span is `<start>+<size>`, a list of spans is joined by
  `,` and `-` when empty, and a firmware reservation is its span, `/` and
  its flag, `no-map`, `reusable` or `none`;
- `do=` the earlier calls of the test, `-` for none, joined by `;`, run in
  order before the call, their outputs dropped;
- `call=` the call of the case;
- `ask=` what the test asserts of the state after the call, `-` for nothing,
  joined by `;`.

A call is `<entry>(<arguments>)`, the arguments joined by `,`:
`map_page(set,v,p,kind,base,bits)`, `map_block(set,v,p,base,bits)`,
`unmap_page(set,v,base,bits)`, `lookup_page(set,v,base,bits)`,
`lookup_block(set,v,base,bits)`, `used(set)`, `reset(set)`,
`clone_kernel_from(target,source,source_base,base,bits)`,
`descriptor(kind,address)` and `direct_map(set,base,bits)`, which maps the
boot memory map of `memory=` into an upper set; and the forms of a test that
are not one entry: `set_entry(set,table,index,descriptor)` writes an entry of
the storage, `set_used(set,record)` the record of tables in use,
`map_blocks(set,v,p,count,base,bits)` is the `count` calls
`map_block(set,v+0x200000*i,p+0x200000*i,base,bits)` for `i` from 0 to
`count - 1`, in this order, the first loop of `pt-17`, and
`translate_block(set,pa,base,bits)` is the check of `dm-04` of the 2 MiB
block at the physical address `pa` of a direct map. A write entry that
succeeds has its plan executed on the pool of its set at once, as its caller
does.

The output of a call is `ok`, followed by its fields, or `err=<error>`:
`unmap_page` gives `page=<address>`, `lookup_page`, `lookup_block` and
`descriptor` give `descriptor=<descriptor>`, `used` gives `used=<count>`, and
`direct_map` gives `bytes=<bytes> blocks=<count> pages=<count>`, the counts
of its plan (`Plan.counts`); `map_blocks` gives `ok` when every call
succeeds and the first error otherwise. `translate_block` gives `map=block`
when the lookup of its block slot gives a block that translates the block to
itself, `map=pages absent=<addresses>` when the lookups of its pages give
pages that translate each to itself or `NotMapped`, with the addresses of
the latter joined by `,` or `-`, `map=none` when every page is `NotMapped`,
and `map=wrong page=<address>` for the first page that translates otherwise,
each translation with AP[2], AP[1] and nG 0 and PXN and UXN 1. A call
followed by `.` and the name of a field of its output gives that field
alone, `<field>=<value>`, as the line of a property vector writes it.
Then each item of `ask=` gives `<item>=<value>`: `unchanged(set)` whether the
set, its pool and its record, is the one from before the call;
`zero(set)` whether every entry of its pool is 0; and
`entry(set,table,index)` the entry. An input that names an unknown set,
entry or kind, two sets of different regions or capacities for a copy, or a
boot memory map that the fdt specification refuses, gives `malformed`.
-/

@[expose] public section

namespace Krepi.SpecTests.PageTables.Replay

open Krepi.Spec.PageTables

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

/-- The items of a list joined by `sep`, or none for `-`. -/
def items (sep : Char) (s : String) : List String :=
  if s == "-" then [] else splitOnChar sep s

/-- The value of a hexadecimal digit. -/
def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

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

/-- An 8-bit number, a physical width. -/
def number8 (s : String) : Option UInt8 := do
  let n ← number s
  if n < 2 ^ 8 then some (UInt8.ofNat n) else none

/-- A kind by its name. -/
def kind (s : String) : Option Kind := Kind.all.find? (·.name == s)

/-- A region by its name. -/
def region (s : String) : Option Region :=
  if s == "lower" then some .lower else if s == "upper" then some .upper else none

/-- A call `<entry>(<arguments>)`: the entry and its arguments. -/
def parseCall (s : String) : Option (String × List String) :=
  match s.toList.span (· != '(') with
  | (name, '(' :: rest) =>
    match rest.reverse with
    | ')' :: inner =>
      some (String.ofList name, if inner.isEmpty then [] else splitOnChar ',' (String.ofList inner.reverse))
    | _ => none
  | _ => none

/-- A span `<start>+<size>` of the boot memory map. -/
def span (s : String) : Option Krepi.Spec.Fdt.Span :=
  match splitOnChar '+' s with
  | [start, size] => do pure ⟨← number64 start, ← number64 size⟩
  | _ => none

/-- A list of spans joined by `,`, or `-` for none. -/
def spans (s : String) : Option (List Krepi.Spec.Fdt.Span) :=
  if s == "-" then some [] else (splitOnChar ',' s).mapM span

/-- A firmware reservation `<span>/<flag>`, with the flag `no-map`, `reusable`
or `none`. -/
def reservation (s : String) : Option Krepi.Spec.Fdt.ReservedRegion :=
  match splitOnChar '/' s with
  | [sp, "no-map"] => (span sp).map (⟨·, true, false⟩)
  | [sp, "reusable"] => (span sp).map (⟨·, false, true⟩)
  | [sp, "none"] => (span sp).map (⟨·, false, false⟩)
  | _ => none

/-- A list of firmware reservations joined by `,`, or `-` for none. -/
def reservations (s : String) : Option (List Krepi.Spec.Fdt.ReservedRegion) :=
  if s == "-" then some [] else (splitOnChar ',' s).mapM reservation

/-- The boot memory map of the fields of an input: none without `memory=`;
the value of `MemoryPlan::new` or `MemoryPlan::all_ram` of the fdt
specification on the fields; nothing for a field that cannot be read or a
boot memory map that the specification refuses. -/
def memory (fs : List (String × String)) : Option (Option Krepi.Spec.Fdt.MemoryPlan) :=
  let built (m : Except Krepi.Spec.Fdt.PlanError Krepi.Spec.Fdt.MemoryPlan) := m.toOption.map some
  match field fs "memory" with
  | none => some none
  | some "MemoryPlan::new" => do
    built (Krepi.Spec.Fdt.MemoryPlan.new (← span (← field fs "window"))
      (← spans (← field fs "ram")) (← spans (← field fs "boot"))
      (← reservations (← field fs "firmware")))
  | some "MemoryPlan::all_ram" => do
    built (Krepi.Spec.Fdt.MemoryPlan.allRam (← spans (← field fs "ram"))
      (← spans (← field fs "boot")) (← reservations (← field fs "firmware")))
  | some _ => none

/-- A call and the field of its output that it names after a `.`, if it names
one: `direct_map(s,0x80000,40).bytes` is the call `direct_map(s,0x80000,40)`
and the field `bytes`. -/
def projection (s : String) : String × Option String :=
  match s.toList.reverse.span (· != '.') with
  | (name, '.' :: ')' :: call) =>
    (String.ofList (')' :: call).reverse, some (String.ofList name.reverse))
  | _ => (s, none)

/-! ## Writing the output -/

/-- A number as `0x` and lowercase hexadecimal digits. -/
def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- A Boolean as `true` or `false`. -/
def bool (b : Bool) : String := if b then "true" else "false"

/-- The output of a failed call. -/
def err (e : TableError) : String := "err=" ++ e.name

/-! ## Sets -/

/-- A set of some region and capacity, as a test declares it. -/
structure AnySet where
  region : Region
  n : Nat
  set : Tables region n

/-- The set as one of region `r` and capacity `n`, when it is one. -/
def AnySet.as? (a : AnySet) (r : Region) (n : Nat) : Option (Tables r n) :=
  if h : a.region = r ∧ a.n = n then some (cast (by rw [h.1, h.2]) a.set) else none

/-- Whether two sets are equal: of one region and one capacity, with the same
pool and record. -/
def AnySet.same (a b : AnySet) : Bool :=
  match b.as? a.region a.n with
  | some s => decide (s = a.set)
  | none => false

/-- The sets of a case, by name. -/
abbrev Env := List (String × AnySet)

/-- The set of a name. -/
def Env.get? (env : Env) (name : String) : Option AnySet :=
  (env.find? (·.1 == name)).map (·.2)

/-- The sets with the set of `name` replaced. -/
def Env.put (env : Env) (name : String) (a : AnySet) : Env :=
  env.map fun e => if e.1 == name then (name, a) else e

/-- One declared set: `<name>:<region>:<N>`, made by `Tables::new` from zero
storage, or `<name>:<region>:<N>:<record>`, zero storage with that record. -/
def declare (s : String) : Option (String × AnySet) :=
  match splitOnChar ':' s with
  | [name, r, n] => do
    let r ← region r
    let n ← number n
    pure (name, ⟨r, n, Tables.new (Pool.zero n)⟩)
  | [name, r, n, record] => do
    let r ← region r
    let n ← number n
    let record ← number record
    pure (name, ⟨r, n, ⟨Pool.zero n, record⟩⟩)
  | _ => none

/-! ## Calls -/

/-- A set after a write entry that returned the set `s` and the plan `plan`:
the plan executed on its pool. -/
def written (r : Region) (n : Nat) (s : Tables r n) (plan : Plan) : AnySet :=
  ⟨r, n, s.apply plan⟩

/-- The `count` calls `map_block(set, v + 0x200000 i, p + 0x200000 i, base, bits)`
from `i`, each on the set that the calls before it left: the set after them
and the first error, if one fails. -/
def mapBlocks (s : Tables r n) (v p base : UInt64) (bits : UInt8) :
    (count i : Nat) → Tables r n × Option TableError
  | 0, _ => (s, none)
  | count + 1, i =>
    let step := UInt64.ofNat (i * BLOCK_SIZE)
    match s.mapBlock (v + step) (p + step) base bits with
    | .ok (s', plan) => mapBlocks (s'.apply plan) v p base bits count (i + 1)
    | .error e =>
      ((mapBlocks s v p base bits count (i + 1)).1, some e)

/-- Whether a leaf of the direct map has the permissions of `dm-04`: AP[2],
AP[1] and nG 0, and PXN and UXN 1. -/
def directPermissions (d : UInt64) : Bool :=
  d &&& (0x40 ||| 0x80 ||| 0x800) == 0 && d &&& (2 ^ 53 ||| 2 ^ 54) == (2 ^ 53 ||| 2 ^ 54)

/-- How the pages of the 2 MiB block at the physical address `pa` translate in
a direct map, as the test of `dm-04` reads them: the block slot through
`lookup_block`; otherwise each page through `lookup_page`, `NotMapped` for an
absent page. -/
def translateBlock (s : Tables r n) (pa base : UInt64) (bits : UInt8) : String :=
  match s.lookupBlock (DIRECT_BASE ||| pa) base bits with
  | .ok d =>
    if outputAddress d == pa && directPermissions d then "map=block"
    else "map=wrong page=" ++ hex pa.toNat
  | .error _ =>
    let pages := (List.range ENTRIES).map fun i => UInt64.ofNat (pa.toNat + i * PAGE_SIZE)
    let rec go : List UInt64 → List UInt64 → Bool → String
      | [], absent, mapped =>
        if !mapped then "map=none"
        else "map=pages absent=" ++
          if absent.isEmpty then "-" else ",".intercalate (absent.reverse.map (hex ·.toNat))
      | q :: rest, absent, mapped =>
        match s.lookupPage (DIRECT_BASE ||| q) base bits with
        | .ok d =>
          if outputAddress d == q && directPermissions d then go rest absent true
          else "map=wrong page=" ++ hex q.toNat
        | .error .notMapped => go rest (q :: absent) mapped
        | .error _ => "map=wrong page=" ++ hex q.toNat
    go pages [] false

/-- Runs one call on the sets, with the boot memory map `memory` of the input:
the sets after it and its output, or none for a malformed call. -/
def runCall (memory : Option Krepi.Spec.Fdt.MemoryPlan) (env : Env) (call : String) :
    Option (Env × String) := do
  let (entry, args) ← parseCall call
  match entry, args with
  | "map_page", [name, v, p, k, base, bits] => do
    let ⟨r, n, s⟩ ← env.get? name
    match s.mapPage (← number64 v) (← number64 p) (← kind k) (← number64 base) (← number8 bits) with
    | .ok (s', plan) => pure (env.put name (written r n s' plan), "ok")
    | .error e => pure (env, err e)
  | "map_block", [name, v, p, base, bits] => do
    let ⟨r, n, s⟩ ← env.get? name
    match s.mapBlock (← number64 v) (← number64 p) (← number64 base) (← number8 bits) with
    | .ok (s', plan) => pure (env.put name (written r n s' plan), "ok")
    | .error e => pure (env, err e)
  | "unmap_page", [name, v, base, bits] => do
    let ⟨r, n, s⟩ ← env.get? name
    match s.unmapPage (← number64 v) (← number64 base) (← number8 bits) with
    | .ok (plan, page) => pure (env.put name (written r n s plan), "ok page=" ++ hex page.toNat)
    | .error e => pure (env, err e)
  | "lookup_page", [name, v, base, bits] => do
    let ⟨_, _, s⟩ ← env.get? name
    match s.lookupPage (← number64 v) (← number64 base) (← number8 bits) with
    | .ok d => pure (env, "ok descriptor=" ++ hex d.toNat)
    | .error e => pure (env, err e)
  | "lookup_block", [name, v, base, bits] => do
    let ⟨_, _, s⟩ ← env.get? name
    match s.lookupBlock (← number64 v) (← number64 base) (← number8 bits) with
    | .ok d => pure (env, "ok descriptor=" ++ hex d.toNat)
    | .error e => pure (env, err e)
  | "used", [name] => do
    let ⟨_, _, s⟩ ← env.get? name
    pure (env, "ok used=" ++ toString s.usedTables)
  | "reset", [name] => do
    let ⟨r, n, s⟩ ← env.get? name
    let (s', plan) := s.reset
    pure (env.put name (written r n s' plan), "ok")
  | "clone_kernel_from", [target, source, sourceBase, base, bits] => do
    let ⟨r, n, t⟩ ← env.get? target
    let s ← (← env.get? source).as? r n
    match t.cloneKernelFrom s (← number64 sourceBase) (← number64 base) (← number8 bits) with
    | .ok (t', plan) => pure (env.put target (written r n t' plan), "ok")
    | .error e => pure (env, err e)
  | "descriptor", [k, a] => do
    pure (env, "ok descriptor=" ++ hex (descriptor (← kind k) (← number64 a)).toNat)
  | "set_entry", [name, t, i, d] => do
    let ⟨r, n, s⟩ ← env.get? name
    let s' : Tables r n := { s with pool := Pool.store s.pool (← number t) (← number i) (← number64 d) }
    pure (env.put name ⟨r, n, s'⟩, "ok")
  | "set_used", [name, record] => do
    let ⟨r, n, s⟩ ← env.get? name
    pure (env.put name ⟨r, n, { s with used := ← number record }⟩, "ok")
  | "direct_map", [name, base, bits] => do
    let a ← env.get? name
    let s ← a.as? .upper a.n
    match s.directMap (← memory) (← number64 base) (← number8 bits) with
    | .ok (s', plan) =>
      let c := plan.counts
      pure (env.put name (written .upper a.n s' plan),
        s!"ok bytes={hex c.bytes} blocks={c.blocks} pages={c.pages}")
    | .error e => pure (env, err e)
  | "map_blocks", [name, v, p, count, base, bits] => do
    let ⟨r, n, s⟩ ← env.get? name
    let v ← number64 v
    let p ← number64 p
    let count ← number count
    if 2 ^ 64 < v.toNat + count * BLOCK_SIZE || 2 ^ 64 < p.toNat + count * BLOCK_SIZE then failure
    let (s', e) := mapBlocks s v p (← number64 base) (← number8 bits) count 0
    pure (env.put name ⟨r, n, s'⟩, match e with | some e => err e | none => "ok")
  | "translate_block", [name, pa, base, bits] => do
    let ⟨_, _, s⟩ ← env.get? name
    pure (env, translateBlock s (← number64 pa) (← number64 base) (← number8 bits))
  | _, _ => none

/-- Whether every entry of every table of a pool is 0. -/
def Pool.isZero (p : Pool n) : Bool := p.toList.all fun t => t.toList.all (· == 0)

/-- One item of `ask=` on the sets `before` and `after` the call. -/
def query (before after : Env) (item : String) : Option String := do
  let (what, args) ← parseCall item
  match what, args with
  | "unchanged", [name] => pure (bool ((← after.get? name).same (← before.get? name)))
  | "zero", [name] => pure (bool (Pool.isZero (← after.get? name).set.pool))
  | "entry", [name, t, i] => pure (hex ((← after.get? name).set.entry (← number t) (← number i)).toNat)
  | _, _ => none

/-- The field `name` of the output of a call, `<name>=<value>`; an error stays
as it is. -/
def project (out name : String) : Option String :=
  match splitOnChar ' ' out with
  | "ok" :: fs => fs.find? fun f => (name ++ "=").toList.isPrefixOf f.toList
  | _ => some out

/-- The output of a case. -/
def runCase (fs : List (String × String)) : Option String := do
  let memory ← memory fs
  let env ← (items ',' (← field fs "sets")).mapM declare
  let env ← (items ';' (← field fs "do")).foldlM
    (fun env c => (·.1) <$> runCall memory env c) env
  let (call, name) := projection (← field fs "call")
  let (after, out) ← runCall memory env call
  let out ← match name with
    | some name => project out name
    | none => pure out
  let asked ← (items ';' (← field fs "ask")).mapM fun item => do
    pure (item ++ "=" ++ (← query env after item))
  pure (" ".intercalate (out :: asked))

/-- `replay`: the output of the specification for one input of the vector
file, or `malformed` for an input that it cannot read. -/
def replay (input : String) : String := (runCase (fields input)).getD "malformed"

/-! ## Representative cases

One case of each vector of the file, its input and expected output copied
from the vector file. The long inputs are written in pieces with string gaps:
a backslash at the end of a line, whose newline and the indentation after it
are not part of the string. -/

-- `pt-01.2`: a high page mapped `ReadOnly` keeps every bit of its output address.
#guard replay
  "sets=s:lower:6 do=map_page(s,0x200000000,0x1008000000,ReadOnly,0x100000000,40) \
  call=lookup_page(s,0x200000000,0x100000000,40) ask=-" ==
  "ok descriptor=0x60001008000787"

-- `pt-02.1`: the descriptor of `ReadExecute` is read-only and executable at EL1.
#guard replay
  "sets=- do=- call=descriptor(ReadExecute,0x0) ask=-" ==
  "ok descriptor=0x40000000000787"

-- `pt-03.6`: a page under a free root entry needs two new tables, and all three
-- tables of the pool are in use: `OutOfTables`.
#guard replay
  "sets=s:lower:3 do=map_page(s,0x40000000,0x40000000,ReadWrite,0x100000000,40);used(s);\
  lookup_page(s,0x40000000,0x100000000,40);\
  map_page(s,0x40000000,0x40001000,Device,0x100000000,40);\
  lookup_page(s,0x40000000,0x100000000,40) \
  call=map_page(s,0x80000000,0x0,ReadWrite,0x100000000,40) ask=-" ==
  "err=OutOfTables"

-- `pt-04.11`: a pool that ends above $2^{40}$ is `TableBacking`.
#guard replay
  "sets=s:lower:3 do=map_page(s,0x1,0x0,ReadWrite,0x100000000,40);used(s);\
  map_page(s,0x0,0x1,ReadWrite,0x100000000,40);used(s);\
  map_page(s,0x0,0x0,ReadWrite,0x100000001,40);used(s);\
  map_page(s,0x8000000000,0x0,ReadWrite,0x100000000,40);used(s);\
  map_page(s,0x0,0x10000000000,ReadWrite,0x100000000,40);used(s) \
  call=map_page(s,0x0,0x0,ReadWrite,0xfffffff000,40) ask=-" ==
  "err=TableBacking"

-- `pt-05.3`: `unmap_page` gives the physical page of the leaf.
#guard replay
  "sets=s:lower:4 do=map_page(s,0x0,0x1000,ReadWrite,0x100000000,40);\
  map_page(s,0x1000,0x2000,ReadOnly,0x100000000,40) call=unmap_page(s,0x0,0x100000000,40) \
  ask=-" ==
  "ok page=0x1000"

-- `pt-06.2`: a `UserReadExecute` page is read-only at both levels, executable at EL0
-- only, and not global.
#guard replay
  "sets=s:lower:3 do=map_page(s,0x0,0x0,UserReadExecute,0x100000000,40) \
  call=lookup_page(s,0x0,0x100000000,40) ask=-" ==
  "ok descriptor=0x20000000000fc7"

-- `pt-07.8`: the copy keeps the leaf and points its table descriptors at the target's
-- tables of the source's indices.
#guard replay
  "sets=source:lower:10,target:lower:10 \
  do=map_page(source,0x4000,0x40000000,ReadExecute,0x100000000,40);\
  map_page(source,0x9000000,0x9000000,Device,0x100000000,40);\
  map_page(source,0x40000000,0x200000000,ReadWrite,0x100000000,40);\
  map_page(target,0x80000000,0x0,ReadWrite,0x10000a000,40);\
  clone_kernel_from(target,source,0x100000000,0x10000a000,40);used(target);used(source) \
  call=lookup_page(target,0x4000,0x10000a000,40) ask=entry(target,0,0);entry(target,1,0)" ==
  "ok descriptor=0x40000040000787 entry(target,0,0)=0x10000b003 \
  entry(target,1,0)=0x10000c003"

-- `pt-08.19`: a source root entry with bit 6 set is a table descriptor with an
-- attribute bit, `InvalidDescriptor`, and the target is unchanged.
#guard replay
  "sets=source:lower:6,target:lower:6 \
  do=map_page(source,0x0,0x4000,ReadOnly,0x100000000,40);\
  map_page(target,0x1000,0x8000,ReadWrite,0x100006000,40);\
  clone_kernel_from(target,source,0x100000000,0x100000000,40);used(target);\
  clone_kernel_from(target,source,0x100000000,0x100001000,40);used(target);\
  clone_kernel_from(target,source,0x100000001,0x100006000,40);used(target);\
  clone_kernel_from(target,source,0x100000000,0x100006001,40);used(target);\
  clone_kernel_from(target,source,0x100000000,0x100006000,31);used(target);\
  clone_kernel_from(target,source,0x100000000,0xfffffff000,40);used(target);\
  set_entry(source,0,0,0x100000003);\
  clone_kernel_from(target,source,0x100000000,0x100006000,40);used(target);\
  set_entry(source,0,0,0x100005003);\
  clone_kernel_from(target,source,0x100000000,0x100006000,40);used(target);\
  set_entry(source,0,0,0x100001043) \
  call=clone_kernel_from(target,source,0x100000000,0x100006000,40) ask=unchanged(target)" ==
  "err=InvalidDescriptor unchanged(target)=true"

-- `pt-09.5`: `reset` leaves every entry 0.
#guard replay
  "sets=s:lower:4 do=map_page(s,0x0,0x1000,ReadWrite,0x100000000,40);\
  map_page(s,0x200000,0x2000,UserReadWrite,0x100000000,40);\
  unmap_page(s,0x0,0x100000000,40);used(s) call=reset(s) ask=zero(s)" ==
  "ok zero(s)=true"

-- `pt-10.2`: a source leaf at or above $2^{40}$ is `InvalidDescriptor`, and the target stays zero.
#guard replay
  "sets=source:lower:3,target:lower:3 \
  do=map_page(source,0x0,0x10000000000,ReadOnly,0x100000000,48) \
  call=clone_kernel_from(target,source,0x100000000,0x100003000,40) ask=zero(target)" ==
  "err=InvalidDescriptor zero(target)=true"


-- `pt-11.10`: after `unmap_page` in the first set, the second set still maps its private
-- stack page.
#guard replay
  "sets=first:lower:6,second:lower:6 \
  do=map_page(first,0x20001000,0x41000000,KernelPrivateReadWrite,0x100000000,40);\
  lookup_page(first,0x20001000,0x100000000,40);\
  lookup_page(first,0x20000000,0x100000000,40);\
  map_page(second,0x20001000,0x42000000,KernelPrivateReadWrite,0x100007000,40);\
  lookup_page(second,0x20001000,0x100007000,40);\
  lookup_page(second,0x20000000,0x100007000,40);\
  lookup_page(first,0x20001000,0x100000000,40);\
  lookup_page(second,0x20001000,0x100007000,40);\
  unmap_page(first,0x20001000,0x100000000,40) \
  call=lookup_page(second,0x20001000,0x100007000,40) ask=-" ==
  "ok descriptor=0x60000042000f07"

-- `pt-12.3`: a source leaf of `KernelPrivateReadWrite` is `InvalidDescriptor`, and the
-- target is unchanged.
#guard replay
  "sets=source:lower:3,target:lower:3 \
  do=map_page(source,0x20001000,0x41000000,KernelPrivateReadWrite,0x100000000,40);\
  map_page(target,0x40000000,0x40000000,ReadWrite,0x100004000,40) \
  call=clone_kernel_from(target,source,0x100000000,0x100004000,40) ask=unchanged(target)" ==
  "err=InvalidDescriptor unchanged(target)=true"

-- `pt-13.3`: a set whose storage and record are 0 maps a page after `reset`.
#guard replay
  "sets=s:lower:3:0 do=reset(s);used(s);\
  map_page(s,0x20001000,0x41000000,KernelPrivateReadWrite,0x100000000,40) \
  call=lookup_page(s,0x20001000,0x100000000,40) ask=-" ==
  "ok descriptor=0x60000041000f07"

-- `pt-14.12`: an upper set maps `DIRECT_BASE` and keeps every bit of the output address.
#guard replay
  "sets=lower:lower:3,upper:upper:3 do=map_page(upper,0x0,0x0,ReadWrite,0x100000000,40);\
  map_page(upper,0x1000,0x0,ReadWrite,0x100000000,40);\
  map_page(upper,0x7ffffff000,0x0,ReadWrite,0x100000000,40);\
  map_page(lower,0xffffff8000000000,0x0,ReadWrite,0x100000000,40);\
  map_page(lower,0xffffff8000001000,0x0,ReadWrite,0x100000000,40);\
  map_page(lower,0xfffffffffffff000,0x0,ReadWrite,0x100000000,40);\
  map_page(lower,0x8000000000,0x0,ReadWrite,0x100000000,40);\
  map_page(upper,0x8000000000,0x0,ReadWrite,0x100000000,40);\
  map_page(lower,0xffffff7ffffff000,0x0,ReadWrite,0x100000000,40);\
  map_page(upper,0xffffff7ffffff000,0x0,ReadWrite,0x100000000,40);\
  map_page(upper,0xffffff8000000000,0x100000000,ReadWrite,0x100000000,40) \
  call=lookup_page(upper,0xffffff8000000000,0x100000000,40) ask=-" ==
  "ok descriptor=0x60000100000707"

-- `pt-15.2`: a block is `ReadWrite` with bits 1 and 0 `0b01`, global and execute-never.
#guard replay
  "sets=s:upper:3 do=map_block(s,0xffffff8100000000,0x100000000,0x100000000,40) \
  call=lookup_block(s,0xffffff8100000000,0x100000000,40) ask=-" ==
  "ok descriptor=0x60000100000705"

-- `pt-16.15`: after `unmap_page`, the level 3 table stays, so the block slot is not free
-- of tables.
#guard replay
  "sets=s:lower:3 do=map_page(s,0x0,0x0,ReadOnly,0x100000000,40);\
  map_block(s,0x0,0x0,0x100000000,40);used(s);map_block(s,0x1000,0x0,0x100000000,40);\
  used(s);map_block(s,0x200000,0x1000,0x100000000,40);used(s);\
  map_block(s,0x200000,0x10000000000,0x100000000,40);used(s);\
  map_block(s,0x8000000000,0x0,0x100000000,40);used(s);\
  map_block(s,0x40000000,0x0,0x100000000,40);used(s);unmap_page(s,0x0,0x100000000,40) \
  call=map_block(s,0x0,0x0,0x100000000,40) ask=-" ==
  "err=AlreadyMapped"

-- `pt-17.4103`: after the 4,096 blocks of the loop, the nine tables are in use, so the
-- next block is `OutOfTables`.
#guard replay
  "sets=s:upper:9 do=map_blocks(s,0xffffff8000000000,0x0,4096,0x100000000,40);used(s);\
  lookup_block(s,0xffffff8000000000,0x100000000,40);\
  lookup_block(s,0xffffff803fe00000,0x100000000,40);\
  lookup_block(s,0xffffff8040000000,0x100000000,40);\
  lookup_block(s,0xffffff8100000000,0x100000000,40);\
  lookup_block(s,0xffffff81ffe00000,0x100000000,40) \
  call=map_block(s,0xffffff8200000000,0x200000000,0x100000000,40) ask=-" ==
  "err=OutOfTables"

-- `pt-18.3`: a source with a block is `InvalidDescriptor`, and the target is unchanged.
#guard replay
  "sets=source:upper:3,target:upper:3 \
  do=map_block(source,0xffffff8000000000,0x0,0x100000000,40);\
  map_page(target,0xffffff8000001000,0x1000,ReadOnly,0x100004000,40) \
  call=clone_kernel_from(target,source,0x100000000,0x100004000,40) ask=unchanged(target)" ==
  "err=InvalidDescriptor unchanged(target)=true"

-- `pt-21.1`: the descriptor of `UserDevice` is Device memory, read and write at EL0, never
-- executable, not global.
#guard replay
  "sets=- do=- call=descriptor(UserDevice,0x0) ask=-" ==
  "ok descriptor=0x60000000000c43"

-- `dm-01.1`: the reservation and the boot page break blocks: 6 blocks and 1,021 pages.
#guard replay
  "sets=s:upper:8 memory=MemoryPlan::new window=0x0+0x1000000 ram=0x0+0x1000000 \
  boot=0x80000+0x1000 firmware=0x600fff+0x2/reusable do=- call=direct_map(s,0x80000,40) \
  ask=-" ==
  "ok bytes=0xffd000 blocks=6 pages=1021"

-- `dm-02.2`: a block above 4 GiB keeps its output address.
#guard replay
  "sets=s:upper:3 memory=MemoryPlan::new window=0x100000000+0x400000 \
  ram=0x0+0x200000,0x100000000+0x400000 boot=0x80000+0x1000 firmware=- \
  do=direct_map(s,0x80000,40) call=lookup_block(s,0xffffff8100000000,0x80000,40) ask=-" ==
  "ok descriptor=0x60000100000705"

-- `dm-03.1`: a map that needs more tables than the pool has fails before any write.
#guard replay
  "sets=s:upper:2 memory=MemoryPlan::new window=0x0+0x400000 ram=0x0+0x400000 \
  boot=0x80000+0x1000 firmware=- do=- call=direct_map(s,0x80000,40) ask=-" ==
  "err=OutOfTables"

-- `dm-04.1`: the first 2 MiB block of the 8 GiB map is in pages, without the boot page.
#guard replay
  "sets=s:upper:16 memory=MemoryPlan::all_ram \
  ram=0x0+0x3fc00000,0x40000000+0xc0000000,0x100000000+0x100000000 boot=0x80000+0x1000 \
  firmware=0x1fffff001+0x1/no-map do=direct_map(s,0x80000,40) \
  call=translate_block(s,0x0,0x80000,40) ask=-" ==
  "map=pages absent=0x80000"

-- `dm-04.4097`: the bytes of the 8 GiB map.
#guard replay
  "sets=s:upper:16 memory=MemoryPlan::all_ram \
  ram=0x0+0x3fc00000,0x40000000+0xc0000000,0x100000000+0x100000000 boot=0x80000+0x1000 \
  firmware=0x1fffff001+0x1/no-map do=- call=direct_map(s,0x80000,40).bytes ask=-" ==
  "bytes=0x1ffbfe000"

end Krepi.SpecTests.PageTables.Replay
