module

public import Krepi.Spec.PageTables.Map
public meta import Krepi.Spec.PageTables.Map

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

An input is four fields separated by single spaces:

- `sets=` the sets of the test, `-` for none, or `<name>:<region>:<N>`
  joined by `,`: a set of region `lower` or `upper` and capacity `N`, made by
  `Tables::new` from storage that is zero; `<name>:<region>:<N>:<record>` is
  a set on zero storage whose record of tables in use is `<record>`, as a
  test that writes the storage directly makes it;
- `do=` the earlier calls of the test, `-` for none, joined by `;`, run in
  order before the call, their outputs dropped;
- `call=` the call of the case;
- `ask=` what the test asserts of the state after the call, `-` for nothing,
  joined by `;`.

A call is `<entry>(<arguments>)`, the arguments joined by `,`:
`map_page(set,v,p,kind,base,bits)`, `map_block(set,v,p,base,bits)`,
`unmap_page(set,v,base,bits)`, `lookup_page(set,v,base,bits)`,
`lookup_block(set,v,base,bits)`, `used(set)`, `reset(set)`,
`clone_kernel_from(target,source,source_base,base,bits)` and
`descriptor(kind,address)`; and two writes of a test, which are not entries:
`set_entry(set,table,index,descriptor)` writes an entry of the storage and
`set_used(set,record)` the record of tables in use. A write entry that
succeeds has its plan executed on the pool of its set at once, as its caller
does.

The output of a call is `ok`, followed by its fields, or `err=<error>`:
`unmap_page` gives `page=<address>`, `lookup_page`, `lookup_block` and
`descriptor` give `descriptor=<descriptor>`, and `used` gives `used=<count>`.
Then each item of `ask=` gives `<item>=<value>`: `unchanged(set)` whether the
set, its pool and its record, is the one from before the call;
`zero(set)` whether every entry of its pool is 0; and
`entry(set,table,index)` the entry. An input that names an unknown set,
entry or kind, or two sets of different regions or capacities for a copy,
gives `malformed`.
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

/-- Runs one call on the sets: the sets after it and its output, or none for a
malformed call. -/
def runCall (env : Env) (call : String) : Option (Env × String) := do
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

/-- The output of a case. -/
def runCase (fs : List (String × String)) : Option String := do
  let env ← (items ',' (← field fs "sets")).mapM declare
  let env ← (items ';' (← field fs "do")).foldlM (fun env c => (·.1) <$> runCall env c) env
  let (after, out) ← runCall env (← field fs "call")
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

end Krepi.SpecTests.PageTables.Replay
