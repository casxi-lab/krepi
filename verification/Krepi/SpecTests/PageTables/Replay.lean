module

public import Krepi.Spec.PageTables.Boot
public import Krepi.Spec.PageTables.Ownership
public meta import Krepi.Spec.PageTables.Boot
public meta import Krepi.Spec.PageTables.Ownership

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

The cases of the page ownership table have `sets=-` and name its tables and
values in their calls: `Ownership::new(t,arena,capacity,[banks],[exclusions])`
makes the table `t` of that extent capacity, with the exclusion capacity of the
core, from ranges `<start>+<length>` joined by `,` in brackets, an exclusion
with `/` and its owner, `firmware`, `image` or `boot`;
`choose(t,c,owner,pages,alignment,placement,window)` makes the choice `c`,
with the placement `low` or `high` and the window a range or `-`;
`assign(t,a,c,zeroed)` the receipt `a`, with `true` or `false` for the
outcome of the zeroing; `reserve(t,r,owner,pages,alignment,placement,window)`
the reservation `r`; `Reservation::initialized(x,r,zeroed)` the packet `x`
of the reservation `r`, or, after a failed zeroing, the reservation `r` again;
`publish(t,a,owner,x)` the receipt `a` of the packet `x`; `cancel(t,owner,r)`,
`release(t,owner,a)`, `validate(t,owner,x)` of a receipt or a packet, and
`stats(t)`. `PhysRange::new(start,len)`, `end(r)`, `contains(r,o)` and
`overlaps(r,o)` take ranges. The test write `set_generation(t,g)` sets the
generation counter. `mixed_steps(t,l,count)` is the first `count` steps of
the loop of the row of `own-22`, with `l` its live receipts,
`mixed_step(t,l,s)` its step `s`, and `release_all(t,l)` the release of the
live receipts after the loop. The outputs: `ok range=<range>` for a choice and
`PhysRange::new`; `ok arena= owner= generation= range=` for a receipt, with
`attempted= failures=` for a reservation; `ok value=packet ... failures=` or
`ok value=reservation ... attempted= failures=` for `Reservation::initialized`;
`ok managed= free= allocated= allocations= free_extents= largest_free=
extents= capacity=` for `stats`; `ok end=`, `ok contains=` and `ok overlaps=`;
`ok` for the other entries, and `err=<error>`. A step of `own-22` gives
`start=<address>`, `released` or `err=<error>`, then `free=<bytes>`.
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

/-- The pieces of `s` between the characters `c` outside brackets `[` `]`. -/
def splitOutside (c : Char) (s : String) : List String :=
  let rec go : List Char → Nat → List Char → List String
    | [], _, acc => [String.ofList acc.reverse]
    | x :: rest, depth, acc =>
      if x == c && depth == 0 then String.ofList acc.reverse :: go rest depth []
      else go rest (if x == '[' then depth + 1 else if x == ']' then depth - 1 else depth) (x :: acc)
  go s.toList 0 []

/-- A call `<entry>(<arguments>)`: the entry and its arguments, split at the
commas outside brackets. -/
def parseCall (s : String) : Option (String × List String) :=
  match s.toList.span (· != '(') with
  | (name, '(' :: rest) =>
    match rest.reverse with
    | ')' :: inner =>
      some (String.ofList name, if inner.isEmpty then [] else splitOutside ',' (String.ofList inner.reverse))
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

/-! ## The page ownership table -/

/-- A page ownership table of some extent capacity, with the exclusion
capacity of the core. -/
structure AnyTable where
  e : Nat
  table : Ownership e EXCLUSION_RECORDS

/-- A value that a test keeps under a name: a table, a choice, a receipt, a
reservation, an initialized packet, or the live receipts of the loop of
`own-22`. -/
inductive Item where
  | table (t : AnyTable)
  | choice (c : Choice)
  | receipt (a : Allocation)
  | reservation (r : Reservation)
  | packet (x : Initialized)
  | live (l : List Allocation)

/-- The values of a case, by name. -/
abbrev Items := List (String × Item)

/-- The value of a name. -/
def Items.get? (items : Items) (name : String) : Option Item :=
  (items.find? (·.1 == name)).map (·.2)

/-- The values with `name` bound to `v`, in place of an earlier value of the
name. -/
def Items.bind (items : Items) (name : String) (v : Item) : Items :=
  (name, v) :: items.filter (·.1 != name)

/-- The table of a name. -/
def Items.table? (items : Items) (name : String) : Option AnyTable :=
  match items.get? name with
  | some (.table t) => some t
  | _ => none

/-- The table of a name, replaced by `t`. -/
def Items.putTable (items : Items) (name : String) (e : Nat) (t : Ownership e EXCLUSION_RECORDS) :
    Items :=
  items.bind name (.table ⟨e, t⟩)

/-- A range `<start>+<length>` that `PhysRange::new` accepts. -/
def physRange (s : String) : Option PhysRange :=
  match splitOnChar '+' s with
  | [start, len] => do (PhysRange.new (← number64 start) (← number64 len)).toOption
  | _ => none

/-- A list `[<item>,...]`, the items split at the commas, `[]` for none. -/
def bracketed (s : String) : Option (List String) :=
  match s.toList with
  | '[' :: rest =>
    match rest.reverse with
    | ']' :: inner => some (if inner.isEmpty then [] else splitOnChar ',' (String.ofList inner.reverse))
    | _ => none
  | _ => none

/-- An exclusion `<range>/<owner>`, the owner `firmware`, `image` or `boot`. -/
def exclusion (s : String) : Option Exclusion :=
  match splitOnChar '/' s with
  | [r, "firmware"] => (physRange r).map (⟨·, .firmware⟩)
  | [r, "image"] => (physRange r).map (⟨·, .image⟩)
  | [r, "boot"] => (physRange r).map (⟨·, .bootStorage⟩)
  | _ => none

/-- A placement, `low` or `high`, with a window, a range or `-` for none. -/
def placement (direction window : String) : Option Placement := do
  let d ← if direction == "low" then some Direction.low
    else if direction == "high" then some Direction.high else none
  let w ← if window == "-" then some none else (physRange window).map some
  pure ⟨d, w⟩

/-- A Boolean, `true` or `false`. -/
def boolean (s : String) : Option Bool :=
  if s == "true" then some true else if s == "false" then some false else none

/-- A range as `<start>+<length>`. -/
def showRange (r : PhysRange) : String := hex r.start.toNat ++ "+" ++ hex r.len.toNat

/-- The fields of a receipt. -/
def showAllocation (a : Allocation) : String :=
  s!"arena={hex a.arena.toNat} owner={hex a.owner.toNat} generation={hex a.generation.toNat} \
  range={showRange a.range}"

/-- The fields of a reservation. -/
def showReservation (r : Reservation) : String :=
  s!"{showAllocation r.allocation} attempted={bool r.attempted} failures={r.failures.toNat}"

/-- The output of `stats`. -/
def showStats (s : Stats) : String :=
  s!"ok managed={hex s.managed} free={hex s.free} allocated={hex s.allocated} \
  allocations={s.allocations} free_extents={s.freeExtents} largest_free={hex s.largestFree} \
  extents={s.extents} capacity={s.capacity}"

/-- The output of a refused call of the page ownership table. -/
def ownErr (e : OwnershipError) : String := "err=" ++ e.name

/-- The placement of step `s` of the loop of `own-22`: high when `s` is even
and low when it is odd, with no window. -/
def mixedPlacement (s : Nat) : Placement := ⟨if s % 2 == 0 then .high else .low, none⟩

/-- Step `s` of the loop of `own-22` on the table `t`, with the live receipts
`live` in the order of their allocation, a literal transcription of its row
(contract line 1016), which mirrors `src/memory/tests/banks.rs:148-185` of the
prototype tree: when `s mod 3 ≠ 0` and an allocation is live, the release by
its owner of the live allocation at position `7 s mod n` of the `n` live ones,
`released`; otherwise owner 7 allocates `s mod 5 + 1` pages at an alignment
of `2 ^ (s mod 4)` pages, high when `s` is even and low when it is odd,
`choose` and then `assign` with the zeroing complete, `start=<address>` of
the receipt, which joins the live ones last; `err=<error>` for a call that
fails. The table, the live receipts and the output. -/
def mixedStep (t : Ownership e EXCLUSION_RECORDS) (live : List Allocation) (s : Nat) :
    Ownership e EXCLUSION_RECORDS × List Allocation × String :=
  if s % 3 != 0 && !live.isEmpty then
    let i := 7 * s % live.length
    match live[i]? with
    | some a =>
      match t.release a.owner a with
      | .ok t' => (t', live.eraseIdx i, "released")
      | .error e => (t, live, ownErr e)
    | none => (t, live, "malformed")
  else
    match t.choose 7 (UInt64.ofNat (s % 5 + 1)) (UInt64.ofNat (2 ^ (s % 4))) (mixedPlacement s) with
    | .error e => (t, live, ownErr e)
    | .ok c =>
      match t.assign c true with
      | .ok (t', a) => (t', live ++ [a], "start=" ++ hex a.range.start.toNat)
      | .error e => (t, live, ownErr e)

/-- The steps `s`, `s + 1`, ... of the loop of `own-22`, `count` of them, each
on the table and the live receipts that the steps before it left. -/
def mixedSteps (t : Ownership e EXCLUSION_RECORDS) (live : List Allocation) :
    (count s : Nat) → Ownership e EXCLUSION_RECORDS × List Allocation
  | 0, _ => (t, live)
  | count + 1, s =>
    let (t', live', _) := mixedStep t live s
    mixedSteps t' live' count (s + 1)

/-- The release of every live receipt by its owner, in the order of their
allocation, as `src/memory/tests/banks.rs:196-198` does after the loop: the
table, and the first error, if one fails. -/
def releaseAll (t : Ownership e EXCLUSION_RECORDS) :
    List Allocation → Ownership e EXCLUSION_RECORDS × Option OwnershipError
  | [] => (t, none)
  | a :: rest =>
    match t.release a.owner a with
    | .ok t' => releaseAll t' rest
    | .error err => (t, some err)

/-- Runs one call of the page ownership table on the values: the values after
it and its output, or none for a malformed call. -/
def runOwnership (items : Items) (call : String) : Option (Items × String) := do
  let (entry, args) ← parseCall call
  match entry, args with
  | "PhysRange::new", [start, len] =>
    match PhysRange.new (← number64 start) (← number64 len) with
    | .ok r => pure (items, "ok range=" ++ showRange r)
    | .error e => pure (items, ownErr e)
  | "end", [r] => pure (items, "ok end=" ++ hex (← physRange r).endAddr.toNat)
  | "contains", [r, o] => pure (items, "ok contains=" ++ bool ((← physRange r).contains (← physRange o)))
  | "overlaps", [r, o] => pure (items, "ok overlaps=" ++ bool ((← physRange r).overlaps (← physRange o)))
  | "Ownership::new", [name, arena, capacity, banks, exclusions] => do
    let e ← number capacity
    let banks ← (← bracketed banks).mapM physRange
    let exclusions ← (← bracketed exclusions).mapM exclusion
    match (Ownership.new (← number64 arena) banks exclusions :
        Except OwnershipError (Ownership e EXCLUSION_RECORDS)) with
    | .ok t => pure (items.putTable name e t, "ok")
    | .error err => pure (items, ownErr err)
  | "set_generation", [name, g] => do
    let ⟨e, t⟩ ← items.table? name
    pure (items.putTable name e { t with counter := .next (← number64 g) }, "ok")
  | "choose", [name, c, owner, pages, alignment, direction, window] => do
    let ⟨_, t⟩ ← items.table? name
    match t.choose (← number64 owner) (← number64 pages) (← number64 alignment) (← placement direction window) with
    | .ok choice => pure (items.bind c (.choice choice), "ok range=" ++ showRange choice.range)
    | .error err => pure (items, ownErr err)
  | "assign", [name, a, c, zeroed] => do
    let ⟨e, t⟩ ← items.table? name
    let .choice choice ← items.get? c | none
    match t.assign choice (← boolean zeroed) with
    | .ok (t', x) => pure ((items.putTable name e t').bind a (.receipt x), "ok " ++ showAllocation x)
    | .error err => pure (items, ownErr err)
  | "reserve", [name, r, owner, pages, alignment, direction, window] => do
    let ⟨e, t⟩ ← items.table? name
    match t.reserve (← number64 owner) (← number64 pages) (← number64 alignment) (← placement direction window) with
    | .ok (t', x) => pure ((items.putTable name e t').bind r (.reservation x), "ok " ++ showReservation x)
    | .error err => pure (items, ownErr err)
  | "Reservation::initialized", [x, r, zeroed] => do
    let .reservation res ← items.get? r | none
    match res.initialized (← boolean zeroed) with
    | .packet p =>
      pure (items.bind x (.packet p),
        s!"ok value=packet {showAllocation p.allocation} failures={p.failures.toNat}")
    | .retained res' => pure (items.bind r (.reservation res'), "ok value=reservation " ++ showReservation res')
  | "publish", [name, a, owner, x] => do
    let ⟨e, t⟩ ← items.table? name
    let .packet p ← items.get? x | none
    match t.publish (← number64 owner) p with
    | .ok (t', y) => pure ((items.putTable name e t').bind a (.receipt y), "ok " ++ showAllocation y)
    | .error (err, _) => pure (items, ownErr err)
  | "cancel", [name, owner, r] => do
    let ⟨e, t⟩ ← items.table? name
    let .reservation res ← items.get? r | none
    match t.cancel (← number64 owner) res with
    | .ok t' => pure (items.putTable name e t', "ok")
    | .error (err, _) => pure (items, ownErr err)
  | "release", [name, owner, a] => do
    let ⟨e, t⟩ ← items.table? name
    let .receipt x ← items.get? a | none
    match t.release (← number64 owner) x with
    | .ok t' => pure (items.putTable name e t', "ok")
    | .error err => pure (items, ownErr err)
  | "validate", [name, owner, x] => do
    let ⟨_, t⟩ ← items.table? name
    let (a, state) ← match items.get? x with
      | some (.receipt a) => some (a, HoldState.published)
      | some (.packet p) => some (p.allocation, HoldState.reserved)
      | _ => none
    match t.validate (← number64 owner) a state with
    | .ok () => pure (items, "ok")
    | .error err => pure (items, ownErr err)
  | "stats", [name] => do
    let ⟨_, t⟩ ← items.table? name
    pure (items, showStats t.stats)
  | "mixed_steps", [name, l, count] => do
    let ⟨e, t⟩ ← items.table? name
    let (t', live) := mixedSteps t [] (← number count) 0
    pure ((items.putTable name e t').bind l (.live live), "ok")
  | "mixed_step", [name, l, s] => do
    let ⟨e, t⟩ ← items.table? name
    let .live live ← items.get? l | none
    let (t', live', out) := mixedStep t live (← number s)
    pure ((items.putTable name e t').bind l (.live live'), out ++ " free=" ++ hex t'.stats.free)
  | "release_all", [name, l] => do
    let ⟨e, t⟩ ← items.table? name
    let .live live ← items.get? l | none
    let (t', err) := releaseAll t live
    pure ((items.putTable name e t').bind l (.live []), match err with | some err => ownErr err | none => "ok")
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

/-- The state of a case: its sets and the values that its calls named. -/
structure CaseState where
  sets : Env
  values : Items

/-- Runs one call on the state of a case: a call on a set, or else a call of
the page ownership table or of physical ranges. -/
def runAny (memory : Option Krepi.Spec.Fdt.MemoryPlan) (st : CaseState) (call : String) :
    Option (CaseState × String) :=
  match runCall memory st.sets call with
  | some (sets, out) => some ({ st with sets }, out)
  | none => (runOwnership st.values call).map fun (values, out) => ({ st with values }, out)

/-- The output of a case. -/
def runCase (fs : List (String × String)) : Option String := do
  let memory ← memory fs
  let env ← (items ',' (← field fs "sets")).mapM declare
  let st ← (items ';' (← field fs "do")).foldlM
    (fun st c => (·.1) <$> runAny memory st c) (⟨env, []⟩ : CaseState)
  let (call, name) := projection (← field fs "call")
  let (after, out) ← runAny memory st call
  let out ← match name with
    | some name => project out name
    | none => pure out
  let asked ← (items ';' (← field fs "ask")).mapM fun item => do
    pure (item ++ "=" ++ (← query st.sets after.sets item))
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

-- `own-01.5`: once the generation $2^{64} - 1$ is given, the counter is exhausted and
-- the next request is `GenerationExhausted`.
#guard replay
  "sets=- do=Ownership::new(t,0x1,2,[0x0+0x1000],[]);set_generation(t,0xffffffffffffffff);\
  choose(t,c,0x1,1,1,low,-);assign(t,a,c,true);release(t,0x1,a) \
  call=choose(t,d,0x1,1,1,low,-) ask=-" ==
  "err=GenerationExhausted"

-- `own-02.5`: a range whose end is $2^{64}$ does not fit in 64 bits.
#guard replay
  "sets=- do=end(0x1000000000+0x2000);contains(0x1000000000+0x2000,0x1000001000+0x8);\
  overlaps(0x1000000000+0x2000,0x1000002000+0x1);PhysRange::new(0x1,0x0) \
  call=PhysRange::new(0xfffffffffffffffd,0x3) ask=-" ==
  "err=AddressOverflow"

-- `own-03.3`: one bank is more banks than a capacity of no extent.
#guard replay
  "sets=- do=Ownership::new(t,0x1,8,[0x1+0x1000],[]);\
  Ownership::new(t,0x1,8,[0x0+0x1001],[]) call=Ownership::new(t,0x1,0,[0x0+0x1000],[]) \
  ask=-" ==
  "err=MetadataExhausted"

-- `own-04.5`: the pages that the exclusions touch, rounded out to pages, take no extent,
-- so 5 pages fit only after them.
#guard replay
  "sets=- do=Ownership::new(t,0x1,8,[0x0+0x8000],[0x1001+0x1/firmware,0x1fff+0x2/firmware,\
  0x2000+0x1000/firmware,0x9000+0x1/firmware]);stats(t);choose(t,c1,0x1,1,1,low,-);\
  assign(t,a,c1,true) call=choose(t,c2,0x1,5,1,low,-) ask=-" ==
  "ok range=0x3000+0x5000"

-- `own-05.2`: an exclusion that covers the whole bank leaves no managed bytes.
#guard replay
  "sets=- do=Ownership::new(t,0x1,1,[0x1000+0x4000],[0x0+0x8000/firmware]) \
  call=stats(t).managed ask=-" ==
  "managed=0x0"

-- `own-06.2`: the alignment of 4 pages is of the physical address, above 4 GiB.
#guard replay
  "sets=- do=Ownership::new(t,0x1,8,[0x100001000+0x8000],[]) \
  call=choose(t,c,0x7,2,4,low,-) ask=-" ==
  "ok range=0x100004000+0x2000"

-- `own-07.5`: $2^{64} - 1$ pages do not fit in 64 bits as bytes.
#guard replay
  "sets=- do=Ownership::new(t,0x1,8,[0x0+0x8000],[]);choose(t,c,0x1,0,1,low,-);\
  choose(t,c,0x1,1,3,low,-);choose(t,c,0x1,1,0,low,-) \
  call=choose(t,c,0x1,18446744073709551615,1,low,-) ask=-" ==
  "err=AddressOverflow"

-- `own-08.2`: a page of a bank of two would split its one extent beyond the capacity of
-- 1.
#guard replay
  "sets=- do=Ownership::new(t,0x1,1,[0x0+0x2000],[]) call=choose(t,c1,0x1,1,1,low,-) ask=-" ==
  "err=MetadataExhausted"

-- `own-09.6`: the arena is checked before the owner identity and the range.
#guard replay
  "sets=- do=Ownership::new(t,0x1,2,[0x0+0x1000],[]);\
  Ownership::new(u,0x2,2,[0x2000+0x1000],[]);choose(t,c,0x9,1,1,low,-);assign(t,a,c,true);\
  stats(t);release(t,0x8,a) call=release(u,0x9,a) ask=-" ==
  "err=WrongArena"

-- `own-10.8`: a receipt of an earlier generation of the same range is refused.
#guard replay
  "sets=- do=Ownership::new(t,0x1,2,[0x0+0x1000],[]);choose(t,c1,0x3,1,1,low,-);\
  assign(t,a,c1,true);release(t,0x3,a);release(t,0x3,a);choose(t,c2,0x3,1,1,low,-);\
  assign(t,b,c2,true) call=release(t,0x3,a) ask=-" ==
  "err=InvalidAllocation"

-- `own-11.7`: a failed zeroing consumes no generation.
#guard replay
  "sets=- do=Ownership::new(t,0x1,2,[0x0+0x1000],[]);choose(t,c1,0x1,1,1,low,-);\
  assign(t,a1,c1,false);stats(t);stats(t);choose(t,c2,0x2,1,1,low,-) \
  call=assign(t,a,c2,true) ask=-" ==
  "ok arena=0x1 owner=0x2 generation=0x1 range=0x0+0x1000"

-- `own-16.2`: the first extent is passed over for capacity and a later one fits exactly.
#guard replay
  "sets=- do=Ownership::new(t,0x1,2,[0x0+0x4000],[0x2000+0x1000/firmware]) \
  call=choose(t,c,0x1,1,1,low,-) ask=-" ==
  "ok range=0x3000+0x1000"

-- `own-17.5`: two banks are more than a capacity of 1 extent.
#guard replay
  "sets=- do=Ownership::new(t,0x1,8,[],[]);\
  Ownership::new(t,0x1,8,[0x0+0x2000,0x1000+0x1000],[]);\
  Ownership::new(t,0x1,8,[0x0+0x1000,0x0+0x1000],[]);\
  Ownership::new(t,0x1,8,[0x1+0x1000],[]) \
  call=Ownership::new(t,0x1,1,[0x0+0x1000,0x2000+0x1000],[]) ask=-" ==
  "err=MetadataExhausted"

-- `own-18.23`: adjacent banks keep their own extents after the releases in either order.
#guard replay
  "sets=- do=Ownership::new(t,0x1,8,[0x1000+0x2000,0x3000+0x2000],[]);\
  choose(t,c1,0x1,2,1,low,-);assign(t,a,c1,true);choose(t,c2,0x1,2,1,low,-);\
  assign(t,b,c2,true);release(t,0x1,a);release(t,0x1,b);stats(t);stats(t);\
  choose(t,c3,0x1,3,1,low,-);choose(t,c4,0x2,1,1,high,-);assign(t,d,c4,true);\
  Ownership::new(t,0x1,8,[0x1000+0x2000,0x3000+0x2000],[]);choose(t,c1,0x1,2,1,low,-);\
  assign(t,a,c1,true);choose(t,c2,0x1,2,1,low,-);assign(t,b,c2,true);release(t,0x1,b);\
  release(t,0x1,a);stats(t);stats(t);choose(t,c3,0x1,3,1,low,-) \
  call=choose(t,c4,0x2,1,1,high,-) ask=-" ==
  "ok range=0x4000+0x1000"

-- `own-19.5`: a high placement scans from the highest bank, whatever the order of the
-- input.
#guard replay
  "sets=- do=Ownership::new(t,0x1,8,[0x100000000+0x4000,0x0+0x4000],\
  [0x3001+0xffffd000/firmware,0x1001+0x1/firmware]);stats(t);choose(t,c1,0x1,3,1,high,-);\
  assign(t,a,c1,true) call=choose(t,c2,0x1,1,1,high,-) ask=-" ==
  "ok range=0x2000+0x1000"

-- `own-20.2`: a high placement takes the highest aligned start whose range ends inside
-- the window.
#guard replay
  "sets=- do=Ownership::new(t,0x1,8,[0x100000000+0x10000],[]) \
  call=choose(t,c1,0x1,2,4,high,0x100001001+0xc000) ask=-" ==
  "ok range=0x100008000+0x2000"

-- `own-21.7`: 7 GiB of managed bytes in two extents.
#guard replay
  "sets=- do=Ownership::new(t,0x1,2,[0x40000000+0xc0000000,0x100000000+0x100000000],[]);\
  choose(t,c1,0x1,786432,1,low,-);assign(t,a,c1,true);choose(t,c2,0x1,1048576,1,high,-);\
  assign(t,b,c2,true);stats(t) call=stats(t).managed ask=-" ==
  "managed=0x1c0000000"

-- `own-22.3`: step 2 of the loop, 3 pages at an alignment of 4 pages, high.
#guard replay
  "sets=- do=Ownership::new(t,0x1,128,[0x100000+0x18000,0x118000+0x18000,\
  0x100001000+0x18000],[0x102fff+0x2/firmware,0x117fff+0x2/firmware,\
  0x100014000+0x1000/firmware]);mixed_steps(t,l,2) call=mixed_step(t,l,2) ask=-" ==
  "start=0x100010000 free=0x40000"

-- `own-22.801`: after the release of every live allocation, the pages that no exclusion
-- touches are free.
#guard replay
  "sets=- do=Ownership::new(t,0x1,128,[0x100000+0x18000,0x118000+0x18000,\
  0x100001000+0x18000],[0x102fff+0x2/firmware,0x117fff+0x2/firmware,\
  0x100014000+0x1000/firmware]);mixed_steps(t,l,800);release_all(t,l) call=stats(t).free \
  ask=-" ==
  "free=0x43000"

-- `own-23.8`: the zeroing of a reservation gives its packet.
#guard replay
  "sets=- do=Ownership::new(t,0x7,8,[0x0+0x4000],[]);reserve(t,r,0xb,2,1,low,-);stats(t);\
  stats(t);choose(t,c,0x16,1,1,low,-);assign(t,o,c,true);\
  overlaps(0x2000+0x1000,0x0+0x2000) call=Reservation::initialized(x,r,true) ask=-" ==
  "ok value=packet arena=0x7 owner=0xb generation=0x1 range=0x0+0x2000 failures=0"

-- `own-24.9`: a packet published by another owner identity is refused.
#guard replay
  "sets=- do=Ownership::new(t,0x3,4,[0x0+0x2000],[]);reserve(t,r,0x4,2,1,low,-);stats(t);\
  Reservation::initialized(x,r,false);stats(t);cancel(t,0x4,r);\
  reserve(t,r2,0x9,1,1,low,-);Reservation::initialized(x,r,false);\
  Reservation::initialized(x,r,true) call=publish(t,a,0x9,x) ask=-" ==
  "err=WrongOwner"

-- `own-25.16`: after the release, the receipt of the reused range is stale.
#guard replay
  "sets=- do=Ownership::new(t,0x1,8,[0x0+0x2000],[]);\
  Ownership::new(u,0x2,8,[0x2000+0x2000],[]);reserve(t,r,0x7,1,1,low,-);stats(t);\
  cancel(u,0x7,r);cancel(t,0x8,r);stats(t);Reservation::initialized(x,r,true);\
  validate(u,0x7,x);publish(u,a,0x7,x);stats(t);publish(t,a,0x7,x);release(t,0x7,a);\
  reserve(t,r2,0x7,1,1,low,-);Reservation::initialized(y,r2,true);publish(t,b,0x7,y) \
  call=release(t,0x7,a) ask=-" ==
  "err=InvalidAllocation"

-- `own-26.6`: a cancelled reservation consumed its generation.
#guard replay
  "sets=- do=Ownership::new(t,0x5,4,[0x0+0x3000],[]);reserve(t,r,0x1,3,1,low,-);\
  reserve(t,r2,0x1,1,1,low,-);cancel(t,0x1,r);stats(t) call=reserve(t,r3,0x1,3,1,low,-) \
  ask=-" ==
  "ok arena=0x5 owner=0x1 generation=0x2 range=0x0+0x3000 attempted=false failures=0"

-- `own-27.6`: reservations and packets that their holders drop stay held.
#guard replay
  "sets=- do=Ownership::new(t,0x11,6,[0x0+0x3000],[]);reserve(t,r1,0x15,1,1,low,-);\
  reserve(t,r2,0x16,1,1,low,-);Reservation::initialized(x,r2,true);\
  reserve(t,r3,0x17,1,1,low,-) call=reserve(t,r4,0x18,1,1,low,-) ask=-" ==
  "err=OutOfMemory"

-- `own-28.8`: a high placement at an alignment of 2 pages in a window that holds an
-- exclusion.
#guard replay
  "sets=- do=Ownership::new(t,0x1d,12,[0x0+0x4000,0x8000+0x8000],[0xa000+0x1000/firmware]);\
  stats(t);reserve(t,r,0x3,1,1,low,0x4000+0x4000);reserve(t,r,0x3,1,1,low,0xa000+0x1000);\
  reserve(t,r,0x3,0,1,low,-);reserve(t,r,0x3,1,3,low,-);\
  reserve(t,r,0x3,18446744073709551615,1,low,-);stats(t) \
  call=reserve(t,a,0x3,2,2,high,0x8000+0x8000) ask=-" ==
  "ok arena=0x1d owner=0x3 generation=0x1 range=0xe000+0x2000 attempted=false failures=0"

end Krepi.SpecTests.PageTables.Replay
