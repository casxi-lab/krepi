---
specifications:
  - Krepi.Spec.Fdt.Basic
  - Krepi.Spec.Fdt.Bytes
  - Krepi.Spec.Fdt.Parse
  - Krepi.Spec.Fdt.Nodes
  - Krepi.Spec.Fdt.Translate
---

# Device-tree specification

The Lean specification of the `fdt` component, written from its
[requirements](requirements.md) and [contract](contract.md) and never from an
implementation. It is an executable model: every entry is a computable
definition whose body is public (`@[expose]`), none is `noncomputable` or
chooses with `Classical.choice`, and every loop is structural recursion on a
bound that the contract gives. The modules lie below
[`verification/Krepi/Spec/Fdt/`](../../../../verification/Krepi/Spec/Fdt/) and
import Lean core alone.

This first part covers the parse, the node access and the address
translation: the entries of the rows of `Fdt::parse`, of the node access and
of the translation in the [entry table](contract.md#entry-points), with the
functions of `Span`, the value types that they use and the limits. The memory
discovery, the Pi 5 boot memory, the CPU nodes, the boot memory map and the
publication of the shared results follow in further modules of the same
directory, with the invariants, the properties, the specification tests and
the witnesses.

## Widths and quantifiers

The component writes no state ([check and execute](contract.md#check-and-execute)):
every entry is a function of its arguments, and a failure returns one error
and nothing else, since a result is an `Except Error α`, which holds either a
value or an error. The modification set of every entry is empty.

Each entry is stated for all of its inputs at their machine widths:

| Value | Lean type | Range |
| --- | --- | --- |
| The bytes given to `Fdt::parse`, a property value, the value of `cells_u64`, `Reg::new` and `AddressMap::new` | `ByteArray` of `UInt8` | Every byte string of every length |
| An address, a size, the value of `cells_u64`, `Fdt::total_size` and the nine limits | `UInt64` | $[0, 2^{64})$ |
| A cell, a cell count and a header word | `UInt32` | $[0, 2^{32})$ |
| A span | `Span`, two `UInt64` without an invariant | Every pair, also one whose end leaves 64 bits |
| A path and a property name | `String` | Every string |
| A node | `Node`, a tree with an index below its number of nodes | Every node of every tree |
| An absent or present property given to `AddressMap::new` | `Option ByteArray` | Both |

Inside a definition, arithmetic is on `Nat`, which does not wrap. Each sum
that the contract checks against 64 bits is compared with $2^{64}$ before it
is used (`checkedAdd`, `Span.new`, `Span.Valid`), as the checked arithmetic of
the implementation does, and a width check of one cell compares with
$2^{32}$. Offsets inside a tree stay below `MAX_BLOB_SIZE` and need no check.

The functions are total, so "for every input the entry returns" holds of the
specification by construction, which is why the vector `fdt-parser-6` only
checks that the entries return. A tree that the parse did not build, such as
a value written by hand, is still an input of the node entries: they return
for it as well, and the results that the contract fixes are those on trees
that the parse accepted.

## Model

### Basic

[`Basic.lean`](../../../../verification/Krepi/Spec/Fdt/Basic.lean): the
shared values.

- **Limits.** The nine constants of the entry table with the values of
  [format and bounds](contract.md#format-and-bounds): `MAX_BLOB_SIZE`
  2 MiB, `MAX_DEPTH` 32, `MAX_TOKENS` 65,536, `MAX_PROPERTIES` 512,
  `MAX_PROPERTY_NAME` 64, `MAX_RESERVATIONS` 128, `MAX_MEMORY_REGIONS` 32,
  `MAX_RESERVED_REGIONS` 128 and `PI5_MAX_BLOB_SIZE` 128 KiB.
- **Errors.** `Error` with its 21 variants and `PlanError` with its 7, in the
  order of the error table of
  [rejection and error priority](contract.md#rejection-and-error-priority),
  and the name of each variant as the contract and the vector notation write
  it.
- **Checked arithmetic.** `checkedAdd a b` is `a + b` when it is below
  $2^{64}$ and `Overflow` otherwise.
- **Spans.** `Span` is the pair of `start` and `size`; `Span.Valid` is the
  contract's condition that `start + size` fits in 64 bits. `Span.new`,
  `Span.endAddr` and `Span.contains` are `Span::new`, `end` and `contains`.
  `Span.holds` and `Span.overlaps` compare spans at their exact ends and are
  used by the parse and the translation on valid spans.

### Bytes

[`Bytes.lean`](../../../../verification/Krepi/Spec/Fdt/Bytes.lean): the
byte-level reads.

- **Words.** `u32At` and `u64At` read a big-endian word and fail with
  `Truncated` when it runs past the end of the bytes they are given.
- **Strings.** `cString b start` finds the first NUL at or after `start`
  within `b`, trying at most the bytes up to the end of `b`, and decodes the
  bytes before it as UTF-8 with `String.fromUTF8?`; no NUL, or bytes that are
  not UTF-8, give `BadString`.
- **Padding.** `paddedEnd b e requireZero` is the next multiple of 4 from
  `e`: `Truncated` when it lies past the end of `b`, and, for a node name,
  `BadPadding` for a nonzero byte in the padding.
- **Names.** `isNodeNameChar` and `isPropertyNameChar` are the character
  sets of node and property names.
- **Ranges of offsets.** `intersects` is the intersection of two half-open
  ranges of offsets, which is empty when either range is.

### Parse

[`Parse.lean`](../../../../verification/Krepi/Spec/Fdt/Parse.lean):
`Fdt::parse`, steps 1 to 3 of the error order of the parse and the entries on
a tree.

- **The tree.** `Fdt` holds `totalSize`, the header's `totalsize`; the
  entries of the reservation map in their order, `reservations`; and the
  nodes in the order of the structure block, `records`, each a `NodeRecord`
  with its name, the index of its parent, none for the root, and its
  properties with their names and values in their order. A value is exactly
  its declared length.
- **The header and the blocks.** `header` checks step 1 in the order of the
  contract and yields the first `totalsize` bytes, the layout and the two
  blocks. `block` checks one block: its start inside the header,
  `BadLayout`; its end beyond 64 bits, `Overflow`; past the tree,
  `Truncated`.
- **The reservation map.** `reservationsFrom` checks step 2 entry by entry
  and stops at the terminator, two zeros. It reads at most
  `MAX_RESERVATIONS + 1` entries, enough for 128 entries and the terminator.
- **Tokens.** `decodeToken` checks the encoding of one token in the order of
  step 3 and decodes it as a begin node with its name, an end node, a
  property with its name and value, a no-operation or the end token.
- **The place of a token in the tree.** `Walk.place` checks the place of a
  token in the order of step 3: `BadTree`, the depth, the number of
  properties of the node, then a duplicate name. The walk keeps the open
  nodes, innermost first, each with the names of its properties so far and
  whether a child has begun in it. `walkTokens` decodes and places at most
  `MAX_TOKENS` tokens; the end token ends it.
- **The parse.** `Fdt.parse` runs the three steps in order and builds the
  tree from what they read.

### Nodes

[`Nodes.lean`](../../../../verification/Krepi/Spec/Fdt/Nodes.lean): the node
access of [format and bounds](contract.md#format-and-bounds).

- **Nodes.** `Node` is a tree with the index of one of its nodes.
  `Fdt.nodes` lists them in the order of the structure block, `Fdt.root` is
  the first, and `Node.name` and `Node.parent` read the record.
- **Paths.** `Fdt.findNode` checks the form of the path, `BadPath`, and then
  walks its components from the root: the children of the node so far with
  the name of the component, two of them `AmbiguousMapping`, none a path
  that matches nothing.
- **Properties.** `Node.property` gives the value of the property of a name;
  `Node.stringProperty`, `Node.enabled`, `Node.addressCells` and
  `Node.sizeCells` read it as the contract states, with the defaults 2 and 1
  of the cell counts.

### Translate

[`Translate.lean`](../../../../verification/Krepi/Spec/Fdt/Translate.lean):
[address translation](contract.md#address-translation) and step 7 of the
error order.

- **Cells.** `cellsU64` reads 0, 1 or 2 cells. `checkWidth` is the width of
  an address of one or two cells.
- **Regions.** `Reg` holds the spans of a `reg` value; `Reg.new` checks the
  cells, the length and then every entry before it gives any.
- **Address maps.** `AddressMap` holds the windows of a map, none for an
  absent property and the empty list for the identity, with the cells of both
  sides. `AddressMap.new` checks every window at construction.
  `AddressMap.translate`, through `toParent` and `toChild`, checks the request
  and goes through the windows in order with `throughWindows`.
- **The node entries.** `Node.reg`, `Node.ranges`, `Node.dmaRanges` and
  `Node.translateReg` read the properties of a node in the cells of the right
  node; `climbRanges` translates through the `ranges` of each bus up to the
  root, taking at most `MAX_DEPTH` steps.

## Design decisions

### Readings of the contract

Where the contract leaves a rule open, the specification takes the reading
below and states it. Lines are those of the contract at commit `e099b40`.
Where the contract defers to the prototype tree, which it does for the error
orders ("which are those of the prototype tree", lines 282 to 284), the
reading follows the prototype and names the place.

| Reading | Contract | Basis |
| --- | --- | --- |
| `Span` has no type invariant; `Span.Valid` is the condition of the term, and the entries that take a span check it and fail with `Overflow` | Terms, lines 48 and 49; the vectors `fdt-pi5-boundaries-3` and `platform-4` to `platform-8` give `Overflow` for spans whose end leaves 64 bits, lines 988 and 1031 to 1035 | A type invariant would make those inputs unwritable |
| `Span::new` accepts an empty span; `Span::end` gives `start + size` or `Overflow`; `Span::contains(other)` fails with `Overflow` when `other` and then the span itself end beyond 64 bits, and otherwise holds when `other` lies inside the span | The entry table names the three functions, line 99, and Work bounds gives them a fixed number of steps, line 727; neither states their results | The error table gives `Overflow` to a span that leaves 64 bits, line 267, and `EmptyRegion` is checked by the entries that refuse an empty span, such as step 2, line 301 |
| In step 1, each block is checked for its start inside the header, `BadLayout`, then its end beyond 64 bits, `Overflow`, then its end past the tree, `Truncated`; the structure block before the strings block | Step 1, lines 294 to 297, lists the three errors without their order | The order of the prototype, which the contract adopts: `block` in `src/fdt/format.rs`, lines 18 to 24, and `src/fdt/parser.rs`, lines 55 and 56 |
| The checks of an `Overflow` that 64-bit arithmetic cannot reach stay in the specification at their place in the order: the end of a block in step 1, of a reservation entry before the tree's end in step 2, and of a property value in step 3, and the translated span of a translation | Lines 295, 299, 310 and 358 | Header words have 32 bits and a tree at most 2 MiB, so these sums stay below $2^{33}$, and a translated span lies inside a window that was checked at construction; the order is the contract's, and a theorem states that the entry never returns `Overflow` from these checks |
| `Node::string_property` fails with `BadString` for a value without a NUL or whose bytes before the first NUL are not UTF-8, before `BadProperty` for a byte after that NUL | Format and bounds, lines 206 to 209, lists both errors; step 6, lines 346 to 349, refers to them | The order of the prototype: `string_property` in `src/fdt/nodes.rs`, lines 140 to 150 |
| `Node::reg` checks the parent, `BadTree`, then the `reg`, `MissingProperty`, then the address cells and the size cells of the parent, `BadProperty`; `Node::ranges` and `dma_ranges` check the parent, then the node's address cells, the parent's address cells and the node's size cells; `Node::translate_reg` checks the parent, then translates through each bus from the nearest and checks the end of the result | Lines 607 and 608, 624 to 632 and Work bounds, lines 684 to 691, which give the lookups in this order; the error table gives `BadTree` to a node without a parent where an entry needs one, line 259 | The order of the prototype: `reg`, `address_map` and `translate_reg` in `src/fdt/nodes.rs`, lines 183 to 219 |
| A no-operation token counts toward `MAX_TOKENS`; when `MAX_TOKENS` tokens have been read and none was the end token, the parse fails with `LimitExceeded` without decoding another | Lines 154 and 155 and 315 and 316; Terms counts the no-operation among the tokens, lines 41 and 42 | The prototype reads at most `MAX_TOKENS` tokens and fails after them, `src/fdt/parser.rs`, lines 168 and 227 |
| The letters and digits of node and property names are the ASCII ones; `@` may occur any number of times in a node name | Lines 156 to 160 | Tables 2.1 and 2.2 of DTSpec v0.4, which the contract cites, list exactly `0-9`, `a-z` and `A-Z` with the punctuation; the prototype checks the same set, `src/fdt/format.rs`, lines 9 to 14 |
| UTF-8 is the encoding of a sequence of Unicode scalar values, so an overlong encoding, a surrogate and a code point above `U+10FFFF` are not UTF-8 | Lines 156, 158 and 206 to 208 | Lean core's `ByteArray.IsValidUTF8`, which `String.fromUTF8?` decides, is that definition; it is the one of the Unicode standard and of Rust's `str::from_utf8` |
| `Fdt::find_node` checks the form of the whole path first; then, component by component, a component without a match ends the lookup with none, and the components after it are not looked up | Lines 199 to 203 and step 8, line 360 | The order of the prototype: `find_node` in `src/fdt/nodes.rs`, lines 19 to 43 |
| `Fdt::find_node("/")` gives the first node of the structure block | Lines 150 to 153: the block holds one root, a begin-node token with an empty name | A begin node outside every node is the root and a second one fails with `BadTree` (line 259), so the first node of an accepted tree is its root |
| `Node::translate_reg` of a child of the root translates nothing and returns the span after the check of its end | Lines 630 to 632 | The root has no parent bus, so no `ranges` applies |
| The tree that the parse returns is an abstract value: the header's `totalsize`, the reservation entries and the nodes with their names, parents and properties | Terms, lines 29 to 32, where the tree borrows the bytes | The entries read only these values; the borrowed view of the implementation corresponds to this value |
| Loops on fuel: the reservation map reads at most `MAX_RESERVATIONS + 1` entries, the walk at most `MAX_TOKENS` tokens, a string at most the bytes up to the end of its block, and `Node::translate_reg` at most `MAX_DEPTH` buses; out of fuel, the reservation map and the translation fail with `LimitExceeded` | Work bounds, lines 669 to 691 | The reservation map ends within the limit of lines 147 and 148, and on a tree that the parse accepted no node lies deeper than `MAX_DEPTH - 1` (lines 165 and 166), so neither runs out there; a hand-written tree with a cycle of parents does |

### Vector notation

The vector file holds the cases of
[legacy test vectors](contract.md#legacy-test-vectors) in the
[notation](contract.md#notation) of the contract. Where the notation does not
say how a case of these vectors is written, the file writes it as follows,
and the replay reads it so.

| Form | Meaning | Vectors |
| --- | --- | --- |
| `entry=parse dtb=<bytes> ask=` | The case asks only whether the parse accepts the tree: `result=ok` or `result=err` | `fdt-parser-1`, and the accepted trees of `fdt-parser-7` to `fdt-parser-9` |
| `entry=parse dtb=<bytes> ask=error` | A rejection also names its error, `result=err error=Error::<variant>`; an accepted tree gives `result=ok` | `fdt-parser-2` to `fdt-parser-5` and the rejected trees of `fdt-parser-9` |
| `entry=parse dtb=<bytes> ask=discover_memory,reg,ranges,dma_ranges` | The case calls `discover_memory` and `reg`, `ranges` and `dma_ranges` of every node when the parse accepts the tree; once they have returned, `result=returned` | `fdt-parser-6` |
| `entry=string_property dtb=<bytes> node=<path> name=<name> ask=value` | `value` is the string, or `-` for none | `fdt-parser-7` |
| `entry=translate_reg dtb=<bytes> node=<path> span=<span> ask=span` | `span` is the translated span; the argument is the first span of the node's `reg`, as the test takes it | `fdt-translation-1` |
| `entry=dma_ranges dtb=<bytes> node=<path> ask=to_parent(<span>)` | A query of the map: `to_parent(<span>)=<span>`, or `=Error::<variant>` when the query fails | `fdt-translation-1` |

The vector `fdt-parser-8` places the tree at an odd host address. The parse
reads the bytes one at a time (lines 141 to 143), so the address is no input
of the specification, and the case holds the bytes alone.

## Contract correspondence

| Contract | Lean, below `Krepi.Spec.Fdt` |
| --- | --- |
| `Fdt::parse`, [format and bounds](contract.md#format-and-bounds) | `Fdt.parse` |
| Step 1 of the error order: the header and the blocks | `header`, `block` |
| Step 2: the reservation map | `reservationMap`, `reservationsFrom` |
| Step 3: the tokens | `structureNodes`, `walkTokens`, `decodeToken`, `Walk.place` |
| `Fdt::nodes`, `find_node`, `reservations`, `total_size` | `Fdt.nodes`, `Fdt.findNode`, `Fdt.reservations`, `Fdt.totalSize` |
| `Node::name`, `parent`, `property`, `string_property`, `enabled`, `address_cells`, `size_cells` | `Node.name`, `Node.parent`, `Node.property`, `Node.stringProperty`, `Node.enabled`, `Node.addressCells`, `Node.sizeCells` |
| `Node::reg`, `ranges`, `dma_ranges`, `translate_reg` | `Node.reg`, `Node.ranges`, `Node.dmaRanges`, `Node.translateReg` |
| `cells_u64`, `Reg::new`, `AddressMap::new`, `kind`, `to_parent`, `to_child` | `cellsU64`, `Reg.new`, `AddressMap.new`, `AddressMap.kind`, `AddressMap.toParent`, `AddressMap.toChild` |
| Step 7 of the error order: translation | `cellsU64`, `Reg.new` with `regEntry`, `AddressMap.new` with `window`, `AddressMap.translate` with `throughWindows` |
| Step 8: `Fdt::find_node` | `Fdt.findNode`, `Fdt.descend` |
| `Span::new`, `end`, `contains`, the value type `Span` and [the term](contract.md#terms) | `Span.new`, `Span.endAddr`, `Span.contains`, `Span`, `Span.Valid` |
| The value types `Fdt`, `Node`, `Error`, `PlanError` | `Fdt`, `Node`, `Error`, `PlanError` |
| The nine limits | `MAX_BLOB_SIZE`, `MAX_DEPTH`, `MAX_TOKENS`, `MAX_PROPERTIES`, `MAX_PROPERTY_NAME`, `MAX_RESERVATIONS`, `MAX_MEMORY_REGIONS`, `MAX_RESERVED_REGIONS`, `PI5_MAX_BLOB_SIZE` |
| [Rejection](contract.md#rejection-and-error-priority), rule 1: no partial result | The result type `Except Error α` |
| Rule 2: no panic | Every definition is total; no definition uses `panic!`, `get!` or a partial function |
| Rule 3: no choice among duplicates | `DuplicateProperty` in `Walk.place`, `AmbiguousMapping` in `Fdt.descend` and `throughWindows` |
| [Check and execute](contract.md#check-and-execute) | Every entry is a function of its arguments; a `Reg` and an `AddressMap` hold only checked spans |
| [Work bounds](contract.md#work-bounds) | The fuel of each loop: `MAX_RESERVATIONS + 1`, `MAX_TOKENS`, the size of a block and `MAX_DEPTH` |

## Requirement correspondence

### FDT-R01

[FDT-R01](requirements.md#fdt-r01), the bounded parse of an untrusted tree,
is `Fdt.parse` with the limits of `Basic`: the size of the tree in `header`,
the reservation entries in `reservationsFrom`, the tokens in `walkTokens`, and
the depth, the properties of a node and the length of a property name in
`Walk.place` and `decodeToken`. The replay of
[`Krepi.SpecTests.Fdt.Replay`](../../../../verification/Krepi/SpecTests/Fdt/Replay.lean)
answers the cases of `fdt-parser-1` to `fdt-parser-9` in the
[vector file](../../../../verification/vectors/boot-platform/fdt.vectors)
through it. The statements that each limit accepts an input at the limit and
rejects one 1 above it with the error of the contract are stated with the
properties of the component; no theorem is registered yet.

### FDT-R02

[FDT-R02](requirements.md#fdt-r02), rejection without partial results: an
entry returns `Except Error α`, so a failure carries one error and no value,
and every definition is total, so no input makes an entry panic. The error
orders of steps 1 to 3, 7 and 8 are the order of the checks in each
definition. Duplicates are rejected, never chosen: two properties of one name
in `Walk.place`, two sibling nodes on a path in `Fdt.descend`, and two windows
that hold a request in `throughWindows`. The vectors `fdt-parser-1` and
`fdt-parser-6` replay the prefixes and the single-byte changes of the minimal
tree. No theorem is registered yet.

### FDT-R09

[FDT-R09](requirements.md#fdt-r09), address translation, is `Translate`:
`reg` in the cells of the parent, `ranges` and `dma-ranges` with the node's
own cells on the child side, none of them inherited from an ancestor further
up; `cellsU64` that never drops a cell; the kinds of a map; the one window
that holds the whole request; and separate maps for CPU addresses and the
addresses of devices. The replay answers the cases of `fdt-translation-1`.
No theorem is registered yet.

## Dependencies

- Lean core of the Lean version in `verification/lean-toolchain`; the modules
  import neither Mathlib nor the Aeneas library nor generated definitions.
- The [requirements](requirements.md) and the [contract](contract.md) of the
  component, and the format of chapter 5 and the names of sections 2.2.1 and
  2.2.4 of DTSpec v0.4, which the contract cites.
- The [vector file](../../../../verification/vectors/boot-platform/fdt.vectors)
  and its replay,
  [`Krepi.SpecTests.Fdt.Replay`](../../../../verification/Krepi/SpecTests/Fdt/Replay.lean),
  which imports these modules.
