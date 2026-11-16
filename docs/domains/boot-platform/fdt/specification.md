---
specifications:
  - Krepi.Spec.Fdt.Basic
  - Krepi.Spec.Fdt.Bytes
  - Krepi.Spec.Fdt.Parse
  - Krepi.Spec.Fdt.Nodes
  - Krepi.Spec.Fdt.Translate
  - Krepi.Spec.Fdt.Discovery
  - Krepi.Spec.Fdt.Pi5
  - Krepi.Spec.Fdt.Cpus
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

This part covers the parse, the node access, the address translation, the
memory discovery, the Pi 5 boot memory and the CPU nodes: the entries of the
rows of `Fdt::parse`, of the node access, of `Fdt::discover_memory`, of
`Fdt::discover_pi5_boot_memory`, of `Pi5BootMemory::find_available`, of
`Fdt::discover_cpus` and of the translation in the
[entry table](contract.md#entry-points), with the functions of `Span`, the
value types that they use and the limits. The boot memory map and the
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
| The address of a Pi 5 hand-over tree, and the size, alignment, minimum and limit of `Pi5BootMemory::find_available` | `UInt64` | $[0, 2^{64})$ |
| A value of `MPIDR_EL1` given to `CpuProfile::logical_id`, a logical ID, the index given to `CpuTopology::affinity`, and an affinity | `UInt64` | $[0, 2^{64})$ |
| A count: `MemoryMap::dynamic`, `CpuTopology::count` | `UInt64` | $[0, 2^{64})$ |
| The `interrupts` given to `CpuTopology::validate_qemu_timers` | `ByteArray` | Every byte string |
| A CPU profile | `CpuProfile`, three constructors | Each profile |
| A Pi 5 boot memory, a memory map, a CPU topology given to their queries | `Pi5BootMemory`, `MemoryMap`, `CpuTopology` | Every value, also one that no discovery returns |

Inside a definition, arithmetic is on `Nat`, which does not wrap. Each sum
that the contract checks against 64 bits is compared with $2^{64}$ before it
is used (`checkedAdd`, `Span.new`, `Span.Valid`, `alignUp`), as the checked
arithmetic of the implementation does, and a width check of one cell compares
with $2^{32}$. Offsets inside a tree stay below `MAX_BLOB_SIZE` and need no
check. A count is computed on `Nat` and is below the number of nodes of the
tree, at most `MAX_TOKENS` for a tree that the parse accepted, so it fits its
width.

The functions are total, so "for every input the entry returns" holds of the
specification by construction, which is why the vector `fdt-parser-6` only
checks that the entries return. A tree that the parse did not build, such as
a value written by hand, is still an input of the node entries and the
discoveries, and a `Pi5BootMemory` or a `CpuTopology` that no discovery
returned is still an input of their queries: they return for these as well,
and the results that the contract fixes are those on trees that the parse
accepted and on the values that the discoveries returned.

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

### Discovery

[`Discovery.lean`](../../../../verification/Krepi/Spec/Fdt/Discovery.lean):
`Fdt::discover_memory` of [memory discovery](contract.md#memory-discovery) and
step 4 of the error order.

- **Values.** `ReservedRegion` is a span with the flags `noMap` and
  `reusable`. `MemoryMap` holds the RAM ranges in tree order, the reserved
  regions, those of the reservation map first and then those of
  `/reserved-memory` in tree order, and the number of dynamic reservations;
  its fields are `MemoryMap::ram`, `reserved` and `dynamic`.
- **Spans.** `Span.touches` holds when two spans are nonempty and share an
  address; `inOneRange` when one span of a list holds a span.
- **RAM.** `ramOfChild` reads one child of the root in the order of step 4:
  its `device_type`; for a memory node, by name or by `device_type`, its
  `status`, a disabled one skipped; the binding; its `reg`, whole; then each
  range through `addRam`, which checks `EmptyRegion`, `Overlap` with the
  earlier ranges and `LimitExceeded` beyond `MAX_MEMORY_REGIONS`.
- **Reserved regions.** `pushReserved` checks `LimitExceeded` beyond
  `MAX_RESERVED_REGIONS`, for the entries of the reservation map and the
  spans of `/reserved-memory` together. `reservedMemoryBinding` checks the
  cells and the empty `ranges` of `/reserved-memory`; `reservedOfChild`
  reads one of its children: `status`, the flags through `Node.flag`, then
  `reg` and `size`, where `size` without `reg` counts a dynamic reservation
  and reads nothing more, and each span of the `reg` through
  `addReservedSpan`.
- **The discovery.** `Fdt.discoverMemory` runs step 4 in order: the
  reservation map, the root, the children of the root, `NoMemory`, and
  `Fdt.reservedMemory`, which finds `/reserved-memory`, checks its binding
  and then its `status`, and walks its children.

### Pi5

[`Pi5.lean`](../../../../verification/Krepi/Spec/Fdt/Pi5.lean):
`Fdt::discover_pi5_boot_memory` of
[memory discovery](contract.md#memory-discovery), its queries
`Pi5BootMemory::is_available` and `find_available` of
[boot memory map](contract.md#boot-memory-map), and steps 5 and 8 of the
error order.

- **The value.** `Pi5BootMemory` holds the memory map of the tree, the span
  of the tree, the span of the image and the sum of the RAM ranges, which
  `Pi5BootMemory::dtb`, `image` and `ram_bytes` give; `ram`, `reserved` and
  `dynamic` are those of its memory map.
- **The root `compatible`.** `checkPi5Compatible` checks the final NUL, then
  each entry, split at the NUL bytes by `splitAtNul`, in order through
  `compatibleEntries`, then the two names that the list must hold.
- **The discovery.** `Fdt.discoverPi5BootMemory` runs step 5 in order: the
  size of the tree, its address, the root and its cells, `compatible`, the
  span of the tree, the image, the image on the tree, the memory discovery,
  the tree and the image each inside one RAM range, and the sum of the RAM
  ranges with `checkedAdd`.
- **Availability.** `Pi5BootMemory.exclusions` lists the image, the tree
  and every reserved region; `Pi5BootMemory.isAvailable` checks the span,
  `EmptyRegion` then `Overflow`, and then holds when one RAM range holds it
  and it touches no exclusion.
- **Selection.** `Pi5BootMemory.findAvailable` checks the size and the
  bound, `EmptyRegion`, and the alignment, `BadAlignment`, with
  `isPowerOfTwo`; `searchRanges` takes the RAM ranges in tree order and
  starts each at the greater of its start and the minimum, aligned up by
  `alignUp`; `searchRange` tries the candidates of one range: a candidate
  that touches no exclusion is the span, and otherwise the next starts at the
  furthest end of the exclusions that it touches, aligned up. At most
  `Q + 3` candidates are tried in a range, where `Q` is the number of
  reserved regions.

### Cpus

[`Cpus.lean`](../../../../verification/Krepi/Spec/Fdt/Cpus.lean): the
[CPU nodes](contract.md#cpu-nodes) and step 6 of the error order.

- **Profiles.** `CpuProfile` has the constructors `qemuHvc`, `qemuSmc` and
  `pi5`. `CpuProfile.affinityShift` and `CpuProfile.conduit` give the
  affinity level and the PSCI conduit; `CpuProfile.idOf` gives the logical
  ID below 4 whose `id << affinity_shift` is an affinity, and
  `CpuProfile.logicalId` gives it for the affinity fields of a value of
  `MPIDR_EL1`, masked with `AFFINITY_MASK`.
- **The topology.** `CpuTopology` holds the profile and the number of CPUs,
  which `CpuTopology::profile` and `count` give. `CpuTopology.affinity` and
  `CpuTopology.validateQemuTimers` are `CpuTopology::affinity` and
  `validate_qemu_timers`; the latter compares the bytes with the timer
  records of the profile, `CpuProfile.timerInterrupts` encoded by `be32`.
- **The discovery.** `Fdt.discoverCpus` runs step 6 in order: `/cpus`, its
  `status` and size cells, its address cells, each child through
  `cpuOfChild`, the set of IDs through `idsComplete`, and `/psci` with its
  `status`, its `method` and its `compatible`, which must be one of the
  byte lists of `PSCI_COMPATIBLE`.

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
| The memory discovery reads the `device_type` of every child of the root, `/chosen` included, and the `status` only of a memory node, by name or by `device_type`; a child that is neither adds nothing. What no entry reads of `/chosen` are its other properties, such as the seeds that QEMU writes | Step 4, lines 319 and 320, and lines 399 to 403; Determinism, lines 751 to 754, where no entry reads `/chosen` | The order of the prototype, which the contract adopts: `discover_memory` in `src/fdt/discovery.rs`, lines 82 to 92 |
| The `reg` of a memory node or of a child of `/reserved-memory` is read whole, with every error of `Node::reg`, before any of its ranges or spans is added | Step 4, lines 320 and 321 and 324 and 325, "its `reg`, and each of its ranges"; `Reg::new` checks every entry before it gives one, lines 605 to 607 | The contract's rule of `Reg::new`; the prototype reads the entries one at a time, so an error of a later entry would follow the ranges before it |
| Each RAM range is checked for size 0, `EmptyRegion`, then for an address shared with an earlier range, `Overlap`, then for the capacity, `LimitExceeded`; each span of `/reserved-memory` for size 0 and then the capacity | Step 4, lines 321 and 325, and lines 404 to 407 | The order in which step 4 lists them, which is that of the prototype: `add_ram` and `add_reserved` in `src/fdt/discovery.rs`, lines 33 to 60 |
| An entry of the reservation map is a reserved region after the check of the capacity alone; the parse has checked that it is nonempty and ends within 64 bits | Step 4, lines 317 and 318; step 2, lines 298 to 302 | The step names only `LimitExceeded` for these entries |
| The memory discovery and the Pi 5 boot memory find the root first; a tree without one, which the parse never builds, fails with `BadTree` | Lines 692 and 693 and 699, the lookup of the root; the error table gives `BadTree` to a tree without a root, line 259 | The parse rejects an end token without a root, line 259, so the lookup always finds it on a tree that the parse accepted |
| `/reserved-memory`: its binding, all of whose rules give `BadProperty`, before its `status`; a disabled one holds no reservation and its children are not read. A child: its `status`, then its flags, then neither `reg` nor `size`, `MissingProperty`; a child with `size` and without `reg` is counted as a dynamic reservation after its flags, and its `size` is not read | Step 4, lines 322 to 325, and lines 409 to 425 | The order of step 4, with a disabled container holding no reservation, lines 411 and 412 |
| Two spans touch when both are nonempty and share an address; two spans are disjoint when they share none | "touches", lines 459 and 460 and 551 and 552, and "disjoint", lines 405 and 456, which Terms does not define | The plain meaning as sets of addresses; for the nonempty spans that the entries compare, it is the half-open intersection that the prototype's `overlaps` computes |
| The Pi 5 queries know only the image and the tree as the board gives them, and the reserved regions; further boot storage, such as a boot bundle that the board gives as a span of its own, is excluded by the boot memory map alone. The image span is the one that the board passes, with its BSS and stacks and any read-only part of the image within it | Lines 449 and 461 to 463 and 60 to 63 | The queries take no further span, line 447; a page-aligned read-only part of the kernel image lies within the image span that the board passes |
| An empty bound of `Pi5BootMemory::find_available` is a minimum at or above the limit; an alignment is a power of two when it is one of $2^0$ to $2^{63}$ | Step 8, line 362, and line 550; the error table, line 257 | The bound is the interval $[minimum, limit)$, line 551, which is empty exactly then |
| `Pi5BootMemory::find_available` fails with `Overflow` when an alignment of its search leaves 64 bits: the first candidate of a RAM range, the greater of its start and the minimum, or the end of the furthest exclusion that a candidate touches, aligned up. The search meets them in the order of the RAM ranges and of their candidates, so a span found earlier is returned first. A candidate whose end leaves 64 bits or passes the bound ends the search in its range without an error | Step 8, lines 362 and 363, "then `Overflow`"; the vector `fdt-pi5-selection-2`, line 997, where the size `0xffffffffffffffff` gives none | The order of the prototype, which the contract adopts: `find_available` and `align` in `src/fdt/pi5/selection.rs`, lines 24 to 61; the span that the search returns is the one of the rule of lines 549 to 554, which a theorem states |
| The search of a RAM range moves from a candidate to the end of the furthest exclusion that it touches, aligned up, and tries at most `Q + 3` candidates; out of fuel it fails with `LimitExceeded` | Work bounds, lines 705 to 707 | Every start between the candidate and that end touches that exclusion, so no span is passed over; each move passes at least one of the `Q + 2` exclusions for good, so the fuel is never used up |
| The `status` of `/cpus` is read before its size cells | Step 6, lines 338 and 339, "disabled or with size cells other than 0" | The order of the prototype: `discover_cpus` in `src/fdt/cpus.rs`, line 94 |
| A CPU node fails at "its ID" when its `reg` is not `id << affinity_shift` for an ID below 4, flag bits included, or when an earlier CPU node has its ID; "the set of IDs" then checks the number of CPU nodes and that the IDs are `0` to `count - 1` | Step 6, lines 344 and 345; lines 571 to 579; rule 3, lines 235 and 236 | The order of the prototype: `discover_cpus` in `src/fdt/cpus.rs`, lines 110 to 113 and 123 to 128 |
| The `enable-method` of CPU 0 on QEMU virt is not read | Lines 576 and 577 | The prototype reads it only for the other CPUs and on the Pi 5, `src/fdt/cpus.rs`, lines 115 to 118 |
| `/psci`: its `status`, then its `method`, then its `compatible`; the `compatible`, a list of strings, is compared as bytes with the three lists, each string with its NUL, so any other value, also one that is not UTF-8, fails with `BadProperty`. The properties that fail as `Node::string_property` does are those that hold one string: `device_type`, `status`, the `compatible` of a CPU node, `enable-method` and `method` | Step 6, lines 346 to 349, and lines 580 to 584 | `Node::string_property` rejects a byte after the first NUL, lines 206 to 209, so it cannot read a list; the order and the comparison of the prototype: `src/fdt/cpus.rs`, lines 129 to 142 |
| `CpuTopology::validate_qemu_timers` accepts exactly the bytes of the records of the profile; the flags `((1 << count) - 1) << 8 \| 4` are a 32-bit cell, computed at that width | Lines 590 to 596; the error table, line 265 | A topology of the discovery has 1, 2 or 4 CPUs, for which the shift is exact |
| A count, a logical ID, the index of `CpuTopology::affinity` and an affinity are 64-bit values | The entry table, lines 92 and 95, which gives no width | The width of the target's addresses and sizes, as for the values of the first part |

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
| `entry=parse dtb=<bytes> ask=total_size` | `total_size` is the `totalsize` of the tree, in decimal, as the test compares it with the length of the bytes | `fdt-discovery-1` |
| `entry=discover_memory dtb=<bytes> ask=ram,reserved,dynamic` | `ram` is the list of RAM ranges; `reserved` the list of reserved regions, each `<span>/<flag>`; `dynamic` the number of dynamic reservations, in decimal | `fdt-parser-7`, `fdt-parser-8`, `fdt-discovery-1` to `fdt-discovery-6` |
| `entry=reg dtb=<bytes> node=<path> ask=entries` and `entry=Reg::new bytes=<bytes> address_cells=<n> size_cells=<n> ask=entries,end(<i>)` | `entries` is the list of the spans of the value; `end(<i>)` is `Span::end` of the entry `i`, counted from 0 | `fdt-discovery-2`, `fdt-translation-4`, `fdt-translation-5` |
| `entry=AddressMap::new bytes=<bytes> child_cells=<n> parent_cells=<n> size_cells=<n> ask=kind,to_parent(<span>)` | `bytes=-` is an absent property and `bytes=` an empty one; `kind` is `Absent`, `Identity` or `Windows` | `fdt-translation-2` to `fdt-translation-4` |
| `entry=cells_u64 bytes=<bytes> cells=<n> ask=value` | `value` is the number, in hexadecimal | `fdt-translation-4` |
| `entry=discover_pi5_boot_memory dtb=<bytes> dtb_address=<address> image=<span> ask=...` | The fields of the Pi 5 boot memory, `ram_bytes` in hexadecimal, and the query `is_available(<span>)`, `true`, `false` or `Error::<variant>` | `fdt-pi5-1` to `fdt-pi5-4`, `fdt-pi5-boundaries-1` to `fdt-pi5-boundaries-5` |
| `entry=find_available dtb=<bytes> dtb_address=<address> image=<span> size=<n> alignment=<n> minimum=<address> limit=<address> ask=span` | `span` is the selected span, `-` for none; the case may also ask `is_available(<span>)` of the same Pi 5 boot memory. The four arguments are written in hexadecimal, also where the test writes them in decimal | `fdt-pi5-selection-1` to `fdt-pi5-selection-3` |
| `entry=discover_cpus dtb=<bytes> profile=<profile> ask=count,profile,affinity(<i>)` | A profile is `QemuHvc`, `QemuSmc` or `Pi5`; `count` is decimal, `affinity(<i>)` hexadecimal or `-` for none | `fdt-cpus-1` to `fdt-cpus-4` |
| `entry=validate_qemu_timers dtb=<bytes> profile=<profile> interrupts=<bytes> ask=` | The topology of `discover_cpus` on the tree checks the records: `result=ok` or `result=err` | `fdt-cpus-6` |
| `entry=logical_id profile=<profile> mpidr=<value> ask=id` | `id` is the logical ID in decimal, `-` for none | `fdt-cpus-5` |

The vector `fdt-parser-8` places the tree at an odd host address. The parse
reads the bytes one at a time (lines 141 to 143), so the address is no input
of the specification, and the case holds the bytes alone.

A case asks the fields and queries that its test asserts, each whole: where
the test asserts a part of a field, such as the number of RAM ranges, one of
them or a flag of a reserved region, the case asks the whole field, and the
file writes it from the inputs that the row of the contract states. Where the
row states a property of a selected span rather than the span, the file
writes the span that the rule of lines 549 to 554 gives, computed by hand: in
`fdt-pi5-selection-1`, the span that starts at `0xa0000` is `0xa0000+0x2000`,
of the size asked, and the span at or above the end of the tree is
`0x201000+0x1000`, since the tree, at `0x200000`, ends below `0x201000`; in
`fdt-pi5-selection-3`, the span that starts at `0x480000` is
`0x480000+0x8000`.

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
| `Fdt::discover_memory`, `MemoryMap` with `ram`, `reserved` and `dynamic`, [memory discovery](contract.md#memory-discovery) | `Fdt.discoverMemory`, `MemoryMap`, `MemoryMap.ram`, `MemoryMap.reserved`, `MemoryMap.dynamic` |
| Step 4: `Fdt::discover_memory` | `Fdt.discoverMemory` with `pushReserved`, `ramOfChild`, `addRam`, `Fdt.reservedMemory`, `reservedMemoryBinding`, `reservedOfChild` and `addReservedSpan` |
| `Fdt::discover_pi5_boot_memory`, `Pi5BootMemory` with `ram`, `reserved`, `dynamic`, `dtb`, `image`, `ram_bytes` and `is_available` | `Fdt.discoverPi5BootMemory`, `Pi5BootMemory`, `Pi5BootMemory.ram`, `Pi5BootMemory.reserved`, `Pi5BootMemory.dynamic`, `Pi5BootMemory.dtb`, `Pi5BootMemory.image`, `Pi5BootMemory.ramBytes`, `Pi5BootMemory.isAvailable` |
| Step 5: `Fdt::discover_pi5_boot_memory` | `Fdt.discoverPi5BootMemory` with `checkPi5Compatible` and `compatibleEntries` |
| `Pi5BootMemory::find_available`, [boot memory map](contract.md#boot-memory-map) | `Pi5BootMemory.findAvailable` with `searchRanges`, `searchRange`, `alignUp` and `isPowerOfTwo` |
| Step 8: `Pi5BootMemory::is_available` and `find_available` | `Pi5BootMemory.isAvailable`; `Pi5BootMemory.findAvailable`, whose `Overflow` comes from `alignUp` |
| `Fdt::discover_cpus`, `CpuTopology` with `count`, `profile`, `affinity` and `validate_qemu_timers`, and `CpuProfile::logical_id`, `affinity_shift` and `conduit`, [CPU nodes](contract.md#cpu-nodes) | `Fdt.discoverCpus`, `CpuTopology`, `CpuTopology.count`, `CpuTopology.profile`, `CpuTopology.affinity`, `CpuTopology.validateQemuTimers`, `CpuProfile.logicalId`, `CpuProfile.affinityShift`, `CpuProfile.conduit` |
| Step 6: `Fdt::discover_cpus` | `Fdt.discoverCpus` with `cpuOfChild` and `idsComplete` |
| `Span::new`, `end`, `contains`, the value type `Span` and [the term](contract.md#terms) | `Span.new`, `Span.endAddr`, `Span.contains`, `Span`, `Span.Valid` |
| The value types `Fdt`, `Node`, `ReservedRegion`, `MemoryMap`, `Pi5BootMemory`, `CpuProfile`, `CpuTopology`, `Error`, `PlanError` | `Fdt`, `Node`, `ReservedRegion`, `MemoryMap`, `Pi5BootMemory`, `CpuProfile`, `CpuTopology`, `Error`, `PlanError` |
| The nine limits | `MAX_BLOB_SIZE`, `MAX_DEPTH`, `MAX_TOKENS`, `MAX_PROPERTIES`, `MAX_PROPERTY_NAME`, `MAX_RESERVATIONS`, `MAX_MEMORY_REGIONS`, `MAX_RESERVED_REGIONS`, `PI5_MAX_BLOB_SIZE` |
| [Rejection](contract.md#rejection-and-error-priority), rule 1: no partial result | The result type `Except Error α` |
| Rule 2: no panic | Every definition is total; no definition uses `panic!`, `get!` or a partial function |
| Rule 3: no choice among duplicates | `DuplicateProperty` in `Walk.place`, `AmbiguousMapping` in `Fdt.descend` and `throughWindows`, `BadProperty` for two CPU nodes of one ID in `cpuOfChild`, `Overlap` for RAM ranges that share an address in `addRam` |
| [Check and execute](contract.md#check-and-execute) | Every entry is a function of its arguments; a `Reg` and an `AddressMap` hold only checked spans; the discoveries build their result while they check and return it only when every check passed |
| [Work bounds](contract.md#work-bounds) | The fuel of each loop: `MAX_RESERVATIONS + 1`, `MAX_TOKENS`, the size of a block, `MAX_DEPTH`, and `Q + 3` candidates in each RAM range of the selection; the memory discovery and the CPU discovery walk lists of nodes, the memory discovery twice |

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
orders of steps 1 to 8 are the order of the checks in each definition; the
discoveries build their result while they check and return it only at the
end, so a failure leaves nothing of it. Duplicates are rejected, never
chosen: two properties of one name in `Walk.place`, two sibling nodes on a
path in `Fdt.descend`, two windows that hold a request in `throughWindows`,
RAM ranges that share an address in `addRam`, and two CPU nodes of one
logical ID in `cpuOfChild`. The vectors `fdt-parser-1` and `fdt-parser-6`
replay the prefixes and the single-byte changes of the minimal tree, the
latter with the memory discovery and the node entries on every accepted
tree. No theorem is registered yet.

### FDT-R03

[FDT-R03](requirements.md#fdt-r03), memory discovery, is
`Fdt.discoverMemory`: the RAM ranges of the enabled memory nodes below the
root, read in the cells of the root and checked by `addRam`; disabled memory
nodes skipped by `ramOfChild` before their binding; the reserved regions of
the reservation map with `no-map` set and of the static children of
`/reserved-memory` with their flags; the binding of `/reserved-memory` in
`reservedMemoryBinding`; `no-map` with `reusable` refused in
`reservedOfChild`; and `NoMemory` for a tree without RAM. A reserved region
outside every RAM range is kept like any other. The capacities are
`MAX_MEMORY_REGIONS` in `addRam` and `MAX_RESERVED_REGIONS` in
`pushReserved`. The replay answers the cases of `fdt-discovery-1` to
`fdt-discovery-6`, `fdt-parser-7`, `fdt-pi5-boundaries-5` and
`fdt-pi5-selection-3`. No theorem is registered yet.

### FDT-R04

[FDT-R04](requirements.md#fdt-r04), dynamic reservations recorded and not
refused: `reservedOfChild` counts an enabled child of `/reserved-memory` with
`size` and without `reg` in `MemoryMap::dynamic` and reads neither its `size`
nor anything else of it, so the number of cells of its `size` is no reason
to reject the tree; a disabled one is skipped, and a child with `reg` and
`size` is static. `Pi5BootMemory::dynamic` is that of its memory map. The
replay answers the cases of `fdt-discovery-4`, `fdt-pi5-2` and `fdt-pi5-4`
with the outputs of the contract; `fdt-pi5-firmware-1`, whose input lies
outside the repository, has no line in the vector file. No theorem is
registered yet.

### FDT-R05

[FDT-R05](requirements.md#fdt-r05), the Pi 5 hand-over checks, is
`Fdt.discoverPi5BootMemory`: the limit `PI5_MAX_BLOB_SIZE`, the address a
multiple of 8, 2 address cells and 2 size cells at the root, the root
`compatible` in `checkPi5Compatible`, a nonempty image that shares no address
with the tree, and the tree and the image each inside one RAM range. Its
result holds the memory map, the spans of the tree and of the image and the
sum of the RAM ranges. `Pi5BootMemory.isAvailable` and
`Pi5BootMemory.findAvailable` give only spans inside one RAM range that touch
no exclusion, the image, the tree and every reserved region, so no span
bridges two RAM ranges or a hole. The replay answers the cases of
`fdt-pi5-1` to `fdt-pi5-4`, `fdt-pi5-boundaries-1` to
`fdt-pi5-boundaries-5` and `fdt-pi5-selection-1` to `fdt-pi5-selection-3`;
`fdt-pi5-firmware-2`, whose input lies outside the repository, has no line.
No theorem is registered yet.

### FDT-R06

[FDT-R06](requirements.md#fdt-r06), every RAM model of the Pi 5: the 1 to 3
RAM ranges of every model fit `MAX_MEMORY_REGIONS` in
`Fdt.discoverMemory`, and their sum, at most 16 GiB less 4 MiB, is
`Pi5BootMemory::ram_bytes`, computed with `checkedAdd`. The part of the
requirement that the boot memory map holds, through `MemoryPlan::all_ram`
and `from_pi5`, is specified with the boot memory map. No theorem is
registered yet.

### FDT-R08

[FDT-R08](requirements.md#fdt-r08), the CPU nodes, is `Cpus`:
`Fdt.discoverCpus` with `/cpus` enabled with 0 size cells, every CPU node an
enabled Cortex-A76 whose `reg` is the affinity of its logical ID in the
profile, IDs without a repeat in `cpuOfChild` and without a gap in
`idsComplete`, `psci` as the `enable-method` of every CPU but the first and
on the Pi 5 of every CPU, and `/psci` with the conduit of the profile and a
`compatible` of `PSCI_COMPATIBLE`; `CpuProfile.logicalId`, which masks the
flag bits of `MPIDR_EL1`; and `CpuTopology.validateQemuTimers`, which accepts
only the timer records of QEMU virt for the admitted CPUs. The replay answers
the cases of `fdt-cpus-1` to `fdt-cpus-6`. No theorem is registered yet.

### FDT-R09

[FDT-R09](requirements.md#fdt-r09), address translation, is `Translate`:
`reg` in the cells of the parent, `ranges` and `dma-ranges` with the node's
own cells on the child side, none of them inherited from an ancestor further
up; `cellsU64` that never drops a cell; the kinds of a map; the one window
that holds the whole request; and separate maps for CPU addresses and the
addresses of devices. The replay answers the cases of `fdt-translation-1` to
`fdt-translation-5`. No theorem is registered yet.

### FDT-R10

[FDT-R10](requirements.md#fdt-r10), the same result on every boot: every
entry is a function of the bytes of the tree and of its arguments, with no
choice, so equal inputs give equal results. The parse checks the length
and the name of every property but never interprets its value, so the
values of the seeds that QEMU writes into `/chosen` do not decide whether it
accepts a tree; its result holds them as the values of their properties.
`Fdt.discoverMemory` reads of `/chosen` only its `device_type`, as it does of
every child of the root, so the seeds reach none of the RAM ranges, the
reserved regions and the number of dynamic reservations.
`MemoryPlan::all_ram` is specified with the boot memory map. No theorem is
registered yet.

## Dependencies

- Lean core of the Lean version in `verification/lean-toolchain`; the modules
  import neither Mathlib nor the Aeneas library nor generated definitions.
- The [requirements](requirements.md) and the [contract](contract.md) of the
  component, and, as the contract cites them, the format of chapter 5, the
  names of sections 2.2.1 and 2.2.4 and the nodes of sections 3.4, 3.5, 3.7
  and 3.8 of DTSpec v0.4, and the affinity fields of `MPIDR_EL1` of the Arm
  Architecture Reference Manual.
- The [vector file](../../../../verification/vectors/boot-platform/fdt.vectors)
  and its replay,
  [`Krepi.SpecTests.Fdt.Replay`](../../../../verification/Krepi/SpecTests/Fdt/Replay.lean),
  which imports these modules.
