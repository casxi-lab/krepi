---
specifications:
  - Krepi.Spec.Fdt.Basic
  - Krepi.Spec.Fdt.Bytes
  - Krepi.Spec.Fdt.Parse
  - Krepi.Spec.Fdt.Nodes
  - Krepi.Spec.Fdt.Translate
  - Krepi.Spec.Fdt.Discovery
  - Krepi.Spec.Fdt.BootMemory
  - Krepi.Spec.Fdt.Cpus
  - Krepi.Spec.Fdt.Plan
  - Krepi.Spec.Fdt.Boot
  - Krepi.Spec.Fdt.Witnesses
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

The modules cover every row of the [entry table](contract.md#entry-points):
the parse, the node access, the address translation, the memory discovery,
the boot memory, the CPU nodes and the boot memory map, with the
functions of `Span`, the value types and the limits; and the publication of
the shared results that the [state fields](contract.md#state-fields) name.
The entries that check a hand-over tree or the CPU nodes take the profile
that the board gives as an argument, and the specification holds for every
profile; the profiles of the Pi 5 and of QEMU virt are test data of
`Boards` below `Krepi/SpecTests/Fdt`.

The invariants and the properties of the component are stated in two
modules below
[`verification/Krepi/SpecProperties/Fdt/`](../../../../verification/Krepi/SpecProperties/Fdt/),
`Invariants` and `Properties`, which import Lean core and the specification
alone and lie on the statement side. Each proposition that a theorem is to
prove is a definition there, registered in
[`verification/statements.json`](../../../../verification/statements.json)
with its theorem below
[`verification/Krepi/Proofs/Fdt/`](../../../../verification/Krepi/Proofs/Fdt/),
whose proof is planned: it is `sorry` until a proof pull request proves it
([statements and proofs](../../../formal-verification.md#statements-and-proofs)).
The specification tests, for each requirement one input that the
specification must accept and one that it must reject, are stated the same
way in `Stp` below
[`verification/Krepi/SpecTests/Fdt/`](../../../../verification/Krepi/SpecTests/Fdt/),
on trees that `Builder` there writes, with their planned theorems in
`Krepi.Proofs.Fdt.Stp`; `Replay` there replays the vectors. The witnesses
that the specification is not vacuous are theorems of `Witnesses` below
`Krepi/Spec/Fdt`, all proved there; the statements that its unreachable
error branches are never taken are planned ([Witnesses](#witnesses)).

## Widths and quantifiers

The component writes no state ([check and execute](contract.md#check-and-execute)):
every entry is a function of its arguments, and a failure returns one error
and nothing else, since a result is an `Except Error α` or an
`Except PlanError α`, which holds either a value or an error. The
modification set of every entry is empty. The shared results of the boot are
the state of `Boot`, whose transactions each change one field, once.

Each entry is stated for all of its inputs at their machine widths:

| Value | Lean type | Range |
| --- | --- | --- |
| The bytes given to `Fdt::parse`, a property value, the value of `cells_u64`, `Reg::new` and `AddressMap::new` | `ByteArray` of `UInt8` | Every byte string of every length |
| An address, a size, the value of `cells_u64`, `Fdt::total_size` and the eight limits | `UInt64` | $[0, 2^{64})$ |
| A cell, a cell count and a header word | `UInt32` | $[0, 2^{32})$ |
| A span | `Span`, two `UInt64` without an invariant | Every pair, also one whose end leaves 64 bits |
| A path and a property name | `String` | Every string |
| A node | `Node`, a tree with an index below its number of nodes | Every node of every tree |
| An absent or present property given to `AddressMap::new` | `Option ByteArray` | Both |
| The address of a hand-over tree, and the size, alignment, minimum and limit of `BootMemory::find_available` | `UInt64` | $[0, 2^{64})$ |
| A hand-over profile | `HandOverProfile`: a `UInt64` limit, a `UInt8` exponent of the alignment and the `ByteArray` of the required `compatible` entries | Every value |
| A value of `MPIDR_EL1` given to `CpuProfile::logical_id`, a logical ID, the index given to `CpuTopology::affinity`, and an affinity | `UInt64` | $[0, 2^{64})$ |
| A count: `MemoryMap::dynamic`, `CpuTopology::count` | `UInt64` | $[0, 2^{64})$ |
| The `interrupts` given to `CpuTopology::validate_timers` | `ByteArray` | Every byte string |
| A CPU profile | `CpuProfile`: a `PsciConduit`, an `AffinityLevel` of four, a `UInt8` set of CPU counts, a `Bool` and an optional `TimerInterrupts` of five `UInt32` numbers and a `UInt8` count | Every value |
| A boot memory, a memory map, a CPU topology given to their queries | `BootMemory`, `MemoryMap`, `CpuTopology` | Every value, also one that no discovery returns |
| The RAM banks, the boot storage and the further boot storage `more` given to the boot memory map, and its managed window | `List Span`, `Span` | Every list of every length, every span |
| The firmware reservations given to the boot memory map | `List ReservedRegion` | Every list of every length |
| A range given to `MemoryPlan::contains_ram`, `is_available` and `permits_backing` | `Span` | Every span; one that is empty or whose end leaves 64 bits lies in no bank |
| `MemoryPlan::described_bytes` and `managed_bytes` | `UInt64` | $[0, 2^{64})$; at most 16 GiB for a map that an entry built |
| A boot memory map given to its queries | `MemoryPlan` | Every value, also one that no entry builds |
| The boot state and the boot token | `BootState`, `BootToken` | Every state; the token of the boot CPU |

Inside a definition, arithmetic is on `Nat`, which does not wrap. Each sum
that the contract checks against 64 bits is compared with $2^{64}$ before it
is used (`checkedAdd`, `Span.new`, `Span.Valid`, `alignUp`, and in the boot
memory map `checkPlanSpan`, `pagesOf` and `admitBank`), as the checked
arithmetic of the implementation does, and a width check of one cell compares
with $2^{32}$. Offsets inside a tree stay below `MAX_BLOB_SIZE` and need no
check. A count is computed on `Nat` and is below the number of nodes of the
tree, at most `MAX_TOKENS` for a tree that the parse accepted, so it fits its
width.

The functions are total, so "for every input the entry returns" holds of the
specification by construction, which is why the vector `fdt-parser-6` only
checks that the entries return. A tree that the parse did not build, such as
a value written by hand, is still an input of the node entries and the
discoveries, and a `BootMemory` or a `CpuTopology` that no discovery
returned is still an input of their queries, and so is a `MemoryPlan` that
no entry built: they return for these as well, and the results that the
contract fixes are those on trees that the parse accepted and on the values
that the discoveries and the entries of the boot memory map returned.

## Model

### Basic

[`Basic.lean`](../../../../verification/Krepi/Spec/Fdt/Basic.lean): the
shared values.

- **Limits.** The eight constants of the entry table with the values of
  [format and bounds](contract.md#format-and-bounds): `MAX_BLOB_SIZE`
  2 MiB, `MAX_DEPTH` 32, `MAX_TOKENS` 65,536, `MAX_PROPERTIES` 512,
  `MAX_PROPERTY_NAME` 64, `MAX_RESERVATIONS` 128, `MAX_MEMORY_REGIONS` 32
  and `MAX_RESERVED_REGIONS` 128.
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
  earlier ranges and `LimitExceeded` beyond `MAX_MEMORY_REGIONS`. A name is
  a memory name, `isMemoryName`, when it is `memory` or its UTF-8 bytes
  begin with those of `memory@`.
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

### BootMemory

[`BootMemory.lean`](../../../../verification/Krepi/Spec/Fdt/BootMemory.lean):
`Fdt::discover_boot_memory` of
[memory discovery](contract.md#memory-discovery), its queries
`BootMemory::is_available` and `find_available` of
[boot memory map](contract.md#boot-memory-map), and steps 5 and 8 of the
error order.

- **The profile.** `HandOverProfile` holds the limit `maxBlobSize`, the
  exponent `alignmentLog2` of the alignment and the bytes `compatible`;
  `requiredEntries` gives the nonempty pieces of those bytes split at each
  NUL byte, the first and the last included: the entries that the root
  `compatible` must hold. Every value of the fields is a profile.
- **The value.** `BootMemory` holds the memory map of the tree, the span
  of the tree, the span of the image and the sum of the RAM ranges, which
  `BootMemory::dtb`, `image` and `ram_bytes` give, and the limit and the
  exponent of the alignment of the profile that the tree was checked with,
  which no entry gives; `ram`, `reserved` and `dynamic` are those of its
  memory map.
- **The root `compatible`.** `checkCompatible` checks the final NUL, then
  each entry, split at the NUL bytes by `splitAtNul`, in order through
  `compatibleEntries`, then that the list holds an entry of the bytes of
  each entry that the profile requires.
- **The discovery.** `Fdt.discoverBootMemory` runs step 5 in order: the
  size of the tree against the limit of the profile, its address against
  `2 ^ alignmentLog2`, the root and its cells, `compatible`, the
  span of the tree, the image, the image on the tree, the memory discovery,
  the tree and the image each inside one RAM range, and the sum of the RAM
  ranges with `checkedAdd`.
- **Availability.** `BootMemory.exclusions` lists the image, the tree
  and every reserved region; `BootMemory.isAvailable` checks the span,
  `EmptyRegion` then `Overflow`, and then holds when one RAM range holds it
  and it touches no exclusion.
- **Selection.** `BootMemory.findAvailable` checks the size and the
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

- **Profiles.** `CpuProfile` holds the PSCI conduit `conduit`, which is
  `CpuProfile::conduit`; the `AffinityLevel` `affinityLevel`, one of
  `aff0` to `aff3`, whose `AffinityLevel.shift` is 0, 8, 16 or 32; the set
  `cpuCounts`, whose bit `n` allows `n` CPUs (`CpuProfile.allows`, for `n`
  from 1 to 4); `cpu0EnableMethod`; and the optional `TimerInterrupts`
  `timerInterrupts`, whose list is the first `count` of its five `numbers`
  (`TimerInterrupts.list`). Every value of the fields is a profile.
  `CpuProfile.affinityShift` gives the shift of the affinity level;
  `CpuProfile.idOf` gives the logical
  ID below 4 whose `id << affinity_shift` is an affinity, and
  `CpuProfile.logicalId` gives it for the affinity fields of a value of
  `MPIDR_EL1`, masked with `AFFINITY_MASK`.
- **The topology.** `CpuTopology` holds the profile and the number of CPUs,
  which `CpuTopology::profile` and `count` give. `CpuTopology.affinity` and
  `CpuTopology.validateTimers` are `CpuTopology::affinity` and
  `validate_timers`; the latter fails with `BadProperty` for a profile
  without timer interrupts and otherwise compares the bytes with the timer
  records of the profile, its interrupts encoded by `be32`.
- **The discovery.** `Fdt.discoverCpus` runs step 6 in order: `/cpus`, its
  `status` and size cells, its address cells, each child through
  `cpuOfChild`, which reads the `enable-method` of CPU 0 when the profile
  sets `cpu0EnableMethod`, the set of IDs through `idsComplete`, whose
  count the profile must allow, and `/psci` with its
  `status`, its `method` and its `compatible`, which must be one of the
  byte lists of `PSCI_COMPATIBLE`.

### Plan

[`Plan.lean`](../../../../verification/Krepi/Spec/Fdt/Plan.lean): the
[boot memory map](contract.md#boot-memory-map) and the eight steps of its
error order in
[rejection and error priority](contract.md#rejection-and-error-priority).

- **Limits.** `MemoryPlan.PAGE_SIZE`, 4 KiB; `MAX_BANKS`, 32;
  `MAX_BOOT_SPANS`, 4; `MAX_FIRMWARE`, 128; `MAX_WINDOW_BYTES`, 128 MiB; and
  `MAX_RAM_BYTES`, 16 GiB, all in the namespace `MemoryPlan`.
- **The value.** `MemoryPlan` holds the RAM banks sorted by their start, the
  managed banks in address order, and the pages of the boot storage and of
  the firmware reservations, each in input order; `MemoryPlan::ram`,
  `managed_banks`, `boot_ranges` and `firmware_ranges` give them, and
  `reservations` gives the pages of the boot storage and then those of the
  firmware reservations. The flags of a firmware reservation are not kept:
  every page of every reservation is excluded.
- **Spans and pages.** `checkPlanSpan` checks a span: size 0,
  `InvalidRange`, then its end beyond 64 bits, `Overflow`. `pagesOf` rounds
  a checked span outward to whole pages, and its end rounded up beyond
  64 bits fails with `Overflow`.
- **Banks.** `addBank` checks one bank in input order, `checkPlanSpan` and
  then `Overlap` with an earlier bank; `sortByStart` sorts the banks by
  insertion; `admitBank` takes them in address order: the sum, `Overflow`,
  then above 16 GiB, `ArenaTooLarge`, then the start rounded up to a page,
  `Overflow`, and the complete pages of the bank as its managed bank.
- **Boot storage and firmware reservations.** `addBoot` checks the pages of
  one span of boot storage, then that one bank holds them, `OutsideRam`,
  then that they share no page with earlier boot storage, `Overlap`;
  `addFirmware` checks the pages of one firmware reservation, then that they
  share no page with the boot storage, `Overlap`.
- **The entries.** `MemoryPlan.allRam` runs steps 2 to 7 in order: the
  three capacities, `Capacity`, before any span is read; the banks; their
  managed pages and `Alignment` when there are none; the boot storage; the
  firmware reservations. `MemoryPlan.new` checks the window, step 1, runs
  `allRam` and then checks that one bank holds the window, step 8, and
  manages only the window. `MemoryPlan.fromBootMemory` is `MemoryPlan.new`
  with the RAM ranges of a boot memory, the boot storage of its image, its
  tree and the further spans `more`, and its reserved regions.
- **Queries.** `MemoryPlan.containsRam` holds when a range is nonempty, ends
  within 64 bits and one bank holds it; `MemoryPlan.isAvailable` when, in
  addition, no reservation touches it; `MemoryPlan.permitsBacking` when a
  managed bank holds it and it is available. `describedBytes` and
  `managedBytes` sum the banks and the managed banks with `sumSizes`.
- **Usable ranges.** `MemoryPlan.availableRanges` walks each managed bank
  with `usableFrom`: a cursor inside a reservation moves to the furthest end
  of the reservations that hold it; otherwise the range from the cursor to
  the nearest start of a reservation above it, or to the end of the bank, is
  usable. The cursor only moves forward, and `2 * R + 2` steps suffice for
  `R` reservations.

### Boot

[`Boot.lean`](../../../../verification/Krepi/Spec/Fdt/Boot.lean): the three
shared fields of the [state fields](contract.md#state-fields), written as
transactions that publish each field once and hold the boot token.

- **The token.** `BootToken` is the right to publish a shared field.
  In this release one executor, the boot CPU, runs every transaction before
  the secondary CPUs start, so it holds the token, `BootToken.bootCpu`.
- **The state.** `BootState` holds the bytes of the hand-over tree, the boot
  memory map and the CPU topology, each of the last two none until it is
  published, and whether the first secondary CPU has started. Reading a
  field needs no token; `BootState.tree` parses the hand-over bytes.
- **The hand-over.** `BootState.coldEntry` is the state at the cold entry,
  with the bytes that the firmware or the loader wrote before it and nothing
  built: the bytes are published there, and no transaction writes them
  again.
- **The publications.** `BootState.publishPlan` runs the entry of a
  `PlanBuild`, `MemoryPlan::all_ram`, `new` or `from_boot_memory`, and
  `BootState.publishTopology` runs `Fdt::discover_cpus` with a profile on
  the tree of the hand-over bytes. Each is enabled only while its field is
  none and no secondary CPU has started, and gives none otherwise; at the
  return of its entry it publishes the result, or gives the error of the
  entry and no state, so the state stays as it was.
- **The start of the secondary CPUs.** `BootState.startSecondaries` is
  enabled once both results are published and before the secondary CPUs
  have started; from then on no publication is enabled, and every CPU only
  reads the fields.

### Invariants

[`Invariants.lean`](../../../../verification/Krepi/SpecProperties/Fdt/Invariants.lean):
the invariants of the values of the component and of the boot state, a
check that decides each, and the statements of their establishment, of
their preservation and of the well-formedness of each operation.

The component writes no state of its own, so an invariant of a value is
established by the entries that build the value and read by the entries and
the components that take it, and no entry changes a value once it is built.
Only the boot state changes, by its transactions. A structural invariant is
quantified over a whole table of a value; a functional invariant states what
a value means beyond the shape of its tables. Every invariant is decidable:
a computable check, `check...`, decides it, and a statement states that
agreement, so that a check at boot can use it. Lines are those of the
contract.

| Invariant | Kind | States | Established by | Preserved by | Read by | Decidable |
| --- | --- | --- | --- | --- | --- | --- |
| `Fdt.WellFormed` | Structural: the nodes and the reservation entries of a tree | `totalsize` from 40 to `MAX_BLOB_SIZE`; at most `MAX_RESERVATIONS` reservation entries, each nonempty, within 64 bits and disjoint from the others; 1 to `MAX_TOKENS` nodes, the root first without a parent and with the empty name, every other node with a parent before it and a name that is not empty, the characters of the names, a depth of at most `MAX_DEPTH - 1`, at most `MAX_PROPERTIES` properties of distinct names of 1 to `MAX_PROPERTY_NAME` bytes and their characters (format and bounds, lines 151 to 187) | `Fdt::parse` | No entry changes a tree | The node access; `Node::translate_reg`, whose fuel of `MAX_DEPTH` buses it bounds; `discover_memory` and `discover_boot_memory`, which find the root and take the reservation entries as reserved regions | Yes: `Fdt.checkWellFormed` |
| `Reg.WellFormed` | Structural: the entries of a `Reg` | At least one entry, each within the width of its address cells (lines 694 to 698 and 741 to 744) | `Reg::new`; `Node::reg` in the cells of the parent | No entry changes a `Reg` | `discover_memory`, whose RAM ranges and reserved regions are such entries; the device bindings | Yes: `Reg.checkWellFormed` |
| `AddressMap.WellFormed` | Structural: the windows of a map | Child and parent address cells of 1 or 2, at most 2 size cells; every window nonempty, of one size on both sides and each side within its width (lines 700 to 706) | `AddressMap::new`; `Node::ranges` and `dma_ranges` | No entry changes a map | `to_parent` and `to_child`, whose translated span therefore stays within the width of its side; `Node::translate_reg` | Yes: `AddressMap.checkWellFormed` |
| `MemoryMap.WellFormed` | Structural: the RAM ranges and the reserved regions | 1 to `MAX_MEMORY_REGIONS` RAM ranges, each nonempty and within 64 bits, no two sharing an address; at most `MAX_RESERVED_REGIONS` reserved regions, each nonempty and within 64 bits, none both `no-map` and `reusable`; at most `MAX_TOKENS` dynamic reservations, so that the count fits its width (lines 451 to 484) | `discover_memory` and `discover_boot_memory`, on a tree that keeps `Fdt.WellFormed` | No entry changes a memory map | `discover_boot_memory`, whose sum of the RAM ranges therefore fits 64 bits; the queries of the boot memory; `MemoryPlan::all_ram` and `from_boot_memory`, which take the RAM ranges as banks and the reserved regions as firmware reservations | Yes: `MemoryMap.checkWellFormed` |
| `MemoryPlan.WellFormed` | Structural: the banks, the managed banks, the boot storage and the firmware reservations | 1 to 32 banks, each nonempty and within 64 bits, sorted by their start and disjoint, adjacent ones kept apart, of at most 16 GiB together; managed banks nonempty, on pages, each inside one bank, in address order; 1 to 4 spans of boot storage, each nonempty, on pages and inside one bank, no two sharing a page; at most 128 firmware reservations, each nonempty and on pages, none sharing a page with boot storage (lines 583 to 600, 616 and 617) | `MemoryPlan::all_ram`, `new` and `from_boot_memory` | The publication of the boot state, which keeps the map unchanged | The queries and `available_ranges`; `described_bytes` and `managed_bytes`, whose sums therefore fit; the kernel direct map and the page ownership table of the page-tables component | Yes: `MemoryPlan.checkWellFormed` |
| `BootState.WellFormed` | Structural: the published boot memory map | The published boot memory map, if any, keeps `MemoryPlan.WellFormed` (line 862) | `BootState.coldEntry` | `publishPlan`, `publishTopology`, `startSecondaries` | Every CPU that reads the boot memory map | Yes: `BootState.checkWellFormed` |
| `BootMemory.Consistent` | Functional | The span of the tree within 64 bits, at a multiple of `2 ^ alignmentLog2` and at most `maxBlobSize` long, the alignment and the limit that the value holds; the image nonempty, within 64 bits and sharing no address with the tree; each inside one RAM range; `ram_bytes` the exact sum of the RAM ranges (lines 502 to 521) | `discover_boot_memory`, which also gives the value the limit and the alignment of its profile | No entry changes it | `is_available` and `find_available`, whose exclusions are the image and the tree; `from_boot_memory`, which takes them as boot storage | Yes: `BootMemory.checkConsistent` |
| `CpuTopology.Supported` | Functional | 1 to 4 CPUs, a count that the profile of the topology allows (lines 647 to 649 and 666 to 668) | `discover_cpus` | No entry changes it | `CpuTopology::affinity`; `validate_timers`, whose flags are exact for these counts; the start of the secondary CPUs | Yes: `CpuTopology.checkSupported` |
| `BootState.FromHandOver` | Functional | The published topology, if any, is what `discover_cpus` gives on the tree of the hand-over bytes with some profile (lines 860 and 863) | `BootState.coldEntry` | `publishPlan`, `publishTopology`, `startSecondaries` | The start of the secondary CPUs | Yes: `BootState.checkFromHandOver`, which runs the discovery with the profile that the topology holds, the profile that a discovery gives its topology |
| `BootState.StartOrder` | Functional | Once the secondary CPUs have started, the boot memory map and the topology are both published (lines 862 to 867) | `BootState.coldEntry` | `publishPlan`, `publishTopology`, `startSecondaries` | Each secondary CPU, which reads both | Yes: `BootState.checkStartOrder` |

`Span` has no invariant of its own: the contract's condition that a span
ends within 64 bits is `Span.Valid`, which the structural invariants require
of every span of their tables. `Span.WithinWidth`, `Span.OnPages` and
`Span.Nonempty` are the conditions on single spans that they share.

The statements of the module, 41 in all, are in four groups:

- **Checks**, 10: `CheckFdtWellFormed`, `CheckRegWellFormed`,
  `CheckAddressMapWellFormed`, `CheckMemoryMapWellFormed`,
  `CheckBootMemoryConsistent`, `CheckCpuTopologySupported`,
  `CheckMemoryPlanWellFormed`, `CheckBootStateWellFormed`,
  `CheckBootStateFromHandOver` and `CheckBootStateStartOrder`: each check
  is true exactly when its invariant holds, for every value.
- **Establishment**, 5: the functional invariants of the values that the
  entries build, `DiscoverBootMemoryConsistent`, which also states that the
  value holds the limit and the alignment of its profile, and
  `DiscoverCpusSupported`; and the three invariants of the boot state at the
  cold entry, `ColdEntryWellFormed`, `ColdEntryFromHandOver` and
  `ColdEntryStartOrder`.
- **Preservation**, 6: each transaction of the boot state preserves each of
  its two functional invariants, `PublishPlanFromHandOver`,
  `PublishPlanStartOrder`, `PublishTopologyFromHandOver`,
  `PublishTopologyStartOrder`, `StartSecondariesFromHandOver` and
  `StartSecondariesStartOrder`.
- **Well-formedness**, 20: one lemma for each operation, apart from the
  functional statements, that on well-formed inputs the value that it
  returns is well-formed. The operations are the entries that build a value
  with a structural invariant, `SpanNewWellFormed`, `ParseWellFormed`,
  `RegNewWellFormed`, `AddressMapNewWellFormed`, `NodeRegWellFormed`,
  `NodeRangesWellFormed`, `NodeDmaRangesWellFormed`,
  `DiscoverMemoryWellFormed`, `DiscoverBootMemoryWellFormed`,
  `AllRamWellFormed`, `MemoryPlanNewWellFormed` and `FromBootMemoryWellFormed`;
  the entries that derive a span or a table of spans from such a value,
  `ToParentWellFormed`, `ToChildWellFormed`, `TranslateRegWellFormed`,
  `FindAvailableWellFormed` and `AvailableRangesWellFormed`, the last with
  `MemoryPlan.UsableWellFormed`, which bounds the usable ranges by one for
  each managed bank and each reservation (Work bounds, lines 810 and 811);
  and the transactions, `PublishPlanWellFormed`,
  `PublishTopologyWellFormed` and `StartSecondariesWellFormed`. An entry
  that builds its value from unchecked input has no hypothesis, so its lemma
  is also the establishment of the structural invariant of its value. The
  other entries return a truth value, a number, a string, bytes, a node or
  a table of a value that they read, whose well-formedness is the invariant
  of that value, so they have no lemma of their own.

### Properties

[`Properties.lean`](../../../../verification/Krepi/SpecProperties/Fdt/Properties.lean):
the cross-cutting properties of the component, each a registered statement,
with the definitions that they need: the path of a node, the RAM ranges that
the rules of the discovery give, the values that the discoveries leave
unread, the spans that `find_available` may give, the two sides of a window,
and a small encoder of device trees, `BuiltTree`, from which the limits are
stated and through which the builder of the specification tests writes its
trees.

| Property | States | Requirements |
| --- | --- | --- |
| `ParseLimitsExact` | For each of the six limits of the parse, `totalsize`, the nodes on a path, the tokens, the properties of a node, the bytes of a property name and the reservation entries, a built tree at the limit is accepted and one 1 above it fails with `LimitExceeded`, or with `BadString` for a property name; with `ParseWellFormed`, every accepted tree lies within them | [FDT-R01](requirements.md#fdt-r01) |
| `PrefixesRejected` | Every prefix of an accepted tree shorter than its `totalsize` fails with `Truncated` | [FDT-R02](requirements.md#fdt-r02) |
| `NoChoiceAmongDuplicates` | On a well-formed tree, two nodes of one path make its lookup fail with `AmbiguousMapping`, and a node that a lookup finds is the only node of its path; an accepted `/cpus` has no two CPU nodes of one `reg`; the RAM ranges of `discover_memory` are all the spans of the enabled memory nodes in tree order; the banks of `all_ram` are all the banks given. With the structural invariants, overlapping RAM ranges and banks are rejected, never dropped or merged | [FDT-R02](requirements.md#fdt-r02), [FDT-R03](requirements.md#fdt-r03), [FDT-R07](requirements.md#fdt-r07), [FDT-R08](requirements.md#fdt-r08) |
| `UsableRangesExact` | On a well-formed boot memory map, each usable range lies inside one managed bank and touches no reservation; every address of a managed bank that no reservation holds lies in a usable range; each starts at the start of its bank or the end of a reservation and ends at the end of its bank or the start of a reservation | [FDT-R06](requirements.md#fdt-r06), [FDT-R07](requirements.md#fdt-r07) |
| `FindAvailableLowest` | A span of `find_available` is available, of the size, alignment and bounds asked, inside a RAM range before which no range in tree order has a span that fits, and no span that fits in its range starts lower; none means that no range has one | [FDT-R05](requirements.md#fdt-r05) |
| `UnreadValuesIgnored` | Two trees that differ only in the values of `/chosen` other than its `device_type` and, when that is `memory`, its `status`, and in the values of a dynamic reservation other than its `status` and flags, give the same memory map, boot memory and CPU topology, with every profile | [FDT-R04](requirements.md#fdt-r04), [FDT-R10](requirements.md#fdt-r10) |
| `AffinityRoundTrip` | For every CPU of a supported topology, `logical_id` of its affinity with any flag bits is its index, and flag bits outside the affinity fields never change a logical ID | [FDT-R08](requirements.md#fdt-r08) |
| `TranslationThroughOneWindow` | For a well-formed map and a nonempty request within the width of its side: an absent map translates nothing; an empty one gives the request; a map of windows succeeds exactly when one window and no other shares an address with the request and holds all of it, and then gives the span at the request's offset in that window | [FDT-R09](requirements.md#fdt-r09) |

### Builder

[`Builder.lean`](../../../../verification/Krepi/SpecTests/Fdt/Builder.lean):
the builder of the trees of the specification tests, with the operations of
the builder of the prototype's tests: begin and end a node; add a property
with a value, cells, a string, a list of strings or no value; add a
no-operation token or a raw word; write over the last bytes of the structure
block, such as the padding after a property value; add a reservation entry;
finish the tree, padded with zero bytes to a larger `totalsize` where one is
asked; and write a word or bytes into a finished tree or invert one of its
bytes. `minimal` is the tree of the helper of that name of those tests. The
builder writes through the encoder of `Properties`, `BuiltTree`, so the tests,
the inputs of the witnesses of the parse and the limits of `ParseLimitsExact`
share one encoding, and it checks nothing: the parse decides about every
tree that it writes. It lies on the statement side, since the tests are
stated with it.

### Boards

[`Boards.lean`](../../../../verification/Krepi/SpecTests/Fdt/Boards.lean):
the profiles of two boards that the tests give the entries, the test data of
the profile names of the vectors: `pi5HandOver`, the hand-over profile of
the Pi 5, a limit of 128 KiB, an alignment of 8 and the entries
`raspberrypi,5-model-b` and `brcm,bcm2712`; and the CPU profiles
`pi5Cpus`, `qemuHvcCpus` and `qemuSmcCpus`, which the
[notation](contract.md#notation) of the contract lists. The specification
tests, the witnesses and the replay take them as inputs; no entry of the
specification and no statement of its invariants or properties names them.

### Specification tests

[`Stp.lean`](../../../../verification/Krepi/SpecTests/Fdt/Stp.lean): for each
requirement, one input that the specification must accept, with the result
that it must give, and one that it must reject, with the error that it must
give. Each test is a proposition, registered in `statements.json` with its
theorem in `Krepi.Proofs.Fdt.Stp`, the name of the test with a lower-case
first letter, whose proof is planned. The expected results are literals
worked out from the requirements and the contract, never computed by the
specification. Every input is below 1 KiB but the two trees of FDT-R05, which
are the limit of 128 KiB itself.

FDT-R02 and FDT-R10 have no rejection of their own: no total function panics,
and every function gives one result for one input. Their rejecting tests take
the rest of each requirement: a prefix of a valid tree is rejected, and a
broken `device_type` of `/chosen`, the one value of `/chosen` that the memory
discovery reads of a QEMU virt tree, makes the discovery fail.

| Requirement | Test | Input | Result |
| --- | --- | --- | --- |
| [FDT-R01](requirements.md#fdt-r01) | Accepted: `ParseAcceptsNameAtLimit` | The root with a property whose name has exactly `MAX_PROPERTY_NAME`, 64, bytes, with each punctuation character of property names, and the `model` of QEMU virt with the bytes `0, 0, 2` in its padding | The tree of 187 bytes: the root with both properties, the value of `model` its 17 bytes without the padding |
| [FDT-R01](requirements.md#fdt-r01) | Rejected: `ParseRejectsNameAboveLimit` | The same tree with a name of 65 bytes | `BadString` |
| [FDT-R02](requirements.md#fdt-r02) | Accepted: `EntriesReturnOnChangedByte` | `minimal` with one byte inverted: the size `0x20_0000` of its RAM range becomes `0xdf_0000` | The parse accepts it, and the memory discovery gives that one RAM range |
| [FDT-R02](requirements.md#fdt-r02) | Rejected: `ParseRejectsPrefix` | `minimal` without its last byte | `Truncated` |
| [FDT-R03](requirements.md#fdt-r03) | Accepted: `DiscoveryAcceptsMaxRamRanges` | 32 RAM ranges in cells of one, and a reservation entry in the hole between the first two | The 32 ranges in tree order; the entry kept as a reserved region with `no-map` |
| [FDT-R03](requirements.md#fdt-r03) | Rejected: `DiscoveryRejectsExcessRamRanges` | The same tree with 33 RAM ranges | `LimitExceeded` |
| [FDT-R04](requirements.md#fdt-r04) | Accepted: `DiscoveryRecordsDynamicReservations` | Children of `/reserved-memory` with `size` and without `reg`: one of one cell below `#size-cells` 2 with `reusable` and `alloc-ranges` of 3 bytes, one of two cells with `no-map`, and a disabled one | 2 dynamic reservations and no reserved region |
| [FDT-R04](requirements.md#fdt-r04) | Rejected: `DiscoveryRejectsEmptyStaticReservation` | A child with `size` and a `reg` of size 0, which is static | `EmptyRegion` |
| [FDT-R05](requirements.md#fdt-r05) | Accepted: `Pi5AcceptsTreeAtLimit` | The hand-over tree of the 8 GB model with `atf@0` and the region of 62 bytes in the hole, padded to exactly 128 KiB, with the hand-over profile of the Pi 5 | The boot memory: the three ranges, both reserved regions, the tree's 128 KiB, the image, `ram_bytes` of 8 GiB less 4 MiB, and the limit and the alignment of the profile |
| [FDT-R05](requirements.md#fdt-r05) | Rejected: `Pi5RejectsTreeAboveLimit` | The same tree padded to 128 KiB and 1 byte, which the parse accepts | `LimitExceeded` |
| [FDT-R06](requirements.md#fdt-r06) | Accepted: `Pi5ModelsBuildBootMemoryMaps` | The hand-over trees of the 1, 2, 4, 8 and 16 GB models with `atf@0` | For each, its RAM ranges, `ram_bytes` of its installed size less 4 MiB, and a boot memory map of `all_ram` whose usable ranges leave out the hole |
| [FDT-R06](requirements.md#fdt-r06) | Rejected: `BootMemoryMapRejectsRamAboveCapacity` | A hand-over tree of the same shape with 32 GB | The discovery gives `ram_bytes` of 32 GiB less 4 MiB, and `all_ram` fails with `ArenaTooLarge` |
| [FDT-R07](requirements.md#fdt-r07) | Accepted: `AllRamAcceptsMaxBootStorage` | One bank, 4 spans of boot storage, one of them off its page, and one `reusable` firmware reservation | The map with each span rounded outward to pages, and usable ranges that leave out all of them |
| [FDT-R07](requirements.md#fdt-r07) | Rejected: `AllRamRejectsExcessBootStorage` | The same with a fifth span of boot storage | `Capacity` |
| [FDT-R08](requirements.md#fdt-r08) | Accepted: `CpusAcceptsQemuPair` | QEMU virt with two CPUs, CPU 0 without an `enable-method`, and the timer records for two CPUs, with the CPU profile `QemuHvc` | A topology of the profile `QemuHvc` with 2 CPUs, and the records accepted |
| [FDT-R08](requirements.md#fdt-r08) | Rejected: `CpusRejectsRepeatedId` | The same tree with the `reg` 0 for both CPUs | `BadProperty` |
| [FDT-R09](requirements.md#fdt-r09) | Accepted: `TranslateRegThroughBus` | A device below a bus of 1 address cell and 1 size cell with a `ranges` and a `dma-ranges` | Its `reg` in the cells of the bus, translated through the `ranges` to `[0xfd00_1000, 0xfd00_1200)` |
| [FDT-R09](requirements.md#fdt-r09) | Rejected: `TranslationRejectsTwoWindows` | A map of two windows that both hold the request | `AmbiguousMapping` |
| [FDT-R10](requirements.md#fdt-r10) | Accepted: `SeedsDoNotReachResults` | Two QEMU virt trees that differ only in the seeds of `/chosen` | The same memory map and the same boot memory map; the parse accepts both, and its trees differ at most in values that no rule reads |
| [FDT-R10](requirements.md#fdt-r10) | Rejected: `ChosenDeviceTypeIsRead` | A QEMU virt tree whose `/chosen` has a `device_type` that is not UTF-8 | `BadString` |


### Witnesses

[`Witnesses.lean`](../../../../verification/Krepi/Spec/Fdt/Witnesses.lean):
the theorems that witness that the specification is not vacuous
([specifications](../../../formal-verification.md#specifications)). For each
frozen function of the entry table, lines 109 to 118, one input on which it
succeeds, with the value that it gives; for each error that the contract
gives that function, one input on which it fails with that error. The errors
of a function are those of its error order, of the rows of the error table
that name it, and of the entries that it calls at the step where it calls
them; a lookup of a fixed path, such as `/reserved-memory` or `/cpus`, fails
with `AmbiguousMapping` on two siblings of that name, by rule 3. The value
types of line 118 and the constants of line 119 are read through the
functions and have no witness of their own. The expected values are literals
worked out from the contract, never computed by the specification.

The parse reads bytes that `Builder`, the builder of the specification
tests, writes, each input below 200 bytes. The entries on a tree read trees of records, written in
preorder by `outline`, and every one of them passes the check of
`Fdt.WellFormed` (`treesWellFormed`); a node is reached through its path
(`atPath`). The other entries take literal spans, maps, topologies and the
boot memory that the success witness of the discovery of the boot memory
gives. The entries that take a profile take those of the Pi 5 and of QEMU
virt of `Boards`.

Each witness is an equation, `f x = .ok v` or `f x = .error e`, or for a
node entry `atPath t path f = some r`, and the module proves it by
`decide +kernel`: the kernel evaluates both sides. Lean core decides no
equality of `Except`, so the module decides it with a local instance that no
statement mentions; it uses no `native_decide`, `sorry` or axiom, and the
audit of each of its theorems lists no axiom but `propext`,
`Classical.choice` and `Quot.sound`. The module builds in about 24 s.

| Line | Functions | Success | Rejection | Unreachable branches |
| --- | ---: | ---: | ---: | ---: |
| 109 | 1 | 1 | 14 | 4 |
| 110 | 15 | 15 | 30 | 2 |
| 111 | 4 | 5 | 10 | 1 |
| 112 | 8 | 9 | 14 | 2 |
| 113 | 1 | 1 | 3 | 1 |
| 114 | 8 | 8 | 6 | 1 |
| 115 | 6 | 6 | 17 | 1 |
| 116 | 3 | 3 | 21 | 1 |
| 117 | 11 | 11 | 0 | 0 |
| 118 | 3 | 3 | 3 | 0 |
| Total | 60 | 62 | 118 | 13, all planned |

`MemoryMap::dynamic` and `BootMemory::dynamic` have a second success
witness with a nonzero count, on trees with dynamic reservations below
`/reserved-memory`: `memoryMapDynamicTwo` and `bootMemoryDynamicOne`.

**Error priority.** For each step of the two error orders of
[rejection and error priority](contract.md#rejection-and-error-priority),
one more witness gives an input that breaks a rule of that step and a later
rule of the same entry, and states the error of the step: `priorityStep1` to
`priorityStep8` for the parse and the entries on a tree, and
`priorityPlanStep1` to `priorityPlanStep7` for the boot memory map. Steps 1
and 2 of the parse and steps 1 to 7 of the boot memory map pair a rule of
the step with one of a later step. The parse ends at step 3; steps 4 to 6
are each the order of one entry, and steps 7 and 8 hold the orders of
several. An entry that calls another reports the error of the callee at the
step where it calls it, so the later rules of an entry of steps 3 to 8 lie
in the same step, and the witnesses of these steps pair two rules of the
step, the earlier first. Step 8 of the boot memory map, the last check of
`MemoryPlan::new`, has no later rule and no witness of this kind. With the
earlier rule repaired, each of these inputs fails with the error of the
later rule, so each witness tells the order of the contract from the
reverse one.

Every success, rejection and priority witness is proved in the module. The kernel
evaluates their inputs because the specification calls neither
`String.startsWith` nor `String.toUTF8`, which have no body that a module of
Lean 4.35.0 can unfold: the memory discovery compares the UTF-8 bytes of a
name with those of `memory@` (`isMemoryName`), and the strings that the
specification and `Builder` write are the bytes of `String.toByteArray`,
which equals `String.toUTF8`.

An error branch that no input of its entry reaches has no witness. For each,
a planned proposition states that the entry, or the step of it where the
branch lies, never takes it; the error of the branch is witnessed through
another branch where the function has one. All but the last are the checks
that the [readings of the contract](#readings-of-the-contract) keep at their
place in the order. The last, `CpuRegNoUnsupportedCells`, is the
`UnsupportedCells` that step 6 names for the value of the `reg` of a CPU
node, which the step reads only in the 1 or 2 address cells that it has
checked for `/cpus`.

| Statement | Branch | Reason |
| --- | --- | --- |
| `HeaderNoOverflow` | `Fdt::parse`, step 1: the end of a block, `Overflow` | Offsets and sizes are 32-bit words |
| `ReservationEntriesFit` | `Fdt::parse`, step 2: an entry past the tree, `Overflow` | The map starts at a 32-bit offset and holds at most 129 entries of 16 bytes; the entry `k` starts at the offset of the map and `16 * k` bytes, so every end that the step checks is below the bound that the statement gives |
| `TokensNoOverflow` | `Fdt::parse`, step 3: the end of a property value, `Overflow` | A value starts within a block of at most 2 MiB and its length is a 32-bit word |
| `ReservationFuelSuffices` | `Fdt::parse`, step 2: out of fuel, `LimitExceeded` | The limit or the terminator ends the map first |
| `ClimbRangesNoBadTree` | `Node::translate_reg`: the `ranges` of a bus without a parent, `BadTree` | The climb reads the `ranges` of a bus only when it has a parent |
| `TranslateRegFuelSuffices` | `Node::translate_reg`: out of fuel, `LimitExceeded` | No node of a well-formed tree lies deeper than `MAX_DEPTH - 1` |
| `DiscoverMemoryNoBadTree` | `Fdt::discover_memory`: no root, `BadTree` | A well-formed tree has a root, and each node whose `reg` is read has a parent |
| `DiscoverBootMemoryNoBadTree` | `Fdt::discover_boot_memory`: no root, `BadTree` | As for the memory discovery |
| `RamBytesFit` | `Fdt::discover_boot_memory`: the sum of the RAM ranges, `Overflow` | The ranges are disjoint and end within 64 bits, so their sum fits, and so does each partial sum that the step adds |
| `FindAvailableNoLimitExceeded` | `BootMemory::find_available`: out of fuel, `LimitExceeded` | Each candidate after the first passes an exclusion for good |
| `WindowTranslationNoOverflow` | `AddressMap::to_parent` and `to_child`, and so `Node::translate_reg`: the translated span, `Overflow` | It lies inside the target side of a window of a well-formed map |
| `BankBytesFit` | `MemoryPlan::all_ram`, `new` and `from_boot_memory`, step 4: the sum, `Overflow` | The banks are disjoint and end within 64 bits, so their sum fits, and so does each partial sum that the step adds |
| `CpuRegNoUnsupportedCells` | `Fdt::discover_cpus`, step 6: the value of the `reg` of a CPU node, `UnsupportedCells` | The step reads it in the address cells of `/cpus`, which it has checked to be 1 or 2, and `cells_u64` refuses only more than 2 |

Some definitions also hold error branches that no entry of the contract
names and that the checks before them exclude: the `Truncated` of `u32At`
in `Node.cellCount`, which reads a value of exactly 4 bytes; the errors of
`cellsU64` in `regEntry` and `window`, whose entries `Reg.new` and
`AddressMap.new` have cut to whole cells of checked counts; and the
`Truncated` of `u64At` in `reservationsFrom`, which reads an entry only once
it has checked that the tree holds it. They are no branches of an entry, so
no statement covers them.

The two variants of the specification that reject every input or accept
every input are refuted by two theorems of the module, each a conjunction
over the 27 functions that can fail. `notAlwaysRejecting` gives an input on
which each succeeds, from the success witnesses, and `notAlwaysSucceeding`
an input on which each fails, from the rejection witnesses. The other 33 functions return a value for
every input and have no error.

## Design decisions

### Readings of the contract

Where the contract leaves a rule open, the specification takes the reading
below and states it. Lines are those of the contract at commit `e099b40`,
before it stated any of these readings; a row whose reading the contract now
states names the section that states it, and the other rows remain readings
of the specification.
Where the contract defers to the prototype tree, which it does for the error
orders ("which are those of the prototype tree", lines 282 to 284), the
reading follows the prototype and names the place.

| Reading | Contract | Basis |
| --- | --- | --- |
| `Span` has no type invariant; `Span.Valid` is the condition of the term, and the entries that take a span check it and fail with `Overflow` | Terms, lines 48 and 49; the vectors `fdt-pi5-boundaries-3` and `platform-4` to `platform-8` give `Overflow` for spans whose end leaves 64 bits, lines 988 and 1031 to 1035; now stated in [Terms](contract.md#terms) | A type invariant would make those inputs unwritable |
| `Span::new` accepts an empty span; `Span::end` gives `start + size` or `Overflow`; `Span::contains(other)` fails with `Overflow` when `other` and then the span itself end beyond 64 bits, and otherwise holds when `other` lies inside the span | The entry table names the three functions, line 99, and Work bounds gives them a fixed number of steps, line 727; neither states their results; now stated in [Terms](contract.md#terms) | The error table gives `Overflow` to a span that leaves 64 bits, line 267, and `EmptyRegion` is checked by the entries that refuse an empty span, such as step 2, line 301 |
| In step 1, each block is checked for its start inside the header, `BadLayout`, then its end beyond 64 bits, `Overflow`, then its end past the tree, `Truncated`; the structure block before the strings block | Step 1, lines 294 to 297, lists the three errors without their order; now stated in [Rejection and error priority](contract.md#rejection-and-error-priority) | The order of the prototype, which the contract adopts: `block` in `src/fdt/format.rs`, lines 18 to 24, and `src/fdt/parser.rs`, lines 55 and 56 |
| The checks of an `Overflow` that 64-bit arithmetic cannot reach stay in the specification at their place in the order: the end of a block in step 1, of a reservation entry before the tree's end in step 2, and of a property value in step 3, the translated span of a translation, and the sum of the RAM ranges in step 5 | Lines 295, 299, 310, 336 and 337, and 358; now stated in [Rejection and error priority](contract.md#rejection-and-error-priority) | Header words have 32 bits and a tree at most 2 MiB, so these sums stay below $2^{33}$; a translated span lies inside a window that was checked at construction; and the RAM ranges are disjoint and end within 64 bits, so their sum fits; the order is the contract's, and a theorem states that the entry never returns `Overflow` from these checks |
| `Node::string_property` fails with `BadString` for a value without a NUL or whose bytes before the first NUL are not UTF-8, before `BadProperty` for a byte after that NUL | Format and bounds, lines 206 to 209, lists both errors; step 6, lines 346 to 349, refers to them; now stated in [Format and bounds](contract.md#format-and-bounds) | The order of the prototype: `string_property` in `src/fdt/nodes.rs`, lines 140 to 150 |
| `Node::reg` checks the parent, `BadTree`, then the `reg`, `MissingProperty`, then the address cells and the size cells of the parent, `BadProperty`; `Node::ranges` and `dma_ranges` check the parent, then the node's address cells, the parent's address cells and the node's size cells; `Node::translate_reg` checks the parent, then translates through each bus from the nearest and checks the end of the result | Lines 607 and 608, 624 to 632 and Work bounds, lines 684 to 691, which give the lookups in this order; the error table gives `BadTree` to a node without a parent where an entry needs one, line 259; now stated in [Rejection and error priority](contract.md#rejection-and-error-priority) | The order of the prototype: `reg`, `address_map` and `translate_reg` in `src/fdt/nodes.rs`, lines 183 to 219 |
| A no-operation token counts toward `MAX_TOKENS`; when `MAX_TOKENS` tokens have been read and none was the end token, the parse fails with `LimitExceeded` without decoding another | Lines 154 and 155 and 315 and 316; Terms counts the no-operation among the tokens, lines 41 and 42; now stated in [Rejection and error priority](contract.md#rejection-and-error-priority) | The prototype reads at most `MAX_TOKENS` tokens and fails after them, `src/fdt/parser.rs`, lines 168 and 227 |
| The letters and digits of node and property names are the ASCII ones; `@` may occur any number of times in a node name | Lines 156 to 160; the ASCII letters and digits now stated in [Format and bounds](contract.md#format-and-bounds) | Tables 2.1 and 2.2 of DTSpec v0.4, which the contract cites, list exactly `0-9`, `a-z` and `A-Z` with the punctuation; the prototype checks the same set, `src/fdt/format.rs`, lines 9 to 14 |
| UTF-8 is the encoding of a sequence of Unicode scalar values, so an overlong encoding, a surrogate and a code point above `U+10FFFF` are not UTF-8 | Lines 156, 158 and 206 to 208 | Lean core's `ByteArray.IsValidUTF8`, which `String.fromUTF8?` decides, is that definition; it is the one of the Unicode standard and of Rust's `str::from_utf8` |
| `Fdt::find_node` checks the form of the whole path first; then, component by component, a component without a match ends the lookup with none, and the components after it are not looked up | Lines 199 to 203 and step 8, line 360 | The order of the prototype: `find_node` in `src/fdt/nodes.rs`, lines 19 to 43 |
| `Fdt::find_node("/")` gives the first node of the structure block | Lines 150 to 153: the block holds one root, a begin-node token with an empty name | A begin node outside every node is the root and a second one fails with `BadTree` (line 259), so the first node of an accepted tree is its root |
| `Node::translate_reg` of a child of the root translates nothing and returns the span after the check of its end | Lines 630 to 632 | The root has no parent bus, so no `ranges` applies |
| The tree that the parse returns is an abstract value: the header's `totalsize`, the reservation entries and the nodes with their names, parents and properties | Terms, lines 29 to 32, where the tree borrows the bytes | The entries read only these values; the borrowed view of the implementation corresponds to this value |
| Loops on fuel: the reservation map reads at most `MAX_RESERVATIONS + 1` entries, the walk at most `MAX_TOKENS` tokens, a string at most the bytes up to the end of its block, and `Node::translate_reg` at most `MAX_DEPTH` buses; out of fuel, the reservation map and the translation fail with `LimitExceeded` | Work bounds, lines 669 to 691 | The reservation map ends within the limit of lines 147 and 148, and on a tree that the parse accepted no node lies deeper than `MAX_DEPTH - 1` (lines 165 and 166), so neither runs out there; a hand-written tree with a cycle of parents does |
| The memory discovery reads the `device_type` of every child of the root, `/chosen` included, and the `status` only of a memory node, by name or by `device_type`; a child that is neither adds nothing. What no entry reads of `/chosen` are its other properties, such as the seeds that QEMU writes; a `/chosen` whose `device_type` is `memory` is a memory node by that `device_type`, so its `status` is read as well and, when it is enabled, the discovery fails with `BadProperty`, since its name is no memory name. Of a dynamic reservation the discovery reads its `status`, `no-map` and `reusable` and whether it has `reg` and `size`, and no value besides (`UnreadValuesIgnored`) | Step 4, lines 319 and 320, and lines 399 to 403 and 419 to 423; Determinism, lines 751 to 754, where no entry reads `/chosen`; now stated in [Rejection and error priority](contract.md#rejection-and-error-priority), [Memory discovery](contract.md#memory-discovery) and [Determinism](contract.md#determinism) | The order of the prototype, which the contract adopts: `discover_memory` in `src/fdt/discovery.rs`, lines 82 to 92 |
| The `reg` of a memory node or of a child of `/reserved-memory` is read whole, with every error of `Node::reg`, before any of its ranges or spans is added | Step 4, lines 320 and 321 and 324 and 325, "its `reg`, and each of its ranges"; `Reg::new` checks every entry before it gives one, lines 605 to 607; now stated in [Rejection and error priority](contract.md#rejection-and-error-priority) | The contract's rule of `Reg::new`, which the prototype keeps: `Reg::new` checks every entry before it returns, `src/fdt/translation.rs`, lines 44 to 46; `Node::reg` returns `Reg::new`, `src/fdt/nodes.rs`, lines 183 to 190; and `discover_memory` reads the `status` of a memory node alone, `src/fdt/discovery.rs`, line 91, and its whole `reg` before it adds a range, lines 97 and 98, as for a child of `/reserved-memory`, lines 134 to 140 |
| Each RAM range is checked for size 0, `EmptyRegion`, then for an address shared with an earlier range, `Overlap`, then for the capacity, `LimitExceeded`; each span of `/reserved-memory` for size 0 and then the capacity | Step 4, lines 321 and 325, and lines 404 to 407 | The order in which step 4 lists them, which is that of the prototype: `add_ram` and `add_reserved` in `src/fdt/discovery.rs`, lines 33 to 60 |
| An entry of the reservation map is a reserved region after the check of the capacity alone; the parse has checked that it is nonempty and ends within 64 bits | Step 4, lines 317 and 318; step 2, lines 298 to 302 | The step names only `LimitExceeded` for these entries |
| The memory discovery and the boot memory find the root first; a tree without one, which the parse never builds, fails with `BadTree` | Lines 692 and 693 and 699, the lookup of the root; the error table gives `BadTree` to a tree without a root, line 259 | The parse rejects an end token without a root, line 259, so the lookup always finds it on a tree that the parse accepted |
| `/reserved-memory`: its binding, all of whose rules give `BadProperty`, before its `status`; a disabled one holds no reservation and its children are not read. A child: its `status`, then its flags, then neither `reg` nor `size`, `MissingProperty`; a child with `size` and without `reg` is counted as a dynamic reservation after its flags, and its `size` is not read | Step 4, lines 322 to 325, and lines 409 to 425 | The order of step 4, with a disabled container holding no reservation, lines 411 and 412 |
| Two spans touch when both are nonempty and share an address; two spans are disjoint when they share none | "touches", lines 459 and 460 and 551 and 552, and "disjoint", lines 405 and 456, which Terms does not define; now stated in [Terms](contract.md#terms) | The plain meaning as sets of addresses; for the nonempty spans that the entries compare, it is the half-open intersection that the prototype's `overlaps` computes |
| The queries of the boot memory know only the image and the tree as the board gives them, and the reserved regions; further boot storage, such as a boot bundle that the board gives as a span of its own, is excluded by the boot memory map alone. The image span is the one that the board passes, with its BSS and stacks and any read-only part of the image within it | Lines 449 and 461 to 463 and 60 to 63; now stated in [Terms](contract.md#terms) and [Memory discovery](contract.md#memory-discovery) | The queries take no further span, line 447; a page-aligned read-only part of the kernel image lies within the image span that the board passes |
| An empty bound of `BootMemory::find_available` is a minimum at or above the limit; an alignment is a power of two when it is one of $2^0$ to $2^{63}$ | Step 8, line 362, and line 550; the error table, line 257; now stated in [Rejection and error priority](contract.md#rejection-and-error-priority) | The bound is the interval $[minimum, limit)$, line 551, which is empty exactly then |
| `BootMemory::find_available` fails with `Overflow` when an alignment of its search leaves 64 bits: the first candidate of a RAM range, the greater of its start and the minimum, or the end of the furthest exclusion that a candidate touches, aligned up. The search meets them in the order of the RAM ranges and of their candidates, so a span found earlier is returned first. A candidate whose end leaves 64 bits or passes the bound ends the search in its range without an error | Step 8, lines 362 and 363, "then `Overflow`"; the vector `fdt-pi5-selection-2`, line 997, where the size `0xffffffffffffffff` gives none; now stated in [Rejection and error priority](contract.md#rejection-and-error-priority) | The order of the prototype, which the contract adopts: `find_available` and `align` in `src/fdt/pi5/selection.rs`, lines 24 to 61; the span that the search returns is the one of the rule of lines 549 to 554, which a theorem states |
| The search of a RAM range moves from a candidate to the end of the furthest exclusion that it touches, aligned up, and tries at most `Q + 3` candidates; out of fuel it fails with `LimitExceeded` | Work bounds, lines 705 to 707 | Every start between the candidate and that end touches that exclusion, so no span is passed over; each move passes at least one of the `Q + 2` exclusions for good, so the fuel is never used up |
| The `status` of `/cpus` is read before its size cells | Step 6, lines 338 and 339, "disabled or with size cells other than 0"; now stated in [Rejection and error priority](contract.md#rejection-and-error-priority) | The order of the prototype: `discover_cpus` in `src/fdt/cpus.rs`, line 94 |
| A CPU node fails at "its ID" when its `reg` is not `id << affinity_shift` for an ID below 4, flag bits included, or when an earlier CPU node has its ID; "the set of IDs" then checks the number of CPU nodes and that the IDs are `0` to `count - 1` | Step 6, lines 344 and 345; lines 571 to 579; rule 3, lines 235 and 236; now stated in [Rejection and error priority](contract.md#rejection-and-error-priority) | The order of the prototype: `discover_cpus` in `src/fdt/cpus.rs`, lines 110 to 113 and 123 to 128 |
| The `enable-method` of CPU 0 is not read unless the profile sets `cpu0_enable_method`, so not on QEMU virt | Lines 576 and 577 | The prototype reads it only for the other CPUs and on the Pi 5, `src/fdt/cpus.rs`, lines 115 to 118 |
| `/psci`: its `status`, then its `method`, then its `compatible`; the `compatible`, a list of strings, is compared as bytes with the three lists, each string with its NUL, so any other value, also one that is not UTF-8, fails with `BadProperty`. The properties that fail as `Node::string_property` does are those that hold one string: `device_type`, `status`, the `compatible` of a CPU node, `enable-method` and `method` | Step 6, lines 346 to 349, and lines 580 to 584; now stated in [Rejection and error priority](contract.md#rejection-and-error-priority) | `Node::string_property` rejects a byte after the first NUL, lines 206 to 209, so it cannot read a list; the order and the comparison of the prototype: `src/fdt/cpus.rs`, lines 129 to 142 |
| `CpuTopology::validate_timers` accepts exactly the bytes of the records of the profile; the flags `((1 << count) - 1) << 8 \| 4` are a 32-bit cell, computed at that width | Lines 590 to 596; the error table, line 265 | A topology of the discovery has 1 to 4 CPUs, a count that its profile allows, for which the shift is exact |
| A count, a logical ID, the index of `CpuTopology::affinity` and an affinity are 64-bit values | The entry table, lines 92 and 95, which gives no width | The width of the target's addresses and sizes, as for the values of the first part |
| A span that the boot memory map takes, the managed window, a RAM bank and the span of boot storage or of a firmware reservation whose pages it takes, fails with `InvalidRange` for size 0 and then with `Overflow` for an end beyond 64 bits | Steps 1, 3, 6 and 7 of the order of the boot memory map, lines 367, 371, 376 and 379, "`InvalidRange` or `Overflow`"; the error table, lines 274 and 275; now stated in [Rejection and error priority](contract.md#rejection-and-error-priority) | The order of the prototype, which the contract adopts: `range` in `src/platform/mod.rs`, lines 28 to 34, through `PhysRange::new` in `src/memory/types.rs`, lines 29 to 35 |
| The pages of a span run from its start rounded down to its end rounded up to 4 KiB; when the end rounded up leaves 64 bits, `Overflow` | "rounded outward to whole pages", lines 523 and 526; "its rounding to pages ... leaves 64 bits", line 275; the check of the end rounded up now stated in [Rejection and error priority](contract.md#rejection-and-error-priority) | The prototype adds `PAGE_SIZE - 1` to the end with a checked addition, `covering_pages` in `src/platform/memory.rs`, lines 204 to 213, which fails exactly when the end rounded up is $2^{64}$ |
| The three capacities of step 2 are checked before any bank, span or reservation is read, and all give `Capacity` | Step 2, lines 369 and 370; now stated in [Rejection and error priority](contract.md#rejection-and-error-priority) | The order of the prototype: `all_ram` in `src/platform/memory.rs`, lines 67 to 74 |
| Step 4 takes the banks one at a time in address order: for each, the sum so far, `Overflow`, then above 16 GiB, `ArenaTooLarge`, then the rounding of its start, `Overflow`. Exactly 16 GiB is accepted. The sum leaves 64 bits for no disjoint banks, so its check stays at its place in the order and a theorem states that the entry never returns `Overflow` from it | Step 4, lines 373 and 374; "at most 16 GiB", lines 516 and 517; now stated in [Rejection and error priority](contract.md#rejection-and-error-priority) | The order of the prototype: `all_ram` in `src/platform/memory.rs`, lines 94 to 111 |
| Two RAM banks overlap when they share an address; adjacent banks do not overlap and stay separate | Lines 515 and 516; step 3, lines 371 and 372 | The meaning of `Span.touches` above; the prototype compares with `overlaps` in `src/memory/types.rs`, lines 58 to 60 |
| The banks are sorted by their start with an insertion sort; the order is unique, since disjoint nonempty banks have distinct starts | Lines 515 and 516, 711 and 712, and 744 and 745 | The contract fixes the result, not the sort |
| A span of boot storage, and the managed window of `MemoryPlan::new`, lie inside one bank when one bank as given holds them, not only its managed pages | "lies with its pages inside one RAM bank", lines 523 and 524; "inside one bank", lines 543 and 544; the error table, line 279 | The prototype compares with the banks, `contains_ram` in `src/platform/memory.rs`, lines 51, 117 and 188 to 190; the vector `platform-7` fails boot storage `0x1+0x1` in the bank `0x1+0x2000` with `OutsideRam` |
| The managed window must start and end on pages, and fails with `ArenaTooLarge` only above 128 MiB | Step 1, lines 367 and 368; "a span of whole pages, at most 128 MiB long", lines 543 and 544; now stated in [Rejection and error priority](contract.md#rejection-and-error-priority) | The prototype checks both ends, `new` in `src/platform/memory.rs`, lines 44 to 49 |
| `MemoryPlan::from_boot_memory` gives the boot storage in the order image, tree and then the spans of `more`; more than two spans in `more` fail with `Capacity` at step 2 | Lines 545 to 547; Work bounds, lines 716 and 717, "at most 4 spans of boot storage"; now stated in [Boot memory map](contract.md#boot-memory-map) | The contract names the image, the tree and `more` in this order; the prototype had no `more` and passed the image and the tree, `from_boot_memory` in `src/platform/memory.rs`, lines 145 to 152 |
| A query of the boot memory map takes a span, and a span that is empty or whose end leaves 64 bits lies in no bank, so `contains_ram`, `is_available` and `permits_backing` are false for it; otherwise a bank holds a range when it holds all its addresses | The queries, lines 533 to 536, which give neither the type of a range nor its result for these spans; the queries are in no error order, so they do not fail; now stated in [Boot memory map](contract.md#boot-memory-map) | The page-tables component converts the spans of the boot memory map into nonempty physical ranges whose end fits in 64 bits, the page-tables contract, lines 67 to 71; the prototype's queries took that type, `src/memory/types.rs`, lines 21 to 35 |
| The usable ranges are maximal: in each managed bank, each runs from an address that no reservation holds to the nearest start of a reservation above it, or to the end of the bank | Lines 536 to 538, which do not say maximal; Work bounds, lines 718 and 719, at most one range for each managed bank and each reservation; now stated in [Boot memory map](contract.md#boot-memory-map) | Ranges that ended anywhere else would exceed that bound; the prototype yields these ranges, `src/platform/memory/available.rs`, lines 21 to 53 |
| `MemoryPlan::described_bytes` and `managed_bytes` are 64-bit values; the managed bytes of `MemoryPlan::new` are those of its window | Lines 539 and 540, and 542 to 544 | A map of the entries holds at most 16 GiB in its banks, so the sums fit |
| The three shared fields are a boot state whose transactions hold the boot token and publish each field once: the bytes of the hand-over tree at the cold entry; the boot memory map and the CPU topology at the return of the entry that builds them, while the field is none and no secondary CPU has started. A transaction that is not enabled gives none; one whose entry fails gives the error of the entry and leaves the state unchanged | State fields, lines 764, 766 and 767; check and execute, lines 660 to 665 | The fields are published once and never change, and the component writes no state of its own, line 639, so only their publication is a transaction; in this release one executor, the boot CPU, holds the token |
| The secondary CPUs start only once the boot memory map and the CPU topology are both published | Lines 766 and 767, "Once, before the secondary CPUs start" and "before the first secondary CPU starts"; now stated in [State fields](contract.md#state-fields) | The start of the secondary CPUs reads the topology, and afterwards every CPU reads the boot memory map |
| The CPU topology is published from the tree of the hand-over bytes | Lines 764 and 767; the parse reads the bytes of the hand-over tree, line 90; now stated in [State fields](contract.md#state-fields) | The board's boot code parses the hand-over tree; the boot memory map takes its inputs from the board, lines 511 to 513, so its publication takes the arguments of its entry |

### Vector notation

The vector file holds the cases of
[legacy test vectors](contract.md#legacy-test-vectors) in the
[notation](contract.md#notation) of the contract, which states the forms
below in words; the table gives each with its syntax in the file and the
vectors that use it, and the replay reads it so.

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
| `entry=discover_pi5_boot_memory dtb=<bytes> dtb_address=<address> image=<span> ask=...` | `Fdt::discover_boot_memory` with the hand-over profile of the Pi 5: the fields of the boot memory, `ram_bytes` in hexadecimal, and the query `is_available(<span>)`, `true`, `false` or `Error::<variant>` | `fdt-pi5-1` to `fdt-pi5-4`, `fdt-pi5-boundaries-1` to `fdt-pi5-boundaries-5` |
| `entry=find_available dtb=<bytes> dtb_address=<address> image=<span> size=<n> alignment=<n> minimum=<address> limit=<address> ask=span` | `span` is the selected span, `-` for none; the case may also ask `is_available(<span>)` of the same boot memory. The four arguments are written in hexadecimal, also where the test writes them in decimal | `fdt-pi5-selection-1` to `fdt-pi5-selection-3` |
| `entry=discover_cpus dtb=<bytes> profile=<profile> ask=count,profile,affinity(<i>)` | A profile is `QemuHvc`, `QemuSmc` or `Pi5`, a CPU profile of `Boards`, and `profile` gives the name of the profile of the topology; `count` is decimal, `affinity(<i>)` hexadecimal or `-` for none | `fdt-cpus-1` to `fdt-cpus-4` |
| `entry=validate_qemu_timers dtb=<bytes> profile=<profile> interrupts=<bytes> ask=` | `CpuTopology::validate_timers` of the topology of `discover_cpus` on the tree checks the records: `result=ok` or `result=err` | `fdt-cpus-6` |
| `entry=logical_id profile=<profile> mpidr=<value> ask=id` | `id` is the logical ID in decimal, `-` for none | `fdt-cpus-5` |
| `entry=all_ram ram=<spans> boot=<spans> firmware=<regions> ask=...` | The boot memory map of `MemoryPlan::all_ram`; a firmware reservation is a reserved region, `<span>/<flag>`; an error is `PlanError::<variant>` | `platform-11` to `platform-13` |
| `entry=MemoryPlan::new window=<span> ram=<spans> boot=<spans> firmware=<regions> ask=...` | The boot memory map of `MemoryPlan::new`, so named because `new` names several entries | `platform-1` to `platform-10` |
| `entry=from_pi5 dtb=<bytes> dtb_address=<address> image=<span> window=<span> more=<spans> ask=...` | `MemoryPlan::from_boot_memory` on the boot memory of the arguments of `entry=discover_pi5_boot_memory`; an error of the discovery is an `Error`, one of the boot memory map a `PlanError` | `fdt-pi5-platform-1`, `fdt-pi5-platform-2` |
| The fields `ram`, `managed`, `boot`, `firmware`, `reservations` and `available` of a boot memory map | Lists of spans: the banks, the managed banks, the pages of the boot storage, of the firmware reservations, both in that order, and the usable ranges | `fdt-pi5-platform-1`, `platform-1`, `platform-2`, `platform-10` to `platform-12` |
| The fields `described_bytes`, `managed_bytes` and `available_bytes` | Hexadecimal; `available_bytes` is the sum of the sizes of the usable ranges | `platform-11` |
| The queries `contains_ram(<span>)`, `is_available(<span>)` and `permits_backing(<span>)` of a boot memory map | `true` or `false` | `fdt-pi5-platform-1`, `platform-1` to `platform-3`, `platform-6`, `platform-9` to `platform-11` |
| The query `available_count(<span>)` | The number of usable ranges that hold the span, in decimal, the output of the oracle of the test | `platform-13` |

The vector `fdt-parser-8` places the tree at an odd host address. The parse
reads the bytes one at a time (lines 160 to 162), so the address is no input
of the specification, and the case holds the bytes alone.

A case asks the fields and queries that its test asserts, each whole: where
the test asserts a part of a field, such as the number of RAM ranges, one of
them or a flag of a reserved region, the case asks the whole field, and the
file writes it from the inputs that the row of the contract states. Where the
row states a property of a selected span rather than the span, the file
writes the span that the rule of lines 624 to 629 gives, computed by hand: in
`fdt-pi5-selection-1`, the span that starts at `0xa0000` is `0xa0000+0x2000`,
of the size asked, and the span at or above the end of the tree is
`0x201000+0x1000`, since the tree, at `0x200000`, ends below `0x201000`; in
`fdt-pi5-selection-3`, the span that starts at `0x480000` is
`0x480000+0x8000`. In `fdt-pi5-platform-1`, whose test asserts the first
boot range, the field `boot` holds the image and then the pages of the tree,
`0x200000+0x1000`, since the tree is shorter than a page; in `platform-10`,
whose test asserts the numbers of banks and of reservations, the fields
`ram` and `reservations` hold the 32 banks and the 130 page ranges.

### Vector disposition

The component has 55 of the 90 vectors of
[legacy test vectors](contract.md#legacy-test-vectors); the other 35, of the
Pi 5 device bindings, are replayed by the components that the contract
names and have no line in the vector file. Of the 55:

| Disposition | Vectors | Reason |
| --- | --- | --- |
| Replayed, 48 | `fdt-parser-1` to `-6` and `-9`, `fdt-translation-1` to `-5`, `fdt-discovery-1` to `-6`, `fdt-cpus-1` to `-6`, `fdt-pi5-1` to `-4`, `fdt-pi5-boundaries-1`, `-3` to `-5`, `fdt-pi5-selection-1` to `-3`, `fdt-pi5-platform-1` and `-2`, `platform-1`, `platform-3` to `platform-10`, `platform-12` and `platform-13` | Every case is a line of the vector file |
| Replayed with a large input, 1 | `fdt-pi5-boundaries-2` | Its second case is a tree longer than 128 KiB, a line of the vector file that the generator of the file builds; the representative case of the replay module is the first |
| Replayed in part, 4 | `fdt-parser-7`, `fdt-parser-8`, `platform-2`, `platform-11` | `fdt-parser-7`: its two cases of the padding bound call a function internal to the parse, which no entry reaches with them, as the row of the contract states. `fdt-parser-8`: the odd host address is no input of the specification, which reads bytes one at a time. `platform-2`: its three cases of the page allocator, two allocations and the free bytes, go through the page ownership table of the page-tables component, whose vectors cover them; the boot memory map that it takes is replayed. `platform-11`: the comparison of the usable bytes with the free bytes of a page allocator goes through the same table; the case compares them instead with the managed bytes less `0x80000`, `0x38000`, `0x14000` and `0x2000`, the difference that the row writes |
| Not applicable, 2 | `fdt-pi5-firmware-1`, `fdt-pi5-firmware-2` | Their inputs are the trees that the Raspberry Pi firmware ships and trees merged from them, device-tree files outside the prototype tree that the repository does not hold, lines 971 to 974; the requirements that they evidence have other vectors and the specification tests |

The comments of the vector file name the cases that are not applicable. The
replay module checks one representative case of each vector of the file, and
the whole file is replayed through the same `replay` by the driver of
`cargo xtask formal vectors`.

## Contract correspondence

Each row of the [entry table](contract.md#entry-points), lines 109 to 119,
and the Lean definitions that state its entries, below `Krepi.Spec.Fdt`:

| Line | Entries | Lean |
| --- | --- | --- |
| 109 | `fdt::Fdt::parse` | `Fdt.parse`, with `header`, `block`, `reservationMap`, `reservationsFrom`, `structureNodes`, `walkTokens`, `decodeToken` and `Walk.place` |
| 110 | `Fdt::nodes`, `find_node`, `reservations` and `total_size`; `Node::name`, `parent`, `property`, `string_property`, `enabled`, `address_cells`, `size_cells`, `reg`, `ranges`, `dma_ranges` and `translate_reg` | `Fdt.nodes`, `Fdt.findNode` with `Fdt.descend`, `Fdt.reservations`, `Fdt.totalSize`; `Node.name`, `Node.parent`, `Node.property`, `Node.stringProperty`, `Node.enabled`, `Node.addressCells`, `Node.sizeCells`, `Node.reg`, `Node.ranges`, `Node.dmaRanges` and `Node.translateReg` with `climbRanges` |
| 111 | `Fdt::discover_memory`, and `MemoryMap` with `ram`, `reserved` and `dynamic` | `Fdt.discoverMemory`, with `pushReserved`, `ramOfChild`, `addRam`, `Fdt.reservedMemory`, `reservedMemoryBinding`, `reservedOfChild` and `addReservedSpan`; `MemoryMap`, `MemoryMap.ram`, `MemoryMap.reserved`, `MemoryMap.dynamic` |
| 112 | `Fdt::discover_boot_memory`, and `BootMemory` with `ram`, `reserved`, `dynamic`, `dtb`, `image`, `ram_bytes` and `is_available` | `Fdt.discoverBootMemory`, with `checkCompatible`, `requiredEntries` and `compatibleEntries`; `BootMemory`, `BootMemory.ram`, `BootMemory.reserved`, `BootMemory.dynamic`, `BootMemory.dtb`, `BootMemory.image`, `BootMemory.ramBytes`, `BootMemory.isAvailable` |
| 113 | `BootMemory::find_available` | `BootMemory.findAvailable`, with `searchRanges`, `searchRange`, `alignUp` and `isPowerOfTwo` |
| 114 | `Fdt::discover_cpus`, and `CpuTopology` with `count`, `profile`, `affinity` and `validate_timers`; `CpuProfile::logical_id`, `affinity_shift` and `conduit` | `Fdt.discoverCpus`, with `cpuOfChild`, `idsComplete` and `CpuProfile.allows`; `CpuTopology`, `CpuTopology.count`, `CpuTopology.profile`, `CpuTopology.affinity`, `CpuTopology.validateTimers` with `TimerInterrupts.list`; `CpuProfile.logicalId`, `CpuProfile.affinityShift` with `AffinityLevel.shift`, `CpuProfile.conduit` |
| 115 | `cells_u64`, `Reg::new`, and `AddressMap::new`, `kind`, `to_parent` and `to_child` | `cellsU64`, `Reg.new` with `regEntry`, `AddressMap.new` with `window`, `AddressMap.kind`, `AddressMap.toParent` and `AddressMap.toChild` with `AddressMap.translate` and `throughWindows`; the entries of a `Reg` are its list `Reg.entries` |
| 116 | `MemoryPlan::all_ram`, `new` and `from_boot_memory` | `MemoryPlan.allRam`, with `addBank`, `sortByStart`, `admitBank`, `addBoot`, `addFirmware`, `checkPlanSpan` and `pagesOf`; `MemoryPlan.new`; `MemoryPlan.fromBootMemory` |
| 117 | `MemoryPlan::managed_banks`, `ram`, `reservations`, `boot_ranges`, `firmware_ranges`, `described_bytes`, `managed_bytes`, `contains_ram`, `is_available`, `permits_backing` and `available_ranges` | `MemoryPlan.managedBanks`, `MemoryPlan.ram`, `MemoryPlan.reservations`, `MemoryPlan.bootRanges`, `MemoryPlan.firmwareRanges`, `MemoryPlan.describedBytes`, `MemoryPlan.managedBytes`, `MemoryPlan.containsRam`, `MemoryPlan.isAvailable`, `MemoryPlan.permitsBacking`, and `MemoryPlan.availableRanges` with `usableFrom` |
| 118 | `Span::new`, `end` and `contains`; the value types `Fdt`, `Node`, `Span`, `ReservedRegion`, `MemoryMap`, `HandOverProfile`, `BootMemory`, `CpuProfile`, `PsciConduit`, `AffinityLevel`, `TimerInterrupts`, `CpuTopology`, `MemoryPlan`, `Error` and `PlanError` | `Span.new`, `Span.endAddr`, `Span.contains`; `Fdt`, `Node`, `Span` with `Span.Valid`, `ReservedRegion`, `MemoryMap`, `HandOverProfile`, `BootMemory`, `CpuProfile`, `PsciConduit`, `AffinityLevel`, `TimerInterrupts`, `CpuTopology`, `MemoryPlan`, `Error` and `PlanError` |
| 119 | `MAX_BLOB_SIZE`, `MAX_DEPTH`, `MAX_TOKENS`, `MAX_PROPERTIES`, `MAX_PROPERTY_NAME`, `MAX_RESERVATIONS`, `MAX_MEMORY_REGIONS` and `MAX_RESERVED_REGIONS` | The eight constants of the same names |

The rules of the contract and the definitions that state them:

| Contract | Lean, below `Krepi.Spec.Fdt` |
| --- | --- |
| [Format and bounds](contract.md#format-and-bounds) | `Fdt.parse` and the limits of `Basic`; the node access of `Nodes`; the invariant `Fdt.WellFormed`, with `ParseWellFormed` and `ParseLimitsExact` |
| [Rejection](contract.md#rejection-and-error-priority), rule 1: no partial result | The result types `Except Error α` and `Except PlanError α` |
| Rule 2: no panic | Every definition is total; no definition uses `panic!`, `get!` or a partial function |
| Rule 3: no choice among duplicates | `DuplicateProperty` in `Walk.place`, `AmbiguousMapping` in `Fdt.descend` and `throughWindows`, `BadProperty` for two CPU nodes of one ID in `cpuOfChild`, `Overlap` for RAM ranges that share an address in `addRam` and for RAM banks in `addBank`; the statements `NoChoiceAmongDuplicates` and `TranslationThroughOneWindow` |
| The error table, 21 and 7 variants | `Error` and `PlanError`, with `Error.name` and `PlanError.name` |
| Step 1 of the order of the parse and the entries on a tree: the header and the blocks | `header`, `block` |
| Step 2: the reservation map | `reservationMap`, `reservationsFrom` |
| Step 3: the tokens | `structureNodes`, `walkTokens`, `decodeToken`, `Walk.place` |
| Step 4: `Fdt::discover_memory` | `Fdt.discoverMemory` and the definitions of line 111 above |
| Step 5: `Fdt::discover_boot_memory` | `Fdt.discoverBootMemory` |
| Step 6: `Fdt::discover_cpus` | `Fdt.discoverCpus` |
| Step 7: translation | `cellsU64`, `Reg.new` with `regEntry`, `AddressMap.new` with `window`, `AddressMap.translate` with `throughWindows`; `Node.reg`, `Node.ranges`, `Node.dmaRanges` and `Node.translateReg` with `climbRanges` |
| Step 8: `Fdt::find_node`, `BootMemory::is_available` and `find_available` | `Fdt.findNode`; `BootMemory.isAvailable`; `BootMemory.findAvailable`, whose `Overflow` comes from `alignUp` |
| The order of the boot memory map, steps 1 and 8 | `MemoryPlan.new`: `checkPlanSpan`, the alignment and the size of the window; then `MemoryPlan.containsRam` of the window |
| Steps 2 to 7 of the boot memory map | `MemoryPlan.allRam`: the capacities; `addBank`; `admitBank`; `Alignment`; `addBoot`; `addFirmware` |
| [Memory discovery](contract.md#memory-discovery) | `Discovery` and `BootMemory`; the invariants `MemoryMap.WellFormed` and `BootMemory.Consistent` |
| [Boot memory map](contract.md#boot-memory-map) | `Plan`, and `BootMemory.findAvailable`; the invariant `MemoryPlan.WellFormed`, with `UsableRangesExact` and `FindAvailableLowest` |
| [CPU nodes](contract.md#cpu-nodes) | `Cpus`; the invariant `CpuTopology.Supported`, with `AffinityRoundTrip` |
| [Address translation](contract.md#address-translation) | `Translate`; the invariants `Reg.WellFormed` and `AddressMap.WellFormed` |
| [Check and execute](contract.md#check-and-execute) | Every entry is a function of its arguments; a `Reg`, an `AddressMap` and a `MemoryPlan` hold only checked spans, as their structural invariants state; the discoveries and the entries of the boot memory map build their result while they check and return it only when every check passed |
| [Work bounds](contract.md#work-bounds) | The fuel of each loop: `MAX_RESERVATIONS + 1`, `MAX_TOKENS`, the size of a block, `MAX_DEPTH`, `Q + 3` candidates in each RAM range of the selection, and `2 * R + 2` steps in each managed bank of `MemoryPlan.availableRanges`; the memory discovery and the CPU discovery walk lists of nodes, the memory discovery twice; the boot memory map folds over its at most 32 banks, 4 spans and 128 reservations, which step 2 bounds before they are read, and sorts the banks once; the usable ranges are at most one for each managed bank and each reservation, `AvailableRangesWellFormed` |
| [Determinism](contract.md#determinism) | Every definition is a function; the banks sorted by `sortByStart`, the boot storage and the firmware reservations in input order, and the usable ranges in address order; the values that no rule reads do not reach the results, `UnreadValuesIgnored` |
| [State fields](contract.md#state-fields), lines 860, 862 and 863 | `BootState`, `BootToken`, `BootState.coldEntry`, `BootState.publishPlan` with `PlanBuild`, `BootState.publishTopology`, `BootState.startSecondaries`; the invariants `BootState.WellFormed`, `BootState.FromHandOver` and `BootState.StartOrder`, which the cold entry establishes and each transaction preserves |
| State fields, line 861: the per-CPU values of the boot CPU | The values `Fdt`, `Node`, `MemoryMap` and `BootMemory` that the entries return, which no transaction holds |

## Requirement correspondence

Each requirement of the [requirements](requirements.md), the definitions that
state it, and its evidence on the specification: the cases of the
[vector file](../../../../verification/vectors/boot-platform/fdt.vectors)
that [`Krepi.SpecTests.Fdt.Replay`](../../../../verification/Krepi/SpecTests/Fdt/Replay.lean)
answers; the registered statements of [invariants](#invariants) and
[properties](#properties), whose theorems are planned; and the
[specification tests](#specification-tests), one input that the
specification must accept and one that it must reject for each requirement,
whose theorems in `Krepi.Proofs.Fdt.Stp` are planned. The last row
is the section of liveness, time and performance of the requirements, which
has no ID. The statements of the boot state serve the
[state fields](contract.md#state-fields), which no requirement observes.

| Requirement | Stated by | Registered statements | Specification tests | Vectors | Not stated by the specification |
| --- | --- | --- | --- | --- | --- |
| [FDT-R01](requirements.md#fdt-r01) | `Fdt.parse` with the limits of `Basic` | `ParseWellFormed`, `ParseLimitsExact`, `CheckFdtWellFormed` | `ParseAcceptsNameAtLimit`, `ParseRejectsNameAboveLimit` | `fdt-parser-1` to `-9` | - |
| [FDT-R02](requirements.md#fdt-r02) | The result types `Except Error α` and `Except PlanError α`; the order of the checks in each entry; rule 3 in `Walk.place`, `Fdt.descend`, `throughWindows`, `cpuOfChild`, `addRam` and `addBank` | `PrefixesRejected`, `NoChoiceAmongDuplicates`, `TranslationThroughOneWindow`; the witnesses of the error orders, `priorityStep1` to `priorityStep8` and `priorityPlanStep1` to `priorityPlanStep7`, proved in [`Witnesses`](#witnesses) | `EntriesReturnOnChangedByte`, `ParseRejectsPrefix` | `fdt-parser-1`, `fdt-parser-6`, and every case that names an error | That no input reads outside the bytes it was given, a property of the code, which the refinement proof of the target relates to the specification |
| [FDT-R03](requirements.md#fdt-r03) | `Fdt.discoverMemory` | `DiscoverMemoryWellFormed`, `NoChoiceAmongDuplicates`, `CheckMemoryMapWellFormed` | `DiscoveryAcceptsMaxRamRanges`, `DiscoveryRejectsExcessRamRanges` | `fdt-discovery-1` to `-6`, `fdt-parser-7`, `fdt-pi5-boundaries-5`, `fdt-pi5-selection-3` | - |
| [FDT-R04](requirements.md#fdt-r04) | `reservedOfChild`, `MemoryMap.dynamic`, `BootMemory.dynamic` | `UnreadValuesIgnored` | `DiscoveryRecordsDynamicReservations`, `DiscoveryRejectsEmptyStaticReservation` | `fdt-discovery-4`, `fdt-pi5-2`, `fdt-pi5-4` | The shipped trees of `fdt-pi5-firmware-1`, which the repository does not hold |
| [FDT-R05](requirements.md#fdt-r05) | `Fdt.discoverBootMemory`, `BootMemory.isAvailable`, `BootMemory.findAvailable` | `DiscoverBootMemoryConsistent`, `DiscoverBootMemoryWellFormed`, `FindAvailableWellFormed`, `FindAvailableLowest`, `CheckBootMemoryConsistent` | `Pi5AcceptsTreeAtLimit`, `Pi5RejectsTreeAboveLimit` | `fdt-pi5-1` to `-4`, `fdt-pi5-boundaries-1` to `-5`, `fdt-pi5-selection-1` to `-3` | Where the firmware leaves the tree and the layout of the image, which the board support of the Pi 5 states |
| [FDT-R06](requirements.md#fdt-r06) | `MAX_MEMORY_REGIONS` in `addRam`, `BootMemory.ramBytes`; `MemoryPlan.MAX_BANKS` and `MAX_RAM_BYTES` in `MemoryPlan.allRam`, and `MemoryPlan.fromBootMemory` | `DiscoverBootMemoryConsistent`, `AllRamWellFormed`, `FromBootMemoryWellFormed`, `UsableRangesExact` | `Pi5ModelsBuildBootMemoryMaps`, `BootMemoryMapRejectsRamAboveCapacity` | `fdt-pi5-platform-1`, the 8 GB model; `platform-1` and `platform-11`, its banks; the other four models only in the specification tests | The ranges that the firmware of the 1, 2, 4 and 16 GB models hands over, which the contract infers |
| [FDT-R07](requirements.md#fdt-r07) | `MemoryPlan.allRam`, `MemoryPlan.new`, `MemoryPlan.fromBootMemory`, the queries and `MemoryPlan.availableRanges` | `AllRamWellFormed`, `MemoryPlanNewWellFormed`, `FromBootMemoryWellFormed`, `AvailableRangesWellFormed`, `UsableRangesExact`, `NoChoiceAmongDuplicates`, `CheckMemoryPlanWellFormed` | `AllRamAcceptsMaxBootStorage`, `AllRamRejectsExcessBootStorage` | `fdt-pi5-platform-1` and `-2`, `platform-1` to `platform-13`, of which `platform-2` and `platform-11` in part | The mapping and the allocation of the usable ranges, which the page-tables component covers |
| [FDT-R08](requirements.md#fdt-r08) | `Fdt.discoverCpus`, `CpuProfile.logicalId`, `CpuTopology.validateTimers` | `DiscoverCpusSupported`, `AffinityRoundTrip`, `NoChoiceAmongDuplicates`, `CheckCpuTopologySupported` | `CpusAcceptsQemuPair`, `CpusRejectsRepeatedId` | `fdt-cpus-1` to `-6` | That the CPUs start, which the multicore domain shows |
| [FDT-R09](requirements.md#fdt-r09) | `Translate`: `cellsU64`, `Reg.new`, `AddressMap.new`, `AddressMap.kind`, `toParent`, `toChild`, `Node.reg`, `Node.ranges`, `Node.dmaRanges`, `Node.translateReg` | `SpanNewWellFormed`, `RegNewWellFormed`, `AddressMapNewWellFormed`, `NodeRegWellFormed`, `NodeRangesWellFormed`, `NodeDmaRangesWellFormed`, `ToParentWellFormed`, `ToChildWellFormed`, `TranslateRegWellFormed`, `TranslationThroughOneWindow`, `CheckRegWellFormed`, `CheckAddressMapWellFormed` | `TranslateRegThroughBus`, `TranslationRejectsTwoWindows` | `fdt-translation-1` to `-5`, `fdt-discovery-2` | The tagged addresses of PCI, which the PCIe and RP1 links cover |
| [FDT-R10](requirements.md#fdt-r10) | Every entry is a function of its arguments; `Fdt.discoverMemory` reads of `/chosen` only its `device_type` and, when that is `memory`, its `status` | `UnreadValuesIgnored`; `ColdEntryFromHandOver`, `PublishPlanFromHandOver`, `PublishTopologyFromHandOver` and `StartSecondariesFromHandOver`, by which the published topology stays that of the hand-over bytes | `SeedsDoNotReachResults`, `ChosenDeviceTypeIsRead` | Every case: the replay gives one output for each input | The three cold boots of QEMU virt, which the QEMU boot suite runs |
| [Liveness, time and performance](requirements.md#liveness-time-and-performance) | Every definition is total and ends by structural recursion on a measure that the contract bounds: the reservation map on fuel `MAX_RESERVATIONS + 1`; the tokens on fuel `MAX_TOKENS`; a string on the bytes up to the end of its block; `Node::translate_reg` on fuel `MAX_DEPTH`; `find_available` on the list of RAM ranges and on fuel `Q + 3` in each; `available_ranges` on the list of managed banks and on fuel `2 * R + 2` in each; the discoveries and the boot memory map on lists of nodes, ranges, banks, spans and reservations; the transactions of the boot state are single steps. No definition waits or takes a lock | None: every definition is total by structural recursion, which Lean checks, so termination needs no statement | None | Every case returns | The time of an entry, which no test bounds |

### FDT-R01

[FDT-R01](requirements.md#fdt-r01), the bounded parse of an untrusted tree,
is `Fdt.parse` with the limits of `Basic`: the size of the tree in `header`,
the reservation entries in `reservationsFrom`, the tokens in `walkTokens`, and
the depth, the properties of a node and the length of a property name in
`Walk.place` and `decodeToken`. The replay of
[`Krepi.SpecTests.Fdt.Replay`](../../../../verification/Krepi/SpecTests/Fdt/Replay.lean)
answers the cases of `fdt-parser-1` to `fdt-parser-9` in the
[vector file](../../../../verification/vectors/boot-platform/fdt.vectors)
through it. `ParseLimitsExact` states that each of the six limits accepts a
built tree at the limit and rejects one 1 above it with the error of the
contract, and `ParseWellFormed` that every tree that the parse accepts keeps
all of them (`Fdt.WellFormed`). The specification tests
`ParseAcceptsNameAtLimit` and `ParseRejectsNameAboveLimit` take the limit of
a property name, 64 bytes, on a tree with the padding that QEMU leaves.

### FDT-R02

[FDT-R02](requirements.md#fdt-r02), rejection without partial results: an
entry returns `Except Error α`, or `Except PlanError α` for the boot memory
map, so a failure carries one error and no value, and every definition is
total, so no input makes an entry panic. The error orders of the parse and
the entries on a tree, steps 1 to 8, and the eight steps of the boot memory
map are the order of the checks in each definition; the discoveries and the
entries of the boot memory map build their result while they check and
return it only at the end, so a failure leaves nothing of it. Duplicates are
rejected, never chosen: two properties of one name in `Walk.place`, two
sibling nodes on a path in `Fdt.descend`, two windows that hold a request in
`throughWindows`, RAM ranges that share an address in `addRam`, RAM banks
that share an address in `addBank`, and two CPU nodes of one logical ID in
`cpuOfChild`. The vectors `fdt-parser-1` and `fdt-parser-6` replay the
prefixes and the single-byte changes of the minimal tree, the latter with
the memory discovery and the node entries on every accepted tree.
`PrefixesRejected` states that every prefix of every accepted tree shorter
than its `totalsize` fails with `Truncated`; `NoChoiceAmongDuplicates` that
paths, CPU nodes, RAM ranges and banks are never chosen among, and
`TranslationThroughOneWindow` the same of the windows of a map. For each
step of the two orders, the witness `priorityStep1` to `priorityStep8` or
`priorityPlanStep1` to `priorityPlanStep7` gives an input that breaks that
step and a later rule and states the error of the step, the last part of the
criterion; the last step of the boot memory map has no later rule. The
specification test `EntriesReturnOnChangedByte` changes one byte of
`minimal` and states what the parse and the memory discovery return, and
`ParseRejectsPrefix` rejects a prefix of `minimal`, the rejection that the
requirement has besides its rule that nothing panics.

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
`fdt-pi5-selection-3`. `DiscoverMemoryWellFormed` states that the memory map
of a well-formed tree keeps `MemoryMap.WellFormed`, and
`NoChoiceAmongDuplicates` that its RAM ranges are all the spans of the
enabled memory nodes in tree order. The specification tests
`DiscoveryAcceptsMaxRamRanges` and `DiscoveryRejectsExcessRamRanges` take 32
and 33 RAM ranges, the first with a reserved region in a hole.

### FDT-R04

[FDT-R04](requirements.md#fdt-r04), dynamic reservations recorded and not
refused: `reservedOfChild` counts an enabled child of `/reserved-memory` with
`size` and without `reg` in `MemoryMap::dynamic` and reads neither its `size`
nor anything else of it, so the number of cells of its `size` is no reason
to reject the tree; a disabled one is skipped, and a child with `reg` and
`size` is static. `BootMemory::dynamic` is that of its memory map. The
replay answers the cases of `fdt-discovery-4`, `fdt-pi5-2` and `fdt-pi5-4`
with the outputs of the contract; `fdt-pi5-firmware-1`, whose input lies
outside the repository, has no line in the vector file.
`UnreadValuesIgnored` states that the values of a dynamic reservation other
than its `status` and flags, its `size` among them, whatever its cells, do
not reach the results of the discoveries. The specification test
`DiscoveryRecordsDynamicReservations` counts dynamic reservations with a
`size` of one and of two cells and ignores a disabled one, and
`DiscoveryRejectsEmptyStaticReservation` reads the `reg` of a child with
`reg` and `size` as a static region.

### FDT-R05

[FDT-R05](requirements.md#fdt-r05), the Pi 5 hand-over checks, is
`Fdt.discoverBootMemory` with the hand-over profile of the Pi 5: the limit
of the profile, 128 KiB, the address a multiple of its alignment, 8, 2
address cells and 2 size cells at the root, the root `compatible` in
`checkCompatible` with the two entries that the profile requires, a nonempty
image that shares no address with the tree, and the tree and the image each
inside one RAM range; the specification states these checks for every
profile. Its result holds the memory map, the spans of the tree and of the
image and the sum of the RAM ranges. `BootMemory.isAvailable` and
`BootMemory.findAvailable` give only spans inside one RAM range that touch
no exclusion, the image, the tree and every reserved region, so no span
bridges two RAM ranges or a hole. The replay answers the cases of
`fdt-pi5-1` to `fdt-pi5-4`, `fdt-pi5-boundaries-1` to
`fdt-pi5-boundaries-5` and `fdt-pi5-selection-1` to `fdt-pi5-selection-3`;
`fdt-pi5-firmware-2`, whose input lies outside the repository, has no line.
`DiscoverBootMemoryConsistent` and `DiscoverBootMemoryWellFormed`
state the checks of its result, `FindAvailableWellFormed` and
`FindAvailableLowest` those of the selection: its span is available and has
the lowest aligned start in the first RAM range that has one. The
specification tests `Pi5AcceptsTreeAtLimit` and `Pi5RejectsTreeAboveLimit`
take the hand-over tree of the 8 GB model at exactly 128 KiB and at 1 byte
more, with the hand-over profile of the Pi 5.

### FDT-R06

[FDT-R06](requirements.md#fdt-r06), every RAM model of the Pi 5: the 1 to 3
RAM ranges of every model fit `MAX_MEMORY_REGIONS` in `Fdt.discoverMemory`
and the 32 banks of `MemoryPlan.allRam`, and their sum, at most 16 GiB less
4 MiB, is `BootMemory::ram_bytes`, computed with `checkedAdd`, and fits
the 16 GiB that `admitBank` admits. `MemoryPlan.fromBootMemory` builds the
boot memory map of a boot memory, whose usable ranges leave out the hole
below 1 GiB, since `MemoryPlan.availableRanges` stays inside each managed
bank. The replay answers `fdt-pi5-platform-1`, the three measured ranges of
the 8 GB model through `discover_boot_memory` and `from_boot_memory`, and
`platform-1` and `platform-11`, the same banks given to `new` and to
`all_ram`. The specification test `Pi5ModelsBuildBootMemoryMaps` takes the
hand-over trees of the inferred ranges of the 1, 2, 4 and 16 GB models and
of the measured ranges of the 8 GB model through `discover_boot_memory`
and `all_ram`, and `BootMemoryMapRejectsRamAboveCapacity` a tree of the same
shape with 32 GB, which the boot memory map refuses. `AllRamWellFormed` and
`FromBootMemoryWellFormed` state that every boot memory map holds at most
32 banks of at most 16 GiB together, `DiscoverBootMemoryConsistent` that
`ram_bytes` is the exact sum of the RAM ranges, and `UsableRangesExact` that
no usable range bridges a hole.

### FDT-R07

[FDT-R07](requirements.md#fdt-r07), the boot memory map, is `Plan`:
`MemoryPlan.allRam` with 1 to 32 banks of at most 16 GiB together, which
`addBank` keeps disjoint and separate even where they are adjacent, sorted
by `sortByStart`, and their complete pages as managed banks in `admitBank`;
1 to 4 spans of boot storage, each rounded outward to pages by `pagesOf`,
inside one bank and on pages of its own in `addBoot`; at most 128 firmware
reservations, rounded outward, none on a page of boot storage in
`addFirmware`; `MemoryPlan.new`, which manages a window of whole pages, at
most 128 MiB, inside one bank; and `MemoryPlan.fromBootMemory`. The usable
ranges of `MemoryPlan.availableRanges` leave out every page of every
reservation, `reusable` ones included, since `addFirmware` keeps no flag,
and lie each inside one managed bank. The replay answers the cases of
`fdt-pi5-platform-1` and `-2` and of `platform-1` to `platform-13`, with the
change of `platform-10`, where three spans of boot storage that are all the
image fail with `Overlap`; `platform-2` and `platform-11` are replayed in
part, as [vector disposition](#vector-disposition) states. Boot storage of 4
spans accepted and of 5 refused with `Capacity` are the specification tests
`AllRamAcceptsMaxBootStorage` and `AllRamRejectsExcessBootStorage`.
`AllRamWellFormed`, `MemoryPlanNewWellFormed` and
`FromBootMemoryWellFormed` state `MemoryPlan.WellFormed` of every map that the
entries build, `AvailableRangesWellFormed` and `UsableRangesExact` that the
usable ranges are exactly the managed banks without the reservations, in
address order and maximal, and `NoChoiceAmongDuplicates` that `all_ram`
keeps every bank it is given.

### FDT-R08

[FDT-R08](requirements.md#fdt-r08), the CPU nodes, is `Cpus`:
`Fdt.discoverCpus` with `/cpus` enabled with 0 size cells, every CPU node an
enabled Cortex-A76 whose `reg` is the affinity of its logical ID in the
profile, IDs without a repeat in `cpuOfChild` and without a gap in
`idsComplete`, a count that the profile allows, `psci` as the
`enable-method` of every CPU but the first and, when the profile asks it,
of the first, and `/psci` with the conduit of the profile and a
`compatible` of `PSCI_COMPATIBLE`; `CpuProfile.logicalId`, which masks the
flag bits of `MPIDR_EL1`; and `CpuTopology.validateTimers`, which accepts
only the timer records of the profile for the admitted CPUs. The profiles
of the Pi 5 and of QEMU virt give the levels, the counts, the
`enable-method` of CPU 0 and the timer records that the requirement names.
The replay answers the cases of `fdt-cpus-1` to `fdt-cpus-6`.
`DiscoverCpusSupported` states the counts of a topology, `AffinityRoundTrip`
that the affinity of each CPU gives back its logical ID whatever the flag
bits, and `NoChoiceAmongDuplicates` that no two CPU nodes of an accepted
`/cpus` have one `reg`. The specification test `CpusAcceptsQemuPair` takes
two CPUs of QEMU virt, the first without an `enable-method`, with their
timer records and the profile `QemuHvc`, and
`CpusRejectsRepeatedId` the same tree with one ID twice.

### FDT-R09

[FDT-R09](requirements.md#fdt-r09), address translation, is `Translate`:
`reg` in the cells of the parent, `ranges` and `dma-ranges` with the node's
own cells on the child side, none of them inherited from an ancestor further
up; `cellsU64` that never drops a cell; the kinds of a map; the one window
that holds the whole request; and separate maps for CPU addresses and the
addresses of devices. The replay answers the cases of `fdt-translation-1` to
`fdt-translation-5` and `fdt-discovery-2`. The well-formedness statements of
`Span::new`, `Reg::new`, `AddressMap::new`, the node entries and the
translations state what each gives, and `TranslationThroughOneWindow` that a
translation succeeds exactly through the one window that holds the whole
request, at the request's offset in it. The specification test
`TranslateRegThroughBus` reads a `reg` in the cells of its bus and
translates it through the bus's `ranges`, not its `dma-ranges`, and
`TranslationRejectsTwoWindows` refuses a request that two windows hold.

### FDT-R10

[FDT-R10](requirements.md#fdt-r10), the same result on every boot: every
entry is a function of the bytes of the tree and of its arguments, with no
choice, so equal inputs give equal results. The parse checks the length
and the name of every property but never interprets its value, so the
values of the seeds that QEMU writes into `/chosen` do not decide whether it
accepts a tree; its result holds them as the values of their properties.
`Fdt.discoverMemory` reads of `/chosen` its `device_type`, as it does of
every child of the root, and, when that is `memory`, which makes `/chosen` a
memory node, its `status`: it skips a disabled one and fails with
`BadProperty` on the name of an enabled one, and reads nothing else of it.
So the seeds reach none of the RAM ranges, the reserved regions and the
number of dynamic reservations, and `MemoryPlan.allRam` takes only values,
the RAM ranges, the boot storage and the reserved regions, so the seeds reach
no boot memory map either. `UnreadValuesIgnored` states this of the memory
map, the boot memory and the CPU topology, for every value of `/chosen`
that the requirement leaves unread; the boot state publishes only the
topology of the hand-over bytes (`BootState.FromHandOver`). The
specification test `SeedsDoNotReachResults` boots two QEMU virt trees that
differ only in their seeds to the same memory map and boot memory map, and
states that the trees of their parse differ at most in values that no rule
reads, and `ChosenDeviceTypeIsRead` makes the memory discovery fail through
a broken `device_type` of `/chosen`, the one value of it that the discovery
reads there, the rejection that the requirement has besides its rule that
results are functions of their inputs.

## Dependencies

- Lean core of the Lean version in `verification/lean-toolchain`; the modules
  of the specification, of its invariants, of its properties and of its
  tests import neither Mathlib nor the Aeneas library nor generated
  definitions. The proof modules below `Krepi.Proofs.Fdt` also import
  Mathlib, so that the gate counts the heartbeats of their theorems.
- The [requirements](requirements.md) and the [contract](contract.md) of the
  component, and, as the contract cites them, the format of chapter 5, the
  names of sections 2.2.1 and 2.2.4 and the nodes of sections 3.4, 3.5, 3.7
  and 3.8 of DTSpec v0.4, and the affinity fields of `MPIDR_EL1` of the Arm
  Architecture Reference Manual.
- The [vector file](../../../../verification/vectors/boot-platform/fdt.vectors)
  and its replay,
  [`Krepi.SpecTests.Fdt.Replay`](../../../../verification/Krepi/SpecTests/Fdt/Replay.lean),
  which imports these modules.
