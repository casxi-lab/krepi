# Device-tree contract

This page governs the code of the `fdt` component of the
[boot and platform](../README.md) domain: the bounded parsing of the
flattened device tree that the firmware hands to the kernel, which the
kernel reads as untrusted input; the access to its nodes and properties and
the translation of addresses through `reg`, `ranges` and `dma-ranges`; the
discovery of the RAM ranges, the reserved regions and the dynamic
reservations of a tree; the CPU nodes and the PSCI conduit of the supported
boards; the Pi 5 boot memory, which checks the hand-over tree of the
Raspberry Pi 5 against the storage of the image and of the tree; and the
boot memory map, the RAM banks with the boot storage and the firmware
reservations excluded by whole pages, which the
[page-tables](../../memory/page-tables/contract.md) component of the
[memory domain](../../memory/README.md) takes as its input. The bindings of
the Pi 5 devices, its interrupt controller and timer, its UART, the PCIe
link to RP1, RP1 and the SD card, are not part of the component: the
components that use them read the tree through its node access and
translation. The observable behaviour that these rules serve, with its
evidence, is in the [requirements](requirements.md), the other document of
the component.

## Terms

- **Device tree.** A flattened devicetree blob in the format of chapter 5 of
  the Devicetree Specification, release v0.4: a 40-byte header, the memory
  reservation block, the structure block and the strings block. Its bytes
  are untrusted input ([security model](../../../security.md)).
- **Tree.** The value `Fdt` that `Fdt::parse` returns: a view of the bytes of
  a device tree whose header, blocks, reservation map and tokens have passed
  every check of [Format and bounds](#format-and-bounds). It borrows the
  bytes and copies none of them.
- **Hand-over tree.** The device tree that the firmware, or the loader of
  QEMU, leaves for the kernel at boot. The Raspberry Pi 5 firmware writes
  the RAM banks into the tree that it ships, adds reservations and applies
  the overlays of its configuration, so its hand-over tree differs from the
  shipped file.
- **Shipped tree.** A device-tree file as Raspberry Pi publishes it with its
  firmware, such as `bcm2712-rpi-5-b.dtb`, whose memory node is a
  placeholder that the firmware replaces.
- **Token.** One element of the structure block: begin node (1), end node
  (2), property (3), no-operation (4) or end (9).
- **Depth.** The number of nodes above a node on its path from the root: the
  root is at depth 0.
- **Cells.** Big-endian 32-bit words. The `#address-cells` and
  `#size-cells` of a node give the number of cells of the addresses and sizes
  in the `reg` of its children.
- **Span.** The value `Span`: the addresses `[start, start + size)`, where
  `start + size` fits in 64 bits.
- **RAM range.** A span of the `reg` of an enabled memory node that is a
  child of the root. The boot memory map calls the RAM ranges it keeps its
  **RAM banks**.
- **Reserved region.** The value `ReservedRegion`: a span that the kernel
  does not hand out, with the flags `no-map` and `reusable`. It is an entry
  of the memory reservation block, which counts as `no-map`, or a span of
  the `reg` of an enabled child of `/reserved-memory`.
- **Dynamic reservation.** An enabled child of `/reserved-memory` with a
  `size` property and no `reg`: a request that the operating system
  allocate a pool, such as the `linux,cma` node of the Raspberry Pi trees.
- **Boot storage.** The spans that hold what the kernel needs while it
  boots: the image with its BSS and stacks, the device tree, and the boot
  bundle where the board loads it apart from the image. The board gives
  them as a table of at most 4 spans.
- **Firmware reservation.** A reserved region as the boot memory map takes
  it.
- **Boot memory map.** The value `MemoryPlan`: the RAM banks, sorted by
  their start; the boot storage and the firmware reservations, each rounded
  outward to whole 4 KiB pages; and the managed banks, the complete pages
  of the banks that it manages.
- **Usable range.** A span of whole pages of a managed bank that no boot
  storage and no firmware reservation touches.
- **Pi 5 boot memory.** The value `Pi5BootMemory`: the memory map of a Pi 5
  hand-over tree, checked against the spans of the image and of the tree.
- **CPU profile.** The value `CpuProfile`: QEMU virt with PSCI over HVC,
  QEMU virt with EL2 and PSCI over SMC, or the Pi 5. It fixes the affinity
  level of the CPU IDs and the PSCI conduit.
- **RAM model.** One of the five Raspberry Pi 5 models, with 1, 2, 4, 8 or
  16 GB of RAM.

## Entry points

The module `fdt` of the provable core is planned, and so is every entry
below; the names are those that this contract fixes. Every entry is `pub`:
the boot code of the boards calls them, and the device bindings of the
boards read the tree through them. The page-tables component, which is part
of the core too, reads the boot memory map.

| Entry point | Kind | Called by | Rules |
| --- | --- | --- | --- |
| `fdt::Fdt::parse` (planned) | Function, host-testable | The boot code of a board, once on the boot CPU, with the bytes of the hand-over tree | [Format and bounds](#format-and-bounds), [Rejection and error priority](#rejection-and-error-priority) |
| `Fdt::nodes`, `find_node`, `reservations` and `total_size`, and `Node::name`, `parent`, `property`, `string_property`, `enabled`, `address_cells`, `size_cells`, `reg`, `ranges`, `dma_ranges` and `translate_reg` (planned) | Functions and iterators, host-testable | The entries of this component; the device bindings that the boards and other components read from a tree | [Format and bounds](#format-and-bounds), [Address translation](#address-translation) |
| `Fdt::discover_memory`, which returns a `MemoryMap` with `ram`, `reserved` and `dynamic` (planned) | Function, host-testable | The boot code of a board | [Memory discovery](#memory-discovery) |
| `Fdt::discover_pi5_boot_memory`, which returns a `Pi5BootMemory` with `ram`, `reserved`, `dynamic`, `dtb`, `image`, `ram_bytes` and `is_available` (planned) | Function, host-testable | The boot code of the Pi 5 board | [Memory discovery](#memory-discovery) |
| `Pi5BootMemory::find_available` (planned) | Function, host-testable | The boot code of the Pi 5 board, before the page ownership table exists | [Boot memory map](#boot-memory-map) |
| `Fdt::discover_cpus`, which returns a `CpuTopology` with `count`, `profile`, `affinity` and `validate_qemu_timers`, and `CpuProfile::logical_id`, `affinity_shift` and `conduit` (planned) | Functions, host-testable | The boot code of a board; the start of the secondary CPUs | [CPU nodes](#cpu-nodes) |
| `cells_u64`, `Reg::new`, and `AddressMap::new`, `kind`, `to_parent` and `to_child` (planned) | Functions and an iterator, host-testable | The node access of this component; device bindings | [Address translation](#address-translation) |
| `MemoryPlan::all_ram`, `new` and `from_pi5` (planned) | Functions, host-testable | The boot code of a board | [Boot memory map](#boot-memory-map) |
| `MemoryPlan::managed_banks`, `ram`, `reservations`, `boot_ranges`, `firmware_ranges`, `described_bytes`, `managed_bytes`, `contains_ram`, `is_available`, `permits_backing` and `available_ranges` (planned) | Functions and an iterator, host-testable | The kernel direct map and the page ownership table of the page-tables component; the boot code of a board | [Boot memory map](#boot-memory-map) |
| `Span::new`, `end` and `contains`, and the value types `Fdt`, `Node`, `Span`, `ReservedRegion`, `MemoryMap`, `Pi5BootMemory`, `CpuProfile`, `CpuTopology`, `MemoryPlan`, `Error` and `PlanError` (planned) | Functions and value types | Every caller of the entries above | [Rejection and error priority](#rejection-and-error-priority) |
| `MAX_BLOB_SIZE`, `MAX_DEPTH`, `MAX_TOKENS`, `MAX_PROPERTIES`, `MAX_PROPERTY_NAME`, `MAX_RESERVATIONS`, `MAX_MEMORY_REGIONS`, `MAX_RESERVED_REGIONS` and `PI5_MAX_BLOB_SIZE` (planned) | Constants | The boot code of a board, which bounds the slice of the tree with them | [Format and bounds](#format-and-bounds) |

## Extractability

- The module `fdt` of the provable core (planned), with its sources in
  `kernel/src/fdt.rs` and below `kernel/src/fdt/` (planned), follows the
  [provable Rust subset](../../../conventions/provable-subset.md): it is the
  module of the role fdt in its scope. It is plain code that reads byte
  slices and values and writes only the values that it returns; it holds no
  `unsafe` code, no assembly and no access to a register or to a physical
  address.
- The component has no hardware action, so no adapter of `kernel/arch` is
  part of it. The page-table logic and the `mmu` adapter of `kernel/arch`
  (planned), which turns the MMU on and stores into live tables, belong to
  the [page-tables](../../memory/page-tables/contract.md) component.
- The board crate obtains the bytes of the hand-over tree and wires the
  results into its boot code. It forms a slice of the 40-byte header at the
  address where its firmware leaves the tree, reads `totalsize`, and forms
  the slice of the whole tree only when `totalsize` is at least 40 and at
  most the limit of its board, within storage that it gives the boot memory
  map as boot storage; then it passes that slice to `Fdt::parse`. Forming a
  slice from an address is the `unsafe` site of
  [Open obligations](#open-obligations).
- The contract is written before the code, so this section holds no `paths`
  block; the change that adds the module writes its paths here.

## Format and bounds

`Fdt::parse` accepts a device tree in the format of chapter 5 of DTSpec
v0.4, of version 17 or of a later version that declares itself compatible
with version 16 or 17, and checks all of it before it returns a tree:

- **Header.** Ten big-endian words. The magic is `0xd00d_feed`.
  `totalsize` is at least 40 and at most `MAX_BLOB_SIZE`, and the bytes
  given hold at least `totalsize` bytes, of which only the first `totalsize`
  belong to the tree. `version` is at least 17, and `last_comp_version` is 16
  or 17 and not above `version`.
- **Blocks.** The structure block starts at a multiple of 4, has a size
  that is a multiple of 4 and is at least 12 bytes long; the memory
  reservation block starts at a multiple of 8. Every block starts after the
  header and ends within `totalsize`, and the structure and strings blocks
  do not intersect. The parse reads the bytes one at a time, so the bytes
  may lie at any address of the host; the alignment of the tree in physical
  memory is a rule of the board, 8 bytes on the Pi 5
  ([Memory discovery](#memory-discovery)).
- **Reservation map.** Entries of 16 bytes, an address and a size of 64
  bits each, up to an entry of two zeros. No entry, the terminator included,
  intersects the structure or strings block. At most `MAX_RESERVATIONS`
  entries precede the terminator; each is nonempty, ends within 64 bits and
  is disjoint from every earlier entry.
- **Tokens.** The structure block is a sequence of tokens: one root, a
  begin-node token with an empty name; in every node, its properties before
  its child nodes; every begin node closed by an end node; and the end
  token as the last token, where the block ends. No-operation tokens may
  appear between any two tokens. At most `MAX_TOKENS` tokens are read, the
  end token included.
- **Names.** A node name is a NUL-terminated UTF-8 string of letters,
  digits and `,._+-@`, empty only for the root, followed by zero bytes up to
  the next multiple of 4. A property name, read from the strings block at
  the offset that its token gives, is a NUL-terminated UTF-8 string of 1 to
  `MAX_PROPERTY_NAME` bytes of letters, digits and `,._+?#-`. The limit is
  above the 31 characters of section 2.2.4 of DTSpec v0.4, because vendor
  property names reach 32 characters in the Pi 5 tree. No property name
  occurs twice in one node, and no node holds more than `MAX_PROPERTIES`
  properties.
- **Depth.** No node lies deeper than `MAX_DEPTH - 1`: a path from the root
  holds at most `MAX_DEPTH` nodes, the root included.
- **Property padding.** The value of a property is exactly its declared
  length. The padding after it, up to the next multiple of 4, lies within
  the structure block, and its bytes are not checked: QEMU leaves bytes of
  earlier values there, as its tree of the machine `virt` shows in
  QEMU 11.1.2, where section 5.4 of DTSpec v0.4 requires zero bytes. The
  padding of node names stays zero.

The limits are those of the prototype tree. Each covers the trees of the
supported boards with a margin. The Pi 5 column gives the tree that the
firmware of commit `016253866bbd6c77fcb2a744a97d81e79ad4884f` ships,
`bcm2712-rpi-5-b.dtb`, and the 8 GB hand-over tree as the prototype measured
it with its firmware; the QEMU virt column gives the tree that QEMU 11.1.2
builds for the machine options of `cargo xtask qemu`, read with
`dumpdtb`. QEMU 8.2.2, which CI runs, builds the same machine type; that
its values are equal is an inference.

| Limit | Value | Pi 5 | QEMU virt | Margin | Vectors and tests |
| --- | --- | --- | --- | --- | --- |
| `totalsize`, `MAX_BLOB_SIZE`; for the Pi 5 also `PI5_MAX_BLOB_SIZE` | 2 MiB; 128 KiB for the Pi 5 | Shipped file 78,770 bytes; hand-over tree 80,588 and 80,596 bytes in the prototype's measurements | 1,048,576 bytes, whose blocks end at byte 7,793; the rest is zero | 2 for QEMU virt; about 1.6 for the Pi 5 hand-over tree | Above the limit: `fdt-parser-2` (2 MiB + 1) and `fdt-pi5-boundaries-2` (above 128 KiB); at the limit, and 1 above for the Pi 5: [Testing obligations](#testing-obligations) |
| Depth, `MAX_DEPTH` | 32 nodes on a path, so depth 31 at most | Depth 6 | Depth 5 | More than 4 | 33 nodes: `fdt-parser-5`; 32 nodes: [Testing obligations](#testing-obligations) |
| Tokens, `MAX_TOKENS` | 65,536, the end token included | 2,973 | 343 | About 22 | At the limit and 1 above: [Testing obligations](#testing-obligations) |
| Properties of one node, `MAX_PROPERTIES` | 512 | 334 in `/__symbols__` | 13 in `/pcie@10000000` | About 1.5 | 334, 512 and 513: `fdt-parser-9` |
| Bytes of a property name, `MAX_PROPERTY_NAME` | 64 | 32, `snps,parkmode-disable-fsls-quirk`, the only name of that length | 20 | 2 | 32, 64 and 65: `fdt-parser-9` |
| Entries of the reservation map, `MAX_RESERVATIONS` | 128, the terminator not counted | 0 in the shipped file; the prototype's measurement of the hand-over tree does not record the number, which is 1 if its region of 62 bytes comes from the map, an inference | 0 | At least 128 | At the limit and 1 above: [Testing obligations](#testing-obligations) |
| RAM ranges, `MAX_MEMORY_REGIONS` | 32 | 3 in the 8 GB hand-over tree, measured; 1 in the shipped placeholder; 1 to 3 for the other RAM models, inferred ([Memory discovery](#memory-discovery)) | 1 | More than 10 | 33: `fdt-discovery-6` and `fdt-pi5-boundaries-5`; 32: [Testing obligations](#testing-obligations) |
| Reserved regions, `MAX_RESERVED_REGIONS`: the entries of the reservation map and the spans of the static children of `/reserved-memory` together | 128 | 1 in the shipped file, `atf@0`, since its dynamic `linux,cma` is no reserved region; 2 in the 8 GB hand-over tree, measured, one of them outside every bank | 0 | 64 | 128: `fdt-pi5-selection-3`; 129: `fdt-pi5-boundaries-5` |

The node access reads only a tree that the parse accepted:

- `Fdt::nodes` gives every node in the order of the structure block.
  `Fdt::reservations` gives the entries of the reservation map in their
  order, and `total_size` the `totalsize` of the tree.
- `Fdt::find_node(path)` takes an absolute path with exact unit addresses,
  `/` for the root. A path that does not start with `/`, ends in `/` other
  than the root, or holds `//` fails with `BadPath`; a path that matches two
  sibling nodes fails with `AmbiguousMapping`; a path that matches nothing
  gives none. Aliases and abbreviated names are not resolved.
- `Node::property(name)` gives the value of the named property of the node,
  or none; `parent` gives the parent node, and none for the root.
- `Node::string_property(name)` gives a value that holds one NUL-terminated
  UTF-8 string, and fails with `BadString` for a value without a NUL or
  with a string that is not UTF-8, and with `BadProperty` for a byte after
  the NUL.
- `Node::enabled` reads `status` as `string_property` does, with its
  errors. It is true when `status` is absent or `okay`, the value of an
  operational device in section 2.3.4 of DTSpec v0.4, or `ok`, which that
  section does not list and which the prototype accepts, as Linux does; it
  is false for any other string.
- `Node::address_cells` and `size_cells` read the node's own
  `#address-cells` and `#size-cells`, each a value of 4 bytes or
  `BadProperty`, and are 2 and 1 when the property is absent (section 2.3.5
  of DTSpec v0.4). They are never inherited from an ancestor further up.

## Rejection and error priority

Three rules hold for every entry:

1. **No partial result.** An entry that fails returns its error and nothing
   else: no tree, memory map, topology, boot memory map or translation that
   a later check would have refused.
2. **No panic.** Every entry returns, for every input: for any byte string,
   `Fdt::parse` returns a tree or an error, and the entries on a tree return
   a value or an error. No input makes an entry panic or read outside the
   bytes it was given.
3. **No choice among duplicates.** Where an entry looks for one item and
   finds two, it rejects the input and never picks one of them: two
   properties of one name in a node (`DuplicateProperty`), two sibling nodes
   on a path (`AmbiguousMapping`), two translation windows that each hold a
   request (`AmbiguousMapping`), two CPU nodes of one logical ID
   (`BadProperty`), and RAM ranges or RAM banks that overlap (`Overlap`).
   Sibling nodes of one name that no path lookup meets, such as two
   `memory@0` nodes of which one is disabled, are no error.

The component has two error types. `Error`, of the parse, the node access,
the translation, the memory discovery, the CPU nodes and the Pi 5 boot
memory, has 21 variants; `PlanError`, of the boot memory map, has 7. The
variants keep the names of the two error types of the prototype tree,
`fdt::Error` and `platform::Error`, which `PlanError` renames. `Overflow`
and `Overlap` occur in both, for different rules. The prototype's
`fdt::Error::DynamicReservation` is gone, because a dynamic reservation is
no error ([Memory discovery](#memory-discovery)), and
`platform::Error::DeviceSize` is not taken, because only device windows,
which are not part of the component, use it.

| Error | Rule that it reports |
| --- | --- |
| `Error::Truncated` | The input holds fewer than 40 bytes or fewer than `totalsize`; or a block, a reservation entry, a token, a property value or the padding after it runs past the end of its block or of the tree |
| `Error::BadMagic` | The first word of the header is not `0xd00d_feed` |
| `Error::UnsupportedVersion` | `version` is below 17, or `last_comp_version` is not 16 or 17 or is above `version` |
| `Error::BadLayout` | `totalsize` is below 40; a block or the reservation map starts inside the header; the structure block is shorter than 12 bytes; the structure and strings blocks intersect; or a reservation entry intersects one of them |
| `Error::BadAlignment` | The offset or the size of the structure block is not a multiple of 4 or the offset of the reservation map not a multiple of 8; the address of a Pi 5 hand-over tree is not a multiple of 8; or the alignment of a selection is not a power of two |
| `Error::BadToken` | A token other than 1, 2, 3, 4 and 9 |
| `Error::BadTree` | A second root or a root with a name; a child without a name; a property outside every node or after the first child of its node; an end node without an open node; an end token with open nodes, without a root or before the end of the block; or a node without a parent where an entry needs one |
| `Error::BadString` | A node name or property name that is not a NUL-terminated UTF-8 string within its block or holds a character outside its set; a property name that is empty or longer than `MAX_PROPERTY_NAME`; a string property without a NUL or not UTF-8; or an entry of the Pi 5 `compatible` that is not UTF-8 |
| `Error::BadPadding` | A nonzero byte in the padding after a node name |
| `Error::DuplicateProperty` | Two properties of one name in a node |
| `Error::LimitExceeded` | A limit of [Format and bounds](#format-and-bounds) is exceeded: the size of the tree, also the Pi 5 limit, the depth, the tokens, the properties of a node, the entries of the reservation map, the RAM ranges or the reserved regions |
| `Error::UnsupportedCells` | A `reg` or a translation with address cells other than 1 or 2, or size cells above 2; a number of more than 2 cells; a Pi 5 root whose cells are not 2 and 2; or `/cpus` whose address cells are not 1 or 2 |
| `Error::BadProperty` | A property whose value breaks its binding: a cell count that is not 4 bytes; a `reg` or translation value that is empty where a value is required or not a whole number of entries; a flag with a value; a string property with a byte after its NUL; an enabled node with only one of a memory name and the `device_type` `memory`; a `/reserved-memory` without explicit cells equal to those of the root or without an empty `ranges`; `no-map` with `reusable`; a CPU, PSCI or timer binding of [CPU nodes](#cpu-nodes) that does not hold; or a Pi 5 `compatible` that does not end with a NUL, lacks an entry or has an empty one |
| `Error::MissingProperty` | A required node or property is absent: the `reg` of a node asked for it; `reg` and `size` alike in an enabled child of `/reserved-memory`; `/cpus`, the `reg` of a CPU node or `/psci`; or the `compatible` of a Pi 5 root |
| `Error::Overflow` | An offset, span, translated address, page rounding or sum leaves 64 bits; or a span of a one-cell address leaves the first 4 GiB |
| `Error::EmptyRegion` | A reservation entry, RAM range, reserved region, translation window or translation request of size 0; an empty image; a selection of size 0 or with an empty bound; or an empty span asked of the Pi 5 boot memory |
| `Error::Overlap` | Two reservation entries or two RAM ranges overlap, or the image overlaps the Pi 5 hand-over tree |
| `Error::Unmapped` | A translation through an absent map, or through windows of which none holds the whole request or one holds part of it; or a Pi 5 hand-over tree or image outside every single RAM range |
| `Error::AmbiguousMapping` | A path that matches two sibling nodes, or a request that two windows hold |
| `Error::BadPath` | A path that is not absolute, ends in `/` other than the root or holds `//` |
| `Error::NoMemory` | No enabled RAM range |
| `PlanError::InvalidRange` | A managed window, RAM bank, boot storage span or firmware reservation of size 0 |
| `PlanError::Overflow` | A span, its rounding to pages or the sum of the RAM banks leaves 64 bits |
| `PlanError::Alignment` | A managed window whose ends are not on 4 KiB pages, or RAM banks without one complete page |
| `PlanError::Capacity` | No RAM bank or more than 32; no boot storage or more than 4 spans of it; more than 128 firmware reservations |
| `PlanError::Overlap` | Two RAM banks overlap; two spans of boot storage share a page; or a firmware reservation shares a page with boot storage |
| `PlanError::OutsideRam` | The pages of a boot storage span, or a managed window, lie outside every single RAM bank |
| `PlanError::ArenaTooLarge` | A managed window above 128 MiB, or RAM banks of more than 16 GiB together |

When an input breaks several rules, the entry reports the error of the
first broken rule in the orders below, which are those of the prototype
tree. An entry that calls another, such as `discover_pi5_boot_memory` with
`discover_memory`, reports the error of the callee at the step where it
calls it.

The parse and the entries on a tree:

1. `Fdt::parse`: fewer than 40 bytes, `Truncated`; the magic, `BadMagic`;
   `totalsize` below 40, `BadLayout`; above `MAX_BLOB_SIZE`,
   `LimitExceeded`; fewer bytes than `totalsize`, `Truncated`; the
   versions, `UnsupportedVersion`; the alignment of the structure block and
   of the reservation map, `BadAlignment`; the structure block and then the
   strings block within the tree, `BadLayout`, `Overflow` or `Truncated`;
   a structure block shorter than 12 bytes or a reservation map inside the
   header, then intersecting blocks, `BadLayout`.
2. The reservation map, entry by entry: an entry past the tree,
   `Overflow` or `Truncated`; on a block, `BadLayout`; then, unless it is
   the terminator, more than `MAX_RESERVATIONS` entries, `LimitExceeded`;
   its end, `Overflow`; its size, `EmptyRegion`; overlap with an earlier
   entry, `Overlap`.
3. The tokens, in the order of the structure block. For each token, first
   its encoding: its tag past the end of the block, `Truncated`, then a tag
   other than 1, 2, 3, 4 and 9, `BadToken`. For a begin node, then its
   name without a NUL in the block or not UTF-8, `BadString`; the padding
   after the name past the end of the block, `Truncated`, then a nonzero
   byte in it, `BadPadding`; then a character of the name outside its set,
   `BadString`. For a property, then its length and name offset past the
   end of the block, `Truncated`; the end of its value beyond 64 bits,
   `Overflow`, then past the end of the block, `Truncated`; its name,
   `BadString`; then the padding after the value past the end of the block,
   `Truncated`. Then its place in the tree: `BadTree`, the depth
   `LimitExceeded`, the properties of its node `LimitExceeded`, then
   `DuplicateProperty`. More than `MAX_TOKENS` tokens without the end
   token, `LimitExceeded`.
4. `Fdt::discover_memory`: the entries of the reservation map, in order,
   as reserved regions, `LimitExceeded` beyond `MAX_RESERVED_REGIONS`; the
   children of the root, in tree order: `device_type`, `status`, the
   binding of an enabled memory node `BadProperty`, its `reg`, and each of
   its ranges `EmptyRegion`, `Overlap` or `LimitExceeded`; no RAM range,
   `NoMemory`; the lookup of `/reserved-memory`, its binding `BadProperty`
   and its `status`; its children, in tree order: `status`, the flags
   `BadProperty`, neither `reg` nor `size` `MissingProperty`, the `reg`,
   and each of its spans `EmptyRegion` or `LimitExceeded`.
5. `Fdt::discover_pi5_boot_memory`: `totalsize` above `PI5_MAX_BLOB_SIZE`,
   `LimitExceeded`; the address of the tree, `BadAlignment`; the address
   cells of the root, a value that is not 4 bytes `BadProperty`, then a
   number other than 2 `UnsupportedCells`, and then its size cells in the
   same way; the root `compatible`: absent, `MissingProperty`; a value that
   does not end with a NUL, `BadProperty`; then each entry in order, not
   UTF-8 `BadString`, then empty `BadProperty`; then without
   `raspberrypi,5-model-b` or without `brcm,bcm2712`, `BadProperty`; the
   span of the tree, `Overflow`; the image, `EmptyRegion` then `Overflow`;
   the image on the tree, `Overlap`; `discover_memory`; the tree, then the
   image, outside every single RAM range, `Unmapped`; the sum of the RAM
   ranges, `Overflow`.
6. `Fdt::discover_cpus`: `/cpus` absent, `MissingProperty`; disabled or
   with size cells other than 0, `BadProperty`; its address cells,
   `UnsupportedCells`; each child of `/cpus` in tree order: first its
   `device_type`, `BadString` or `BadProperty`, and a child whose
   `device_type` is not `cpu` is skipped; then, for a CPU node, disabled or
   another model, `BadProperty`; no `reg`, `MissingProperty`; its value,
   `UnsupportedCells` or `BadProperty`; its ID, `BadProperty`; its
   `enable-method`, `BadProperty`; then the set of IDs, `BadProperty`;
   `/psci` absent, `MissingProperty`; its binding, `BadProperty`. Each
   string property of these steps, such as `status`, `compatible` and
   `method`, fails as `Node::string_property` does, `BadString` or
   `BadProperty`, at its step.
7. Translation: `cells_u64`, the number of cells `UnsupportedCells`, then
   the length `BadProperty`. `Reg::new`, the cells `UnsupportedCells`, the
   length `BadProperty`, then each entry `Overflow`. `AddressMap::new`, the
   cells `UnsupportedCells`, the length `BadProperty`, then each window
   `EmptyRegion` then `Overflow`. A translation: the request
   `EmptyRegion`, its width `Overflow`, an absent map `Unmapped`, an
   identity map the target width `Overflow`; the windows in order, a second
   window that holds the request `AmbiguousMapping`, a window that holds
   part of it `Unmapped`, the translated span `Overflow`; no window that
   holds it, `Unmapped`.
8. `Fdt::find_node`: the path, `BadPath`; each component, `AmbiguousMapping`.
   `Pi5BootMemory::is_available`: `EmptyRegion`, then `Overflow`.
   `Pi5BootMemory::find_available`: a size of 0 or an empty bound,
   `EmptyRegion`; the alignment, `BadAlignment`; then `Overflow`.

The boot memory map:

1. `MemoryPlan::new` only: the managed window, `InvalidRange` or
   `Overflow`; its alignment, `Alignment`; above 128 MiB, `ArenaTooLarge`.
2. The numbers of RAM banks, boot storage spans and firmware reservations,
   `Capacity`.
3. Each RAM bank in input order: `InvalidRange` or `Overflow`, then
   `Overlap` with an earlier bank.
4. The RAM banks in address order: the sum `Overflow`, then above 16 GiB
   `ArenaTooLarge`, then the rounding of the start of the bank `Overflow`.
5. No complete page in any bank, `Alignment`.
6. Each boot storage span in input order: its pages `InvalidRange` or
   `Overflow`; outside every single bank, `OutsideRam`; a page shared with
   earlier boot storage, `Overlap`.
7. Each firmware reservation in input order: its pages `InvalidRange` or
   `Overflow`; a page shared with boot storage, `Overlap`.
8. `MemoryPlan::new` only: the managed window outside every single bank,
   `OutsideRam`.

The orders differ from the prototype in two places, both changes of
behaviour ([Behaviour changes](#behaviour-changes)): at step 4 of the
entries on a tree, a child with `size` and without `reg` is a dynamic
reservation, where the prototype failed with `DynamicReservation`; and at
step 2 of the boot memory map, boot storage may hold up to 4 spans, where
the prototype allowed 2.

## Memory discovery

`Fdt::discover_memory` reads the RAM ranges, the reserved regions and the
dynamic reservations of a tree, as sections 3.4 and 3.5 of DTSpec v0.4
describe them:

- **Reservation map.** Each entry of the memory reservation block is a
  reserved region with `no-map` set and `reusable` clear.
- **RAM.** A child of the root whose name is `memory` or starts with
  `memory@`, or whose `device_type` is `memory`, is a memory node. A disabled
  memory node is skipped before its binding is checked, so a disabled node
  that describes RAM of the secure state under another name is no error and
  no RAM. An enabled memory node has both the name and the `device_type`,
  or the discovery fails with `BadProperty`. Each span of its `reg`, in the
  cells of the root, is a RAM range: nonempty, disjoint from every other RAM
  range (`Overlap`) and at most `MAX_MEMORY_REGIONS` of them
  (`LimitExceeded`). Without a RAM range the discovery fails with
  `NoMemory`.
- **Reserved memory.** `/reserved-memory`, where it exists, has its own
  `#address-cells` and `#size-cells`, equal to those of the root, and an
  empty `ranges`, or the discovery fails with `BadProperty`; a disabled
  `/reserved-memory` holds no reservation. Each enabled child has `no-map`
  and `reusable` as flags without a value (`BadProperty`), not both of them
  (`BadProperty`: section 3.5.2 of DTSpec v0.4 makes them exclusive). Each
  span of the `reg` of a child is a reserved region with those flags, and
  the reservation map and these spans together hold at most
  `MAX_RESERVED_REGIONS` (`LimitExceeded`). A child with `reg` and `size` is
  static, as DTSpec v0.4 states. A child with neither fails with
  `MissingProperty`.
- **Dynamic reservations.** An enabled child of `/reserved-memory` with
  `size` and without `reg` is a dynamic reservation. The discovery checks
  only that form, counts the node in `MemoryMap::dynamic` and goes on: a
  dynamic reservation is no reserved region and no error, its `size` is not
  read, so the number of its cells is no reason to reject it, and its
  `alloc-ranges` are not read either. The kernel allocates no pool for it.
  The Pi 5 trees hold such a node, `linux,cma`, with a `size` of one cell
  below a `#size-cells` of 2, as the Raspberry Pi device tree source writes
  it for older firmware; because the tree is accepted with it, no boot
  configuration has to disable the node.
- **Reserved regions and RAM.** A reserved region need not lie in a RAM
  range: one in a hole between banks, or outside RAM, is accepted and kept
  like any other. An entry of the reservation map may overlap a span of
  `/reserved-memory`, and the spans of `/reserved-memory` may overlap each
  other; only the entries of the reservation map are disjoint from each
  other ([Format and bounds](#format-and-bounds)). Reserved regions may also
  overlap RAM ranges; every one stays excluded
  ([Boot memory map](#boot-memory-map)).
- **No-map.** The `no-map` flag of a reserved region, which section 3.5.2 of
  DTSpec v0.4 defines as a region that the operating system must not map as
  part of its standard mapping of system memory, is kept with the region.
  The boot memory map keeps every page of every reserved region out of its
  usable ranges, whatever its flags, and the
  [kernel direct map](../../memory/page-tables/contract.md#kernel-direct-map)
  maps usable ranges only, so no `no-map` region is mapped. `reusable` is
  kept too and releases nothing.

`Fdt::discover_pi5_boot_memory(dtb_address, image)` checks the hand-over
tree of a Raspberry Pi 5 against the spans that the board gives for the
tree and for the image with its BSS and stacks. The tree is at most
`PI5_MAX_BLOB_SIZE`, 128 KiB; its address is a multiple of 8, as section 5.6
of DTSpec v0.4 requires; the root has 2 address cells and 2 size cells
(`UnsupportedCells`); the root `compatible` is a list of nonempty,
NUL-terminated UTF-8 strings that holds `raspberrypi,5-model-b` and
`brcm,bcm2712`, in any order and with other entries. The span of the tree
is `[dtb_address, dtb_address + totalsize)`. The image is nonempty and
disjoint from the tree. After `discover_memory`, the tree and the image each
lie inside one RAM range, and `ram_bytes` is the sum of the RAM ranges.
`Pi5BootMemory::is_available(span)` is true for a nonempty span inside one
RAM range that touches neither the tree nor the image nor any reserved
region, `reusable` ones included. The answer describes memory; it is no
ownership. These queries know only the image and the tree: boot storage
beyond them, such as a boot bundle that the board loads apart from the
image, is excluded only by the boot memory map.

A shipped tree is parsed like any other, but its memory node is the
placeholder of the Raspberry Pi tree, `/memory@0` with `reg` `[0,
0x2800_0000)`, 640 MiB, which the bootloader replaces, and the mainline
Linux tree of the board has no memory node at all. The RAM of a shipped
tree therefore says nothing about the installed RAM: a board takes its RAM
only from the hand-over tree.

The Pi 5 is sold with 1, 2, 4, 8 or 16 GB of RAM. The 8 GB model hands over
three RAM ranges, as the prototype measured on three cold boots with its
firmware: `[0, 0x3fc0_0000)`, `[0x4000_0000, 0x1_0000_0000)` and
`[0x1_0000_0000, 0x2_0000_0000)`, which span 8 GiB with a hole of 4 MiB at
`[0x3fc0_0000, 0x4000_0000)`, below 1 GiB, and hold 8,585,740,288 bytes,
8 GiB less 4 MiB. Its hand-over tree held two reserved regions, both
`no-map` and not `reusable`: `atf@0` at `[0, 0x8_0000)`, inside the first
range, and 62 bytes at `[0x3fd2_31e0, 0x3fd2_321e)`, in the hole and so
inside no range, which the discovery accepts. No public document gives the
ranges of the other models, and the Raspberry Pi device tree source has
only the placeholder that the bootloader fills, so their shapes are
inferred from the 8 GB measurement: RAM from address 0 up to the installed
size, with ranges divided at 1 GiB and at 4 GiB and the same hole of 4 MiB
below 1 GiB.

| RAM model | RAM ranges of the hand-over tree | RAM | Basis |
| --- | --- | --- | --- |
| 1 GB | `[0, 0x3fc0_0000)` | 1 GiB less 4 MiB | Inferred |
| 2 GB | `[0, 0x3fc0_0000)`, `[0x4000_0000, 0x8000_0000)` | 2 GiB less 4 MiB | Inferred |
| 4 GB | `[0, 0x3fc0_0000)`, `[0x4000_0000, 0x1_0000_0000)` | 4 GiB less 4 MiB | Inferred |
| 8 GB | `[0, 0x3fc0_0000)`, `[0x4000_0000, 0x1_0000_0000)`, `[0x1_0000_0000, 0x2_0000_0000)` | 8 GiB less 4 MiB | Measured by the prototype |
| 16 GB | `[0, 0x3fc0_0000)`, `[0x4000_0000, 0x1_0000_0000)`, `[0x1_0000_0000, 0x4_0000_0000)` | 16 GiB less 4 MiB | Inferred |

Every model has 1 to 3 RAM ranges, within `MAX_MEMORY_REGIONS`, and at most
16 GiB less 4 MiB of RAM, within the 16 GiB of the boot memory map. Only
the 8 GB model runs on a board in release 0.1; the other four are covered
by host tests on trees of their inferred shapes
([Testing obligations](#testing-obligations)) and are not run on a board in
that release. The shapes are a property of the firmware: another firmware
version or configuration may hand over other ranges, which the rules
accept within the limits.

On QEMU virt, QEMU's loader places the tree at the start of RAM,
`0x4000_0000`, with one memory node, `/memory@40000000` of 128 MiB on the
machine of `cargo xtask qemu`, no `/reserved-memory` and an empty
reservation map.

## Boot memory map

`MemoryPlan::all_ram(ram, boot, firmware)` builds the boot memory map from
the RAM ranges of a discovery, the boot storage table of the board and the
reserved regions of the discovery as firmware reservations:

- **RAM banks.** 1 to 32 nonempty RAM banks, disjoint, kept separately even
  where two are adjacent, and sorted by their start. Together they hold at
  most 16 GiB (`ArenaTooLarge`), the capacity that every RAM model needs.
  The managed banks are the complete 4 KiB pages of each bank; a bank
  without a complete page contributes none, and at least one bank has one
  (`Alignment`).
- **Boot storage.** 1 to 4 spans: the image with its BSS and stacks, the
  tree, the boot bundle where the board loads it apart from the image, and
  one more. Each is rounded outward to whole pages, lies with
  its pages inside one RAM bank (`OutsideRam`) and shares no page with
  another span of boot storage (`Overlap`).
- **Firmware reservations.** At most 128, each rounded outward to whole
  pages. They may overlap each other and lie outside every bank, but none
  shares a page with boot storage (`Overlap`): a page that the kernel keeps
  and reads as boot storage cannot also be a page that the firmware
  reserved.
- **Reservations.** The pages of the boot storage, in input order, and then
  those of the firmware reservations, in input order.
- **Queries.** `contains_ram(range)` holds when one bank contains the range;
  `is_available(range)` when one bank contains it and no reservation
  touches it; `permits_backing(range)` when a managed bank contains it and
  it is available. `available_ranges` gives the usable ranges: the managed
  banks without the union of the reservations, in address order, each
  inside one bank, so that no usable range bridges two banks or a hole.
  `described_bytes` is the sum of the banks and `managed_bytes` that of the
  managed banks.

`MemoryPlan::new(window, ram, boot, firmware)` builds the same map but
manages only `window`: a span of whole pages, at most 128 MiB long, inside
one bank, for a board or a test that manages a part of RAM.
`MemoryPlan::from_pi5(memory, window, more)` is `new` with the RAM ranges,
the image, the tree, the further boot storage `more` of the board and the
reserved regions of a Pi 5 boot memory.

`Pi5BootMemory::find_available(size, alignment, minimum, limit)` selects a
span of `size` bytes, aligned to `alignment`, a power of two, within
`[minimum, limit)` and inside one RAM range, that touches neither the
image, nor the tree, nor any reserved region. It takes the RAM ranges in
tree order and gives the span with the lowest aligned start in the first
range that has one, and none when no range has one. A selected span
describes memory and grants no ownership; the page ownership table of the
page-tables component hands out pages.

The boot memory map allocates nothing and maps nothing: the
[kernel direct map](../../memory/page-tables/contract.md#kernel-direct-map)
and the [page ownership](../../memory/page-tables/contract.md#page-ownership)
table of the page-tables component take its usable ranges and its
reservations as values.

## CPU nodes

`Fdt::discover_cpus(profile)` reads the CPUs of a board before any of them
is started, as sections 3.7 and 3.8 of DTSpec v0.4 describe the nodes:

- `/cpus` exists (`MissingProperty`), is enabled, has a `#size-cells` of 0
  (`BadProperty`) and an `#address-cells` of 1 or 2 (`UnsupportedCells`).
- Each child with the `device_type` `cpu` is a CPU node. It is enabled, its
  `compatible` is exactly `arm,cortex-a76`, and its `reg`, of the address
  cells of `/cpus`, is the affinity of the CPU. The affinity is
  `id << affinity_shift` for a logical ID from 0 to 3, where the shift is 8
  on the Pi 5, whose CPU IDs are affinity level 1 of `MPIDR_EL1`, and 0 on
  QEMU virt. No two CPU nodes have one ID. Every CPU but ID 0, and on the
  Pi 5 every CPU, has the `enable-method` `psci`.
- The IDs are 0 to `count - 1`, where `count` is 1, 2 or 4, and 4 on the
  Pi 5; any other set fails with `BadProperty`.
- `/psci` exists (`MissingProperty`), is enabled, its `method` is the
  conduit of the profile, `hvc` for QEMU virt without EL2 and `smc` for
  QEMU virt with EL2 and for the Pi 5, and its `compatible` is exactly one
  of the lists `arm,psci-0.2`; `arm,psci-1.0`, `arm,psci-0.2`; and
  `arm,psci-1.0`, `arm,psci-0.2`, `arm,psci` (`BadProperty`).
- `CpuProfile::logical_id(mpidr)` takes only the affinity fields of
  `MPIDR_EL1`, `mpidr & 0xff_00ff_ffff`, so that the U, MT and other flag
  bits do not change the ID; it gives none for an affinity that is not
  `id << affinity_shift` with an ID below 4. `CpuTopology::affinity(i)` is
  `i << affinity_shift` for `i` below `count`, and none otherwise.
- `CpuTopology::validate_qemu_timers(interrupts)` checks the `interrupts` of
  the timer node of QEMU virt: records of three cells, type 1 for a private
  interrupt, its number and the flags `((1 << count) - 1) << 8 | 4`, the
  admitted CPUs and a level-high trigger, for the private interrupts 13, 14,
  11 and 10 in this order and, with EL2, 12 after them, with nothing else.
  For the Pi 5 profile it fails with `BadProperty`: the timer of the Pi 5
  belongs to its board support.

## Address translation

- `cells_u64(bytes, cells)` reads a number of 0, 1 or 2 cells and fails
  with `UnsupportedCells` for more, and with `BadProperty` when the bytes
  are not exactly that many cells. It never drops a high cell.
- `Reg::new(bytes, address_cells, size_cells)` accepts 1 or 2 address
  cells and 0 to 2 size cells (`UnsupportedCells`), a nonempty value of
  whole entries (`BadProperty`), and checks every entry before it gives
  one: its span ends within 64 bits and, with one address cell, within the
  first 4 GiB (`Overflow`). `Node::reg` reads the `reg` of the node in the
  cells of its parent (`MissingProperty` without `reg`).
- `AddressMap::new(bytes, child_cells, parent_cells, size_cells)` accepts
  1 or 2 child and parent address cells and 0 to 2 size cells
  (`UnsupportedCells`). An absent property is the kind `Absent`, which maps
  nothing; an empty one the kind `Identity`; any other value the kind
  `Windows`, which needs size cells and whole windows (`BadProperty`), each
  nonempty (`EmptyRegion`) and with child and parent spans within 64 bits
  and within their widths (`Overflow`), all checked at construction.
- `to_parent(span)` and `to_child(span)` translate a nonempty request within
  the width of its side. An absent map fails with `Unmapped`; an identity
  map gives the same span, within the width of the other side; a map of
  windows translates through the one window that holds the whole request,
  adding the request's offset in it. Two windows that hold it fail with
  `AmbiguousMapping`, a window that holds part of it fails with `Unmapped`
  even when another holds all of it, and no window that holds it fails with
  `Unmapped`.
- `Node::ranges` and `dma_ranges` read the `ranges` and `dma-ranges` of the
  node, with its own cells for the child side and the address cells of its
  parent for the parent side (sections 2.3.8 and 2.3.9 of DTSpec v0.4).
  `ranges` is the translation of CPU addresses, `dma-ranges` a separate map
  of the addresses that devices use: neither stands in for the other, and an
  absent `dma-ranges` is absent, not identity.
- `Node::translate_reg(span)` translates a span of the node's parent bus
  through the `ranges` of each bus above it, the nearest first, up to the
  root, and fails when the result leaves 64 bits.
- Addresses of three cells, such as those of PCI, fail with
  `UnsupportedCells` and are never truncated; their tagged translation
  belongs to the [PCIe and RP1 links](../README.md#pcie-and-rp1-links).

## Check and execute

The component writes no state: every entry reads its inputs and fills
only a local result value, which the caller cannot see before the entry
returns. Its only write that is visible outside is the return, so every
check of an entry completes before that write, and the write phase, the
return of the value, cannot fail
([rule 1](../../../conventions/provable-subset.md#1-check-then-execute)):

- `Fdt::parse` checks the header, the blocks, the reservation map and every
  token before it returns a tree.
- The node access, the translation, the queries and `find_available` read
  their inputs and return a value or an error.
- The iterators, `Fdt::nodes`, `Fdt::reservations`, the entries of a `Reg`
  and `MemoryPlan::available_ranges`, read only what was checked before
  they were made: the parse checked the tokens and the reservation map,
  `Reg::new` the entries of the `Reg`, and the entry that built the boot
  memory map its banks and reservations. Each call of `next` advances only
  the iterator's own cursor and does not fail.
- `discover_memory`, `discover_pi5_boot_memory`, `discover_cpus`,
  `MemoryPlan::all_ram`, `new` and `from_pi5` fill their local result value
  while they check, and may fail with any error of their order in
  [Rejection and error priority](#rejection-and-error-priority) after
  they have put a part of it there, such as `BadProperty`, `NoMemory` or
  `MissingProperty` after the RAM ranges of `discover_memory`, or
  `Overflow`, `OutsideRam` or `Overlap` after the RAM banks of `all_ram`.
  On any failure the local value is dropped and the caller receives only
  the error ([no partial result](#rejection-and-error-priority)), so the
  state of the caller is that from before the call.

## Work bounds

The loops of each entry have bounds in the limits of
[Format and bounds](#format-and-bounds): $T \le 65536$ tokens, $P \le 512$
properties of a node, $D \le 32$ nodes on a path, $R \le 128$ entries of the
reservation map, $M \le 32$ RAM ranges, $Q \le 128$ reserved regions and
$N \le T$ nodes. They bound the number of steps, not the time.

- `Fdt::parse` reads at most $T$ tokens, compares the name of each property
  with at most $P - 1$ earlier properties of its node, and reads at most
  $R + 1$ reservation entries, each compared with at most $R$ earlier ones.
  A string is read up to the end of its block.
- `Fdt::nodes` reads at most $T$ tokens; `Node::property` at most the $T$
  tokens after its node; `Node::parent` at most $T$ tokens;
  `Fdt::find_node` at most $D$ path components, each over at most $N$ nodes.
  `Node::string_property` and `enabled` make one lookup of `property` and
  read the value once; `address_cells` and `size_cells` make one lookup;
  `Node::reg` takes `parent`, one lookup on the node and two on its parent,
  and the construction below; `ranges` and `dma_ranges` take `parent`,
  three lookups on the node and one on its parent, and the construction
  below. `Fdt::reservations` reads at most $R$ entries.
- `Reg::new` and `AddressMap::new` read each entry of their value once; a
  translation compares the request with each window once;
  `Node::translate_reg` translates through at most $D$ buses, each with its
  `parent` and `ranges`.
- `Fdt::discover_memory` reads at most $R$ map entries, calls `find_node`
  twice, for the root and for `/reserved-memory`, and walks the nodes at
  most twice, at most $N$ nodes each time: once for the children of the
  root and once for the children of `/reserved-memory`, with a fixed number
  of the property and parent lookups above for each child and for
  `/reserved-memory` itself. It compares each RAM range with at most $M$
  others.
- `Fdt::discover_pi5_boot_memory` makes the root lookup of `find_node`, its
  cell and `compatible` lookups, reads the `compatible` value once, makes a
  fixed number of comparisons of the tree and the image, calls
  `discover_memory` once, compares the tree and the image each with at most
  $M$ RAM ranges and sums at most $M$ ranges. `Pi5BootMemory::is_available`
  makes at most $M + Q + 2$ comparisons: the span with each RAM range, the
  tree, the image and each reserved region. `find_available` tries, in each
  RAM range, at most $Q + 3$ candidates, each compared with the image, the
  tree and $Q$ regions.
- `Fdt::discover_cpus` reads the children of `/cpus`, each at most once,
  with at most five lookups of each; `validate_qemu_timers` reads at most
  5 records; `logical_id` and `affinity` make a fixed number of steps.
- `MemoryPlan::all_ram` reads at most 32 banks, each compared with the
  earlier ones, and sorts them once; it reads at most 4 boot storage spans,
  each compared with the earlier ones, and at most 128 firmware
  reservations, each compared with the boot storage. `MemoryPlan::new` makes
  a fixed number of checks of its window, calls `all_ram` once and
  compares the window with at most 32 banks; `from_pi5` builds at most 4
  spans of boot storage and calls `new` once. The queries compare a range
  with at most 32 banks and 132 reservations. `available_ranges` yields at
  most one range for each managed bank and each reservation, 164 in all.
  Its cursor only moves forward within a bank, so in each bank at most 132
  of its passes over the 132 reservations move the cursor past a
  reservation; each range that it yields takes one more pass, which moves
  nothing, and one that finds the end of the range. A range found without
  leaving its bank takes at most 134 passes, and the whole iteration at
  most $32 \cdot 132 + 2 \cdot 164$.
- The other entries make a fixed number of steps: `Fdt::total_size`,
  `Node::name`, `Span::new`, `end` and `contains`, `cells_u64`,
  `AddressMap::kind`, `CpuProfile::affinity_shift` and `conduit`,
  `CpuTopology::count` and `profile`, and the accessors of `MemoryMap`,
  `Pi5BootMemory` and `MemoryPlan`, such as `MemoryMap::ram`,
  `Pi5BootMemory::dtb` and `MemoryPlan::managed_banks`.
  `MemoryPlan::described_bytes` and `managed_bytes` each sum at most 32
  banks.
- The component has no long operation: every entry runs to its end on the
  boot CPU, before the secondary CPUs start, and stores no progress.

## Determinism

The component makes no internal choice. Every result is a function of the
bytes of the tree and of the arguments of the entry:

- Nodes come in the order of the structure block, RAM ranges in tree
  order, and reserved regions in the order of the reservation map and then
  of the tree. The boot memory map sorts its banks by their start, which
  disjoint banks fix uniquely, and keeps boot storage and firmware
  reservations in input order; usable ranges come in address order.
  `find_available` takes the RAM ranges in tree order and the lowest
  aligned start in the first range that has a span.
- Duplicates and ambiguities are rejected, never chosen among
  ([Rejection and error priority](#rejection-and-error-priority)).
- No entry reads `/chosen`. QEMU virt writes new random values into the
  `kaslr-seed` and `rng-seed` of `/chosen` at every boot, by default, so its
  trees differ from boot to boot in those bytes, while the results of the
  parse, of the discoveries and of the boot memory map stay the same.

The specification of the component leaves no choice open, so the section
cites no entry of the register of
[permitted nondeterminism](../../../security.md#permitted-nondeterminism).

## State fields

| Field | Class | Lock or owner | Linearization point | Publication |
| --- | --- | --- | --- | --- |
| The bytes of the hand-over tree | Shared, read-only | No writer while the kernel runs: the firmware or QEMU's loader writes them before the entry of the image, and the boot memory map keeps their pages as boot storage, so that no allocation reuses them | The hand-over, before the cold entry | Once, before the kernel reads them; they never change afterwards |
| The tree `Fdt`, its `Node` values, a `MemoryMap` and a `Pi5BootMemory` | Per-CPU, of the boot CPU | The boot CPU, which builds them while it boots | - | `none`: their single owner never changes |
| The boot memory map, a `MemoryPlan` | Shared, immutable once built | The boot CPU builds it; afterwards every CPU only reads it | The return of the entry that builds it | Once, before the secondary CPUs start; it never changes afterwards |
| The CPU topology, a `CpuTopology` | Shared, immutable once built | The boot CPU builds it; the start of the secondary CPUs reads it | The return of `discover_cpus` | Once, before the first secondary CPU starts; it never changes afterwards |

## Testing obligations

- The host tests of the module `fdt` (planned) replay every vector of
  [Legacy test vectors](#legacy-test-vectors) that is part of this
  component, with the expected outputs of that section; the vectors that
  are not part of it are replayed by the components that the section names.
- Each limit of [Format and bounds](#format-and-bounds) has a test at the
  limit and one 1 above it, where no vector holds that case: a tree of
  exactly 2 MiB is accepted; a Pi 5 hand-over tree of exactly 128 KiB is
  accepted and one of 128 KiB and 1 byte fails with `LimitExceeded`; a tree
  with a node at depth 31 is accepted; a tree of exactly 65,536 tokens, the
  end token included, is accepted and one of 65,537 tokens fails with
  `LimitExceeded`; a reservation map of 128 entries is accepted and one of
  129 entries fails with `LimitExceeded`; and a tree with 32 RAM ranges is
  accepted.
- For each of the 1, 2, 4 and 16 GB RAM models, one host test parses a Pi 5
  hand-over tree with the inferred RAM ranges of the model, as
  [Memory discovery](#memory-discovery) lists them, and with `atf@0`, and
  holds the RAM ranges, `ram_bytes`, which is the installed size less
  4 MiB, and the boot memory map of `MemoryPlan::all_ram`, whose usable
  ranges leave out the hole. The 8 GB model is covered by the vector
  `fdt-pi5-platform-1`, a tree with its three ranges through
  `discover_pi5_boot_memory` and `MemoryPlan::from_pi5`.
- A tree with the three ranges and the two reserved regions of the 8 GB
  hand-over tree is accepted, and the region of 62 bytes, which lies in the
  hole, is kept and excluded.
- Dynamic reservations: trees with an enabled child of `/reserved-memory`
  that has a `size` of one cell, of two cells, with and without
  `alloc-ranges`, are accepted with one dynamic reservation and no reserved
  region for it; a child with both `reg` and `size` is a static region.
- Boot storage of 4 spans is accepted, and 5 fail with `Capacity`.
- Each error of the table of
  [Rejection and error priority](#rejection-and-error-priority) that no
  applicable case of the vectors of this component gives has a test of its
  own: `Fdt::parse` of fewer than 40 bytes fails with `Truncated`;
  `discover_cpus` on a tree without `/cpus` fails with `MissingProperty`;
  and `find_node` with a path that holds `//` fails with `BadPath`.
- For each step of the two error orders of
  [Rejection and error priority](#rejection-and-error-priority), an input
  that breaks that step and a later one gives the error of that step.
- The QEMU boot suite boots QEMU virt three times, each in a new QEMU
  process, and the results of the parse and of the boot memory map are the
  same, although each tree holds other seeds in `/chosen`.
- The tests take their expected values from this page, from the vectors and
  from the trees that they build, never from an earlier run of the code
  under test ([testing](../../../conventions/testing.md#independent-evidence)).
- The RAM models other than 8 GB are not run on a board in release 0.1.

## Open obligations

The module `fdt` has no `unsafe` code and no assembly, and its targets are
to cover it, so its only open obligation is the board's: forming the slice
of the hand-over tree from the address where the firmware leaves it
([Extractability](#extractability)). Each board forms that slice in its
board crate; the row of the Pi 5 board is added with its board crate.

| Obligation | Kind | Verified state | Carrier | Stage |
| --- | --- | --- | --- | --- |
| `kernel/boards/qemu-virt/src/main.rs#image::device_tree` (planned) | `unsafe` | Neither (forms the byte slice of the tree at the start of RAM, where QEMU's loader places it, first of its 40-byte header and then of `totalsize` bytes) | The proof of the boot and board assembly, the kernel boot and initialization code and the unsafe sites | `0.2` |

## Legacy test vectors

The vectors are the host tests of the prototype tree at
`prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e` that test the code of
this component and of the Pi 5 device bindings next to it: the tests of
`src/fdt` and the tests of the memory plan in `src/platform/tests.rs`, 90
in all. Of them, 55 test this component; 35 test the Pi 5 device bindings,
which are not part of it, and are frozen here with the component that
receives them. Their expected outputs are those that the test bodies
assert. The vectors are not yet in a file of the repository, so the
section holds no `vectors` block.

A vector of this page is one test function. The vector file is to hold one
line for each case of it through an entry of this page, with the id
`<vector>.<n>`, `n` counting those cases from 1, so that a vector of this
page corresponds to the lines of the file whose ids start with its id; a
case that its row marks not applicable has no line. Six vectors are
ignored tests whose input is a device-tree file outside the prototype tree:
they freeze the name of the test and its expected output, and their inputs
stay outside this repository.

### Notation

The vector file writes inputs and outputs in this notation, as
[test vectors](../../../formal-verification.md#vector-and-result-files)
require:

- Bytes are lowercase hexadecimal digits, two for each byte. Addresses,
  sizes and other values that the tests write in hexadecimal are `0x` and
  lowercase hexadecimal digits; counts are decimal.
- A span is `<start>+<size>`; a list of spans is the spans joined by `,`,
  and `-` when empty. A reserved region is its span, `/` and its flags:
  `no-map`, `reusable` or `none`.
- An input is `entry=<entry>`; then `dtb=<bytes>`, the bytes of the tree,
  for the parse and for every entry on a tree, and `node=<path>` for an
  entry on a node; then the other arguments of the entry, each
  `<name>=<value>`, in the order in which the rule sections of this page
  write its parameters, such as `discover_pi5_boot_memory(dtb_address,
  image)` in [Memory discovery](#memory-discovery):
  `entry=discover_pi5_boot_memory dtb=<bytes> dtb_address=0x200000
  image=0x80000+0x20000`. It ends with `ask=` and the fields and queries
  that the case asks, joined by `,`.
- An output is `result=err error=<type>::<variant>` for a case whose test
  asserts the error, with the type `Error` or `PlanError` of
  [Rejection and error priority](#rejection-and-error-priority), such as
  `error=Error::Overlap` or `error=PlanError::Overlap`; `result=err` for
  one whose test asserts only a rejection; and
  `result=ok` followed by the asked fields and queries, each
  `<field>=<value>` or `<query>(<arguments>)=<value>`, in the order of
  `ask`. The fields of a value are those of its entry: `ram`, `reserved`,
  `dynamic`, `dtb`, `image` and `ram_bytes` of the memory maps; `count`,
  `profile` and `affinity(<i>)` of a topology; `managed`, `ram`, `boot`,
  `firmware` and `available` of a boot memory map; `span` of a translation
  or a selection, `-` for none.
- A property vector, whose test asserts a property over a family of inputs,
  states the property and the rule that generates the inputs; the vector
  file holds one case for each generated input, with the output
  `result=err`, `result=returned`, or the output of the independent model
  of the test for that input.
- The tables below name an error without its type where the row leaves no
  doubt: an error of the rows of `src/platform/tests.rs` is a `PlanError`,
  and an error of every other row of this component is an `Error`; a row
  whose cases reach both types names the type, as `fdt-pi5-platform-2`
  does. The rows of the device bindings, which are not part of this
  component, name the owner of each error that is not an `Error`.

### Behaviour changes

Three vectors expect another output than the prototype gave, because a
dynamic reservation is accepted and recorded
([Memory discovery](#memory-discovery)): `fdt-discovery-4`, `fdt-pi5-4` and
`fdt-pi5-firmware-1`. One case of `platform-10` expects `PlanError::Overlap`
where the prototype gave `Capacity`, because boot storage may hold 4 spans
([Boot memory map](#boot-memory-map)). The renaming of the prototype's
`platform::Error` to `PlanError` changes no output. The limits and every
other step of the error orders are those of the prototype.

### Parsing and translation

`src/fdt/tests/parser.rs`, 9 vectors. The minimal tree of these tests is a
root with `#address-cells` and `#size-cells` of 2 and one node
`memory@100000000` with the `device_type` `memory` and the `reg`
`0x100000000+0x200000`.

| Vector | Test | Expected output | Entry |
| --- | --- | --- | --- |
| `fdt-parser-1` | `all_truncations_are_rejected_without_panics` | Property: every prefix of the minimal tree, of 0 bytes up to one byte less than the tree, is rejected; one case per length, `result=err` | `Fdt::parse` |
| `fdt-parser-2` | `rejects_bad_header_layout_version_and_reservation_map` | The minimal tree with one header word replaced: magic 0, `BadMagic`; `totalsize` 12, `BadLayout`; `totalsize` 2 MiB + 1, `LimitExceeded`; structure offset 57, `BadAlignment`; reservation offset 41, `BadAlignment`; version 16, `UnsupportedVersion`; last compatible version 18 and 0, `UnsupportedVersion`; strings offset 4, `BadLayout`; reservation offset 56, on the structure block, `BadLayout`; strings offset equal to the structure offset, `BadLayout`; a first reservation entry `0x1+0x1`, after which the next entry lies on the structure block, `BadLayout` | `Fdt::parse` |
| `fdt-parser-3` | `reservation_overflow_and_overlap_fail_closed` | A reservation entry `0xffffffffffffffff+0x1`, `Overflow`; entries `0x1000+0x2000` and `0x2000+0x2000`, `Overlap` | `Fdt::parse` |
| `fdt-parser-4` | `rejects_bad_tokens_names_padding_and_property_order` | A property after a child node, `BadTree`; `#address-cells` twice in the root, `DuplicateProperty`; a first token `0xff`, `BadToken`; a nonzero byte in the padding of the root name, `BadPadding`; a property name offset `0xffffffff`, `BadString`; a strings block without a NUL, `BadString` | `Fdt::parse` |
| `fdt-parser-5` | `rejects_unbalanced_tree_trailing_tokens_and_excess_depth` | A root without its end node, `BadTree`; one end node too many, `BadTree`; an end token followed by another end token, `BadTree`; a root with 32 nested children, 33 nodes on a path, `LimitExceeded` | `Fdt::parse` |
| `fdt-parser-6` | `header_and_structure_single_byte_corruptions_do_not_panic` | Property: for each byte of the minimal tree, the tree with that byte inverted (XOR `0xff`) is parsed and, when accepted, its memory is discovered and `reg`, `ranges` and `dma_ranges` of every node are read; every call returns, `result=returned`. That no input panics holds of the specification by construction, so the replay checks only that the entries return | `Fdt::parse`, `Fdt::discover_memory`, `Node::reg`, `ranges` and `dma_ranges` |
| `fdt-parser-7` | `qemu_property_padding_residue_is_not_payload_or_a_token` | A tree minimized from the QEMU 11.1.2 tree of the machine `virt`: the root `model` `linux,dummy-virt`, 17 bytes, with the padding bytes `00 00 02`, and `memory@40000000` whose `device_type` padding holds `0x73`, with `reg` `0x40000000+0x8000000`. Accepted; the root `model` reads `linux,dummy-virt`; RAM `0x40000000+0x8000000`. Of the padding bound, which the parse computes internally: a value that ends at byte 5 of a block of 5 bytes, `Truncated`; of a block of 8 bytes, the next token at byte 8 | `Fdt::parse`, `Fdt::find_node`, `Node::string_property`, `Fdt::discover_memory`. The two cases of the padding bound: not applicable, they call a function internal to the parse, which no entry reaches with them: a block of 5 bytes is not a multiple of 4, one of 8 bytes is shorter than the 12 bytes of the smallest structure block, and the value of a property starts at least at byte 12 of its block, so it never ends at byte 5; only the host tests of the module hold them, and the vector file has no line for them |
| `fdt-parser-8` | `accepts_unaligned_host_bytes_and_compatible_future_version` | The minimal tree with version 18 and last compatible version 17, at an odd host address: accepted, and the memory discovery succeeds | `Fdt::parse`, `Fdt::discover_memory` |
| `fdt-parser-9` | `vendor_property_names_and_symbol_tables_remain_bounded` | A node `__symbols__` with 334 and with 512 properties, accepted; with 513, `LimitExceeded`. A root property named `snps,parkmode-disable-fsls-quirk`, 32 bytes, and one of 64 bytes of `x`, accepted; one of 65 bytes, `BadString` | `Fdt::parse` |

`src/fdt/tests/translation.rs`, 5 vectors.

| Vector | Test | Expected output | Entry |
| --- | --- | --- | --- |
| `fdt-translation-1` | `translation_is_recursive_and_dma_is_separate` | `/bus` with 1 and 1 cells, `ranges` from child 0 to parent `0x200000000`, size `0x10000`, and `dma-ranges` from 0 to `0x300000000`, size `0x10000`; `/bus/bridge` with 1 and 1 cells and `ranges` from 0 to `0x1000`, size `0x1000`; `/bus/bridge/serial@20` with `reg` `0x20+0x10`: `translate_reg` gives `0x200001020+0x10`; the `dma-ranges` of `/bus` take `0x1020+0x10` to the parent as `0x300001020+0x10` and back | `Fdt::find_node`, `Node::reg`, `translate_reg` and `dma_ranges`, `AddressMap::to_parent` and `to_child` |
| `fdt-translation-2` | `identity_and_absent_are_distinct_and_width_checked` | With 2, 2 and 2 cells, an absent map is of the kind `Absent` and fails `0x100000000+0x1000` with `Unmapped`; an empty map is of the kind `Identity` and gives the same span; an empty map with 1 parent address cell and 1 size cell fails the same span with `Overflow` | `AddressMap::new`, `kind` and `to_parent` |
| `fdt-translation-3` | `windows_refuse_crossing_unmapped_and_ambiguous_requests` | With 1 child cell, 2 parent cells and 1 size cell, windows from 0 to `0x100000000` and from `0x1000` to `0x200000000`, each of size `0x1000`: `0xff0+0x20`, `Unmapped`; `0x4000+0x1`, `Unmapped`. Windows from 0 to `0x100000000` and from 0 to `0x200000000`: `0x4+0x4`, `AmbiguousMapping` | `AddressMap::new` and `to_parent` |
| `fdt-translation-4` | `numeric_cells_and_pci_tags_cannot_truncate` | Cells `0x12`, `0x34567890` as 2 cells, `0x1234567890`; 3 cells, `UnsupportedCells`; an empty map with 3 child cells, `UnsupportedCells`; a `reg` of 3 address cells, `UnsupportedCells`; a `reg` `0xffffffffffffffff+0x1` with 2 and 2 cells, `Overflow`; a window from 0 to `0xffffffffffffffff` of size 2, with 1, 2 and 1 cells, `Overflow`; a `reg` of 7 bytes with 1 and 1 cells, `BadProperty`; a map of 7 bytes with 1, 1 and 1 cells, `BadProperty` | `cells_u64`, `Reg::new`, `AddressMap::new` |
| `fdt-translation-5` | `one_cell_regions_cannot_cross_their_address_space` | With 1 and 1 cells, `reg` `0xffffffff+0x2`, `Overflow`; `0xffffffff+0x1` is accepted and its span ends at `0x100000000` | `Reg::new`, `Span::end` |

### Memory discovery vectors

`src/fdt/tests/discovery.rs`, 6 vectors, on the minimal tree of
`src/fdt/tests/parser.rs`.

| Vector | Test | Expected output | Entry |
| --- | --- | --- | --- |
| `fdt-discovery-1` | `discovers_high_ram_and_both_reservation_sources` | A reservation entry `0x100000000+0x1000` and a `/reserved-memory` with 2 and 2 cells and an empty `ranges`, whose child `firmware@100001000` has `reg` `0x100001000+0x2000` and `no-map`: `total_size` is the length of the bytes; RAM `0x100000000+0x200000`; 2 reserved regions, both `no-map`, the second `0x100001000+0x2000` | `Fdt::parse`, `total_size` and `discover_memory` |
| `fdt-discovery-2` | `disabled_ram_is_not_allocatable_and_defaults_are_not_inherited` | A disabled `memory@200000000` besides the minimal memory node: 1 RAM range. A node `/bus` without cell counts and with an empty `ranges`, whose child `dev@0` has `reg` cells `0`, `0`, `0x1000`: the first span of its `reg` has size `0x1000`, in the default 2 address cells and 1 size cell of `/bus` | `Fdt::discover_memory`, `find_node`, `Node::reg` |
| `fdt-discovery-3` | `disabled_secure_memory_is_excluded_before_binding_validation` | A node `secram@e000000` with the `device_type` `memory`, `secure-status` `okay` and `reg` `0xe000000+0x1000000`: with `status` `disabled`, 1 RAM range, at `0x100000000`; with `okay`, `BadProperty`; with `okay`, NUL and `junk`, `BadProperty` | `Fdt::discover_memory` |
| `fdt-discovery-4` | `reserved_memory_requires_explicit_identity_and_static_regions` | A `/reserved-memory` with 2 and 2 cells and a child `pool` with `size` cells `0`, `0x1000` and no `reg`: without `ranges`, `BadProperty`. With an empty `ranges`, the prototype gave `DynamicReservation`; this contract expects `result=ok`: RAM `0x100000000+0x200000`, no reserved region, 1 dynamic reservation (behaviour change) | `Fdt::discover_memory` |
| `fdt-discovery-5` | `empty_or_overlapping_ram_is_rejected` | Two memory nodes of the minimal range, `Overlap`; no memory node, `NoMemory` | `Fdt::discover_memory` |
| `fdt-discovery-6` | `discovery_capacity_and_reserved_flags_fail_closed` | 33 memory nodes of one page each, `LimitExceeded`; a child of `/reserved-memory` with `reg`, `no-map` and `reusable`, `BadProperty` | `Fdt::discover_memory` |

### CPU node vectors

`src/fdt/tests/cpus.rs`, 6 vectors. Their trees have `/cpus` with 2 address
cells and 0 size cells, unless a case states 1, CPU nodes with the
`device_type` `cpu`, the `compatible` `arm,cortex-a76` and the
`enable-method` `psci`, and `/psci` with the `compatible` `arm,psci-1.0`,
`arm,psci-0.2`, `arm,psci`.

| Vector | Test | Expected output | Entry |
| --- | --- | --- | --- |
| `fdt-cpus-1` | `separate_pi5_and_virtual_affinities_and_conduits` | The Pi 5 profile with IDs `0`, `0x100`, `0x200`, `0x300` and `smc`: count 4, profile Pi 5, `affinity(i)` is `i << 8` for `i` below 4 and none for 4. The QEMU profiles with `hvc` and with `smc` and 1, 2 or 4 CPUs of IDs 0 up: count 1, 2 or 4. Rejected: the Pi 5 profile with IDs 0 to 3; the Pi 5 profile with `hvc`; the HVC profile with `smc`; the SMC profile with `hvc` | `Fdt::discover_cpus`, `CpuTopology::count`, `profile` and `affinity` |
| `fdt-cpus-2` | `reject_alias_holes_foreign_affinities_and_incomplete_board` | The HVC profile rejects the IDs `[0, 0, 2, 3]`, `[0, 1, 3]`, `[0, 1, 2]`, `[1, 2]`, `[0, 4]`, `[0, 0x100]`, `[0, 0x100000000]` and `[0, 0x80000000]`; the Pi 5 profile rejects `[0, 0x100]`, `[0, 0x100, 0x200, 0x301]` and `[0, 0x100, 0x200, 0x400]` | `Fdt::discover_cpus` |
| `fdt-cpus-3` | `cpu_status_model_and_enable_method_are_required` | The Pi 5 tree with CPU 2 disabled, with the `enable-method` `spin-table` or with the `compatible` `arm,cortex-a53`: rejected | `Fdt::discover_cpus` |
| `fdt-cpus-4` | `cpu_reg_cell_width_is_checked_without_truncation` | The Pi 5 tree with 1 and with 2 address cells: count 4. With the ID `0x100000300`: rejected | `Fdt::discover_cpus` |
| `fdt-cpus-5` | `register_flags_do_not_change_logical_identity` | For IDs 0 to 3 and the flags 0, `0x1000000`, `0x40000000`, `0x80000000` and `0xc1000000`: `logical_id` of the Pi 5 of the flags with `id << 8` is the ID, and of the HVC profile of the flags with the ID is the ID. `logical_id` of the Pi 5 of `0x1`, `0x101`, `0x400`, `0x10000` and `0x100000000`: none | `CpuProfile::logical_id` |
| `fdt-cpus-6` | `qemu_timer_records_follow_profile_and_admitted_cpus` | For each QEMU profile and 1, 2 or 4 CPUs, the records of type 1 for the private interrupts 13, 14, 11 and 10, and 12 for the SMC profile, with the flags `((1 << count) - 1) << 8 \| 4`: accepted. Rejected: the records cut to 0 bytes, 12 bytes, one byte short and one record short; one record added; any word with its lowest bit inverted; the byte of the CPU mask of the first record with its lowest bit inverted; and the valid records for the Pi 5 topology | `CpuTopology::validate_qemu_timers` |

### Pi 5 boot memory vectors

The trees of these tests have a root with 2 and 2 cells and the
`compatible` `raspberrypi,5-model-b`, `brcm,bcm2712`; the address of the
tree is `0x200000` and the image `0x80000+0x20000`, unless a case states
others.

`src/fdt/pi5/tests.rs`, 4 vectors.

| Vector | Test | Expected output | Entry |
| --- | --- | --- | --- |
| `fdt-pi5-1` | `retains_high_ram_and_excludes_all_boot_and_firmware_storage` | A reservation entry `0x200000+0x20000`; RAM `0x0+0x100000000`, `0x100000000+0x100000000` and `0x300000000+0x100000`; `atf@0` `0x0+0x80000` with `no-map` and `pool@100000000` `0x100000000+0x10000` with `reusable`; a PCIe node of 3 address cells with a child `ethernet@0`, which is no RAM. 3 RAM ranges, the second `0x100000000+0x100000000`; `ram_bytes` `0x200100000`; `dtb` `0x200000+` the length of the tree; `image` `0x80000+0x20000`; reserved regions 0 and 1 `no-map`, 2 `reusable`. Not available: `0x0+0x1000`, the image, `0x200000+0x8`, `0x100000000+0x1000`, `0x200000000+0x1000`, `0xfffff000+0x2000` and `0x1fffff000+0x100002000`; available: `0x100010000+0x1000` | `Fdt::discover_pi5_boot_memory`, `Pi5BootMemory::is_available` |
| `fdt-pi5-2` | `ignores_disabled_ram_and_disabled_dynamic_reservations` | RAM `0x0+0x200000000` and a second, disabled `memory@0`; a disabled `linux,cma` with a `size` of one cell and `reusable`: `ram_bytes` `0x200000000`, 1 RAM range, no reserved region and no dynamic reservation | `Fdt::discover_pi5_boot_memory` |
| `fdt-pi5-3` | `compatibility_allows_model_revision_and_extra_compatible_entries` | A root `model` `Raspberry Pi 5 Model B Rev 1.1` and `compatible` `vendor,new-revision`, `raspberrypi,5-model-b`, `brcm,bcm2712`; RAM `0x0+0x200000000`: `ram_bytes` `0x200000000` | `Fdt::discover_pi5_boot_memory` |
| `fdt-pi5-4` | `rejects_active_dynamic_reservations_and_conflicting_flags` | RAM `0x0+0x200000000`; a child `pool` of `/reserved-memory` with `reusable`: with a `size` of one cell, `0x4000000`, and no `reg`, the prototype gave `DynamicReservation`; this contract expects `result=ok`: `ram_bytes` `0x200000000`, no reserved region, 1 dynamic reservation (behaviour change). With `reg` `0x400000+0x1000` and `no-map`, `BadProperty` | `Fdt::discover_pi5_boot_memory` |

`src/fdt/pi5/tests/boundaries.rs`, 5 vectors.

| Vector | Test | Expected output | Entry |
| --- | --- | --- | --- |
| `fdt-pi5-boundaries-1` | `rejects_missing_wrong_and_malformed_compatible_values` | With RAM `0x0+0x200000000`, a root `compatible` that is absent; `raspberrypi,4-model-b`, `brcm,bcm2711`; the Pi 5 list without its last NUL; with an empty entry between the two; with a further entry of the byte `0xff`: each rejected | `Fdt::discover_pi5_boot_memory` |
| `fdt-pi5-boundaries-2` | `rejects_wrong_root_cells_and_oversized_handoff` | A root with 1 and 1 cells, `UnsupportedCells`; a root property of 128 KiB of zeros, so that the tree is longer than 128 KiB, `LimitExceeded` | `Fdt::discover_pi5_boot_memory` |
| `fdt-pi5-boundaries-3` | `validates_storage_alignment_overflow_overlap_and_ram_containment` | RAM `0x0+0x400000`. The address of the tree `0x200001`, `BadAlignment`; `0xfffffffffffffff8`, `Overflow`; the image `0x200000+0x1000`, on the tree, `Overlap`; the image `0x0+0x0`, `EmptyRegion`; the image `0xffffffffffffffff+0x1`, `Overflow`; the address of the tree `0x400000`, `Unmapped`; `0x3ffff8`, `Unmapped`; the image `0x3ff000+0x2000`, `Unmapped`. With the default arguments, `is_available` of `0x0+0x0`, `EmptyRegion`, and of `0xffffffffffffffff+0x1`, `Overflow` | `Fdt::discover_pi5_boot_memory`, `Pi5BootMemory::is_available` |
| `fdt-pi5-boundaries-4` | `rejects_overlapping_ram_aliases_and_out_of_range_regs` | A RAM `reg` `0x0+0x200000000` with `0x100000000+0x100000000`, `Overlap`; `0xffffffffffffffff+0x1`, `Overflow`; `0x0+0x0`, `EmptyRegion` | `Fdt::discover_pi5_boot_memory` |
| `fdt-pi5-boundaries-5` | `capacity_exhaustion_never_returns_a_partial_memory_map` | One `reg` of 33 RAM ranges of 4 GiB each, `LimitExceeded`; RAM `0x0+0x200000000` and one child of `/reserved-memory` with 129 spans of one page, `LimitExceeded` | `Fdt::discover_pi5_boot_memory` |

`src/fdt/pi5/tests/selection.rs`, 3 vectors.

| Vector | Test | Expected output | Entry |
| --- | --- | --- | --- |
| `fdt-pi5-selection-1` | `selection_skips_boot_storage_reservations_and_bank_holes` | RAM `0x0+0x400000` and `0x100000000+0x10000`; reservation entries `0x4000+0x1001`, `0x0+0x4000` and `0x100000000+0x3000`. `find_available` of size `0x2000`, alignment `0x1000`, in `[0, 0x10000)`: `0x6000+0x2000`; in `[0x80000, 0x200000)`: a span that starts at `0xa0000`, the end of the image; of size `0x1000` in `[0x200000, 0x400000)`: a span at or above the end of the tree that `is_available` accepts; of size `0x2000` in `[0x3ff000, 0x100005000)`: `0x100003000+0x2000`; in `[0x3ff000, 0x100004000)`: none | `Pi5BootMemory::find_available` and `is_available` |
| `fdt-pi5-selection-2` | `selection_rejects_invalid_bounds_alignment_and_overflow` | RAM `0x0+0x200000000`. Size 0, `EmptyRegion`; minimum equal to the limit, `EmptyRegion`; alignments 0, 3 and 4095, `BadAlignment`; size 4096 with the minimum `0xfffffffffffffffe`, `Overflow`; size `0xffffffffffffffff`, none | `Pi5BootMemory::find_available` |
| `fdt-pi5-selection-3` | `selection_preserves_reusable_reservations_and_full_capacity` | RAM `0x0+0x200000000` and 128 `reusable` regions of one page each from `0x400000`: accepted. `find_available` of size 32768, alignment 4096, in `[0x400000, 0x10000000)`: a span that starts at `0x480000` and is available | `Fdt::discover_pi5_boot_memory`, `Pi5BootMemory::find_available` and `is_available` |

`src/fdt/pi5/tests/firmware.rs`, 2 vectors, both ignored tests whose input
lies outside the prototype tree: the two trees that the Raspberry Pi
firmware ships, `bcm2712-rpi-5-b.dtb` and `bcm2712d0-rpi-5-b.dtb`, and three
trees merged from them with overlays of a boot configuration, `c1.dtb`,
`d0.dtb` and `d0-auto.dtb`. The image of both is `0x80000+0x80000`.

| Vector | Test | Expected output | Entry |
| --- | --- | --- | --- |
| `fdt-pi5-firmware-1` | `source_firmware_rejects_dynamic_reservations` | For each of the two shipped trees, the prototype gave `DynamicReservation`; this contract expects `result=ok` with one dynamic reservation (behaviour change). For `bcm2712-rpi-5-b.dtb`, whose bytes are equal in the firmware commits that [References](#references) names: RAM `0x0+0x28000000`, the placeholder; one reserved region, `0x0+0x80000/no-map`; `dtb` `0x200000+0x133b2`; `ram_bytes` 640 MiB. The other fields of `bcm2712d0-rpi-5-b.dtb` follow from that file | `Fdt::discover_pi5_boot_memory` |
| `fdt-pi5-firmware-2` | `merged_firmware_preserves_placeholder_ram_and_boot_exclusions` | For each merged tree: RAM `0x0+0x28000000`; `ram_bytes` 640 MiB; one reserved region, `0x0+0x80000/no-map`; `image` as given; `dtb` `0x200000+` the length of the file; not available: the region, the image, the tree and `0x28000000+0x1000`; available `0x100000+0x1000`; no reservation entry; `/reserved-memory/linux,cma` disabled. `MemoryPlan::from_pi5` with the window `0x0+0x8000000`: the first RAM bank 640 MiB long; the region, the image and the tree do not permit backing, `0x100000+0x1000` does. Its assertions on the Pi 5 kernel resources, the UART at `0x107d001000`, the GIC distributor at `0x107fff9000` and no high page, are not part of this component: they go with the [Pi 5 board support](../README.md#qemu-virt-and-pi-5-board-support) | `Fdt::discover_pi5_boot_memory`, `Pi5BootMemory::is_available`, `Fdt::reservations`, `find_node`, `Node::enabled`, `MemoryPlan::from_pi5` and `permits_backing` |

`src/fdt/pi5/tests/platform.rs`, 2 vectors, through the boot memory map.

| Vector | Test | Expected output | Entry |
| --- | --- | --- | --- |
| `fdt-pi5-platform-1` | `kernel_projection_preserves_discovered_banks_and_excludes_boot_pages` | The three RAM ranges of the 8 GB model, `0x0+0x3fc00000`, `0x40000000+0xc0000000` and `0x100000000+0x100000000`, and a reservation entry `0x0+0x80000`; `from_pi5` with the window `0x0+0x8000000` and no further boot storage: 3 RAM banks; the first boot range is the image, `0x80000+0x20000`; the pages at 0, at the start of the image and at the start of the tree do not permit backing, `0x400000+0x1000` does; `0x3fc00000+0x1000`, in the hole, is not available; `0x100000000+0x1000` is available and does not permit backing | `Fdt::discover_pi5_boot_memory`, `MemoryPlan::from_pi5`, `ram`, `boot_ranges`, `is_available` and `permits_backing` |
| `fdt-pi5-platform-2` | `kernel_projection_rejects_boot_pages_claimed_by_firmware` | RAM `0x0+0x200000000` and a reservation entry `0x200000+0x20000` on the tree: the discovery accepts it, and `from_pi5` with the window `0x0+0x8000000` fails with `PlanError::Overlap` | `Fdt::discover_pi5_boot_memory`, `MemoryPlan::from_pi5` |

### Boot memory map vectors

`src/platform/tests.rs`, 13 vectors: the tests of the memory plan, without
the 4 tests of device windows of the same file, which are not part of this
component. Their default RAM is `0x0+0x8000000`, their image
`0x80000+0x38000`, their tree `0x200000+0x13ad4`, 80,596 bytes, and their
`atf@0` the region `0x0+0x80000/no-map`.

| Vector | Test | Expected output | Entry |
| --- | --- | --- | --- |
| `platform-1` | `pi5_shaped_banks_keep_holes_high_ram_and_page_exclusions` | `new` with the window `0x0+0x8000000`, the three RAM ranges of the 8 GB model, the image and the tree, and `atf@0` and `0x3fd231e0+0x3e/no-map`, in the hole: boot ranges `0x80000+0x38000` and `0x200000+0x14000`; firmware ranges `0x0+0x80000` and `0x3fd23000+0x1000`; the pages at `0x213000`, `0x3fc00000` and `0x80000` are neither available nor permit backing; `0x100000000+0x1000` is available and does not permit backing; `0x214000+0x1000` permits backing | `MemoryPlan::new`, `boot_ranges`, `firmware_ranges`, `is_available` and `permits_backing` |
| `platform-2` | `allocator_consumes_the_same_rounded_boot_and_firmware_exclusions` | `new` with the window `0x100000+0x5000`, the default RAM, the image, and `0x101fff+0x2/no-map`; a page allocator over the managed bank and the reservations allocates one page at `0x100000` and then two pages at `0x103000`, each permitted for backing, and has no free byte left | `MemoryPlan::new`, `managed_banks`, `reservations` and `permits_backing`; the allocations through the [page ownership](../../memory/page-tables/contract.md#page-ownership) table of the page-tables component |
| `platform-3` | `qemu_prefix_is_reserved_without_truncating_installed_ram` | `new` with the window `0x40000000+0x8000000`, RAM `0x40000000+0x100100000`, 4,097 MiB, and boot storage `0x40000000+0x300000`: `0x40000000+0x1000` does not permit backing, `0x40300000+0x1000` does; `0x100000000+0x1000` is available; `0x48000000+0x1000` does not permit backing | `MemoryPlan::new`, `is_available` and `permits_backing` |
| `platform-4` | `rejects_empty_overflowing_unaligned_and_oversized_mapping_windows` | `new` with the default RAM and the image and the window `0x0+0x0`, `InvalidRange`; `0xffffffffffffffff+0x1`, `Overflow`; `0x1+0x1000` and `0x0+0x1001`, `Alignment`; `0x0+0x8001000`, `ArenaTooLarge` | `MemoryPlan::new` |
| `platform-5` | `rejects_invalid_overlapping_or_missing_ram_banks` | `new` with the window of the default RAM and the image, and the banks: the default RAM with `0x0+0x0`, `InvalidRange`; with `0xffffffffffffffff+0x1`, `Overflow`; with `0x1000+0x1000`, `Overlap`; `0x0+0x1000` and `0x2000+0x1000`, `OutsideRam` | `MemoryPlan::new` |
| `platform-6` | `neither_adjacent_banks_nor_holes_can_supply_one_allocation` | Banks `0x0+0x200000`, `0x200000+0x200000` and `0x800000+0x100000`, the image, and the window of the first bank: `contains_ram` of `0x1ff000+0x2000` is false; `0x3ff000+0x402000` is not available. The window `0x0+0x400000`, `OutsideRam` | `MemoryPlan::new`, `contains_ram` and `is_available` |
| `platform-7` | `boot_storage_must_occupy_disjoint_pages_inside_one_ram_bank` | With the default RAM and window and boot storage of the image and: the image again, `Overlap`; `0xb7fff+0x2`, `Overlap`; `0x8000000+0x1`, `OutsideRam`; `0x100000+0x0`, `InvalidRange`; `0xfffffffffffffffe+0x1`, `Overflow`. The window `0x1000+0x1000`, RAM `0x1+0x2000` and boot storage `0x1+0x1`, `OutsideRam` | `MemoryPlan::new` |
| `platform-8` | `rejects_firmware_on_boot_pages_even_without_byte_overlap` | Boot storage `0x80001+0x1` and the firmware reservation `0x80fff+0x1/no-map`, `Overlap`. With the image, the firmware reservations `0x0+0x0`, `InvalidRange`; `0xffffffffffffffff+0x1` and `0xfffffffffffffffe+0x1`, `Overflow` | `MemoryPlan::new` |
| `platform-9` | `overlapping_and_reusable_firmware_reservations_stay_excluded` | The image and the tree, and the reservations `0x400001+0x1/reusable` and `0x400fff+0x2/no-map`: `0x400000+0x2000` is not available; `0x402000+0x1000` permits backing | `MemoryPlan::new`, `is_available` and `permits_backing` |
| `platform-10` | `exact_capacity_is_supported_and_excess_input_is_rejected` | 32 banks, the default RAM and 31 banks of one page at `i * 0x10000000` for `i` from 1 to 31, the image and the tree, and 128 firmware reservations `0x400000+0x1/no-map`: accepted, with 32 RAM banks and 130 reservations; `0x400000+0x1000` does not permit backing. `Capacity` for no bank; for no boot storage; for 33 banks; for 129 firmware reservations. For three spans of boot storage that are all the image, the prototype gave `Capacity`; this contract expects `Overlap`, since 4 spans fit and the second shares the pages of the first (behaviour change) | `MemoryPlan::new`, `ram`, `reservations` and `permits_backing` |
| `platform-11` | `full_ram_registers_all_bank_pages_and_reservation_union` | `all_ram` with the three RAM ranges of the 8 GB model in the order `0x100000000+0x100000000`, `0x0+0x3fc00000`, `0x40000000+0xc0000000`, the image and the tree, and `atf@0`, `0x40002001+0x1000/no-map` and `0x40003000+0x1/no-map`: managed bytes 8 GiB less 4 MiB in 3 managed banks; `0x1fffff000+0x1000` permits backing, `0xfffff000+0x2000` does not; the usable ranges hold the managed bytes less `0x80000`, `0x38000`, `0x14000` and `0x2000`, as many bytes as a page allocator over the managed banks and the reservations has free | `MemoryPlan::all_ram`, `managed_bytes`, `managed_banks`, `permits_backing`, `reservations` and `available_ranges`; the free bytes through the [page ownership](../../memory/page-tables/contract.md#page-ownership) table of the page-tables component |
| `platform-12` | `partial_bank_pages_are_not_managed_and_total_ram_is_bounded` | `all_ram` with the banks `0x1+0x5000` and `0x10001+0x8` and the boot storage `0x1000+0x1000`: managed banks `0x1000+0x4000`; usable ranges `0x2000+0x3000`. One bank of 16 GiB and 1 byte with the image, `ArenaTooLarge` | `MemoryPlan::all_ram`, `managed_banks` and `available_ranges` |
| `platform-13` | `available_iterator_matches_page_oracle_across_unsorted_overlapping_exclusions` | Property: `all_ram` with the banks of 24 pages at page 0 and at page 32, the boot storage of page 0, and the regions of pages 9 to 13, 5 to 11 and 22 to 33 and of the byte 1 of page 40; for each page from 0 to 59, the number of usable ranges that contain it is 1 when a bank holds the page, the page is not page 0 and no region touches it, and 0 otherwise. One case per page, whose output is the count of the model | `MemoryPlan::all_ram`, `available_ranges` |

### Pi 5 device binding vectors

These 35 vectors test the Pi 5 device bindings, which are not part of this
component. Each group is frozen with the component that receives it, and
their expected outputs are frozen here.

`src/fdt/pi5/tests/kernel.rs`, 3 vectors, and
`src/fdt/pi5/interrupts/tests.rs`, 4 vectors, the interrupt controller and
timer and the kernel resources of the Pi 5. Not part of this component:
they go with the [Pi 5 board support](../README.md#qemu-virt-and-pi-5-board-support)
and its [interrupt controller](../README.md#interrupt-controllers). The
expected interrupts of the second file are the GIC distributor
`0x107fff9000+0x1000`, the GIC CPU interface `0x107fffa000+0x2000` and the
Non-secure physical timer, interrupt ID 30, for the CPU mask `0xf`, level
low.

| Vector | Test | Expected output | Entry |
| --- | --- | --- | --- |
| `fdt-pi5-kernel-1` | `full_kernel_resources_preserve_high_memory_and_actual_device_windows` | The Pi 5 kernel resources of a tree with the three RAM ranges of the 8 GB model, a UART at `/soc@107c000000/serial@7d001000` and a GIC-400: 3 RAM banks; device windows at `0x107d001000` and `0x107fff9000`, the third of size `0x2000`; a high page at `0x100000000` | Not part of this component |
| `fdt-pi5-kernel-2` | `kernel_rejects_missing_disabled_or_incompatible_uart_handoff` | A missing UART, another UART `compatible`, a window of `0x1000`, a disabled UART: the UART error of the Pi 5 resources; a disabled bus: the device-tree error `BadProperty` | Not part of this component |
| `fdt-pi5-kernel-3` | `kernel_rejects_wrong_dtb_and_image_colliding_with_its_buffer` | The address of the tree 8 bytes above the expected one, or the images `0x80000+0xf80001`, `0x81000+0x20000` and `0x80000+0x0`: the hand-over error of the Pi 5 resources | Not part of this component |
| `fdt-pi5-interrupts-1` | `translates_gic_windows_and_decodes_nonsecure_physical_timer` | The expected interrupts | Not part of this component |
| `fdt-pi5-interrupts-2` | `accepts_explicit_timer_parent_and_supported_binding_fallbacks` | With the `interrupt-parent` on the timer instead of the root, `interrupt-names`, the fallbacks `arm,armv7-timer` and `arm,cortex-a15-gic` and a `linux,phandle`: the expected interrupts | Not part of this component |
| `fdt-pi5-interrupts-3` | `accepts_deprecated_phandle_alias_only_when_unambiguous` | With `linux,phandle` in place of `phandle`: the expected interrupts | Not part of this component |
| `fdt-pi5-interrupts-4` | `ignores_unrelated_pci_cells_and_dynamic_memory_requests` | With a PCIe node of 3 address cells and a `shared-dma-pool` node with a `size` and `reusable`: the expected interrupts | Not part of this component |

`src/fdt/pi5/interrupts/tests/adversarial.rs`, 8 vectors, and
`src/fdt/pi5/interrupts/tests/firmware.rs`, 2 ignored vectors on the
shipped and merged trees outside the prototype tree. Not part of this
component: they go with the interrupt controller of the Pi 5 board support.

| Vector | Test | Expected output | Entry |
| --- | --- | --- | --- |
| `fdt-pi5-interrupts-adversarial-1` | `rejects_wrong_board_and_root_cell_profile` | The root `compatible` of the Pi 4, 1 address cell, 1 size cell, or the Pi 5 list without its last NUL: rejected | Not part of this component |
| `fdt-pi5-interrupts-adversarial-2` | `rejects_disabled_gic_timer_and_ancestor` | A disabled GIC, timer or bus: `BadProperty` | Not part of this component |
| `fdt-pi5-interrupts-adversarial-3` | `rejects_duplicate_compatible_nodes_and_duplicate_phandle_target` | A second GIC, a second timer, or a second node with `phandle` 1: `AmbiguousMapping` | Not part of this component |
| `fdt-pi5-interrupts-adversarial-4` | `rejects_unresolved_invalid_or_conflicting_interrupt_phandles` | A timer `interrupt-parent` of 0, 2, `0xffffffff`, two cells or none: rejected; a GIC `phandle` of 0, `0xffffffff`, two cells or none: rejected; a `linux,phandle` 2 besides `phandle` 1: `BadProperty`; no `interrupt-parent`: `MissingProperty` | Not part of this component |
| `fdt-pi5-interrupts-adversarial-5` | `rejects_bad_gic_binding_and_missing_or_ambiguous_bus_translation` | A GIC with `#interrupt-cells` 2 or of 8 bytes, `interrupt-controller` with a value, `cpu-offset`, the `compatible` `arm,gic-v3` added, two register windows, or overlapping windows: rejected. A bus without `ranges`: `Unmapped`; with two equal windows: `AmbiguousMapping`; with a window to parent 0: `BadProperty` | Not part of this component |
| `fdt-pi5-interrupts-adversarial-6` | `rejects_wrong_timer_type_number_trigger_cpu_mask_and_reserved_flag_bits` | The second timer record with the type 0 or 2, the number 13 or 16, or the flags `0xf01`, `0xf02`, `0xf04`, `0xf00`, `0xe08`, `0x8`, `0x1000f08` or `0xf18`: `BadProperty` | Not part of this component |
| `fdt-pi5-interrupts-adversarial-7` | `rejects_unsupported_timer_descriptions_and_interrupt_nexus` | A timer with only one record, no record, `interrupts-extended`, the `interrupt-names` of another set, `interrupt-map`, `interrupt-map-mask` or the `compatible` `vendor,unknown-timer` added: `BadProperty` | Not part of this component |
| `fdt-pi5-interrupts-adversarial-8` | `rejects_oversized_pi5_interrupt_handoff_tree` | A root property of 128 KiB: `LimitExceeded` | Not part of this component |
| `fdt-pi5-interrupts-firmware-1` | `discovers_source_firmware_interrupts_without_resolving_dynamic_cma` | For each of the two shipped trees: the expected interrupts | Not part of this component |
| `fdt-pi5-interrupts-firmware-2` | `discovers_merged_firmware_interrupts_for_all_supported_profiles` | For each of the three merged trees: the expected interrupts | Not part of this component |

`src/fdt/pci/tests.rs`, 5 vectors, the tagged PCI translation, and
`src/fdt/pi5/rp1/tests.rs`, 6 vectors, `src/fdt/pi5/rp1/tests/firmware.rs`,
1 ignored vector on the merged trees outside the prototype tree, and
`src/fdt/pi5/rp1/tests/resources.rs`, 2 vectors, the RP1 binding. Not part
of this component: they go with the
[PCIe and RP1 links](../README.md#pcie-and-rp1-links). The expected RP1
profile is the controller `0x1000120000+0x9310`, the peripherals
`0x1f00000000+0x410000`, the GPIO banks `0x1f000d0000+0xc000`,
`0x1f000e0000+0xc000` and `0x1f000f0000+0xc000`, the clocks
`0x1f00018000+0x10038`, an oscillator of 50 MHz, the resistor calibration
`0x1000119500+0x10`, the bridge reset `0x1001504318+0x30` with the index 44,
and the controller interrupts 265 and 266.

| Vector | Test | Expected output | Entry |
| --- | --- | --- | --- |
| `fdt-pci-1` | `full_width_cpu_translation_preserves_pci_tags` | Windows for 32-bit memory from 0 to `0x1f00000000`, size `0xfffffffc`, and for 64-bit prefetchable memory from `0x400000000` to `0x1c00000000`, size `0x300000000`: 32-bit memory `0xd0000+0xc000` gives `0x1f000d0000+0xc000`; 64-bit prefetchable `0x400001234+0x10` gives `0x1c00001234+0x10`; the tags of 64-bit memory, 32-bit prefetchable and 64-bit prefetchable memory at `0xd0000`: `Unmapped`; 32-bit memory `0xfffffff8+0x8`: `Unmapped` | Not part of this component |
| `fdt-pci-2` | `tags_and_width_fail_before_any_translation` | The tags 0, `0x1000000`, `0x82000000`, `0x22000000`, `0x2000800` and `0x4000000`: `BadProperty`; 32-bit memory at `0x100000000`: `Overflow`; 64-bit memory `0xffffffffffffffff+0x1`: `Overflow`; size 0: `EmptyRegion`; an address of 11 bytes: `BadProperty` | Not part of this component |
| `fdt-pci-3` | `absent_empty_truncated_overflow_and_capacity_ranges_are_rejected` | Absent and empty `ranges`: `Unmapped`; 27 bytes: `BadProperty`; a window whose parent span leaves 64 bits: `Overflow`; 17 windows, one more than the limit of 16: `LimitExceeded` | Not part of this component |
| `fdt-pci-4` | `overlapping_parent_or_child_windows_are_never_ambiguous` | A second window, of another tag, that overlaps the first in its child addresses or in its parent addresses: `Overlap`. Two adjacent windows: a request across them, `Unmapped`; `0x1000+0x4`, `0x1f00001000+0x4` | Not part of this component |
| `fdt-pci-5` | `high_parent_and_child_add_only_the_relative_offset` | A 64-bit window from `0xffff000000000000` to `0xffff100000000000`, size `0x1000`: `0xffff000000000008+0x4` gives `0xffff100000000008+0x4` | Not part of this component |
| `fdt-pi5-rp1-1` | `resolves_internal_x4_host_and_full_width_peripherals` | The expected RP1 profile | Not part of this component |
| `fdt-pi5-rp1-2` | `rejects_external_host_and_unsupported_encodings` | Each of 15 changes of the host, RP1, GPIO, clock, reset and interrupt properties: rejected | Not part of this component |
| `fdt-pi5-rp1-3` | `rejects_disabled_ancestors_providers_and_duplicate_phandles` | A disabled root, bus, host, RP1, GPIO, clocks, clock, calibration or reset node; a clock `phandle` of 0, 4 or `0xffffffff`; a conflicting `linux,phandle`: rejected | Not part of this component |
| `fdt-pi5-rp1-4` | `rejects_missing_or_malformed_cpu_translations` | An empty or malformed host or RP1 translation, an overlapping bus window, wrong `reset-names`, or a missing host `ranges`, RP1 `ranges` or `gpio-controller`: rejected | Not part of this component |
| `fdt-pi5-rp1-5` | `link_profile_rejects_additional_host_dependencies` | The link profile is the expected RP1 profile; each of 12 further host dependencies makes the link profile fail while the plain discovery still succeeds | Not part of this component |
| `fdt-pi5-rp1-6` | `intx_rejects_changed_wiring_and_trigger_before_mapping` | The INTx line is the interrupt 261; a change of any of the 32 words of `interrupt-map`, an `#interrupt-cells` of 2 or another `interrupt-map-mask`: rejected | Not part of this component |
| `fdt-pi5-rp1-firmware-1` | `discovers_rp1_in_all_merged_firmware_profiles` | For each merged tree: the INTx line 261, the expected RP1 profile, the device windows of each of the five resource profiles, and the link profile | Not part of this component |
| `fdt-pi5-rp1-resources-1` | `every_rp1_profile_fits_the_complete_device_mapping_plan` | Each of the five resource profiles adds the expected RP1 profile and holds 4, 6, 7, 10 or 11 device windows at their expected addresses | Not part of this component |
| `fdt-pi5-rp1-resources-2` | `rp1_projection_is_atomic_on_late_binding_and_capacity_failure` | A late binding failure leaves the device windows unchanged; with the device list full, the capacity error of the memory plan, `Capacity`, and the windows unchanged | Not part of this component |

`src/fdt/pi5/sdio/tests.rs`, 4 vectors, one of them ignored and on the
merged trees outside the prototype tree: the binding of the SD card slot.
Not part of this component: they go with the SD card host of the EL0
services and storage domain.

| Vector | Test | Expected output | Entry |
| --- | --- | --- | --- |
| `fdt-pi5-sdio-1` | `both_silicon_pin_layouts_resolve_the_same_card_slot` | For both pin layouts: the host `0x1000fff000+0x260`, the configuration `0x1000fff400+0x200`, the GPIO `0x107d517c00+0x40`, a clock of 200 MHz, the interrupt 305, and a first pin span of `0x30` in the first layout and `0x20` in the second | Not part of this component |
| `fdt-pi5-sdio-2` | `invalid_routes_clocks_power_and_pin_dependencies_fail_closed` | Each of 27 changes of the route, clock, supply and pin properties: rejected | Not part of this component |
| `fdt-pi5-sdio-3` | `missing_disabled_and_ambiguous_dependencies_are_rejected` | A disabled node of the slot or of one of its providers, a missing required property, or a clock `phandle` of 0, 1, 13 or `0xffffffff`: rejected | Not part of this component |
| `fdt-pi5-sdio-4` | `sd_and_rp1_share_the_complete_firmware_mapping_plan` | For each merged tree, the SD card host after the RP1 resources: 15 device windows; a second addition fails and leaves them unchanged | Not part of this component |

## References

- devicetree.org, *Devicetree Specification*, release v0.4, 2023,
  <https://github.com/devicetree-org/devicetree-specification/releases/download/v0.4/devicetree-specification-v0.4.pdf>:
  section 2.2.1 node names, 2.2.4 property names, 2.3.4 `status`, 2.3.5
  `#address-cells` and `#size-cells`, 2.3.6 `reg`, 2.3.8 `ranges`, 2.3.9
  `dma-ranges`, 3.4 the `/memory` node, 3.5 the `/reserved-memory` node with
  3.5.2 its child nodes, static and dynamic, `no-map` and `reusable`, 3.7
  and 3.8 the `/cpus` and `/cpus/cpu*` nodes, and chapter 5, the flattened
  format: 5.2 the header, 5.3 the memory reservation block, 5.4 the
  structure block, 5.5 the strings block and 5.6 the alignment.
- Arm Limited, *Arm Architecture Reference Manual for A-profile
  architecture*, DDI 0487, version M.d, 2026,
  <https://documentation-service.arm.com/static/6abbec2a6db85c5e6614a4a1>:
  `MPIDR_EL1` and its affinity fields.
- Arm Limited, *Arm Power State Coordination Interface*, DEN 0022: the
  conduits of PSCI.
- Raspberry Pi Ltd, *Raspberry Pi 5 Product Brief*,
  <https://datasheets.raspberrypi.com/rpi5/raspberry-pi-5-product-brief.pdf>:
  the five RAM sizes of the Pi 5.
- Raspberry Pi Ltd, the device tree that the firmware ships, commit
  `016253866bbd6c77fcb2a744a97d81e79ad4884f`,
  <https://github.com/raspberrypi/firmware/blob/016253866bbd6c77fcb2a744a97d81e79ad4884f/boot/bcm2712-rpi-5-b.dtb>,
  equal byte for byte to that of commit
  `dcca4969e53d2a25e688f0f228a09486786d54c0`, the firmware of the
  prototype's measurements: the counts of the limits, the placeholder memory
  node, `atf@0` and `linux,cma`.
- Raspberry Pi Ltd, the device trees of the BCM2712 in the Raspberry Pi
  Linux tree, commit `ef71464298cd2dd89f6d190c08e812296240281e`:
  `arch/arm64/boot/dts/broadcom/bcm2712-rpi-5-b.dts`, the placeholder memory
  node that the bootloader fills; `bcm2712.dtsi`, `atf@0` and `linux,cma`;
  `bcm2712-ds.dtsi`, the `size` of one cell of `linux,cma`; and
  `arch/arm/boot/dts/overlays/README`, the overlay `cma` that sets its size.
- The QEMU Project, QEMU 8.2.2, `hw/arm/virt.c`,
  <https://gitlab.com/qemu-project/qemu/-/blob/v8.2.2/hw/arm/virt.c>: the
  random `kaslr-seed` and `rng-seed` that `create_randomness` writes into
  `/chosen` by default, and the memory node of the machine; QEMU 11.1.2,
  whose tree of the machine `virt-8.2` gives the QEMU virt column of the
  limits.
- The prototype tree at `prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`,
  whose documents the rules of this page restate as clauses of the
  component; where a document and the code differ, as the 128 properties of
  a node in the first document against 512 in the code and in the others,
  the code and its tests decide:
  - `docs/features/kernel/memory.md`, lines 93 to 154, the device-tree
    contract and the reservations, and lines 237 to 259, the multiple banks
    and high backing;
  - `docs/pi5-bring-up.md`, lines 63 to 80, the firmware memory discovery;
  - `docs/pi5-kernel.md`, lines 166 to 224, the firmware and resource
    contract;
  - `docs/platform-resources.md`, lines 8 to 66, the memory contract and the
    device and CPU contracts;
  - `docs/records/kernel/concurrency-fdt-review/README.md`, lines 86 to 152,
    the framing, bounds and borrowed lifetime and the memory and device
    descriptions.
