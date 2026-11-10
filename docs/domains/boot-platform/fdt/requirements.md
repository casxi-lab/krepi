---
features: none
---

# Device-tree requirements

The observable behaviour of the `fdt` component of the
[boot and platform](../README.md) domain: the bounded parsing of the device
tree that the firmware hands over, the discovery of memory and CPUs from it,
the Pi 5 boot memory and the boot memory map. The rules that its code and
tests follow are in the [contract](contract.md).

## Sources

- The parser, the node access and the translation of addresses, the memory
  discovery, the CPU nodes and the Pi 5 boot memory are to be ported from
  `src/fdt` of the prototype tree at
  `prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e`, without its Pi 5
  device bindings, and the boot memory map from
  `src/platform/memory.rs` and `src/platform/memory/available.rs` of the
  same tree. The tests of these files are the frozen vectors of the
  [contract](contract.md#legacy-test-vectors), with two changes of
  behaviour: a dynamic reservation is accepted and recorded, and boot
  storage holds up to 4 spans.
- The format and the bindings follow the Devicetree Specification, release
  v0.4. The limits are set from the tree that the Raspberry Pi 5 firmware
  ships, from the prototype's measurements of the hand-over tree of the
  8 GB model and from the tree that QEMU builds for the machine `virt`, as
  the [contract](contract.md#format-and-bounds) gives them with their
  sources.
- The five RAM models come from the product brief of the Raspberry Pi 5;
  the RAM ranges of the 8 GB model are the prototype's measurement, and
  those of the other four are inferred from it
  ([Memory discovery](contract.md#memory-discovery)).

## Configurations

- **QEMU virt.** The machine `virt-8.2` without EL2 and EL3, with GICv2,
  one Cortex-A76 and 128 MiB of RAM, the machine of `cargo xtask qemu`, at
  the QEMU version that `toolchains.toml` pins. Its loader places the
  hand-over tree at the start of RAM, `0x4000_0000`, with one memory node
  and PSCI over HVC. The same machine with EL2, whose PSCI conduit is SMC,
  is a configuration of FDT-R08 only.
- **Raspberry Pi 5.** The five RAM models, with 1, 2, 4, 8 and 16 GB, and
  the hand-over tree that the firmware leaves. Only the 8 GB model runs on
  a board in release 0.1; the 1, 2, 4 and 16 GB models are covered by host
  tests on trees of their inferred RAM ranges and are not run on a board in
  that release.
- **Host.** The host tests of the module `fdt` (planned), on the
  development host and in CI, with the frozen vectors and the trees that
  the tests build.
- The component runs on the boot CPU before the secondary CPUs start; more
  than one CPU only reads its results.

## Requirements

### FDT-R01

**Bounded parse of an untrusted tree.** `Fdt::parse` accepts a device tree
only when its header, its blocks, its reservation map and every token of
its structure block keep the format of chapter 5 of DTSpec v0.4 and the
limits of the parse in the contract: at most 2 MiB; 32 nodes on a path;
65,536 tokens; 512 properties in a node; property names of up to 64 bytes;
and 128 entries of the reservation map. It accepts the trees of the
supported boards, among them a node with 334 properties and property names
of 32 bytes, as the Pi 5 tree has, and the bytes that QEMU leaves in the
padding after a property value. The criterion: for each of these limits,
an input at the limit is accepted and one 1 above it fails with the error
of the contract, and every vector of the parse gives its expected output.
The limits of the RAM ranges, of the reserved regions and of the Pi 5
hand-over tree are those of FDT-R03 and FDT-R05.

- **Examples.** None: no feature document describes the component.
- **Entry points.** `fdt::Fdt::parse` (planned).
- **Contract.** [Format and bounds](contract.md#format-and-bounds),
  [Rejection and error priority](contract.md#rejection-and-error-priority).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: no target is registered for the component.
- **Evidence.** The host tests of the module `fdt` (planned) that replay the
  vectors `fdt-parser-1` to `fdt-parser-9` and the tests of each limit
  that the [testing obligations](contract.md#testing-obligations) list. They
  show the limits on trees that the tests build. They do not show the trees
  of other firmware versions or configurations, which the limits cover only
  with their margins.

### FDT-R02

**Rejection without partial results.** An entry that rejects its input
returns one error, the error of the first broken rule in the error orders
of the contract, and no partial tree, memory map, topology or boot memory
map. No byte string makes an entry panic. Where an entry looks for one item
and finds two, it rejects the input and never picks one. The criterion:
every prefix of a valid tree is rejected; every tree with one byte changed
returns from the parse and from the entries on it; each error of the error
table is reached by a vector or a test; and for each step of the error
orders, an input that breaks that step and a later one gives the error of
that step.

- **Examples.** None: no feature document describes the component.
- **Entry points.** Every entry of the
  [contract](contract.md#entry-points).
- **Contract.**
  [Rejection and error priority](contract.md#rejection-and-error-priority),
  [Check and execute](contract.md#check-and-execute).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: no target is registered for the component.
- **Evidence.** The host tests that replay the property vectors
  `fdt-parser-1` and `fdt-parser-6`, the vectors whose expected output is
  an error, and the tests of the error orders of the
  [testing obligations](contract.md#testing-obligations). They show the
  errors on these inputs. The prefixes and single changes of one small tree
  are examples, not every input.

### FDT-R03

**Memory discovery.** `Fdt::discover_memory` gives the RAM ranges of the
enabled memory nodes below the root, the reserved regions of the
reservation map, marked `no-map`, and of the static children of
`/reserved-memory`, with their `no-map` and `reusable` flags, and the
number of dynamic reservations. It skips disabled memory nodes before it
checks their binding, accepts reserved regions outside every RAM range, and
fails on overlapping RAM, on `no-map` with `reusable`, on a
`/reserved-memory` whose cells differ from the root's or whose `ranges` is
not empty, on a tree without RAM, and on more than 32 RAM ranges or more
than 128 reserved regions. The criterion: the vectors of the discovery give
their expected outputs; 32 RAM ranges and 128 reserved regions are
accepted, and 33 and 129 fail with `LimitExceeded`; and a tree with the RAM
ranges and both reserved regions of the 8 GB hand-over tree is accepted,
with the region of 62 bytes in the hole between two ranges kept.

- **Examples.** None: no feature document describes the component.
- **Entry points.** `Fdt::discover_memory` and the `MemoryMap` that it
  returns (planned).
- **Contract.** [Memory discovery](contract.md#memory-discovery).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: no target is registered for the component.
- **Evidence.** The host tests that replay `fdt-discovery-1` to
  `fdt-discovery-6`, `fdt-parser-7`, `fdt-pi5-boundaries-5` and
  `fdt-pi5-selection-3`, and the tests of 32 RAM ranges and of the 8 GB
  hand-over shape of the
  [testing obligations](contract.md#testing-obligations). They
  show the discovery on trees that the tests build. They do not show that a
  hand-over tree describes the installed RAM, which only a board run shows.

### FDT-R04

**Dynamic reservations are recorded, not refused.** An enabled child of
`/reserved-memory` with a `size` and without a `reg` is counted as a
dynamic reservation and is neither a reserved region nor a reason to
reject the tree, whatever the number of cells of its `size`; the kernel
allocates no pool for it. A disabled one is ignored, and a child with both
`reg` and `size` is a static region. So the shipped Pi 5 tree, whose
`linux,cma` has a `size` of one cell, is accepted without an overlay that
disables it. The criterion: the vectors `fdt-discovery-4`, `fdt-pi5-4` and
`fdt-pi5-firmware-1` give the outputs of this contract, which the prototype
did not, and `fdt-pi5-2` its own; and the tests of dynamic reservations of
the [testing obligations](contract.md#testing-obligations) pass.

- **Examples.** None: no feature document describes the component.
- **Entry points.** `Fdt::discover_memory`, `MemoryMap::dynamic`,
  `Fdt::discover_pi5_boot_memory` and `Pi5BootMemory::dynamic` (planned).
- **Contract.** [Memory discovery](contract.md#memory-discovery),
  [Behaviour changes](contract.md#behaviour-changes).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: no target is registered for the component.
- **Evidence.** The host tests that replay these vectors and the tests of
  the testing obligations. The vector `fdt-pi5-firmware-1` needs the
  shipped trees, which lie outside the repository; its other vectors and
  tests build their trees. None of them shows a board booting with the
  reservation enabled, which only a board run shows.

### FDT-R05

**Pi 5 hand-over checks.** `Fdt::discover_pi5_boot_memory` accepts a Pi 5
hand-over tree only when it is at most 128 KiB, its address is a multiple of
8, its root has 2 address cells and 2 size cells and a `compatible` that
names `raspberrypi,5-model-b` and `brcm,bcm2712`, the image is nonempty and
disjoint from the tree, and the tree and the image each lie inside one RAM
range; it gives the memory map, the spans of the tree and of the image and
the sum of the RAM ranges. `is_available` and `find_available` never give a
span that touches the image, the tree or a reserved region, or that bridges
two RAM ranges or a hole. The criterion: the vectors of the Pi 5 boot memory
give their expected outputs, and a hand-over tree of exactly 128 KiB is
accepted and one of 1 byte more fails with `LimitExceeded`.

- **Examples.** None: no feature document describes the component.
- **Entry points.** `Fdt::discover_pi5_boot_memory`,
  `Pi5BootMemory::is_available` and `find_available` (planned).
- **Contract.** [Memory discovery](contract.md#memory-discovery),
  [Boot memory map](contract.md#boot-memory-map).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: no target is registered for the component.
- **Evidence.** The host tests that replay `fdt-pi5-1` to `fdt-pi5-4`,
  `fdt-pi5-boundaries-1` to `fdt-pi5-boundaries-5`, `fdt-pi5-selection-1`
  to `fdt-pi5-selection-3` and `fdt-pi5-firmware-2`, the last on merged
  trees outside the repository, and the tests of the 128 KiB limit of the
  [testing obligations](contract.md#testing-obligations). They show the
  checks on these trees. They do not show the address at which the
  firmware leaves the tree or the layout in which it loads the image, which
  the board support of the Pi 5 states and a board run shows.

### FDT-R06

**Every RAM model of the Pi 5.** The limits and capacities hold the RAM of
each of the five RAM models: 1 to 3 RAM ranges, within the 32 of the
discovery and the boot memory map, and at most 16 GiB less 4 MiB, within
the 16 GiB of the boot memory map. The 8 GB model hands over the three
ranges that the prototype measured, and the 1, 2, 4 and 16 GB models the
ranges that the contract infers from that measurement. The criterion: for
each of the 1, 2, 4 and 16 GB models, a host test parses a hand-over tree
of its inferred ranges and builds its boot memory map, with the installed
size less 4 MiB as RAM and the hole left out of the usable ranges; for the
8 GB model, the vector `fdt-pi5-platform-1` does the same with the
measured ranges.

- **Examples.** None: no feature document describes the component.
- **Entry points.** `Fdt::discover_pi5_boot_memory` and
  `MemoryPlan::all_ram` and `from_pi5` (planned).
- **Contract.** [Memory discovery](contract.md#memory-discovery),
  [Boot memory map](contract.md#boot-memory-map),
  [Testing obligations](contract.md#testing-obligations).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: no target is registered for the component.
- **Evidence.** The four host tests of the testing obligations and the
  vector `fdt-pi5-platform-1`. They show that trees of these shapes are
  accepted and fit the capacities. They do not show the shapes that the
  firmware of the 1, 2, 4 and 16 GB models hands over, which are inferred:
  only the 8 GB model runs on a board in release 0.1.

### FDT-R07

**Boot memory map.** `MemoryPlan::all_ram` keeps 1 to 32 disjoint RAM banks
of at most 16 GiB together, separate even where they are adjacent, and
manages their complete 4 KiB pages; it rounds the 1 to 4 spans of boot
storage and the at most 128 firmware reservations outward to whole pages,
requires each span of boot storage to lie inside one bank on pages of its
own, and rejects a firmware reservation on a page of boot storage. Its usable
ranges leave out every page of boot storage and of every firmware
reservation, `reusable` ones included, and never bridge two banks or a hole.
`MemoryPlan::new` manages a window of at most 128 MiB inside one bank. The
criterion: the vectors of the boot memory map give their expected outputs,
with the one change of `platform-10`, and boot storage of 4 spans is
accepted and of 5 fails with `Capacity`.

- **Examples.** None: no feature document describes the component.
- **Entry points.** `MemoryPlan::all_ram`, `new` and `from_pi5`, and its
  queries and `available_ranges` (planned).
- **Contract.** [Boot memory map](contract.md#boot-memory-map).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: no target is registered for the component.
- **Evidence.** The host tests that replay `platform-1` to `platform-13`,
  `fdt-pi5-platform-1`, `fdt-pi5-platform-2` and `fdt-pi5-firmware-2`, and
  the test of the capacity of boot storage of the
  [testing obligations](contract.md#testing-obligations); `platform-2` and
  `platform-11` also use the page ownership table of the
  [page-tables](../../memory/page-tables/requirements.md) component. They
  show the map as a value. They do not show the mapping of its usable
  ranges or their allocation, which the page-tables component covers.

### FDT-R08

**CPU nodes.** `Fdt::discover_cpus` accepts the CPUs of a tree only when
`/cpus` is enabled with 0 size cells, every CPU node is an enabled
Cortex-A76 whose `reg` is the affinity of its logical ID in the profile,
level 1 of `MPIDR_EL1` on the Pi 5 and level 0 on QEMU virt, the logical
IDs run from 0 to `count - 1` without a gap or a repeat for a count of 1, 2
or 4, and of 4 on the Pi 5, every CPU but the first uses PSCI, on the Pi 5
every CPU, and `/psci` has the conduit of the profile and a supported
`compatible`. The flag bits of `MPIDR_EL1` do
not change a logical ID. `validate_qemu_timers` accepts only the timer
records of QEMU virt for the admitted CPUs. The criterion: the vectors of
the CPU nodes give their expected outputs.

- **Examples.** None: no feature document describes the component.
- **Entry points.** `Fdt::discover_cpus`, `CpuTopology::count`, `profile`,
  `affinity` and `validate_qemu_timers`, and `CpuProfile::logical_id`
  (planned).
- **Contract.** [CPU nodes](contract.md#cpu-nodes).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: no target is registered for the component.
- **Evidence.** The host tests that replay `fdt-cpus-1` to `fdt-cpus-6`.
  They show the checks on trees that the tests build. They do not show that
  the CPUs start, which the multicore domain shows.

### FDT-R09

**Address translation.** `reg`, `ranges` and `dma-ranges` are read in the
cells of the right node, never truncated and never inherited from an
ancestor further up; a translation goes through the one window that holds
the whole request, an absent map maps nothing and an empty one is the
identity, and a request that two windows hold, that a window holds only in
part, or whose result leaves the width of its side, fails. CPU addresses
and the addresses of devices are separate maps. The criterion: the vectors
of the translation give their expected outputs.

- **Examples.** None: no feature document describes the component.
- **Entry points.** `cells_u64`, `Reg::new`, `AddressMap::new`, `kind`,
  `to_parent` and `to_child`, and `Node::reg`, `ranges`, `dma_ranges` and
  `translate_reg` (planned).
- **Contract.** [Address translation](contract.md#address-translation),
  [Format and bounds](contract.md#format-and-bounds).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: no target is registered for the component.
- **Evidence.** The host tests that replay `fdt-translation-1` to
  `fdt-translation-5` and `fdt-discovery-2`. They show the translation on
  these maps. They do not show the tagged addresses of PCI, which the
  [PCIe and RP1 links](../README.md#pcie-and-rp1-links) cover.

### FDT-R10

**The same result on every boot.** The results of the parse, of the
discoveries and of the boot memory map are functions of the bytes of the
tree and of the arguments; no entry reads `/chosen`, where QEMU virt writes
new random seeds at every boot. The criterion: three cold boots of QEMU
virt, each in a new QEMU process, give the same results of the parse and of
the boot memory map.

- **Examples.** None: no feature document describes the component.
- **Entry points.** `Fdt::parse`, `Fdt::discover_memory` and
  `MemoryPlan::all_ram` (planned), as the boot code of QEMU virt calls them.
- **Contract.** [Determinism](contract.md#determinism).
- **Specification.** None: no specification covers the component.
- **Proof path.** None: no target is registered for the component.
- **Evidence.** The case of the QEMU boot suite that the
  [testing obligations](contract.md#testing-obligations) name, on the QEMU
  virt configuration. It shows that the seeds do not reach the results on
  that machine. It shows nothing for the Pi 5, whose hand-over trees a
  board run compares.

## Liveness, time and performance

- Every entry ends within the loop bounds of the
  [contract](contract.md#work-bounds) and waits for nothing: the component
  has no long operation and takes no lock.
- The structure block of the tree that the Pi 5 firmware ships holds 2,973
  tokens, and that of QEMU virt 343, far below the limit of 65,536; the
  number of tokens of the Pi 5 hand-over tree, which is 1,826 bytes longer
  than the shipped file in the prototype's measurement, was not counted.
  No test bounds the time of an entry.

## Scope

- The component reads the tree and never changes it: it applies no
  overlay, resolves no alias and no abbreviated path, and does not resolve
  `phandle` references.
- The bindings of the Pi 5 devices, its interrupt controller and timer, its
  UART, the PCIe link to RP1, RP1 and the SD card, are not part of it; the
  components that use them read the tree through its node access and
  translation, and their vectors are frozen in the
  [contract](contract.md#pi-5-device-binding-vectors).
- A dynamic reservation is recorded, not allocated: the kernel has no pool
  for it.
- The boot memory map describes memory; it allocates and maps nothing.
  The page ownership table and the kernel direct map belong to the
  [page-tables](../../memory/page-tables/requirements.md) component.
- RAM above 16 GiB in all is not supported, and neither is a tree above
  2 MiB, or above 128 KiB on the Pi 5.
- The 1, 2, 4 and 16 GB models of the Pi 5 are not run on a board in
  release 0.1.

## Contract sections without a requirement

- [Check and execute](contract.md#check-and-execute),
  [Work bounds](contract.md#work-bounds) and
  [State fields](contract.md#state-fields) bind the code without an
  observable behaviour of their own.
- [Open obligations](contract.md#open-obligations) records the board's
  forming of the slice of the tree, which no requirement observes apart
  from the parse that follows it.
