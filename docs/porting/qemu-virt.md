---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - src/board/qemu/mod.rs
  - src/entry.rs
  - src/main.rs
  - src/fault.rs
  - link.ld
  - .cargo/config.toml
  - src/mmu.rs
  - src/boot_memory/banks.rs
destination:
  - kernel/boards/qemu-virt/Cargo.toml
  - kernel/boards/qemu-virt/build.rs
  - kernel/boards/qemu-virt/link.ld
  - kernel/boards/qemu-virt/src/lib.rs
  - kernel/boards/qemu-virt/src/main.rs
  - kernel/boards/qemu-virt/examples/kernel-memory.rs
  - kernel/boards/qemu-virt/examples/boot-memory.rs
  - kernel/boards/qemu-virt/examples/memory/mod.rs
  - .cargo/config.toml
treatment: ported
features:
  - krepi.platform.qemu-virt-boot
  - krepi.platform.device-tree
  - krepi.kernel.kernel-memory
---

# Porting record: kernel/boards/qemu-virt/src/lib.rs

## Summary

The crate roots of the QEMU virt board crate `krepi-qemu-virt` and the
build of its images. The library root takes from `src/board/qemu/mod.rs`
the board constants that the boot uses. The binary root `src/main.rs` is the
default image: `kernel_main`, which `src/entry.rs` defined for QEMU virt,
with the initialization checks of the legacy `src/main.rs`, the CPU identity
check `verify_cpu` of `src/board/qemu/mod.rs`, the boot records, the echo
loop, the exception dispatch of the legacy `src/main.rs` and the panic
handler, which writes the panic record of the legacy `src/fault.rs`. The
link script `link.ld` and the flags of the bare-metal target from the
legacy `.cargo/config.toml` build the image and the test images, the
examples of the crate; a new build script hands the linker the script.

`src/main.rs` and `src/entry.rs`, the root of the legacy kernel binary and
its firmware entry, `src/fault.rs`, its fatal records, and `link.ld` and
`.cargo/config.toml` at the root of the legacy tree lie outside the areas
that the
[classification](../conventions/porting.md#classification-of-the-legacy-areas)
lists. They are ported in part, with each board's image: the entry checks,
the panic handler with its record, the layout of the image and the target
flags. The rest of `src/main.rs`, the start of the resource controller, the
runtime, the user domains and the serial diagnostic commands, belongs to the
areas it served, which are redesigned or retired. The rest of `src/fault.rs`
is ported with the exception record, in the [fault](fault.md) record, and
with fault symbolization.

The default image calls the boot wiring of the board between its boot
records: `image::device_tree` forms the slice of the device tree at the
start of RAM and `image::boot_memory` calls `boot_memory::wire` on it, whose
record is [boot_memory](boot_memory.md). Two examples are the test images
of kernel memory, with a module that only they declare,
`examples/memory/mod.rs`, which forms the slice of the tree as the default
image does and calls the wiring: `examples/kernel-memory.rs` takes the probes `memory_probe_load`,
`memory_probe_store` and `memory_probe_execute` of `src/mmu.rs` with their
resume labels, written again under the names of the test image, and the
pattern of the edge pages of `src/boot_memory/banks.rs`, and reads and
writes the edge pages of the usable ranges, takes the faults of the
excluded pages, of the read-only data, of an execute-never page and of the
guard, and checks the `Device` console; `examples/boot-memory.rs` writes
the counts of the wiring. The test image dispatches its faults itself: the
fault plans of `src/mmu/fault.rs` and the probe of the publication of code
of `src/mmu/code.rs`, boot-time probes of the prototype, are not taken. The
legacy area `src/boot_memory` is classified in
[boot_memory](boot_memory.md#summary).

## Changes

- `UART_BASE`, `0x0900_0000`, is a constant of the crate root, in place of
  the `UART` span of type `fdt::Span`, and so are `GIC_DISTRIBUTOR`,
  `0x0800_0000`, and `GIC_CPU`, `0x0801_0000`, the starts of the
  `GIC_DISTRIBUTOR` and `GIC_CPU` spans, and `TIMER_INTID`, 27, of the
  virtual profile, which the interrupt wiring [irq](irq.md) uses.
  `TIMER_PRIORITY`, `0x80`, and `TIMER_RATE`, 100, name the priority and
  the rate that the legacy `irq.rs` wrote as literals.
- `CONSOLE_BOUNDS` gives the console bounds of QEMU virt, the legacy
  values, as platform parameters; the [console](console.md) record describes
  them.
- `verify_cpu` keeps its check and its record. The mask and the value of the
  check are the named constants `MIDR_PART_MASK` and `MIDR_CORTEX_A76` of the
  library root, and the check is an `assert!` with the static message `QEMU
  Cortex-A76 required` in place of an `assert_eq!`, whose formatted message
  the panic record would leave out. It is a function of the image module of
  `src/main.rs`, its only caller, which is compiled only for the bare-metal
  target, so that no item of the library root needs a `cfg` of its own.
- `counter`, the virtual counter of the legacy virtual profile, is an import
  of the PL011 driver, the only code that uses it, without its `cfg`.
- `kernel_main` calls the initialization directly. It does not build the
  legacy entry record `Info`: on QEMU virt its exception level and affinity
  were the constants 1 and 0 and its control value was `SCTLR_EL1`, which
  the checks read themselves. The assertions on the record's exception
  level, 1 or 2, and on its affinity, which held for those constants, go
  with it.
- The initialization checks keep their order and conditions, each as an
  `assert!` with a static message: BSS, data, EL1, the MMU and the caches
  off, `verify_cpu`, then the check of the entry control. That legacy check
  against `0x0200_1005` adds to the cache and MMU bits only bit 25,
  `SCTLR_EL1.EE`, and checks only that bit here, as `EL1 data must be
  little-endian`, after `verify_cpu` as before. The check that FP/SIMD
  traps, which the legacy kernel made after its initialization, follows
  it.
- After the checks the image writes `CASXI_BOOT kernel=krepi board=qemu-virt
  el=<level>`, runs the boot wiring and writes `CASXI_READY`, the records of
  the [boot contract](../domains/boot-platform/boot/contract.md#records), and
  then echoes its serial input, in place of the legacy banner and runtime.
- The wiring takes the place of the legacy calls of boot memory, the MMU
  and the allocators: `image::device_tree` forms the slice of the 40-byte
  header of the tree at `boot_memory::TREE_BASE`, the legacy `DTB_ADDRESS`,
  and then of its `totalsize` bytes, at most 2 MiB, and `image::boot_memory`
  calls `boot_memory::wire` once, which reads the tree, builds the boot
  memory map, the page ownership table and the kernel tables and turns the
  MMU on with the caches off ([boot_memory](boot_memory.md)). Each is a
  function of its own, so that the `unsafe` site of each has its row in
  the open obligations of the fdt and page-tables contracts and
  `kernel_main` keeps none but its export. The sizes of the `UART` and
  `GIC_CPU` spans, one page and 64 KiB, are constants of the layout of the
  wiring.
- The panic handler takes from `panic` of `src/fault.rs` the rule that only
  a static message is written, passes that message, if the panic has one,
  and the location to `uart::report_panic`, which writes the panic record
  through the [console](console.md#changes), and halts. It leaves out the
  rest of the legacy `panic`: the masking of IRQs, as no code of the image
  unmasks them; the takeover of the console lease, which is not ported; and
  the frame trace from the stack registers, with the build-id, which come
  with fault symbolization.
- The exception dispatch of the image, `exception_dispatch` of the legacy
  `src/main.rs` (lines 370-385), keeps only its last step: every exception
  writes the exception record and `CASXI_HALTED` through
  `uart::report_fatal` and halts. The image unmasks no exception, so only a
  synchronous exception of its own code reaches it.
- On the host the binary is an empty program, so that the repository checks
  build and lint the crate; the image module and the panic handler are
  compiled only for the bare-metal target.
- The link script keeps the memory layout, the program headers, the
  sections, with the exception vectors in `.text.vectors` after the cold
  entry, the guard page and the 64 KiB stack, the discarded unwind sections
  and the assertions on the entry, the 2 KiB alignment of the vectors, the
  stack alignment, the end of the image and the 36-byte build-id note. The
  comments are written again and name the feature.
- The `.cargo/config.toml` of the repository root, which holds the alias of
  `cargo xtask`, gains the flags of the bare-metal target
  `aarch64-unknown-none-softfloat` from the legacy `.cargo/config.toml`,
  unchanged; Cargo reads them when it builds at the root or below it, in
  `kernel/` too. The proof gate refuses Cargo configuration below the root,
  so the kernel workspace has none of its own.
- The manifest and the build script are new. The manifest depends on
  `krepi-arch` and on the provable core `krepi-kernel`, whose `fdt` and
  `page_tables` the boot wiring calls. The build script passes
  `-T<crate>/link.ld` to the linker for the binaries and the examples of the
  crate when the target OS is `none`, and nothing on the host. The examples,
  the test images, also get `--entry=krepi_test_entry`: each test image
  names its own entry, a branch to `_start` or, for the image that enters at
  EL2, its EL2 entry, so that the default image and its link script keep
  `_start` as the entry. The legacy link script kept a section
  `.text.test_entry` for the entry of a fixture in the same image.
- The comment of the link script says that the runner gives QEMU virt
  128 MiB of RAM at `0x4000_0000`, its `-m 128M`, which is also QEMU's
  default, in place of a minimum; the layout is unchanged.
- The test images of kernel memory take the slice of the tree and the call
  of the wiring from `examples/memory/mod.rs`. `kernel-memory` takes every
  address from the boot memory map and the link symbols, not the fixed
  addresses of the prototype's probes. It writes the
  complement of the pattern of `banks.rs`, unchanged, into each edge page
  through the direct map, zeroes the page with `krepi_arch::mmu::zero_frames`,
  reads it back as zero and then writes and reads the pattern, where the
  legacy probe took its pages from the page allocator with high and low
  placement. Its probes keep the instructions of the legacy probes: a load
  `ldr x1, [x0]`, a store `str x1, [x0]` and a call `blr x0` with its frame
  record saved, each followed by its resume label. Its dispatch counts a
  synchronous exception at the armed site, disarms it, reports it with the
  exception record and resumes at the label; any other exception is fatal.
  The absolute symbol `krepi_test_execute_never` names the direct-map page
  of the execute-never probe, which a word of its read-only data holds, so
  that the suite reads the return address of that fault from the ELF file.
- `boot-memory` writes two count records, `CASXI_MEMORY` with the size of
  the tree and the numbers of RAM banks, firmware reservations, spans of
  boot storage, managed banks and usable ranges of the boot memory map, and
  `CASXI_TABLES` with the tables, blocks and pages of the plans of the two
  kernel sets, from what the wiring returns, and the self-check
  `stack-depth`, from the lowest word of the stack that is not zero, as the
  cold entry clears the stack. The legacy `CASXI_MEMORY` of
  `verify_allocators` had another form.

## Tests carried over

None: the legacy files held no host tests.

## Behaviour changes

| Change | Test |
| --- | --- |
| The boot writes `CASXI_CPU`, `CASXI_BOOT kernel=krepi board=qemu-virt el=1` and `CASXI_READY`, each with CR LF, in place of the legacy `CASXI_CPU`, `CASXI_KERNEL_ENTRY`, `CASXI_BUILD`, banner lines and `CASXI_READY` | The case `cold-boot-echo` of `cargo xtask qemu-boot` |
| After `CASXI_READY` the image echoes each received byte, with a line feed after a carriage return, and no byte triggers a command | The same case; `console::tests::examples::ex3_the_echo_adds_lf_after_cr_only` |
| Between `CASXI_BOOT` and `CASXI_READY` the image reads the device tree, builds the boot memory map and the kernel tables and turns the MMU on with the caches off, and reports none of it: no `CASXI_FDT`, `CASXI_MMU`, `CASXI_DIRECT`, `CASXI_MEMORY` or cache mode record | The same case, whose transcript holds nothing else and is the transcript of the image without the wiring |
| The edge pages of the usable ranges are written and read back through the direct map after a zeroing, the excluded pages, the read-only data, an execute-never page and the guard fault as the layout says, and the console is a `Device` page | The case `kernel-memory` of `cargo xtask qemu-boot` |
| The counts of the boot memory map and of the kernel tables are written, and are the same at three cold boots | The case `boot-memory` of `cargo xtask qemu-boot` |
| A panic, such as a check that fails, writes its static message in `CASXI_PANIC`, its location and `CASXI_HALTED`, without `truncated=` and without a frame trace | `console::tests::panic_record::a_static_message_is_written_with_its_location`, `console::tests::panic_record::a_dynamic_message_is_replaced_by_the_fixed_text`, `console::tests::panic_record::a_panic_without_a_location_has_no_location_record` |
| An exception writes the exception record and `CASXI_HALTED` and halts, without the user, IRQ and MMU recovery steps of the legacy dispatch | `fault::tests::examples::ex5_a_fatal_exception_ends_in_the_halt_record`; the cases `el1-fp-trap` and `injected-serror` of `cargo xtask qemu-boot`, whose test images dispatch as the default image does |

## Hardware evidence to re-obtain

- The cold boot of the default image on QEMU virt `virt-8.2` with one
  Cortex-A76 into EL1, its records and its echo, three times with identical
  transcripts: the case `cold-boot-echo`, in CI.
- The exception record and halt of the dispatch: the cases `el1-fp-trap` and
  `injected-serror`, in CI.
- The edge pages of the usable RAM, the faults of the kernel tables and the
  `Device` console with the MMU on, and the counts of the boot wiring at
  three cold boots, with identical transcripts: the cases `kernel-memory`
  and `boot-memory`, in CI.

## Not carried over

- From `src/board/qemu/mod.rs`: the `physical-kernel-test` branches, the
  physical profile with `physical_counter` and interrupt 30, and the
  `smp-el2-test` choice of `CPU_PROFILE`, all feature-profile branches; the
  declarations of `topology` and `memory` and the re-export of
  `discover_memory`: `topology` comes with secondary CPU startup, and the
  memory discovery of `memory` is in [boot_memory](boot_memory.md); the
  re-exports of the MMU configuration of `cached` and `uncached`, whose
  register writes [mmu](mmu.md) takes from `cached`; `fdt::Span`, as the
  core's `fdt` has its own; `fdt::CpuProfile` and `CPU_PROFILE`, which come
  with secondary CPU startup; `MINIMUM_RAM`, as the runner gives the machine
  its RAM; `CPU_COMPATIBLE`, whose check of the CPU node is not taken; and
  `LABEL`, `CLOCK_NAME` and `TIMER_NAME`, the names of the legacy diagnostic
  records.
- From `src/entry.rs`: `Info` and `pi5_probe_main`.
- From `src/main.rs`: the `global_asm!` symbols of the feature profiles; the
  records `CASXI_KERNEL_ENTRY` and `CASXI_BUILD`; the calls of boot memory,
  the MMU and the allocators, which the call of the wiring replaces; the
  resource controller, the runtime and the user domains; the serial
  diagnostic dispatch of lines 217-368; the CPU-local record of the boot
  CPU, `cpu_local::initialize_boot`, which comes with the first code that
  needs CPU-local state; the setup of the interrupt controller and the
  timer, `irq::init`, which the default image does not call, as it takes no
  interrupt, and which the test images of the timer interrupt call; from
  `exception_dispatch`, the user dispatch and the IRQ branch, which come
  with the user domains and the first image that takes interrupts, and the
  recovery of MMU faults, as every exception of the default image halts and
  the test image of `kernel-memory` dispatches its own faults; and the
  multicore start of `smp_kernel`.
- From `src/fault.rs`: `exception`, the exception record, which the
  [fault](fault.md) record covers; `build_id`, `stack_bounds` and
  `append_trace`, the build-id and the frame trace, which come with fault
  symbolization; `emit` with `TX_ATTEMPTS_PER_BYTE`, the emission of a
  record, which is not carried over; and the parts of `panic` that the
  Changes name. `trace_probe`, a diagnostic probe, is not ported.
- From `src/mmu.rs`: the arming of the probes in the CPU-local fault plan
  with their expected syndromes, `expect_read_fault`, `expect_write_fault`
  and `unarmed_fault`, as the suite judges the syndromes of the exception
  records, and the probe pages; its other parts are in
  [boot_memory](boot_memory.md#not-carried-over), [mmu](mmu.md) and
  [page_tables](page_tables.md).
- From `src/boot_memory/banks.rs`: `inspect` and `verify`, which took the
  edge pages of each bank from the page allocator with low and high
  placement, checked the usable bytes against its free bytes, kept every
  edge until all patterns were read again, so that an alias across banks
  showed, and allocated each page again after its release, which come with
  the first code that allocates from the page ownership table; and the
  records `CASXI_RAM`, `CASXI_RAM_BANK` and `CASXI_RAM_TEST`.
- From `link.ld`: the sections `.text.user` and `.text.test_entry` and the
  user probe page with its assertions.
- From `.cargo/config.toml`: the alias, the vendored sources and the flags
  of the EL0 target `aarch64-unknown-none`.
- The legacy feature annotations `system.platform.qemu-boot` and
  `system.kernel.foundations`.
