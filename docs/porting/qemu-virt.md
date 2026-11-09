---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - src/board/qemu/mod.rs
  - src/entry.rs
  - src/main.rs
  - src/fault.rs
  - link.ld
  - .cargo/config.toml
destination:
  - kernel/boards/qemu-virt/Cargo.toml
  - kernel/boards/qemu-virt/build.rs
  - kernel/boards/qemu-virt/link.ld
  - kernel/boards/qemu-virt/src/lib.rs
  - kernel/boards/qemu-virt/src/main.rs
  - .cargo/config.toml
treatment: ported
features:
  - krepi.platform.qemu-virt-boot
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

## Changes

- `UART_BASE`, `0x0900_0000`, is a constant of the crate root, in place of
  the `UART` span of type `fdt::Span`.
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
  el=<level>` and `CASXI_READY`, the records of the
  [boot contract](../domains/boot-platform/boot/contract.md#records), and
  then echoes its serial input, in place of the legacy banner and runtime.
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
- The manifest and the build script are new. The build script passes
  `-T<crate>/link.ld` to the linker for the binaries and the examples of the
  crate when the target OS is `none`, and nothing on the host. The examples,
  the test images, also get `--entry=krepi_test_entry`: each test image
  names its own entry, a branch to `_start` or, for the image that enters at
  EL2, its EL2 entry, so that the default image and its link script keep
  `_start` as the entry. The legacy link script kept a section
  `.text.test_entry` for the entry of a fixture in the same image.

## Tests carried over

None: the legacy files held no host tests.

## Behaviour changes

| Change | Test |
| --- | --- |
| The boot writes `CASXI_CPU`, `CASXI_BOOT kernel=krepi board=qemu-virt el=1` and `CASXI_READY`, each with CR LF, in place of the legacy `CASXI_CPU`, `CASXI_KERNEL_ENTRY`, `CASXI_BUILD`, banner lines and `CASXI_READY` | The case `cold-boot-echo` of `cargo xtask qemu-boot` |
| After `CASXI_READY` the image echoes each received byte, with a line feed after a carriage return, and no byte triggers a command | The same case; `console::tests::examples::ex3_the_echo_adds_lf_after_cr_only` |
| The image neither discovers memory from the device tree nor turns the MMU or the caches on, so no `MMU=on` or cache mode is reported | The same case, whose transcript holds nothing else |
| A panic, such as a check that fails, writes its static message in `CASXI_PANIC`, its location and `CASXI_HALTED`, without `truncated=` and without a frame trace | `console::tests::panic_record::a_static_message_is_written_with_its_location`, `console::tests::panic_record::a_dynamic_message_is_replaced_by_the_fixed_text`, `console::tests::panic_record::a_panic_without_a_location_has_no_location_record` |
| An exception writes the exception record and `CASXI_HALTED` and halts, without the user, IRQ and MMU recovery steps of the legacy dispatch | `fault::tests::examples::ex5_a_fatal_exception_ends_in_the_halt_record`; the cases `el1-fp-trap` and `injected-serror` of `cargo xtask qemu-boot`, whose test images dispatch as the default image does |

## Hardware evidence to re-obtain

- The cold boot of the default image on QEMU virt `virt-8.2` with one
  Cortex-A76 into EL1, its records and its echo, three times with identical
  transcripts: the case `cold-boot-echo`, in CI.
- The exception record and halt of the dispatch: the cases `el1-fp-trap` and
  `injected-serror`, in CI.

## Not carried over

- From `src/board/qemu/mod.rs`: the `physical-kernel-test` branches, the
  physical profile with `physical_counter` and interrupt 30, and the
  `smp-el2-test` choice of `CPU_PROFILE`, all feature-profile branches; the
  declarations of `topology` and `memory` and the re-export of
  `discover_memory`, which come with secondary CPU startup and memory
  discovery; the re-exports of the MMU configuration of `cached` and
  `uncached`, which come with the MMU; `fdt::Span`, `fdt::CpuProfile`,
  `MINIMUM_RAM`, `DTB_ADDRESS` and `CPU_COMPATIBLE`, which come with the
  device tree; and `LABEL`, `GIC_DISTRIBUTOR`, `GIC_CPU`, `TIMER_INTID`,
  `CLOCK_NAME` and `TIMER_NAME`, which come with interrupt handling.
- From `src/entry.rs`: `Info` and `pi5_probe_main`.
- From `src/main.rs`: the `global_asm!` symbols of the feature profiles; the
  records `CASXI_KERNEL_ENTRY` and `CASXI_BUILD`; boot memory, the MMU, the
  resource controller, the runtime and the user domains; the serial
  diagnostic dispatch of lines 217-368; the CPU-local record of the boot
  CPU, `cpu_local::initialize_boot`, which comes with the first code that
  needs CPU-local state; the setup of the interrupt controller and the
  timer, `irq::init`, which comes with interrupt handling; from
  `exception_dispatch`, the user dispatch, the IRQ branch and the recovery
  of MMU faults, which come with the user domains, interrupt handling and
  the MMU; and the multicore start of `smp_kernel`.
- From `src/fault.rs`: `exception`, the exception record, which the
  [fault](fault.md) record covers; `build_id`, `stack_bounds` and
  `append_trace`, the build-id and the frame trace, which come with fault
  symbolization; `emit` with `TX_ATTEMPTS_PER_BYTE`, the emission of a
  record, which is not carried over; and the parts of `panic` that the
  Changes name. `trace_probe`, a diagnostic probe, is not ported.
- From `link.ld`: the sections `.text.user` and `.text.test_entry` and the
  user probe page with its assertions.
- From `.cargo/config.toml`: the alias, the vendored sources and the flags
  of the EL0 target `aarch64-unknown-none`.
- The legacy feature annotations `system.platform.qemu-boot` and
  `system.kernel.foundations`.
