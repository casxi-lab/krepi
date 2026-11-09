---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - src/arch/mod.rs
  - src/arch/aarch64/mod.rs
destination:
  - kernel/arch/src/lib.rs
  - kernel/arch/Cargo.toml
treatment: ported
features:
  - krepi.platform.qemu-virt-boot
---

# Porting record: kernel/arch/src/lib.rs

## Summary

The crate root of the architecture crate `krepi-arch`, which takes the place
of the two module files of the legacy architecture area: `src/arch/mod.rs`,
which declared `aarch64`, and `src/arch/aarch64/mod.rs`, which declared the
AArch64 modules and compiled those that touch the CPU only for the
bare-metal target. krepi has one architecture, so the crate is the AArch64
module itself: its root declares `boot`, `cache`, `cpu`, `gic` and
`timer`, each compiled only for `target_arch = "aarch64"` with
`target_os = "none"`, as the legacy root compiled `cache` and `cpu`, and
`exception` and `cache_range`, compiled on the host too, as the legacy root
compiled them. The records of the two cache modules are
[cache](cache.md) and [cache_range](cache_range.md). The manifest makes the
crate a member of the kernel workspace. The legacy area `src/arch` is
ported, as
[porting](../conventions/porting.md#classification-of-the-legacy-areas)
classifies it.

## Changes

- The two legacy module levels, `arch` and `arch::aarch64`, become the crate
  root of `krepi-arch`, a library of the kernel workspace without
  dependencies, with `missing_docs` warned and undocumented `unsafe` blocks
  denied.
- The crate is `no_std` outside its tests. On the host, where the
  repository checks build it, it holds the exception frame, the classes of
  exceptions and the cache-line walks, whose tests run there.
- The cold entry `boot`, which the legacy kernel included from `src/boot.S`
  at the root of the prototype's kernel, is a module of this crate; its
  record is [boot](boot.md).
- The root declares only the modules that are present.
- The crate is the processor layer together with the ARM interrupt
  controller and timer that the boards share: `gic`, the GICv2 driver, and
  `timer`, the generic timer, which take the driver part of the QEMU virt
  interrupt code of `src/board/qemu/irq.rs` and have the records
  [gic](gic.md) and [timer](timer.md). The description of the manifest and
  the crate documentation say so, in place of processor primitives alone,
  and name the cache and TLB maintenance of the executing CPU.

## Tests carried over

None: the two module files held no tests.

## Behaviour changes

None: module declarations have no behaviour of their own.

## Hardware evidence to re-obtain

None of its own; the records of the declared modules name theirs.

## Not carried over

- The declarations of `address`, `asid`, `context`, `gic_sgi`, `paging`,
  `gic`, `physical_timer`, `transaction` and `local`: their modules are not
  part of this crate. The legacy `gic` is the GIC-400 module of the Pi 5
  path, not the GICv2 driver that this crate's `gic` holds. The re-export
  of `ExceptionFrame` is left out: the
  module `exception` is public, and its frame is `Frame`. Page tables,
  user contexts, user addresses and ASIDs, the GIC-400 and the physical timer
  of the Pi 5 path, SGIs and the CPU-local and transaction adapters are
  ported or redesigned with the code that needs them.
- The module documentation, which described the legacy modules; the crate
  documentation describes this crate.
