---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - src/boot.S
  - src/entry.rs
destination:
  - kernel/arch/src/boot.rs
  - kernel/arch/src/boot.S
treatment: ported
features:
  - krepi.platform.qemu-virt-boot
---

# Porting record: kernel/arch/src/boot.rs

## Summary

The cold entry `_start` of the QEMU virt image: the assembly of
`src/boot.S`, which the legacy kernel included with `global_asm!` in
`src/entry.rs`, and that include. `_start` masks every exception, parks
every CPU but CPU 0 and a CPU that is not at EL1, makes FP/SIMD
instructions trap, clears `TPIDR_EL1`, selects `SP_EL1`, sets the stack
pointer, clears BSS and the whole stack, and calls `kernel_main`. The module
`boot` of `krepi-arch` holds the include, and its documentation states the
entry contract; the [boot contract](../domains/boot-platform/boot/contract.md#cold-entry)
states the rules. The file `src/boot.S` lies at the root of the legacy
`src/` tree, outside the areas that
[porting](../conventions/porting.md#classification-of-the-legacy-areas)
lists: it is the QEMU entry of the legacy architecture code, and it is
ported with it.

## Changes

- The install of the exception vectors, `__exception_vectors` written to
  `VBAR_EL1` with an `ISB` after BSS was cleared, is left out: this image
  installs no vector table, and the symbol does not exist.
- The comments are written again: the entry contract names the symbols that
  the link script and the image provide, and the line
  `//! Feature: krepi.platform.qemu-virt-boot`, an assembly comment, names
  the feature. The instructions are unchanged.
- The include is the only item of the module `boot`, compiled only for the
  bare-metal target, in place of the include in `src/entry.rs` under the
  absence of the Pi 5 and physical-entry features.

## Tests carried over

None: the legacy tree had no host test of the entry.

## Behaviour changes

- `VBAR_EL1` keeps its reset value: an exception after the cold entry is not
  handled. The QEMU boot suite, case `cold-boot-echo`, shows that the image
  reaches its records and echo without an exception.

## Hardware evidence to re-obtain

- The boot of the default image on QEMU virt `virt-8.2` with one Cortex-A76
  into EL1, which the case `cold-boot-echo` of `cargo xtask qemu-boot`
  obtains in CI.
- The prototype parked the CPUs of a multi-CPU QEMU virt machine in the
  entry; a run with more than one CPU is obtained again with secondary CPU
  startup.

## Not carried over

- From `src/entry.rs`: the include of the vector assembly
  `src/arch/aarch64/kernel_vectors.S`, which comes with the exception
  vectors; the Pi 5 entry `src/board/pi5/boot.S` with
  `src/arch/aarch64/boot_el1.S` under the `pi5-kernel` and
  `physical-kernel-test` features and the fixture entry
  `src/board/boot_test/entry.S`, all feature-profile branches or Pi 5 code;
  `Info` and `pi5_probe_main`, the entry record of the Pi 5 path; and
  `kernel_main`, which the record [qemu-virt](qemu-virt.md) covers.
- The legacy feature annotation `system.platform.qemu-boot` of
  `src/entry.rs`.
