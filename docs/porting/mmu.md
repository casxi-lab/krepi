---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - src/mmu.rs
  - src/mmu/address_space.rs
  - src/board/cached.rs
  - src/arch/aarch64/address.rs
destination:
  - kernel/arch/src/mmu.rs
  - kernel/arch/src/mmu/tests.rs
treatment: ported
features:
  - krepi.kernel.kernel-memory
---

# Porting record: kernel/arch/src/mmu.rs

## Summary

The adapter of the page tables in the architecture crate `krepi-arch`, the
module `mmu`: it carries out the write plans that the module `page_tables`
of the provable core returns, turns the MMU on with the kernel tables and
zeroes frames through the direct map, as the
[page-tables contract](../domains/memory/page-tables/contract.md) fixes.
It takes from `enable_mmu` of `src/board/cached.rs` the writes of
`MAIR_EL1`, `TCR_EL1`, `TTBR0_EL1`, `TTBR1_EL1` and `SCTLR_EL1`, which are
`enable`; from `src/arch/aarch64/address.rs` `translation_control`, the
value of `TCR_EL1`; from `init_and_verify` of `src/mmu.rs` the read of
`ID_AA64MMFR0_EL1` with the checks of the 4 KiB granule and of the physical
address range, which are `physical_width`; and from
`src/mmu/address_space.rs` `pa_bits`, the physical address size that the
kernel takes from the CPU, which `physical_width` returns, and
`kernel_base`, the address of the pool of the lower kernel tables, which a
`Pool` names. `apply`, which executes a whole plan through the trait
`Plan`, the cursor `WriteSteps` over the plan of a write entry and
`zero_frames` are new code, written from the contract: the prototype's
tables stored their descriptors inside `map_page`, which the core replaced
by plans ([page_tables](page_tables.md#changes)), and the prototype zeroed
pages in a callback of its allocators. The legacy areas `src/arch`,
`src/board` and `src/mmu` are ported, as
[porting](../conventions/porting.md#classification-of-the-legacy-areas)
classifies them. The boot wiring of QEMU virt, which calls the adapter, has
the record [boot_memory](boot_memory.md); the other parts of `src/mmu.rs`
are in that record, in [page_tables](page_tables.md) and in
[qemu-virt](qemu-virt.md).

## Changes

- **Plans.** `apply(pool, plan)` takes a whole plan, any value of the
  trait `Plan<N>`, which the plan iterators of the core implement with
  their `next` and `WriteSteps` with the steps of a `WritePlan`, `Zero(0)`
  to `Zero(zero_tables - 1)` and then at most seven steps. It executes
  each step before it asks for the next: `Zero` and `Store` by `zero_table`
  and `store_descriptor`, with volatile stores of 8 bytes into the pool,
  `Fence` by `DMB ISHST`, `Sync` by `DSB ISH` and `ISB`, and `Invalidate`
  by `krepi_arch::cache::invalidate_tlb_page`. A step whose table or entry
  lies outside the pool panics with `a step outside its pool` before it
  writes; no plan of a set of that pool names one. The prototype wrote the
  descriptors inside its table code and invalidated with `TLBI VMALLE1IS`
  after its diagnostic remaps.
- **The pool.** `Pool::new(base)`, an `unsafe` `const fn`, names the pool
  of one table set at the address at which the executing CPU reaches it, in
  place of `kernel_base`, which read the address of the prototype's static
  tables. The caller vouches for the pool, for the exposed provenance of its
  storage, which the stores take, and for the plans of the set as its only
  writer; a `Pool` is neither `Clone` nor `Copy`, and `apply` takes it
  mutably. The `SAFETY` comments of the stores state why no Rust reference
  reads an entry after a step writes it: a plan reads an entry only before
  its own steps write it. That argument is not shown under either aliasing
  model of Rust, Stacked Borrows or Tree Borrows: a plan that `apply` takes
  by value holds a shared reference to its set, which the entry of `apply`
  protects for the whole call, and the helpers of the plans of the core
  reborrow the whole set after stores into it. Miri reports undefined
  behaviour for a host copy of the boot wiring under both models, whether
  the plan is passed by value or by reference. The open obligations of the
  module leave the question to the proof of its unsafe sites; a later design
  of the core, in which a plan holds no reference while it executes, removes
  it.
- **Turning the MMU on.** `enable(lower, direct, bits, caches)` takes the
  roots of the two kernel sets, the physical address size in bits and the
  choice of the caches, in place of the root of the lower tables, the root
  of the upper tables and the encoding of the size. It first invalidates
  the TLB entries of the executing CPU with `TLBI VMALLE1`, `DSB NSH` and
  `ISB`, then writes `MAIR_EL1`, `TCR_EL1` and the TTBRs and executes `ISB`,
  and then sets `SCTLR_EL1.M` and `WXN`, followed by `ISB`; the prototype
  wrote the registers after a `DSB SY` and invalidated with
  `TLBI VMALLE1IS` and `DSB SY` between the TTBRs and `SCTLR_EL1`. The
  `Sync` that ends each plan of the two sets completes the stores before
  the call.
- **The caches.** Normal memory is inner and outer Non-cacheable, `0x44`
  at index 1 of `MAIR_EL1`, and the walks of `TCR_EL1` are Non-cacheable
  when `caches` is false, which the boot wiring of QEMU virt passes; with
  `caches` they are Write-Back, `0xff`, as the prototype's only value
  `NORMAL_ATTRIBUTE` was, and `SCTLR_EL1.C` and `I` are set. The prototype
  always set `C` and `I`, its `MMU_ENABLE_BITS` `0x1005`, and invalidated
  the caches before it, by set and way or over the image that the firmware
  hands over; `enable` does no cache maintenance, which its caller does
  before it passes `caches`.
- **Arguments.** `enable` and `zero_frames` check nothing and do not fail,
  as the contract has their callers vouch for their arguments: a `bits`
  other than 32, 36, 40, 42, 44 and 48 has no encoding in `TCR_EL1.IPS`, so
  `enable` writes no register and the MMU stays off, where the prototype's
  `expect("PA width")` panicked; a range that leaves the window of the
  direct map has no address there, so `zero_frames` writes nothing.
- **`TCR_EL1`.** The private `translation_control(bits, caches)` takes the
  size in bits and gives the encoding of `IPS` for it, in place of the
  encoding 0 to 5, and none for another size; the fields are those of the
  prototype: `T0SZ` and `T1SZ` 25, 4 KiB granules, inner-shareable walks of
  the cacheability of Normal memory, the 8-bit ASID of `TTBR0_EL1`, and no
  top-byte ignore or hardware update of the access and dirty flags. It is
  no longer `pub` and `const`, and `memory_attributes` and
  `system_control_bits` give the other two values; the three are compiled
  for the host tests and the bare-metal target only, as nothing else calls
  them.
- **The physical address size.** `physical_width()` reads
  `ID_AA64MMFR0_EL1` and returns the size for a `PARange` of 0 to 5, or
  none for another `PARange` or for a `TGran4` other than `0b0000` and
  `0b0001`: it admits the 4 KiB granule with the 52-bit form as well, where
  the prototype asserted `TGran4` 0, and it returns none where the
  prototype asserted. The caller keeps the size; the prototype stored it in
  the atomic `PA_BITS`, which `pa_bits` read and asserted set.
- **Zeroing frames.** `zero_frames(range)` writes 0 into each byte of a
  physical range through `page_tables::direct_address`, with volatile
  bytes up to the first multiple of 8, words, then bytes, for the holder of
  the pages or, at boot, for pages that nothing else uses; it takes a
  `PhysRange` through `start` and `size`.
- **Layout of the module.** The trait, `WriteSteps` and their
  implementations for the plan iterators of the core are plain code,
  compiled on every target, so that the board's host tests drive plans
  through them; `Pool`, `apply`, `enable`, `zero_frames` and
  `physical_width` are compiled only for the bare-metal target. The module
  documentation names `//! Feature: krepi.kernel.kernel-memory`, in place
  of the legacy feature annotations.

## Tests carried over

| Legacy test | krepi test |
| --- | --- |
| `src/arch/aarch64/address.rs`, `both_walk_regions_have_matching_policies_and_ttbr0_asids` | Its cases in `mmu::tests::translation_control_sets_the_fields_of_the_contract` and `mmu::tests::translation_control_refuses_other_widths`, with the size in bits in place of its encoding and each field read at its position; they also hold `HA` and `HD`, which the legacy test left out, and that no other bit is set; the vector `as-33` of the [address-space contract](../domains/memory/address-space/contract.md#legacy-test-vectors) is this test, whose host test comes with this code |

The other tests of the module are new: the two values of `TCR_EL1` for 40
bits written out, `MAIR_EL1`, the bits of `SCTLR_EL1`, the physical
address size of each `PARange` and `TGran4`, and the steps of `WriteSteps`
for a plan with zeroed tables, a reset and a plan whose `len` exceeds its
steps.

## Behaviour changes

| Change | Evidence |
| --- | --- |
| With the caches off, Normal memory is Non-cacheable and `SCTLR_EL1.C` and `I` stay clear | `mmu::tests::memory_attributes_put_device_at_index_0_and_normal_at_index_1`, `mmu::tests::system_control_sets_the_caches_only_when_asked`, `mmu::tests::translation_control_of_qemu_virt_is_written_out`; the cases `kernel-memory` and `boot-memory` of `cargo xtask qemu-boot` and the case `cold-boot-echo`, whose images turn the MMU on with the caches off |
| The physical address size admits `TGran4` `0b0001` and is none, not a panic, for another granule or `PARange` | `mmu::tests::physical_width_follows_the_physical_address_range` |
| `TCR_EL1` is computed from the size in bits, none for a size without an encoding | `mmu::tests::translation_control_sets_the_fields_of_the_contract`, `mmu::tests::translation_control_refuses_other_widths` |
| The descriptors are stored by the steps of a plan, the zeroed tables first, and a step outside the pool panics before it writes | `mmu::tests::write_steps_give_the_zeroed_tables_first`, `mmu::tests::write_steps_of_a_reset_and_of_an_overlong_plan`; the case `kernel-memory`, whose image runs with the tables that the plans built; no test takes the panic |

## Hardware evidence to re-obtain

- On QEMU virt, `virt-8.2` with one Cortex-A76 and 128 MiB: the plans of
  the two kernel sets executed, the MMU on with the caches off and the
  frames zeroed through the direct map, with the faults and the `Device`
  console of the contract: the case `kernel-memory` of
  `cargo xtask qemu-boot`, in CI, and the same tables at three cold boots,
  the case `boot-memory`.
- With the caches on, on a Raspberry Pi 5 of 8 GB with its board support
  and bench runs (planned): the values of `MAIR_EL1`, `TCR_EL1` and
  `SCTLR_EL1` for Write-Back memory after the cache maintenance of the
  board.

## Not carried over

- From `src/board/cached.rs`: the calls of `invalidate_at_reset` and of
  `invalidate_handoff_image` before the MMU is on, with the window of the
  image, which come with the code that turns the caches on (planned); the
  constants `NORMAL_ATTRIBUTE`, `CACHE_MODE` and `MMU_ENABLE_BITS`, which
  `memory_attributes` and `system_control_bits` replace; the branches of
  the feature profiles; and the legacy feature annotation
  `system.platform.physical-entry`.
- From `src/mmu/address_space.rs`: `activate`, `restore_kernel`,
  `invalidate_asid`, `invalidate_page`, `clone_kernel_into`,
  `require_kernel_root` and `require_masked_irq`, the switch of the root of
  an address space and the TLB lifecycle of its ASIDs, which come with the
  address spaces of processes; `verify_retired`, a probe of a feature
  profile; `verify_guard`, a probe of the guard page, which the test image
  of `kernel-memory` rewrites ([qemu-virt](qemu-virt.md)); and the atomic
  `PA_BITS` that `pa_bits` read.
- From `src/mmu.rs`: the read of `DAIF` with the assertion of masked
  interrupts, which the `# Safety` of `enable` requires of its caller;
  `invalidate`, the broadcast invalidation of the diagnostic remaps; and
  `translation` and `user_read_translation`, the address translations of
  the checks after the MMU was on, which the boot wiring does not repeat.
- From `src/arch/aarch64/address.rs`: the `const` and `pub` form of
  `translation_control`; its other items are in
  [page_tables](page_tables.md#not-carried-over).
- The legacy feature annotation `system.kernel.memory`.
