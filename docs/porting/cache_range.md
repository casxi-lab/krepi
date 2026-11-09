---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - src/arch/aarch64/cache_range.rs
destination:
  - kernel/arch/src/cache_range.rs
  - kernel/arch/src/cache_range/tests.rs
treatment: ported
features:
  - krepi.platform.qemu-virt-boot
---

# Porting record: kernel/arch/src/cache_range.rs

## Summary

The cache-line walks of a byte range, as plain code that the host tests
run: `lines`, which gives the address of every cache line that a byte of a
range lies in, at a line size in the encoding of `CTR_EL0`, and refuses an
empty range, a range longer than a limit, a range that wraps and a field
above 15; and `handoff_lines`, the walk of a whole, page-aligned image that
firmware hands over, within the reserved window of its platform. The
module is compiled on the host too, as in the legacy tree, where it was
also declared without a condition. The cache maintenance by address of
[cache](cache.md) walks its ranges with `data_lines` and
`instruction_lines`, new walks of `lines` at the line size that a value of
`CTR_EL0` gives. `handoff_lines` has no caller in the kernel yet: its
user is the invalidation of the image that firmware hands over, once the
MMU and the caches are turned on (planned). The legacy area `src/arch` is
ported, as
[porting](../conventions/porting.md#classification-of-the-legacy-areas)
classifies it.

## Changes

- `lines` and `handoff_lines` keep their signatures, their return type and
  their logic. Their documentation is written again: it states the walk,
  the encoding of the line size and each refusal.
- The new constant `MAX_RANGE_BYTES`, 64 KiB, is the limit of one call of
  the cache maintenance by address: the legacy functions of the code
  publication passed it as the literal 65536. It lives here, on the host,
  so that the host tests can use it.
- The new functions `data_lines` and `instruction_lines` give the walk of
  `lines` at the field `DminLine` or `IminLine` of a value of `CTR_EL0`,
  with the limit `MAX_RANGE_BYTES`: each legacy maintenance function
  extracted its field and passed its limit itself. They live here so that
  the host tests hold the field and the limit of each walk.
- The tests are in `cache_range/tests.rs`, in place of an inline test
  module, and two new tests are the examples ex7 and ex8 of the
  [QEMU virt boot](../features/platform/qemu-virt-boot.md) feature
  document. Three new tests hold `data_lines` and `instruction_lines` at a
  value of `CTR_EL0` whose line fields differ, and a fourth at a value with
  bit 3 set in both line fields.
- The line `//! Feature: krepi.platform.qemu-virt-boot` names the feature in
  both files.

## Tests carried over

| Legacy test | krepi test |
| --- | --- |
| `src/arch/aarch64/cache_range.rs`: `firmware_image_walk_uses_the_complete_platform_window`, `partial_lines_and_exact_boundaries`, `rejects_unbounded_or_wrapping_requests` | The same names in `kernel/arch/src/cache_range/tests.rs` |

No expected value changed.

## Behaviour changes

None: the walks are those of the legacy functions, and `data_lines` and
`instruction_lines` walk at the fields and the limit of the legacy cache
functions.

## Hardware evidence to re-obtain

None of its own: the walks are arithmetic, which the host tests show. The
record of [cache](cache.md) names the evidence of the maintenance that
uses them.

## Not carried over

- The module documentation line of the legacy file, which the module
  documentation replaces.
