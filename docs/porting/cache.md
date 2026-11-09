---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - src/arch/aarch64/cache.rs
destination:
  - kernel/arch/src/cache.rs
treatment: ported
features:
  - krepi.platform.qemu-virt-boot
---

# Porting record: kernel/arch/src/cache.rs

## Summary

The cache maintenance of the executing CPU by address, taken from the
legacy cache module, with a new TLB invalidation of one page:
`clean_code_to_pou`, the clean of data cache lines to the point of
unification with `DC CVAU` and `DSB ISH`; `invalidate_to_poc`, the
invalidation of data cache lines to the point of coherency with
`DC IVAC`, followed by the invalidation of the instruction caches of the
CPU, which takes the line invalidation and the barriers of the legacy
`invalidate_handoff_image`; `invalidate_code_to_pou`, the invalidation of
instruction cache lines with `IC IVAU`, `DSB ISH` and `ISB`, which
completes the publication of code; and the private `ctr`, which reads
`CTR_EL0`. `invalidate_tlb_page`, the TLB invalidation of one page with
`DSB ISH`, `TLBI VAAE1IS`, `DSB ISH` and `ISB`, is new code, written from
the [SMP design rules](../conventions/smp.md#s6c-tlb-invalidation) and the
Arm Architecture Reference Manual: the legacy module had no TLB
maintenance. The range functions walk their lines with
[cache_range](cache_range.md). The module is compiled only for the
bare-metal target, as in the legacy tree. The legacy area `src/arch` is
ported, as
[porting](../conventions/porting.md#classification-of-the-legacy-areas)
classifies it.

## Changes

- `invalidate_handoff_image` becomes `invalidate_to_poc` and keeps only the
  line invalidation, `DC IVAC` on each line at `CTR_EL0.DminLine` between
  `DSB SY` and `DSB SY`, `IC IALLU`, `DSB SY` and `ISB`. It takes any range
  of at most 64 KiB, with unaligned ends, through `cache_range::data_lines`.
  It no longer requires the MMU and the caches off, every asynchronous
  exception masked, a page-aligned image, a line of at most 4 KiB or the
  window of the platform, and it no longer asserts them.
- `clean_code_to_pou`, `invalidate_code_to_pou` and `invalidate_tlb_page`
  are safe functions with documented `unsafe` blocks inside. A CPU may
  clean any data cache line, and drop any instruction cache line or TLB
  entry, at any time, so a clean, an instruction cache invalidation and a
  TLB invalidation only bring about a behaviour that the architecture
  already permits: the clean changes no value that a data access reads,
  and after an invalidation later fetches and translations read memory and
  the tables. The obligations of the code and of the tables lie with the
  code that wrote them, and a fault of an address is taken as a Data
  Abort, which the vectors report, so a caller cannot cause undefined
  behaviour with these functions. The legacy functions were `unsafe fn`
  whose callers vouched for the ownership of the lines, a parked set of
  other CPUs and masked IRQs. `invalidate_to_poc` stays an `unsafe fn`: an
  invalidation discards data that was written and not yet cleaned, so its
  caller owns every block of a cache writeback granule that the range
  touches and vouches that none holds data that must be kept.
- The limit of each walk is `cache_range::MAX_RANGE_BYTES`, 64 KiB, the
  literal 65536 of the legacy code publication; the panic messages
  `bounded code cache walk` and, for `invalidate_to_poc`,
  `bounded cache walk` come before any maintenance instruction.
  `invalidate_to_poc` panics with `bounded cache walk` in place of the
  legacy `bounded image cache walk`.
- The field of `CTR_EL0` that gives the line size of a walk, and its limit,
  are chosen by `cache_range::data_lines`, `DminLine`, and
  `cache_range::instruction_lines`, `IminLine`, which take the value of the
  register, in place of the field extraction and the literal limit inside
  each legacy function, so that host tests hold them.
- Each function documents the shareability domain of its instructions and
  barriers, that the final `ISB` synchronizes only the executing CPU, and
  that a CPU calls it for its own maintenance. The `SAFETY` comments are
  written again for each block; every `asm!` is `nostack` and
  `preserves_flags`, and the maintenance instructions are not `nomem`, so
  that the stores before a call stay before them.
- `invalidate_tlb_page` is new: `TLBI VAAE1IS` with bits 12 to 55 of the
  address, which invalidates the entries of the EL1&0 regime for any ASID
  on every CPU of the inner-shareable domain, between `DSB ISH` and
  `DSB ISH`, then `ISB`.
- The line `//! Feature: krepi.platform.qemu-virt-boot` takes the place of
  the legacy feature annotation.

## Tests carried over

None: the legacy module had no host tests, as its functions run only on the
bare-metal target. The lines that a walk covers, the field of `CTR_EL0`
that gives its line size and its limit are held by the tests of
[cache_range](cache_range.md).

## Behaviour changes

| Change | Evidence |
| --- | --- |
| The data cache invalidation takes any range of at most 64 KiB, with unaligned ends, without the checks of an image handoff | A case of the QEMU boot suite that runs it over a range with unaligned ends (planned) |
| A range that is empty, wraps or exceeds 64 KiB is refused before any maintenance in all three range functions, which panic; the legacy handoff invalidation was bounded by the platform window instead | The host tests of `cache_range::lines`, which each range function calls before any maintenance, `cache_range::tests::ex8_an_empty_or_oversized_range_is_refused` among them |

## Hardware evidence to re-obtain

- The four functions at EL1 on QEMU virt with one Cortex-A76, which cases
  of the QEMU boot suite are to obtain (planned). QEMU does not model the
  data and instruction caches, so such cases show the execution and the TLB
  invalidation, not the effect on a cache.
- The clean, the invalidations and the publication of code with the MMU and
  the caches on, and the invalidation of the image that the Pi 5 firmware
  hands over, on the Pi 5 with its board support and bench runs (planned).
  The prototype verified the publication of code in an image with the MMU
  and the caches on; krepi obtains that again with the code that turns them
  on.

## Not carried over

- `invalidate_at_reset`, the invalidation of the data and unified caches by
  set and way at a cold reset, which comes with the code that turns the MMU
  and the caches on (planned).
- `line_sizes`, which comes with the first code that needs both line sizes
  (planned).
- From `invalidate_handoff_image`: its assertions of the MMU and the caches
  off, of the masked exceptions, of a page-aligned image and of a line of
  at most 4 KiB, and its walk within the window of the platform with
  `handoff_lines`, which come with the invalidation of the image that
  firmware hands over (planned).
- The legacy feature annotation `system.platform.physical-entry`.
