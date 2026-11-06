---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - tools/src/elf.rs
  - tools/tests/kernel/foundations.rs
destination:
  - tools/src/elf.rs
treatment: ported
features: none
---

# Porting record: tools/src/elf.rs

## Summary

A bounded reader of little-endian AArch64 ELF64 executables for offline
diagnostics on the host: `parse_elf` and `read_elf` check the headers, the
program and section headers, the section names, the 36-byte GNU SHA-1
build-id note mapped in a read-only load segment, and the one unstripped
symbol table, and return an `ElfSnapshot` with the image bytes, the build-id,
the function symbols and the file-backed ranges of the executable segments;
`symbol_at` finds the function that contains an address, with zero-size
assembly functions ending at the next function or at their section end;
`symbol_address` and `patch_symbol` locate one symbol and patch one checked
word of a fixture image into a new file. It is not a loader and never runs
what it reads. The module is ported with its bounds, checks and messages;
four sums over header fields that could exceed 64 bits are now checked or
reordered, so that such fields fail the check they belong to instead of
overflowing. The tests come from the legacy integration tests of the kernel
foundations, which exercised this reader on a synthetic image.

## Changes

- The module documentation describes the reader and the fixture patching.
  The legacy text described the reader as a copy of the ELF parser of a
  Python symbolization script, and the documentation of `patch_symbol` named
  the Python test it was taken from.
- `entry_fixture` is removed; see [Not carried over](#not-carried-over).
- Header fields that no bound limits no longer overflow the arithmetic that
  places them. In `parse_elf`, the end of the build-id note and the file
  offset that its address gives in a read-only segment, the segment's file
  offset plus the distance of the note into the segment, are checked
  additions. In `patch_symbol`, the file offset of the target in its section,
  the section's file offset plus the distance into the section, is a checked
  addition, and its file offset in a load segment adds the distance into the
  segment to the segment's file offset, a sum that the region check keeps
  below the file length. A sum that exceeds 64 bits agrees with no mapping,
  so the existing check fails with its message; see
  [Behaviour changes](#behaviour-changes).
- The synthetic image of the legacy foundations tests, an executable segment
  with `.text`, a read-only segment with the build-id note and four symbols,
  is built in the unit tests of the module, which read it from memory and
  from files in a scratch directory.
- `symbol_address` and `patch_symbol` had no direct test. The unit tests
  locate symbols, patch one word and compare the returned report and the
  written file with the expected bytes and SHA-256 digests, and check each
  refusal: an existing destination, a prefix or duplicated name, a symbol
  outside its section, an unaligned target, unexpected contents, a load
  segment without the requested rights or with a physical address other than
  its virtual one, a section file offset whose sum exceeds 64 bits, and a
  file outside the fixture size bound. A fixture whose text lies on the top
  page of the address space is patched at its file offset.
- A new check covers the 64 MiB bound of `parse_elf` and of `read_elf` on a
  sparse file beyond the bound, and the malformed images include note
  addresses whose placement sums exceed 64 bits, beside a note that is
  accepted at the start of a segment ending at the top of the address space.

## Tests carried over

| Legacy test | krepi test | Expected values |
| --- | --- | --- |
| `tools/tests/kernel/foundations.rs` `examples::ex5_symbolization_resolves_functions_and_adjusts_saved_return_addresses` | `tools/src/elf.rs` `tests::a_synthetic_image_yields_its_build_id_segments_and_function_symbols` and `tests::an_address_resolves_to_the_function_that_contains_it` | Unchanged for the build-id, the three function symbols and the `symbol_at` lookups at offsets `0x44`, `0x80` and `0xa0`. The assertions on the symbolization result are replaced by the reader values they rest on: `symbol_at` at offsets `0`, `0x90` and `0xf0` gives `kernel_main`, `after_asm` and none, at offset `0x40`, the lookup address of the case adjusted for a saved return address, it gives `asm_entry`, and the snapshot's only executable range is `.text`, outside which address `0` lies |
| `tools/tests/kernel/foundations.rs` `examples::ex6_a_mismatched_identity_or_malformed_image_is_rejected` | `tools/src/elf.rs` `tests::a_malformed_image_is_rejected_with_its_reason` | Unchanged for the thirteen mutated images. The three truncated images, which the legacy test only required to be rejected, are checked for their messages. Two images with note addresses whose placement sums exceed 64 bits, and an accepted note at the top of the address space, are added |
| `tools/tests/kernel/foundations.rs` `properties::real_image_resolves_kernel_main_to_its_source` | `tools/src/elf.rs` `tests::a_file_is_read_and_parsed_like_its_bytes` | Only the reading of an image file with `read_elf` is carried over, with a changed input: `read_elf` reads the synthetic image from a file and must give the snapshot that `parse_elf` gives for its bytes, in which `kernel_main` is found and resolves to itself. The check of a linker-built image is not carried over; see [Not carried over](#not-carried-over) |

The tests `examples::ex1_...` to `examples::ex4_...` of the same file test
the serial record parsers of the legacy `tools/src/receipt.rs`. They are
carried over with that module and recorded in its record, not here.

## Behaviour changes

Every bound and message of the reader and of the fixture patching is
unchanged. Header fields whose placement sums exceed 64 bits now fail a check
or are placed correctly; the legacy arithmetic overflowed on them, which
panics in a build with overflow checks, such as a test build.

| Behaviour | Legacy | krepi | Test |
| --- | --- | --- | --- |
| A build-id note address within 36 bytes of the top of the address space, or one whose distance into a read-only segment overflows when added to the segment's file offset | Overflow in the mapping check | Rejected: `build-id note is not mapped read-only` | `tests::a_malformed_image_is_rejected_with_its_reason` |
| A target section file offset whose sum with the distance of the symbol into the section exceeds 64 bits | Overflow before the comparison with the load mapping | Refused: `Target section and unique load mapping disagree` | `tests::a_patch_is_refused_unless_every_check_holds` |
| A patch target on the top page of the address space | Overflow when the address was added to the section or segment file offset | Patched at its file offset | `tests::a_word_on_the_top_page_of_the_address_space_is_patched` |

## Hardware evidence to re-obtain

None. The module runs on the host and had no QEMU or board results.

## Not carried over

- `entry_fixture`, which rewrote the entry of the prototype kernel image,
  required to be `0x4020_0000`, to its boot-test wrapper symbol
  `__boot_test_start` below `__rodata_start`. It encodes the layout of that
  image and served only prototype boot suites.
- The symbolization parts of `examples::ex5_...`, `examples::ex6_...` and
  `properties::real_image_resolves_kernel_main_to_its_source` in
  `tools/tests/kernel/foundations.rs`: the address resolution, the
  return-address adjustment, the build-id comparison with a record, the image
  digest of the result and the source location through LLVM objdump. They
  test the legacy symbolization module, which is not part of this crate.
- The check of a linker-built image in
  `properties::real_image_resolves_kernel_main_to_its_source`: the legacy
  test read the built prototype kernel image, when it existed, and found
  `kernel_main` among the sections, build-id note and symbols that the linker
  produced. No kernel image of this repository exists yet to read.
- `boundaries::address_and_request_limits_are_enforced` in the same file,
  which tests only the symbolization module.
- The test helpers of that file for the symbolization tests (`TempElf`,
  `root`, `resolve`, `item`) and its use of the repository root to find the
  built prototype image.
