---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - tools/src/sha256.rs
destination:
  - tools/src/sha256.rs
treatment: ported
features: none
---

# Porting record: tools/src/sha256.rs

## Summary

SHA-256 (FIPS 180-4): an incremental hasher (`Sha256` with `new`, `update`
and `finish`), the lowercase hexadecimal digest of a byte slice (`hex`) and
of a file read in 64 KiB chunks (`file_hex`). The fixture patching of
`tools/src/elf.rs` digests images with it. The module is self-contained and
uses only the standard library, so it is ported as it is.

## Changes

- The module documentation states the hexadecimal form directly. The legacy
  text described it as matching the digest text of Python's `hashlib`.
- The code is unchanged.
- `file_hex` had no test; `tests::a_file_digest_covers_every_chunk` checks a
  file of one million `a` against the FIPS 180-4 vector across sixteen reads,
  the empty file, and the error of a missing file.

## Tests carried over

| Legacy test | krepi test | Expected values |
| --- | --- | --- |
| `tools/src/sha256.rs` `tests::known_vectors_match` | `tools/src/sha256.rs` `tests::known_vectors_match` | Unchanged: the FIPS 180-4 vectors for the empty message, `abc` and one million `a` |
| `tools/src/sha256.rs` `tests::incremental_updates_match_one_shot` | `tools/src/sha256.rs` `tests::incremental_updates_match_one_shot` | Unchanged |

## Behaviour changes

None.

## Hardware evidence to re-obtain

None. The module runs on the host and had no QEMU or board results.

## Not carried over

- The comparison with Python's `hashlib` in the module documentation. It
  described the output of the legacy Python runners, which are not ported,
  and no code depended on it.
