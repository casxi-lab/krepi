---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - tools/src/sha512.rs
destination:
  - tools/src/sha512.rs
treatment: ported
features: none
---

# Porting record: tools/src/sha512.rs

## Summary

SHA-512 (FIPS 180-4) with the same incremental shape as
`tools/src/sha256.rs`: `Sha512` with `new`, `update` and `finish`, the
lowercase hexadecimal digest of a byte slice (`hex`) and of a file read in
1 MiB blocks (`file_hex`). The module is self-contained and uses only the
standard library, so it is ported as it is. No other module of the tooling
crate calls it.

## Changes

- The module documentation describes the digest in general. The legacy text
  named the catalog entries whose published upstream digests its callers
  compared, which are not ported.
- The code is unchanged.
- `file_hex` had no test; `tests::a_file_digest_covers_every_block_read`
  checks a file of one million `a` against the FIPS 180-4 vector, a file of
  1,500,000 bytes that spans two reads against the digest of the same bytes,
  and the error of a missing file.

## Tests carried over

| Legacy test | krepi test | Expected values |
| --- | --- | --- |
| `tools/src/sha512.rs` `tests::known_vectors` | `tools/src/sha512.rs` `tests::known_vectors` | Unchanged: the FIPS 180-4 vectors for the empty message, `abc` and the 896-bit message |
| `tools/src/sha512.rs` `tests::incremental_updates_match_one_shot` | `tools/src/sha512.rs` `tests::incremental_updates_match_one_shot` | Unchanged, including the vector for one million `a` |

## Behaviour changes

None.

## Hardware evidence to re-obtain

None. The module runs on the host and had no QEMU or board results.

## Not carried over

- The sentence of the module documentation that named the legacy callers,
  verifiers of catalog records that are not ported.
