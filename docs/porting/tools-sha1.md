---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths:
  - tools/src/sha1.rs
destination:
  - tools/src/sha1.rs
treatment: ported
features: none
---

# Porting record: tools/src/sha1.rs

## Summary

SHA-1 (FIPS 180-4) over a byte slice, written as lowercase hexadecimal, for
Git object identities: the digest of an object header followed by the object
bytes. The module is self-contained, uses only the standard library and
carries its known-answer tests, so it is ported as it is. No other module of
the tooling crate calls it.

## Changes

- The module documentation describes Git object identities in general. The
  legacy text named the record verifier that called the function, which is
  not ported.
- The code is unchanged.

## Tests carried over

| Legacy test | krepi test | Expected values |
| --- | --- | --- |
| `tools/src/sha1.rs` `tests::known_vectors` | `tools/src/sha1.rs` `tests::known_vectors` | Unchanged: the FIPS 180-4 vectors for the empty message, `abc`, the 448-bit message and one million `a` |
| `tools/src/sha1.rs` `tests::git_blob_identity` | `tools/src/sha1.rs` `tests::git_blob_identity` | Unchanged: the object identity of the empty Git blob |

## Behaviour changes

None.

## Hardware evidence to re-obtain

None. The module runs on the host and had no QEMU or board results.

## Not carried over

- The sentence of the module documentation that named the legacy caller, an
  audit of a pinned upstream commit that is not ported.
