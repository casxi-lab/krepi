---
source: prototype@ec8305c618a8f4e84e0707fa56beac5673f4675e
paths: none
destination:
  - kernel/Cargo.toml
  - kernel/Cargo.lock
  - kernel/src/lib.rs
treatment: redesigned
features: none
---

# Porting record: kernel/src/lib.rs

## Summary

The crate root of the provable core `krepi-kernel`, the root package of the
kernel workspace: the `[package]` and `[lints.rust]` tables of the root
manifest `kernel/Cargo.toml`, the entry of the package in
`kernel/Cargo.lock` and the library root `kernel/src/lib.rs`. The prototype
tree has no counterpart to take: its kernel was a single crate, whose
boards, products and diagnostics were chosen at compile time, while the
core is a library of its own that holds only the modules of the components
that the proofs cover, in the shape that the
[source layout](../architecture.md#kernel-workspace-crates) fixes. No
prototype path is taken, so the record lists none, and the treatment is
redesigned. Each module of the core that takes prototype code has a record
of its own.

## Changes

- The root manifest of the kernel workspace gains the root package
  `krepi-kernel`, version `0.0.0`, with the edition, license, publication
  setting and Rust version of the workspace. It has no dependency table,
  no features, no build script and no binary, example or benchmark target,
  forbids `unsafe` code and warns about missing documentation. The members
  of the workspace are unchanged.
- The library `krepi_kernel` is `no_std` without a condition, so the same
  code builds for the host, where its tests run, and for the bare-metal
  target, and it holds no `cfg` other than `#[cfg(test)]` on a module.
- The library root declares only the modules of the core that are present.

## Tests carried over

None: the crate root holds no tests.

## Behaviour changes

None: a crate root and a manifest have no behaviour of their own.

## Hardware evidence to re-obtain

None of its own; the records of the declared modules name theirs.

## Not carried over

Nothing: the record takes no prototype path.
