//! The calibration target of the krepi proof gate: the code shapes of the
//! first kernel targets in a crate that no part of krepi uses. A table of
//! slots whose capacity is fixed when it is made, with a generation per
//! slot; a handle that encodes a slot and its generation in bit fields;
//! checked arithmetic on budgets and ranges; writes after a check; and a
//! bounded loop. `cargo xtask formal run --calibration` extracts it for the
//! extraction triple of the kernel and checks the proofs about it, and the
//! registered mutants show that each proof depends on the code it is about.
#![no_std]

pub mod arith;
pub mod handle;
pub mod table;
