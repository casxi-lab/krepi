//! The host tests of the page tables: the frozen vectors of the contract,
//! the rows of the kind table and the direct address.
//!
//! Feature: krepi.kernel.kernel-memory
//!
//! The expected values come from the contract and its frozen vectors, never
//! from an earlier run.

extern crate std;

use super::*;

mod kinds;
mod ownership;
mod paging;
