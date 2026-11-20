//! The provable core of the krepi kernel.
//!
//! The core holds the logic of the kernel components that the proofs cover,
//! one module per component, in the provable Rust subset. The architecture
//! crate and the board crates call its `pub` entries, the rows of the entry
//! tables of the component contracts; everything else is `pub(crate)`. It
//! defines no callback for a hardware action: an entry that changes
//! hardware state returns a plan, which the architecture crate carries out.
//!
//! The core depends on no crate, forbids `unsafe` code and is `no_std`
//! without a condition, so the same code builds for the host, where its
//! tests run, and for the bare-metal target of the images.

#![no_std]

pub mod fdt;
