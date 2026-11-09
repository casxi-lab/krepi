//! The AArch64 processor primitives of the krepi kernel.
//!
//! The crate holds the cold entry of an image, `_start`, which the link
//! script of each image places at the start of its RAM, and the functions
//! that read the processor registers of EL1 and halt the executing CPU. The
//! board crates build their images on it.
//!
//! The assembly and the register accesses mean something only on the
//! bare-metal AArch64 target, so their modules are compiled only for
//! `target_arch = "aarch64"` with `target_os = "none"`. On the host, where
//! the repository checks build, lint and test the workspace, the crate is
//! empty.

#![cfg_attr(not(test), no_std)]

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod boot;
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
pub mod cpu;
