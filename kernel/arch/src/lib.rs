//! The AArch64 processor layer of the krepi kernel, with the ARM interrupt
//! controller and timer that the boards share.
//!
//! The crate holds the cold entry of an image, `_start`, which the link
//! script of each image places at the start of its RAM, the exception
//! vectors of EL1 with the frame that they save, the functions that read
//! the processor registers of EL1 and halt the executing CPU, the cache and
//! TLB maintenance of the executing CPU by address with the cache-line
//! walks of a range, the GICv2 driver and the generic timer. The board
//! crates give the addresses of the controller, the interrupt IDs and the
//! timer that they use, and build their images on it.
//!
//! The assembly, the register accesses, the maintenance instructions and
//! the MMIO mean something only on the bare-metal AArch64 target, so their
//! modules are compiled only for `target_arch = "aarch64"` with
//! `target_os = "none"`. On the host, where the repository checks build,
//! lint and test the workspace, the crate holds the exception frame, the
//! classes of exceptions and the cache-line walks of a range, which its
//! tests run.

#![cfg_attr(not(test), no_std)]

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod boot;
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
pub mod cache;
pub mod cache_range;
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
pub mod cpu;
pub mod exception;
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
pub mod gic;
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
pub mod timer;
