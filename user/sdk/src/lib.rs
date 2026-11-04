//! The native SDK for krepi programs.
//!
//! The SDK reaches the kernel only through the ABI crate, which it re-exports.

#![no_std]

pub use krepi_abi as abi;
