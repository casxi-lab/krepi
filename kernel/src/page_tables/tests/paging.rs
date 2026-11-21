//! The vectors of `src/arch/aarch64/paging/tests.rs` of the contract: the
//! descriptors, the table sets and the copy of the kernel tables. Each set
//! is at `base` `0x100000000` with width 40 unless the test says otherwise.
//!
//! Feature: krepi.kernel.kernel-memory

use super::*;

/// `pt-02`.
#[test]
fn attributes_separate_text_data_and_mmio() {
    assert_eq!(descriptor(Kind::ReadExecute, 0), 0x40_0000_0000_0787);
    assert_eq!(descriptor(Kind::ReadWrite, 0), 0x60_0000_0000_0707);
    assert_eq!(descriptor(Kind::Device, 0), 0x60_0000_0000_0403);
}

/// `pt-21`.
#[test]
fn delegated_device_pages_are_rw_nx_non_global_with_device_attributes() {
    assert_eq!(descriptor(Kind::UserDevice, 0), 0x60_0000_0000_0c43);
}
