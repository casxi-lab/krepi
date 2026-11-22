//! What the test images of kernel memory share: the slice of the device
//! tree that QEMU's loader places at the start of RAM, and the boot wiring
//! of the board on it, which turns the MMU on with the kernel tables.
//!
//! Feature: krepi.platform.device-tree
//! Feature: krepi.kernel.kernel-memory
//!
//! Only those test images declare this module, so every function of it has
//! a caller in each image that compiles it; the other test images share
//! only the module `common`.

use core::slice;

use krepi_kernel::fdt::MAX_BLOB_SIZE;
use krepi_qemu_virt::boot_memory::{self, TREE_BASE, Wired};

/// The size of the header of a device tree, which holds its `totalsize` at
/// offset 4.
const HEADER_SIZE: usize = 40;

/// The device tree that QEMU's loader placed at the start of RAM, as the
/// default image slices it: its 40-byte header, then its `totalsize` bytes
/// once that is at least 40 and at most `MAX_BLOB_SIZE`, 2 MiB, so that the
/// tree ends at or below the start of the image.
///
/// # Panics
///
/// Panics with `device tree size out of bounds` on another `totalsize`.
fn device_tree() -> &'static [u8] {
    // SAFETY: the 40 bytes at `TREE_BASE` are RAM below the image, where
    // QEMU's loader places the tree, which the CPU reads with the MMU off
    // and which nothing writes while the image runs; a byte slice needs no
    // alignment.
    let header = unsafe { slice::from_raw_parts(TREE_BASE as *const u8, HEADER_SIZE) };
    let size = u64::from(u32::from_be_bytes([
        header[4], header[5], header[6], header[7],
    ]));
    assert!(
        (HEADER_SIZE as u64..=MAX_BLOB_SIZE).contains(&size),
        "device tree size out of bounds"
    );
    // SAFETY: the `size` bytes from `TREE_BASE` are RAM below the start of
    // the image, which the bound above keeps them in, and hold the tree,
    // which nothing writes while the image runs.
    unsafe { slice::from_raw_parts(TREE_BASE as *const u8, size as usize) }
}

/// Runs the boot wiring of the board on the device tree: the boot memory
/// map, the page ownership table and the kernel tables, and the MMU turned
/// on with the caches off. The image calls it once, right after its start
/// record.
pub fn wire() -> Wired {
    let tree = device_tree();
    // SAFETY: the image calls this function once, on CPU 0 at EL1 with every
    // exception masked and the MMU off, as the cold entry left them and as
    // `wire` checks, and `tree` is the tree at the start of RAM, which
    // nothing writes.
    unsafe { boot_memory::wire(tree) }
}
