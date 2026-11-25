//! The tests of the CPU nodes that need the private functions of the
//! module: the copy of the code before the CPU profile of a board became a
//! value, which the differential tests compare with the code.
//!
//! Feature: krepi.platform.device-tree

// The copy keeps the lines of its source; the suffix of its names makes
// some of them longer than the formatter allows.
#[rustfmt::skip]
pub(in crate::fdt) mod before;
