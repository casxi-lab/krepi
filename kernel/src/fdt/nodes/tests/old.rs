//! The lookup of a path before it returned at the last component: the code
//! of krepi commit 512ed1b at the lines below, copied verbatim with the
//! suffix `_old` added to the name of the function, for the differential
//! tests, which compare it with the code that replaced it. The functions
//! that it calls did not change; they are those of the module, and the copy
//! reaches them through `super::super`.
//!
//! - `kernel/src/fdt/nodes.rs:603-615`: `Fdt::find_node`.
//!
//! Feature: krepi.platform.device-tree

use super::super::*;

impl<'a> Fdt<'a> {
    /// The node of an absolute path with exact unit addresses, `/` for the
    /// root: a path that does not start with `/`, ends in `/` other than the
    /// root or holds `//`, `BadPath`; then each component in order, one that
    /// matches two sibling nodes, `AmbiguousMapping`; a path that matches
    /// nothing gives none. Aliases and abbreviated names are not resolved.
    pub fn find_node_old(self, path: &str) -> Result<Option<Node<'a>>, Error> {
        let path = path.as_bytes();
        if !path_valid(path) {
            return Err(Error::BadPath);
        }
        let found = find_path(self.structure, path)?;
        Ok(node_of(self, found))
    }
}
