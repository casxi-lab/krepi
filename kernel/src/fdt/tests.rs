//! The host tests of the device tree: the builder of test trees, the
//! minimal tree of the parser tests, the profiles of the boards and the test
//! modules of the parse, the node access, the translation, the memory
//! discovery, the CPU nodes, the limits, the dynamic reservations, the error
//! orders, the frozen vectors and the examples of the feature document.
//!
//! Feature: krepi.platform.device-tree
//!
//! The trees are built here from their tokens; the expected values come
//! from the contract and its frozen vectors, never from an earlier run.

extern crate std;

use super::format::{HEADER_SIZE, MAGIC, padded_end, u32_at};
use super::*;
use std::{vec, vec::Vec};

mod cpus;
mod discovery;
mod dynamic;
mod examples;
mod limits;
mod order;
mod parser;
mod profiles;
mod results;
mod translation;

pub(crate) use profiles::{PI5_CPUS, PI5_HAND_OVER, QEMU_HVC_CPUS, QEMU_SMC_CPUS};

/// A device tree under construction: its structure block, strings block
/// and reservation map.
#[derive(Default)]
pub(crate) struct Builder {
    structure: Vec<u8>,
    strings: Vec<u8>,
    pub(crate) reservations: Vec<Span>,
}

impl Builder {
    fn word(&mut self, value: u32) {
        self.structure.extend(value.to_be_bytes());
    }

    fn align(&mut self) {
        while !self.structure.len().is_multiple_of(4) {
            self.structure.push(0);
        }
    }

    pub(crate) fn begin(&mut self, name: &str) {
        self.word(1);
        self.structure.extend(name.bytes());
        self.structure.push(0);
        self.align();
    }

    pub(crate) fn end(&mut self) {
        self.word(2);
    }

    pub(crate) fn property(&mut self, name: &str, bytes: &[u8]) {
        self.word(3);
        self.word(bytes.len() as u32);
        self.word(self.strings.len() as u32);
        self.strings.extend(name.bytes());
        self.strings.push(0);
        self.structure.extend(bytes);
        self.align();
    }

    pub(crate) fn cells(&mut self, name: &str, values: &[u32]) {
        self.property(name, &cells(values));
    }

    pub(crate) fn root(&mut self) {
        self.begin("");
        self.cells("#address-cells", &[2]);
        self.cells("#size-cells", &[2]);
    }

    fn memory(&mut self) {
        self.begin("memory@100000000");
        self.property("device_type", b"memory\0");
        self.cells("reg", &[1, 0, 0, 0x200000]);
        self.end();
    }

    pub(crate) fn finish(mut self) -> Vec<u8> {
        self.word(9);
        let reserve_len = (self.reservations.len() + 1) * 16;
        let structure_offset = HEADER_SIZE + reserve_len;
        let strings_offset = structure_offset + self.structure.len();
        let total = strings_offset + self.strings.len();
        let mut result = Vec::new();
        for field in [
            MAGIC,
            total as u32,
            structure_offset as u32,
            strings_offset as u32,
            HEADER_SIZE as u32,
            17,
            16,
            0,
            self.strings.len() as u32,
            self.structure.len() as u32,
        ] {
            result.extend(field.to_be_bytes());
        }
        for span in self.reservations {
            result.extend(span.start.to_be_bytes());
            result.extend(span.size.to_be_bytes());
        }
        result.extend([0; 16]);
        result.extend(self.structure);
        result.extend(self.strings);
        result
    }
}

fn cells(values: &[u32]) -> Vec<u8> {
    values.iter().flat_map(|n| n.to_be_bytes()).collect()
}

/// The minimal tree: a root with 2 and 2 cells and one node
/// `memory@100000000` of `0x100000000+0x200000`.
fn minimal() -> Vec<u8> {
    let mut b = Builder::default();
    b.root();
    b.memory();
    b.end();
    b.finish()
}

pub(crate) fn set_word(bytes: &mut [u8], at: usize, value: u32) {
    bytes[at..at + 4].copy_from_slice(&value.to_be_bytes());
}

/// The nodes of a tree, in the order of its structure block.
fn all_nodes(tree: Fdt<'_>) -> Vec<Node<'_>> {
    let mut nodes = tree.nodes();
    let mut all = Vec::new();
    while let Some(node) = nodes.next() {
        all.push(node);
    }
    all
}
