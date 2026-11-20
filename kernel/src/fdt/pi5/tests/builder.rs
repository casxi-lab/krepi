//! The builder of the Pi 5 test trees, with a reservation map that a test
//! may fill.
//!
//! Feature: krepi.platform.device-tree

use super::*;

#[derive(Default)]
pub(super) struct Builder {
    structure: Vec<u8>,
    strings: Vec<u8>,
    pub reservations: Vec<Span>,
}

impl Builder {
    fn word(&mut self, word: u32) {
        self.structure.extend(word.to_be_bytes());
    }

    fn align(&mut self) {
        while !self.structure.len().is_multiple_of(4) {
            self.structure.push(0);
        }
    }

    pub fn begin(&mut self, name: &str) {
        self.word(1);
        self.structure.extend(name.bytes());
        self.structure.push(0);
        self.align();
    }

    pub fn end(&mut self) {
        self.word(2);
    }

    pub fn property(&mut self, name: &str, bytes: &[u8]) {
        self.word(3);
        self.word(bytes.len() as u32);
        self.word(self.strings.len() as u32);
        self.strings.extend(name.bytes());
        self.strings.push(0);
        self.structure.extend(bytes);
        self.align();
    }

    pub fn cells(&mut self, name: &str, values: &[u32]) {
        let bytes: Vec<_> = values
            .iter()
            .flat_map(|value| value.to_be_bytes())
            .collect();
        self.property(name, &bytes);
    }

    pub fn finish(mut self) -> Vec<u8> {
        self.word(9);
        let structure_start = 40 + (self.reservations.len() + 1) * 16;
        let strings_start = structure_start + self.structure.len();
        let total = strings_start + self.strings.len();
        let mut bytes = Vec::new();
        for word in [
            0xd00dfeed,
            total as u32,
            structure_start as u32,
            strings_start as u32,
            40,
            17,
            16,
            0,
            self.strings.len() as u32,
            self.structure.len() as u32,
        ] {
            bytes.extend(word.to_be_bytes());
        }
        for span in self.reservations {
            bytes.extend(span.start.to_be_bytes());
            bytes.extend(span.size.to_be_bytes());
        }
        bytes.extend([0; 16]);
        bytes.extend(self.structure);
        bytes.extend(self.strings);
        bytes
    }
}
