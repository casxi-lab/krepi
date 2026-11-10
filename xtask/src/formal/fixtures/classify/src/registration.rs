//! A table of slots with generations: free functions, an inherent and a
//! trait method, a default method with a loop, derived methods, a function
//! of an inline module that the extraction cuts and external items.

use core::sync::atomic::{AtomicU32, Ordering};

#[derive(Clone, Copy, PartialEq)]
pub struct Slot {
    pub generation: u32,
    pub value: u32,
}

pub trait Table {
    fn value(&self, index: usize) -> Option<u32>;

    fn total(&self) -> u32 {
        let mut sum: u32 = 0;
        let mut index = 0;
        while index < 4 {
            if let Some(value) = self.value(index) {
                sum = sum.wrapping_add(value);
            }
            index += 1;
        }
        sum
    }
}

pub struct Slots {
    pub slots: [Slot; 4],
}

impl Slots {
    pub fn bump(&mut self, index: usize) -> Option<u32> {
        if index < 4 {
            let generation = self.slots[index].generation.checked_add(1)?;
            self.slots[index].generation = generation;
            Some(generation)
        } else {
            None
        }
    }
}

impl Table for Slots {
    fn value(&self, index: usize) -> Option<u32> {
        if index < 4 {
            Some(self.slots[index].value)
        } else {
            None
        }
    }
}

pub fn same(a: &Slot, b: &Slot) -> bool {
    a == b
}

pub fn copied(slot: &Slot) -> Slot {
    slot.clone()
}

pub fn probe() -> u32 {
    hardware::read()
}

pub fn load(counter: &AtomicU32) -> u32 {
    counter.load(Ordering::Relaxed)
}

pub mod hardware {
    pub fn read() -> u32 {
        0
    }
}
