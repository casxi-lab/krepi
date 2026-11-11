//! A handle: the index of a slot in its low bits and the generation of the
//! slot above them.

/// The bits of the index.
pub const INDEX_BITS: u32 = 8;

/// The mask of the index, the largest index.
pub const INDEX_MASK: u32 = 255;

/// The largest generation that a handle holds.
pub const GENERATION_MAX: u32 = 0x00ff_ffff;

/// The handle of the slot `index` at `generation`, when both fit.
pub fn encode(index: u32, generation: u32) -> Option<u32> {
    if index > INDEX_MASK || generation > GENERATION_MAX {
        return None;
    }
    Some((generation << INDEX_BITS) | index)
}

/// The index of the slot of `handle`.
pub fn index(handle: u32) -> u32 {
    handle & INDEX_MASK
}

/// The generation of `handle`.
pub fn generation(handle: u32) -> u32 {
    handle >> INDEX_BITS
}

/// The handle of the same slot at the next generation, unless the
/// generation of `handle` is the largest.
pub fn next(handle: u32) -> Option<u32> {
    match generation(handle).checked_add(1) {
        Some(later) => encode(index(handle), later),
        None => None,
    }
}
