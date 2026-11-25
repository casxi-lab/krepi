//! The CPU nodes before the CPU profile of a board became a value: the code
//! of krepi commit 5ffa296 at the lines below, copied verbatim with the
//! suffix `_before` added to the name of each item and of each call of a
//! copied item, for the differential tests, which compare it with the code
//! that replaced it. The functions that it calls and that did not change
//! are those of the module, and the copy reaches them through
//! `super::super`.
//!
//! - `kernel/src/fdt.rs:375-385`: `CpuProfile`;
//! - `kernel/src/fdt.rs:387-395`: `CpuTopology`;
//! - `kernel/src/fdt/cpus.rs:23-29`: `is_pi5`;
//! - `kernel/src/fdt/cpus.rs:46-56`: `id_of`;
//! - `kernel/src/fdt/cpus.rs:58-81`: `CpuProfile::affinity_shift`,
//!   `conduit` and `logical_id`;
//! - `kernel/src/fdt/cpus.rs:83-125`: `CpuTopology::count`, `profile`,
//!   `affinity` and `validate_qemu_timers`;
//! - `kernel/src/fdt/cpus.rs:127-128`: `TIMER_INTERRUPTS`;
//! - `kernel/src/fdt/cpus.rs:130-155`: `timer_records`;
//! - `kernel/src/fdt/cpus.rs:157-202`: `cpu_of_child`;
//! - `kernel/src/fdt/cpus.rs:204-237`: `cpu_children`;
//! - `kernel/src/fdt/cpus.rs:239-249`: `ids_complete`;
//! - `kernel/src/fdt/cpus.rs:270-315`: `Fdt::discover_cpus`.
//!
//! Feature: krepi.platform.device-tree

#![allow(non_camel_case_types, non_upper_case_globals, dead_code)]

use super::super::*;

/// The CPU profile of a board: it fixes the affinity level of the CPU IDs
/// and the PSCI conduit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CpuProfile_before {
    /// QEMU virt with PSCI over HVC.
    QemuHvc,
    /// QEMU virt with EL2 and PSCI over SMC.
    QemuSmc,
    /// The Raspberry Pi 5.
    Pi5,
}

/// The result of [`Fdt::discover_cpus`]: the profile and the number of
/// CPUs, whose logical IDs are 0 to `count - 1`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CpuTopology_before {
    /// The profile.
    profile: CpuProfile_before,
    /// The number of CPUs: 1, 2 or 4.
    count: u64,
}

/// Whether `profile` is that of the Pi 5.
fn is_pi5_before(profile: CpuProfile_before) -> bool {
    match profile {
        CpuProfile_before::Pi5 => true,
        _ => false,
    }
}

/// The logical ID below 4 whose `id << affinity_shift` is `affinity`, or
/// none.
fn id_of_before(profile: CpuProfile_before, affinity: u64) -> Option<u64> {
    let shift = profile.affinity_shift_before();
    let id = affinity >> shift;
    if id < 4 && affinity == id << shift {
        Some(id)
    } else {
        None
    }
}

impl CpuProfile_before {
    /// The affinity level of the CPU IDs as a shift: 8 on the Pi 5, whose
    /// CPU IDs are affinity level 1 of `MPIDR_EL1`, and 0 on QEMU virt.
    pub fn affinity_shift_before(self) -> u64 {
        if is_pi5_before(self) { 8 } else { 0 }
    }

    /// The PSCI conduit: HVC for QEMU virt without EL2, SMC for QEMU virt
    /// with EL2 and for the Pi 5.
    pub fn conduit_before(self) -> PsciConduit {
        match self {
            CpuProfile_before::QemuHvc => PsciConduit::Hvc,
            _ => PsciConduit::Smc,
        }
    }

    /// The logical ID of the affinity fields of `mpidr`,
    /// `mpidr & 0xff_00ff_ffff`, so that the flag bits do not change it;
    /// none for an affinity that is not `id << affinity_shift` with an ID
    /// below 4.
    pub fn logical_id_before(self, mpidr: u64) -> Option<u64> {
        id_of_before(self, mpidr & AFFINITY_MASK)
    }
}

impl CpuTopology_before {
    /// The number of CPUs: 1, 2 or 4.
    pub fn count_before(self) -> u64 {
        self.count
    }

    /// The profile of the topology.
    pub fn profile_before(self) -> CpuProfile_before {
        self.profile
    }

    /// The affinity of the CPU `index`, `index << affinity_shift` for an
    /// index below the count, and none otherwise.
    pub fn affinity_before(self, index: u64) -> Option<u64> {
        if index < self.count {
            Some(index << self.profile.affinity_shift_before())
        } else {
            None
        }
    }

    /// Checks the `interrupts` of the timer node of QEMU virt: records of
    /// three cells, type 1 for a private interrupt, its number and the
    /// flags `((1 << count) - 1) << 8 | 4`, the admitted CPUs and a
    /// level-high trigger, for the private interrupts 13, 14, 11 and 10 in
    /// this order and, with EL2, 12 after them, with nothing else; any other
    /// value, `BadProperty`. For the Pi 5 profile, whose timer belongs to its
    /// board support, `BadProperty`.
    pub fn validate_qemu_timers_before(self, interrupts: &[u8]) -> Result<(), Error> {
        let records = match self.profile {
            CpuProfile_before::QemuHvc => 4,
            CpuProfile_before::QemuSmc => 5,
            CpuProfile_before::Pi5 => return Err(Error::BadProperty),
        };
        // The flags are a cell of 32 bits; the shift is taken modulo 32.
        let cpus = (1u32 << ((self.count as u32) & 31)) - 1;
        let flags = (cpus << 8) | 4;
        if !timer_records_before(interrupts, records, flags) {
            return Err(Error::BadProperty);
        }
        Ok(())
    }
}

/// The private interrupts of the timer of QEMU virt, in their order.
const TIMER_INTERRUPTS_before: [u32; 5] = [13, 14, 11, 10, 12];

/// Whether `interrupts` holds exactly the first `records` timer records,
/// each with `flags`.
fn timer_records_before(interrupts: &[u8], records: usize, flags: u32) -> bool {
    if interrupts.len() != records * 12 {
        return false;
    }
    let mut index = 0;
    while index < records {
        let at = index * 12;
        let matches = match (
            u32_at(interrupts, at),
            u32_at(interrupts, at + 4),
            u32_at(interrupts, at + 8),
        ) {
            (Ok(kind), Ok(number), Ok(cell)) => {
                kind == 1 && number == TIMER_INTERRUPTS_before[index] && cell == flags
            }
            _ => false,
        };
        if !matches {
            return false;
        }
        index += 1;
    }
    true
}

/// One child of `/cpus`, whose address cells are `cells`, after the CPU
/// nodes whose IDs `ids` holds as bits: its ID, or none for a child that is
/// no CPU node. First its `device_type`, and a child whose `device_type` is
/// not `cpu` is skipped. Then, for a CPU node: disabled, or a `compatible`
/// other than exactly `arm,cortex-a76`, `BadProperty`; no `reg`,
/// `MissingProperty`; its value in `cells` cells, `UnsupportedCells` or
/// `BadProperty`; its ID: a value that is not `id << affinity_shift` for an
/// ID below 4, or the ID of an earlier CPU node, `BadProperty`; then, for
/// every CPU but ID 0 and on the Pi 5 for every CPU, an `enable-method`
/// other than `psci`, `BadProperty`.
fn cpu_of_child_before(
    structure: &[u8],
    strings: &[u8],
    node: NodeAt,
    profile: CpuProfile_before,
    cells: u32,
    ids: u64,
) -> Result<Option<u64>, Error> {
    if !string_is(structure, strings, node, b"device_type", b"cpu")? {
        return Ok(None);
    }
    if !enabled_at(structure, strings, node)? {
        return Err(Error::BadProperty);
    }
    if !string_is(structure, strings, node, b"compatible", b"arm,cortex-a76")? {
        return Err(Error::BadProperty);
    }
    let (start, end) = match value_at(structure, strings, node, b"reg") {
        Some(range) => range,
        None => return Err(Error::MissingProperty),
    };
    let affinity = cells_u64(&structure[start..end], cells)?;
    let id = match id_of_before(profile, affinity) {
        Some(id) => id,
        None => return Err(Error::BadProperty),
    };
    if ids & (1 << id) != 0 {
        return Err(Error::BadProperty);
    }
    if (id != 0 || is_pi5_before(profile))
        && !string_is(structure, strings, node, b"enable-method", b"psci")?
    {
        return Err(Error::BadProperty);
    }
    Ok(Some(id))
}

/// The IDs of the CPU nodes below `/cpus`, the node `cpus`, as bits, and
/// their number.
fn cpu_children_before(
    structure: &[u8],
    strings: &[u8],
    cpus: NodeAt,
    profile: CpuProfile_before,
    cells: u32,
) -> Result<(u64, u64), Error> {
    let mut ids = 0;
    let mut count = 0;
    let mut walker = START;
    let mut read = 0;
    while read < TOKENS {
        let (next, found) = node_step(structure, walker);
        match found {
            Some(node) => {
                let id = if is_child(node, cpus.offset) {
                    cpu_of_child_before(structure, strings, node, profile, cells, ids)?
                } else {
                    None
                };
                if let Some(id) = id {
                    ids |= 1 << id;
                    count += 1;
                }
            }
            None => return Ok((ids, count)),
        }
        walker = next;
        read += 1;
    }
    Ok((ids, count))
}

/// Whether the IDs `ids` of `count` CPU nodes are complete: their number is
/// 1, 2 or 4, and 4 on the Pi 5, and they are 0 to `count - 1`.
fn ids_complete_before(profile: CpuProfile_before, ids: u64, count: u64) -> bool {
    if count != 1 && count != 2 && count != 4 {
        return false;
    }
    if is_pi5_before(profile) && count != 4 {
        return false;
    }
    ids == (1 << count) - 1
}

impl Fdt<'_> {
    /// The CPU topology of the tree for `profile`, or the error of the
    /// first rule that it breaks: `/cpus` absent, `MissingProperty`, or two
    /// siblings of that name, `AmbiguousMapping`; disabled, then with size
    /// cells other than 0, `BadProperty`; its address cells,
    /// `UnsupportedCells`; each child of `/cpus` in tree order; then the
    /// number and the set of IDs, `BadProperty`; `/psci` absent,
    /// `MissingProperty`, or two siblings of that name, `AmbiguousMapping`;
    /// its `status`, then its `method`, then its `compatible`,
    /// `BadProperty`.
    pub fn discover_cpus_before(self, profile: CpuProfile_before) -> Result<CpuTopology_before, Error> {
        let (structure, strings) = (self.structure, self.strings);
        let cpus = match find_path(structure, b"/cpus")? {
            Some(cpus) => cpus,
            None => return Err(Error::MissingProperty),
        };
        if !enabled_at(structure, strings, cpus)? {
            return Err(Error::BadProperty);
        }
        if size_cells_at(structure, strings, cpus)? != 0 {
            return Err(Error::BadProperty);
        }
        let cells = address_cells_at(structure, strings, cpus)?;
        if cells != 1 && cells != 2 {
            return Err(Error::UnsupportedCells);
        }
        let (ids, count) = cpu_children_before(structure, strings, cpus, profile, cells)?;
        if !ids_complete_before(profile, ids, count) {
            return Err(Error::BadProperty);
        }
        let psci = match find_path(structure, b"/psci")? {
            Some(psci) => psci,
            None => return Err(Error::MissingProperty),
        };
        if !enabled_at(structure, strings, psci)? {
            return Err(Error::BadProperty);
        }
        if !method_is(structure, strings, psci, profile.conduit_before())? {
            return Err(Error::BadProperty);
        }
        if !psci_compatible(structure, value_at(structure, strings, psci, b"compatible")) {
            return Err(Error::BadProperty);
        }
        Ok(CpuTopology_before { profile, count })
    }
}
