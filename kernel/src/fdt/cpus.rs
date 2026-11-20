//! The CPU nodes of a tree for the supported CPU profiles: the CPUs below
//! `/cpus`, their logical IDs and the PSCI conduit of `/psci`, and the
//! timer records of QEMU virt.
//!
//! Feature: krepi.platform.device-tree
//!
//! A profile fixes the affinity level of the CPU IDs, 1 on the Pi 5 and 0
//! on QEMU virt, and the PSCI conduit. The discovery reads the children of
//! `/cpus` once each, in tree order, before any CPU but the boot CPU is
//! started.

use super::format::{same_bytes, u32_at};
use super::nodes::{
    START, address_cells_at, enabled_at, find_path, is_child, node_step, size_cells_at, string_is,
    value_at,
};
use super::{CpuProfile, CpuTopology, Error, Fdt, NodeAt, PsciConduit, TOKENS, cells_u64};

/// The affinity fields of `MPIDR_EL1`: bits 0 to 23 and 32 to 39, without
/// the U, MT and other flag bits.
const AFFINITY_MASK: u64 = 0xff_00ff_ffff;

/// Whether `profile` is that of the Pi 5.
fn is_pi5(profile: CpuProfile) -> bool {
    match profile {
        CpuProfile::Pi5 => true,
        _ => false,
    }
}

/// Whether the `method` of `/psci` at `psci` names `conduit`, with the
/// errors of [`string_is`]. Each arm gives its name as an argument: a
/// byte-string literal returned as `&'static [u8]` is not translated.
fn method_is(
    structure: &[u8],
    strings: &[u8],
    psci: NodeAt,
    conduit: PsciConduit,
) -> Result<bool, Error> {
    match conduit {
        PsciConduit::Hvc => string_is(structure, strings, psci, b"method", b"hvc"),
        PsciConduit::Smc => string_is(structure, strings, psci, b"method", b"smc"),
    }
}

/// The logical ID below 4 whose `id << affinity_shift` is `affinity`, or
/// none.
fn id_of(profile: CpuProfile, affinity: u64) -> Option<u64> {
    let shift = profile.affinity_shift();
    let id = affinity >> shift;
    if id < 4 && affinity == id << shift {
        Some(id)
    } else {
        None
    }
}

impl CpuProfile {
    /// The affinity level of the CPU IDs as a shift: 8 on the Pi 5, whose
    /// CPU IDs are affinity level 1 of `MPIDR_EL1`, and 0 on QEMU virt.
    pub fn affinity_shift(self) -> u64 {
        if is_pi5(self) { 8 } else { 0 }
    }

    /// The PSCI conduit: HVC for QEMU virt without EL2, SMC for QEMU virt
    /// with EL2 and for the Pi 5.
    pub fn conduit(self) -> PsciConduit {
        match self {
            CpuProfile::QemuHvc => PsciConduit::Hvc,
            _ => PsciConduit::Smc,
        }
    }

    /// The logical ID of the affinity fields of `mpidr`,
    /// `mpidr & 0xff_00ff_ffff`, so that the flag bits do not change it;
    /// none for an affinity that is not `id << affinity_shift` with an ID
    /// below 4.
    pub fn logical_id(self, mpidr: u64) -> Option<u64> {
        id_of(self, mpidr & AFFINITY_MASK)
    }
}

impl CpuTopology {
    /// The number of CPUs: 1, 2 or 4.
    pub fn count(self) -> u64 {
        self.count
    }

    /// The profile of the topology.
    pub fn profile(self) -> CpuProfile {
        self.profile
    }

    /// The affinity of the CPU `index`, `index << affinity_shift` for an
    /// index below the count, and none otherwise.
    pub fn affinity(self, index: u64) -> Option<u64> {
        if index < self.count {
            Some(index << self.profile.affinity_shift())
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
    pub fn validate_qemu_timers(self, interrupts: &[u8]) -> Result<(), Error> {
        let records = match self.profile {
            CpuProfile::QemuHvc => 4,
            CpuProfile::QemuSmc => 5,
            CpuProfile::Pi5 => return Err(Error::BadProperty),
        };
        // The flags are a cell of 32 bits; the shift is taken modulo 32.
        let cpus = (1u32 << ((self.count as u32) & 31)) - 1;
        let flags = (cpus << 8) | 4;
        if !timer_records(interrupts, records, flags) {
            return Err(Error::BadProperty);
        }
        Ok(())
    }
}

/// The private interrupts of the timer of QEMU virt, in their order.
const TIMER_INTERRUPTS: [u32; 5] = [13, 14, 11, 10, 12];

/// Whether `interrupts` holds exactly the first `records` timer records,
/// each with `flags`.
fn timer_records(interrupts: &[u8], records: usize, flags: u32) -> bool {
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
                kind == 1 && number == TIMER_INTERRUPTS[index] && cell == flags
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
fn cpu_of_child(
    structure: &[u8],
    strings: &[u8],
    node: NodeAt,
    profile: CpuProfile,
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
    let id = match id_of(profile, affinity) {
        Some(id) => id,
        None => return Err(Error::BadProperty),
    };
    if ids & (1 << id) != 0 {
        return Err(Error::BadProperty);
    }
    if (id != 0 || is_pi5(profile))
        && !string_is(structure, strings, node, b"enable-method", b"psci")?
    {
        return Err(Error::BadProperty);
    }
    Ok(Some(id))
}

/// The IDs of the CPU nodes below `/cpus`, the node `cpus`, as bits, and
/// their number.
fn cpu_children(
    structure: &[u8],
    strings: &[u8],
    cpus: NodeAt,
    profile: CpuProfile,
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
                    cpu_of_child(structure, strings, node, profile, cells, ids)?
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
fn ids_complete(profile: CpuProfile, ids: u64, count: u64) -> bool {
    if count != 1 && count != 2 && count != 4 {
        return false;
    }
    if is_pi5(profile) && count != 4 {
        return false;
    }
    ids == (1 << count) - 1
}

/// Whether the `compatible` of `/psci` at `value` of the structure block is
/// exactly one of the lists `arm,psci-0.2`; `arm,psci-1.0`, `arm,psci-0.2`;
/// and `arm,psci-1.0`, `arm,psci-0.2`, `arm,psci`, each string with its NUL.
fn psci_compatible(structure: &[u8], value: Option<(usize, usize)>) -> bool {
    match value {
        Some((start, end)) => {
            same_bytes(structure, start, end, b"arm,psci-0.2\0")
                || same_bytes(structure, start, end, b"arm,psci-1.0\0arm,psci-0.2\0")
                || same_bytes(
                    structure,
                    start,
                    end,
                    b"arm,psci-1.0\0arm,psci-0.2\0arm,psci\0",
                )
        }
        None => false,
    }
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
    pub fn discover_cpus(self, profile: CpuProfile) -> Result<CpuTopology, Error> {
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
        let (ids, count) = cpu_children(structure, strings, cpus, profile, cells)?;
        if !ids_complete(profile, ids, count) {
            return Err(Error::BadProperty);
        }
        let psci = match find_path(structure, b"/psci")? {
            Some(psci) => psci,
            None => return Err(Error::MissingProperty),
        };
        if !enabled_at(structure, strings, psci)? {
            return Err(Error::BadProperty);
        }
        if !method_is(structure, strings, psci, profile.conduit())? {
            return Err(Error::BadProperty);
        }
        if !psci_compatible(structure, value_at(structure, strings, psci, b"compatible")) {
            return Err(Error::BadProperty);
        }
        Ok(CpuTopology { profile, count })
    }
}
