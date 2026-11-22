//! The boot wiring of QEMU virt: the boot memory map of the device tree that
//! QEMU's loader places at the start of RAM, the page ownership table of the
//! kernel root, the two kernel table sets of the image with the execution of
//! their plans, and the call that turns the MMU on.
//!
//! Feature: krepi.platform.device-tree
//! Feature: krepi.kernel.kernel-memory
//! Feature: krepi.platform.qemu-virt-boot
//!
//! The rules are those of the contracts of the fdt and page-tables
//! components, `docs/domains/boot-platform/fdt/contract.md` and
//! `docs/domains/memory/page-tables/contract.md`. The boot storage is the
//! image, with its BSS, its stack and the pools of the kernel tables, and
//! then the tree. The layout of the lower kernel set maps the text of the
//! image `ReadExecute`, its read-only data `ReadOnly`, its data, BSS and
//! stack `ReadWrite`, the pages of the tree `ReadOnly` and the registers of
//! the PL011 and of the GICv2 `Device`, at their physical addresses, and
//! leaves the guard page below the stack out. The direct map maps the usable
//! ranges of the boot memory map.
//!
//! The boot memory map and the page ownership table are written once into
//! statics of the module, so that no frame carries them, and the two table
//! sets are statics of the image aligned to 4 KiB, which `Tables::new`
//! initializes, so they lie in its data, zero but for the record of the
//! tables in use. The parts that compute the map, the exclusions, the banks,
//! the layout and the counts of the steps of a plan are plain code, which
//! the host tests run; the statics and `wire`, which executes the plans and
//! turns the MMU on with the caches off, are compiled only for the
//! bare-metal target.

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
use core::mem::MaybeUninit;

use krepi_arch::mmu::Plan;
use krepi_kernel::fdt::{MemoryPlan, PlanError, ReservedRegion, Span};
use krepi_kernel::page_tables::{
    EXCLUSION_RECORDS, EXTENTS, Excluder, Exclusion, Layout, LayoutKind, LayoutRange,
    MAX_LAYOUT_RANGES, Ownership, OwnershipError, PhysRange, Step,
};
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
use krepi_kernel::{
    fdt::Fdt,
    page_tables::{DIRECT_MAP_TABLES, ENTRIES, KERNEL_TABLES, Tables, direct_map, kernel_map},
};

use crate::{GIC_CPU, GIC_DISTRIBUTOR, UART_BASE};
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
use krepi_arch::{cpu, mmu};

#[cfg(test)]
mod tests;

/// The address at which QEMU's loader places the device tree: the start of
/// the RAM of QEMU virt, 2 MiB below the image.
pub const TREE_BASE: u64 = 0x4000_0000;

/// The arena of the page ownership table of the kernel root.
pub const ROOT_ARENA: u64 = 1;

/// The most banks of a boot memory map.
pub const BANKS: usize = 32;

/// A page, 4 KiB.
const PAGE_SIZE: u64 = 0x1000;

/// The register frame of the PL011: one page.
const UART_SIZE: u64 = PAGE_SIZE;

/// The register frame of the CPU interface of the GICv2, which follows its
/// distributor: 64 KiB.
const GIC_CPU_SIZE: u64 = 0x1_0000;

/// Bits 1 and 0 of a descriptor.
const TYPE_MASK: u64 = 0b11;

/// Bits 1 and 0 of a block descriptor.
const BLOCK: u64 = 0b01;

/// Bits 1 and 0 of a table or page descriptor.
const TABLE_OR_PAGE: u64 = 0b11;

/// The access flag `AF`, bit 10, which every leaf holds and no table
/// descriptor does.
const ACCESS_FLAG: u64 = 1 << 10;

/// The addresses of the link symbols that bound the parts of the image:
/// `__text_start`, `__text_end`, `__rodata_start`, `__rodata_end`,
/// `__stack_guard`, `__stack_bottom` and `__image_end`, each on a page
/// boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ImageSpans {
    /// The start of the text, the start of the image.
    pub text_start: u64,
    /// The end of the text.
    pub text_end: u64,
    /// The start of the read-only data.
    pub rodata_start: u64,
    /// The end of the read-only data and the start of the data.
    pub rodata_end: u64,
    /// The guard page below the stack, after the BSS.
    pub stack_guard: u64,
    /// The lowest address of the stack.
    pub stack_bottom: u64,
    /// The end of the stack, the end of the image.
    pub image_end: u64,
}

impl ImageSpans {
    /// The span of the image, its boot storage, from the start of its text
    /// to its end.
    pub fn span(&self) -> Span {
        Span {
            start: self.text_start,
            size: self.image_end.wrapping_sub(self.text_start),
        }
    }
}

/// The boot memory map of the RAM ranges `ram` and the reserved regions
/// `firmware` of the tree, with the boot storage of the image `image` and
/// then of the tree `tree`, managing every complete page of every bank.
pub fn memory_plan(
    ram: &[Span],
    firmware: &[ReservedRegion],
    image: Span,
    tree: Span,
) -> Result<MemoryPlan, PlanError> {
    MemoryPlan::all_ram(ram, &[image, tree], firmware)
}

/// The managed banks of `map` in `out`, as physical ranges in address
/// order; their number. More than [`BANKS`], which the boot memory map does
/// not admit, are `MetadataExhausted`.
pub fn banks(map: &MemoryPlan, out: &mut [PhysRange; BANKS]) -> Result<usize, OwnershipError> {
    let managed = map.managed_banks();
    if managed.len() > BANKS {
        return Err(OwnershipError::MetadataExhausted);
    }
    for (slot, bank) in out.iter_mut().zip(managed) {
        *slot = PhysRange::new(bank.start, bank.size)?;
    }
    Ok(managed.len())
}

/// The exclusions of `map` in `out`: the first span of its boot storage,
/// the image, as `Image`, its other spans as `BootStorage`, and its firmware
/// reservations as `Firmware`, in this order; their number. More than
/// `EXCLUSION_RECORDS`, which the boot memory map does not admit, are
/// `MetadataExhausted`.
pub fn exclusions(
    map: &MemoryPlan,
    out: &mut [Exclusion; EXCLUSION_RECORDS],
) -> Result<usize, OwnershipError> {
    if map.reservations().len() > EXCLUSION_RECORDS {
        return Err(OwnershipError::MetadataExhausted);
    }
    let boot = map.boot_ranges().iter().enumerate().map(|(index, span)| {
        let owner = if index == 0 {
            Excluder::Image
        } else {
            Excluder::BootStorage
        };
        (span, owner)
    });
    let firmware = map
        .firmware_ranges()
        .iter()
        .map(|span| (span, Excluder::Firmware));
    let mut count = 0;
    for (slot, (span, owner)) in out.iter_mut().zip(boot.chain(firmware)) {
        *slot = Exclusion {
            range: PhysRange::new(span.start, span.size)?,
            owner,
        };
        count += 1;
    }
    Ok(count)
}

/// The page ownership table of the kernel root, in the arena
/// [`ROOT_ARENA`], of the managed banks and the exclusions of `map`.
pub fn ownership(
    map: &MemoryPlan,
) -> Result<Ownership<EXTENTS, EXCLUSION_RECORDS>, OwnershipError> {
    let unused = PhysRange::new(0, PAGE_SIZE)?;
    let mut ranges = [unused; BANKS];
    let bank_count = banks(map, &mut ranges)?;
    let mut records = [Exclusion {
        range: unused,
        owner: Excluder::Firmware,
    }; EXCLUSION_RECORDS];
    let exclusion_count = exclusions(map, &mut records)?;
    Ownership::new(
        ROOT_ARENA,
        &ranges[..bank_count],
        &records[..exclusion_count],
    )
}

/// The range `[start, end)`, which must not be empty.
fn range(start: u64, end: u64) -> Result<PhysRange, OwnershipError> {
    match end.checked_sub(start) {
        Some(len) => PhysRange::new(start, len),
        None => Err(OwnershipError::InvalidRange),
    }
}

/// The layout of the lower kernel set for the image `image` and the pages
/// `tree` of the tree, with the guard page of `guards`, which holds
/// `__stack_guard`: the text `ReadExecute`; the read-only data `ReadOnly`;
/// the data and BSS, up to the guard, and the stack, from its bottom to the
/// end of the image, `ReadWrite`; the tree `ReadOnly`; and the PL011 and
/// the distributor and CPU interface of the GICv2 `Device`.
pub fn layout<'a>(
    image: &ImageSpans,
    tree: Span,
    guards: &'a [u64; 1],
) -> Result<Layout<'a>, OwnershipError> {
    let parts = [
        (image.text_start, image.text_end, LayoutKind::ReadExecute),
        (image.rodata_start, image.rodata_end, LayoutKind::ReadOnly),
        (image.rodata_end, image.stack_guard, LayoutKind::ReadWrite),
        (image.stack_bottom, image.image_end, LayoutKind::ReadWrite),
        (
            tree.start,
            tree.start.wrapping_add(tree.size),
            LayoutKind::ReadOnly,
        ),
        (
            UART_BASE as u64,
            UART_BASE as u64 + UART_SIZE,
            LayoutKind::Device,
        ),
        (
            GIC_DISTRIBUTOR as u64,
            GIC_CPU as u64 + GIC_CPU_SIZE,
            LayoutKind::Device,
        ),
    ];
    let unused = LayoutRange {
        range: PhysRange::new(0, PAGE_SIZE)?,
        kind: LayoutKind::ReadWrite,
    };
    let mut ranges = [unused; MAX_LAYOUT_RANGES];
    for (slot, (start, end, kind)) in ranges.iter_mut().zip(parts) {
        *slot = LayoutRange {
            range: range(start, end)?,
            kind,
        };
    }
    Ok(Layout {
        ranges,
        count: parts.len(),
        guards,
    })
}

/// The counts of the steps of the plans of one table set: the tables in
/// use, the blocks and the pages that they map.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Counts {
    /// The tables: the root, which `Tables::new` puts in use, and one for
    /// each `Zero` step.
    pub tables: usize,
    /// The `Store` steps of a block descriptor.
    pub blocks: usize,
    /// The `Store` steps of a page descriptor.
    pub pages: usize,
}

impl Counts {
    /// The counts of a set that no plan has written: its root.
    pub const fn new() -> Counts {
        Counts {
            tables: 1,
            blocks: 0,
            pages: 0,
        }
    }

    /// Counts `step`: a `Zero` as a table, a `Store` of bits 1 and 0 `0b01`
    /// as a block and one of `0b11` with the access flag as a page; a table
    /// descriptor, which holds no attribute, and the barriers count as
    /// nothing.
    pub fn count(&mut self, step: Step) {
        match step {
            Step::Zero(_) => self.tables += 1,
            Step::Store(_, _, descriptor) if descriptor & TYPE_MASK == BLOCK => self.blocks += 1,
            Step::Store(_, _, descriptor)
                if descriptor & TYPE_MASK == TABLE_OR_PAGE && descriptor & ACCESS_FLAG != 0 =>
            {
                self.pages += 1
            }
            _ => {}
        }
    }
}

impl Default for Counts {
    fn default() -> Counts {
        Counts::new()
    }
}

/// A plan that counts each step that it passes on into `counts`.
pub struct Counted<'c, P> {
    /// The plan.
    pub plan: P,
    /// The counts.
    pub counts: &'c mut Counts,
}

impl<const N: usize, P: Plan<N>> Plan<N> for Counted<'_, P> {
    fn next_step(&mut self) -> Option<Step> {
        let step = self.plan.next_step()?;
        self.counts.count(step);
        Some(step)
    }
}

/// A table set at the alignment of a table, 4 KiB: the set is the only
/// field, at offset 0, and its pool comes first, so the address of the
/// static is the address of table 0.
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
#[repr(C, align(4096))]
struct Aligned<T>(T);

/// The lower kernel set, of 32 tables.
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
static mut LOWER: Aligned<Tables<KERNEL_TABLES, false>> =
    Aligned(Tables::new([[0; ENTRIES]; KERNEL_TABLES]));

/// The direct map's set, of 80 tables.
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
static mut DIRECT: Aligned<Tables<DIRECT_MAP_TABLES, true>> =
    Aligned(Tables::new([[0; ENTRIES]; DIRECT_MAP_TABLES]));

/// The boot memory map, which `wire` writes once.
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
static mut MEMORY: MaybeUninit<MemoryPlan> = MaybeUninit::uninit();

/// The page ownership table of the kernel root, which `wire` writes once.
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
static mut OWNERSHIP: MaybeUninit<Ownership<EXTENTS, EXCLUSION_RECORDS>> = MaybeUninit::uninit();

/// What the boot wiring leaves: the span of the tree, the link symbols of
/// the image, the physical address size, the counts of the plans of the two
/// kernel table sets and the boot memory map.
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
pub struct Wired {
    /// The span of the tree, of its `totalsize`.
    pub tree: Span,
    /// The link symbols of the image.
    pub image: ImageSpans,
    /// The physical address size of the CPU.
    pub bits: u8,
    /// The counts of the plan of the lower kernel set.
    pub lower: Counts,
    /// The counts of the plan of the direct map.
    pub direct: Counts,
    /// The boot memory map.
    pub memory: &'static MemoryPlan,
}

/// Builds the boot memory, the kernel tables and the page ownership table
/// from the device tree `tree`, and turns the MMU on with the caches off:
/// it parses the tree; writes the boot memory map of its memory with the
/// image and the tree as boot storage, and the page ownership table of the
/// kernel root; reads the physical address size of the CPU; executes the
/// plans of `kernel_map` with the layout of the image and of `direct_map`
/// with the boot memory map on the two kernel table sets, counting their
/// steps; and calls `mmu::enable` with their roots.
///
/// # Panics
///
/// Panics with a static message when a step fails: `MMU must be off`,
/// `invalid device tree`, `boot memory map rejected`, `page ownership table
/// rejected`, `unsupported physical address size` and `kernel tables
/// rejected`.
///
/// # Safety
///
/// It is called once, on the boot CPU at EL1, with every exception masked
/// and the MMU off. `tree` holds the tree that QEMU's loader placed at
/// [`TREE_BASE`], below the image, which nothing writes while the kernel
/// runs.
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
pub unsafe fn wire(tree: &'static [u8]) -> Wired {
    // The link script defines these symbols; only their addresses are read.
    unsafe extern "C" {
        static __text_start: u8;
        static __text_end: u8;
        static __rodata_start: u8;
        static __rodata_end: u8;
        static __stack_guard: u8;
        static __stack_bottom: u8;
        static __image_end: u8;
    }
    assert!(cpu::system_control() & 1 == 0, "MMU must be off");
    let Ok(fdt) = Fdt::parse(tree) else {
        panic!("invalid device tree")
    };
    let tree_span = Span {
        start: tree.as_ptr().addr() as u64,
        size: fdt.total_size(),
    };
    let image = ImageSpans {
        text_start: (&raw const __text_start).addr() as u64,
        text_end: (&raw const __text_end).addr() as u64,
        rodata_start: (&raw const __rodata_start).addr() as u64,
        rodata_end: (&raw const __rodata_end).addr() as u64,
        stack_guard: (&raw const __stack_guard).addr() as u64,
        stack_bottom: (&raw const __stack_bottom).addr() as u64,
        image_end: (&raw const __image_end).addr() as u64,
    };
    let memory_slot = &raw mut MEMORY;
    let ownership_slot = &raw mut OWNERSHIP;
    // SAFETY: `wire` runs once, so no other reference to `MEMORY` exists or
    // has existed; the map is written here and only read afterwards.
    let memory = store_memory(unsafe { &mut *memory_slot }, fdt, image.span(), tree_span);
    // SAFETY: as for `MEMORY`; nothing else forms a reference to the table.
    store_ownership(unsafe { &mut *ownership_slot }, memory);
    let Some(bits) = mmu::physical_width() else {
        panic!("unsupported physical address size")
    };
    let Some(tree_pages) = memory.boot_ranges().get(1).copied() else {
        panic!("boot memory map rejected")
    };
    let guards = [image.stack_guard];
    let Ok(layout) = layout(&image, tree_pages, &guards) else {
        panic!("kernel tables rejected")
    };
    let lower = &raw mut LOWER;
    let direct = &raw mut DIRECT;
    let base_lower = lower.expose_provenance() as u64;
    let base_direct = direct.expose_provenance() as u64;
    // SAFETY: `wire` runs once, so these are the only references to the two
    // sets, and the plans below are their only users. Each set is the first
    // field of its `Aligned` static, at offset 0, and its pool the first
    // field of the set, `#[repr(C)]`, so `[base, base + 4096 N)` is its pool,
    // aligned to 4 KiB, whose provenance the lines above exposed. The image
    // runs at its load address, so the CPU reaches the pool at its physical
    // address with the MMU off, and with the MMU on through the `ReadWrite`
    // range of the layout that holds the data of the image. Only the plans of
    // `kernel_map` and `direct_map` write the pools, through these handles;
    // a plan reads an entry only before its own steps write it, and the
    // references are not used after the plans.
    let (set_lower, set_direct, mut pool_lower, mut pool_direct) = unsafe {
        (
            &mut (*lower).0,
            &mut (*direct).0,
            mmu::Pool::<KERNEL_TABLES>::new(base_lower),
            mmu::Pool::<DIRECT_MAP_TABLES>::new(base_direct),
        )
    };
    let mut counts_lower = Counts::new();
    let Ok(plan) = kernel_map(set_lower, layout, base_lower, bits) else {
        panic!("kernel tables rejected")
    };
    let plan = Counted {
        plan,
        counts: &mut counts_lower,
    };
    mmu::apply(&mut pool_lower, plan);
    let mut counts_direct = Counts::new();
    let Ok(plan) = direct_map(set_direct, memory, base_direct, bits) else {
        panic!("kernel tables rejected")
    };
    let plan = Counted {
        plan,
        counts: &mut counts_direct,
    };
    mmu::apply(&mut pool_direct, plan);
    // SAFETY: the MMU is off, as checked above, and every exception masked,
    // as the caller vouches. Both plans were executed to their last step, a
    // `Sync`, and no plan changes either set afterwards. The lower set maps
    // the text, with the exception vectors, the data, the BSS and the stack
    // of the image, the tree and the PL011 at their physical addresses with
    // kinds that allow the accesses of the code after the call, and `bits`
    // is what `physical_width` reported. The caches stay off.
    unsafe { mmu::enable(base_lower, base_direct, bits, false) };
    Wired {
        tree: tree_span,
        image,
        bits,
        lower: counts_lower,
        direct: counts_direct,
        memory,
    }
}

/// Writes the boot memory map of `tree`, with the image `image` and the
/// tree `tree_span` as boot storage, into `slot`, and returns it. It is a
/// call of its own, so that the discovery and its copies leave the stack
/// before the next step.
///
/// # Panics
///
/// Panics with `boot memory map rejected` on an error of the discovery or
/// of the map.
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
#[inline(never)]
fn store_memory(
    slot: &'static mut MaybeUninit<MemoryPlan>,
    tree: Fdt<'_>,
    image: Span,
    tree_span: Span,
) -> &'static MemoryPlan {
    let Ok(found) = tree.discover_memory() else {
        panic!("boot memory map rejected")
    };
    let Ok(map) = memory_plan(found.ram(), found.reserved(), image, tree_span) else {
        panic!("boot memory map rejected")
    };
    slot.write(map)
}

/// Writes the page ownership table of the kernel root of `memory` into
/// `slot`, in a call of its own, so that its temporaries leave the stack
/// before the next step.
///
/// # Panics
///
/// Panics with `page ownership table rejected` on an error.
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
#[inline(never)]
fn store_ownership(
    slot: &'static mut MaybeUninit<Ownership<EXTENTS, EXCLUSION_RECORDS>>,
    memory: &MemoryPlan,
) {
    let Ok(table) = ownership(memory) else {
        panic!("page ownership table rejected")
    };
    slot.write(table);
}
