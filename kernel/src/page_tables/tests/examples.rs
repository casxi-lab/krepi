//! The examples of the kernel-memory feature document,
//! `docs/features/kernel/kernel-memory.md`: one test for each, named after
//! the example. Each set is at `base` `0x100000000` with width 40 unless
//! the test says otherwise.
//!
//! Feature: krepi.kernel.kernel-memory
//!
//! The expected values are those that the examples write, worked out from
//! the contract, never taken from a run of the code.

use super::*;
use Step::{Fence, Invalidate, Store, Sync, Zero};

#[test]
fn ex1_the_kernel_kinds_give_their_descriptors() {
    let pa = 0x4008_0000;
    assert_eq!(descriptor(Kind::ReadExecute, pa), 0x40_0000_4008_0787);
    assert_eq!(descriptor(Kind::ReadOnly, pa), 0x60_0000_4008_0787);
    assert_eq!(descriptor(Kind::ReadWrite, pa), 0x60_0000_4008_0707);
    let private = descriptor(Kind::KernelPrivateReadWrite, pa);
    assert_eq!(private, 0x60_0000_4008_0f07);
    assert_eq!(descriptor(Kind::Device, pa), 0x60_0000_4008_0403);
    // Only bits 12 to 47 of the address reach the descriptor.
    let wide = descriptor(Kind::ReadWrite, 0xffff_0000_4008_0fff);
    assert_eq!(wide, 0x60_0000_4008_0707);
    // The block form of `ReadWrite`, in a set of the upper region.
    let mut t = set::<2, true>();
    block(&mut t, DIRECT_BASE | 0x4020_0000, 0x4020_0000, BASE, BITS).unwrap();
    let leaf = t.lookup_block(DIRECT_BASE | 0x4020_0000, BASE, BITS);
    assert_eq!(leaf, Ok(0x60_0000_4020_0705));
}

#[test]
fn ex2_a_page_is_mapped_looked_up_and_unmapped() {
    let mut t = set::<3, false>();
    let va = 0x4008_0000;
    let plan = t.map_page(va, va, Kind::ReadWrite, BASE, BITS).unwrap();
    let steps = [
        Zero(2),
        Store(2, 128, 0x60_0000_4008_0707),
        Zero(1),
        Store(1, 0, 0x1_0000_2003),
        Fence,
        Store(0, 1, 0x1_0000_1003),
        Sync,
    ];
    assert_eq!((plan.zero_tables, &plan.steps[..plan.len]), (0, &steps[..]));
    apply(&mut t, plan);
    assert_eq!(t.used(), 3);
    assert_eq!(t.lookup_page(va, BASE, BITS), Ok(0x60_0000_4008_0707));
    let (plan, page) = t.unmap_page(va, BASE, BITS).unwrap();
    assert_eq!(page, va);
    assert_eq!(&plan.steps[..plan.len], [Store(2, 128, 0), Invalidate(va)]);
    apply(&mut t, plan);
    assert_eq!(t.lookup_page(va, BASE, BITS), Err(TableError::NotMapped));
    assert_eq!(t.unmap_page(va, BASE, BITS), Err(TableError::NotMapped));
    assert_eq!(t.used(), 3);
}

#[test]
fn ex3_text_and_data_on_one_page_are_refused() {
    let mut t = set::<KERNEL_TABLES, false>();
    let text = (0x4008_0000, 0x2000, LayoutKind::ReadExecute);
    let data = (0x4008_1000, 0x1000, LayoutKind::ReadWrite);
    let map = kernel(&mut t, layout(&[data, text], &[]), BASE, BITS);
    assert_eq!(map, Err(TableError::AlreadyMapped));
    assert_eq!(t.used(), 1);
    // The data on the page after the text.
    let data = (0x4008_2000, 0x1000, LayoutKind::ReadWrite);
    let steps = kernel(&mut t, layout(&[data, text], &[]), BASE, BITS).unwrap();
    assert_eq!((counts(&steps), t.used()), ((0x3000, 0, 3), 3));
    let page = |pa: u64| t.lookup_page(pa, BASE, BITS);
    assert_eq!(page(0x4008_1000), Ok(0x40_0000_4008_1787));
    assert_eq!(page(0x4008_2000), Ok(0x60_0000_4008_2707));
}

#[test]
fn ex4_the_direct_map_of_qemu_virt() {
    let ram = span(0x4000_0000, 0x800_0000);
    let boot = [span(0x4000_0000, 0x800), span(0x4020_0000, 0x10_0000)];
    let memory = MemoryPlan::all_ram(&[ram], &boot, &[]).unwrap();
    let mut t = set::<DIRECT_MAP_TABLES, true>();
    let steps = direct(&mut t, &memory, BASE, BITS).unwrap();
    assert_eq!((counts(&steps), t.used()), ((0x7ef_f000, 62, 767), 4));
    let page = |pa: u64| t.lookup_page(DIRECT_BASE | pa, BASE, BITS);
    assert_eq!(page(0x4000_0000), Err(TableError::NotMapped));
    assert_eq!(page(0x4000_1000), Ok(0x60_0000_4000_1707));
    assert_eq!(page(0x4020_0000), Err(TableError::NotMapped));
    assert_eq!(page(0x4030_0000), Ok(0x60_0000_4030_0707));
    let leaf = t.lookup_block(DIRECT_BASE | 0x4040_0000, BASE, BITS);
    assert_eq!(leaf, Ok(0x60_0000_4040_0705));
    let address = direct_address(range(0x4040_0000, 0x1000));
    assert_eq!(address, Some(0xffff_ff80_4040_0000));
}

#[test]
fn ex5_the_pi5_8gb_direct_map_takes_11_tables() {
    let banks = [
        span(0, 0x3fc0_0000),
        span(0x4000_0000, 0xc000_0000),
        span(0x1_0000_0000, 0x1_0000_0000),
    ];
    let boot = [span(0x8_0000, 0x12_7000), span(0x20_0000, 0x1_3ad4)];
    let atf = ReservedRegion {
        span: span(0, 0x8_0000),
        no_map: true,
        reusable: false,
    };
    let memory = MemoryPlan::all_ram(&banks, &boot, &[atf]).unwrap();
    let mut t = set::<DIRECT_MAP_TABLES, true>();
    let steps = direct(&mut t, &memory, BASE, BITS).unwrap();
    assert_eq!(counts(&steps), (0x1_ffa4_5000, 4092, 581));
    assert_eq!((t.used(), DIRECT_MAP_TABLES - t.used()), (11, 69));
    let page = |pa: u64| t.lookup_page(DIRECT_BASE | pa, BASE, BITS);
    assert_eq!(page(0x1a_7000), Ok(0x60_0000_001a_7707));
    assert_eq!(page(0x21_3000), Err(TableError::NotMapped));
    assert_eq!(page(0x21_4000), Ok(0x60_0000_0021_4707));
    let leaf = |pa: u64| t.lookup_block(DIRECT_BASE | pa, BASE, BITS);
    assert_eq!(leaf(0x40_0000), Ok(0x60_0000_0040_0705));
    assert_eq!(leaf(0x3fc0_0000), Err(TableError::NotMapped));
    assert_eq!(leaf(0x1_ffe0_0000), Ok(0x60_0001_ffe0_0705));
}

#[test]
fn ex6_pages_are_chosen_zeroed_and_assigned() {
    let bank = range(0x4000_0000, 0x1_0000);
    let firmware = Exclusion {
        range: range(0x4000_0800, 0x10),
        owner: Excluder::Firmware,
    };
    let mut t = Ownership::<8, EXCLUSION_RECORDS>::new(1, &[bank], &[firmware]).unwrap();
    let excluded = Owner::Excluded(Excluder::Firmware);
    assert_eq!(t.owner(0x4000_0000), Some(excluded));
    assert_eq!(t.stats().free, 0xf000);
    // A zeroing that fails leaves the pages free.
    let c = t.choose(7, 2, 1, HIGH).unwrap();
    assert_eq!(c.range, range(0x4000_e000, 0x2000));
    assert_eq!(t.assign(c, false), Err(OwnershipError::ZeroFailed));
    assert_eq!(t.owner(0x4000_e000), Some(Owner::Free));
    assert_eq!(t.stats().free, 0xf000);
    let c = t.choose(7, 2, 1, HIGH).unwrap();
    let a = t.assign(c, true).unwrap();
    assert_eq!(a, receipt(1, 7, 1, 0x4000_e000, 0x2000));
    let held = Owner::Held(7, 1, HoldState::Published);
    assert_eq!(t.owner(0x4000_f000), Some(held));
    assert_eq!((t.stats().free, t.stats().allocated), (0xd000, 0x2000));
    assert_eq!(t.release(8, a), Err(OwnershipError::WrongOwner));
    assert_eq!(t.release(7, a), Ok(()));
    assert_eq!(t.release(7, a), Err(OwnershipError::InvalidAllocation));
    assert_eq!(t.stats().free, 0xf000);
}

#[test]
fn ex7_a_reservation_is_published_after_a_failed_zeroing() {
    let bank = range(0x4000_0000, 0x4000);
    let mut t = Ownership::<4, EXCLUSION_RECORDS>::new(3, &[bank], &[]).unwrap();
    let r = t.reserve(4, 2, 1, LOW).unwrap();
    assert_eq!(r.allocation, receipt(3, 4, 1, 0x4000_0000, 0x2000));
    let reserved = Owner::Held(4, 1, HoldState::Reserved);
    assert_eq!(t.owner(0x4000_1000), Some(reserved));
    let r = r.initialized(false).unwrap_err();
    assert_eq!((r.attempted, r.failures), (true, 1));
    let (error, r) = t.cancel(4, r).unwrap_err();
    assert_eq!(error, OwnershipError::ZeroFailed);
    let x = r.initialized(true).unwrap();
    assert_eq!(x.failures(), 1);
    let a = t.publish(4, x).unwrap();
    assert_eq!(a, receipt(3, 4, 1, 0x4000_0000, 0x2000));
    let published = Owner::Held(4, 1, HoldState::Published);
    assert_eq!(t.owner(0x4000_0000), Some(published));
    assert_eq!(t.release(4, a), Ok(()));
    assert_eq!(t.stats().free, 0x4000);
}

#[test]
fn ex8_the_lower_kernel_set_is_copied_into_a_process_set() {
    let mut source = set::<8, false>();
    let text = (0x4008_0000, 0x1000, LayoutKind::ReadExecute);
    let data = (0x4008_1000, 0x1000, LayoutKind::ReadWrite);
    let console = (0x900_0000, 0x1000, LayoutKind::Device);
    let ranges = [text, data, console];
    kernel(&mut source, layout(&ranges, &[]), BASE, BITS).unwrap();
    assert_eq!(source.used(), 5);
    let original = source.pool;
    let base = 0x2_0000_0000;
    let mut target = set::<8, false>();
    let mut plan = target.clone_kernel_from(&source, BASE, base, BITS).unwrap();
    let steps: Vec<Step> = std::iter::from_fn(|| plan.next()).collect();
    let expected = [
        Zero(0),
        Store(0, 0, 0x2_0000_1003),
        Store(0, 1, 0x2_0000_3003),
        Store(1, 72, 0x2_0000_2003),
        Store(2, 0, 0x60_0000_0900_0403),
        Store(3, 0, 0x2_0000_4003),
        Store(4, 128, 0x40_0000_4008_0787),
        Store(4, 129, 0x60_0000_4008_1707),
        Sync,
    ];
    assert_eq!(steps, expected);
    for step in steps {
        execute(&mut target.pool, step);
    }
    assert!(source.pool == original);
    assert_eq!(target.used(), 5);
    for va in [0x900_0000, 0x4008_0000, 0x4008_1000] {
        let copied = target.lookup_page(va, base, BITS);
        assert_eq!(copied, source.lookup_page(va, BASE, BITS));
    }
    // A page of the process goes into the copy alone.
    let kind = Kind::UserReadWrite;
    map(&mut target, 0x8000, 0x4010_0000, kind, base, BITS).unwrap();
    let own = target.lookup_page(0x8000, base, BITS);
    assert_eq!(own, Ok(0x60_0000_4010_0f47));
    let kept = source.lookup_page(0x8000, BASE, BITS);
    assert_eq!(kept, Err(TableError::NotMapped));
}
