//! The vectors of `src/arch/aarch64/paging/tests.rs` of the contract: the
//! descriptors, the table sets and the copy of the kernel tables. Each set
//! is at `base` `0x100000000` with width 40 unless the test says otherwise.
//!
//! Feature: krepi.kernel.kernel-memory

use super::*;

/// `pt-01`.
#[test]
fn high_addresses_keep_all_bits_and_enforce_permissions() {
    let mut t = set::<6, false>();
    map(
        &mut t,
        0x2_0000_0000,
        0x10_0800_0000,
        Kind::ReadOnly,
        BASE,
        BITS,
    )
    .unwrap();
    let d = t.lookup_page(0x2_0000_0000, BASE, BITS).unwrap();
    assert_eq!(d, 0x60_0010_0800_0787);
    // AP[2] 1, PXN 1, UXN 1 and AP[1] 0.
    assert_eq!(
        (d >> 7 & 1, d >> 53 & 1, d >> 54 & 1, d >> 6 & 1),
        (1, 1, 1, 0)
    );
}

/// `pt-02`.
#[test]
fn attributes_separate_text_data_and_mmio() {
    assert_eq!(descriptor(Kind::ReadExecute, 0), 0x40_0000_0000_0787);
    assert_eq!(descriptor(Kind::ReadWrite, 0), 0x60_0000_0000_0707);
    assert_eq!(descriptor(Kind::Device, 0), 0x60_0000_0000_0403);
}

/// `pt-03`.
#[test]
fn errors_are_atomic_and_no_implicit_remapping() {
    let mut t = set::<3, false>();
    map(
        &mut t,
        0x4000_0000,
        0x4000_0000,
        Kind::ReadWrite,
        BASE,
        BITS,
    )
    .unwrap();
    assert_eq!(t.used(), 3);
    let d = t.lookup_page(0x4000_0000, BASE, BITS);
    assert_eq!(d, Ok(0x60_0000_4000_0707));
    let device = map(&mut t, 0x4000_0000, 0x4000_1000, Kind::Device, BASE, BITS);
    assert_eq!(device, Err(TableError::AlreadyMapped));
    assert_eq!(t.lookup_page(0x4000_0000, BASE, BITS), d);
    let far = map(&mut t, 0x8000_0000, 0, Kind::ReadWrite, BASE, BITS);
    assert_eq!(far, Err(TableError::OutOfTables));
    assert_eq!(t.used(), 3);
    let missing = t.lookup_page(0x8000_0000, BASE, BITS);
    assert_eq!(missing, Err(TableError::NotMapped));
}

/// `pt-04`.
#[test]
fn invalid_width_alignment_and_table_backing_rejected() {
    let mut t = set::<3, false>();
    for (va, pa, base, error) in [
        (1, 0, BASE, TableError::Alignment),
        (0, 1, BASE, TableError::Alignment),
        (0, 0, BASE + 1, TableError::Alignment),
        (1 << 39, 0, BASE, TableError::AddressWidth),
        (0, 1 << 40, BASE, TableError::AddressWidth),
        (0, 0, 0xff_ffff_f000, TableError::TableBacking),
    ] {
        assert_eq!(map(&mut t, va, pa, Kind::ReadWrite, base, BITS), Err(error));
        assert_eq!(t.used(), 1);
    }
}

/// `pt-05`.
#[test]
fn unmap_and_reuse_only_the_requested_leaf() {
    let mut t = set::<4, false>();
    map(&mut t, 0, 0x1000, Kind::ReadWrite, BASE, BITS).unwrap();
    map(&mut t, 0x1000, 0x2000, Kind::ReadOnly, BASE, BITS).unwrap();
    assert_eq!(unmap(&mut t, 0, BASE, BITS), Ok(0x1000));
    assert_eq!(unmap(&mut t, 0, BASE, BITS), Err(TableError::NotMapped));
    assert_eq!(t.lookup_page(0x1000, BASE, BITS), Ok(0x60_0000_0000_2787));
    map(&mut t, 0, 0x3000, Kind::ReadOnly, BASE, BITS).unwrap();
    assert_eq!(t.lookup_page(0, BASE, BITS), Ok(0x60_0000_0000_3787));
}

/// `pt-06`.
#[test]
fn user_pages_enforce_el0_access_wx_and_asid_scope() {
    let mut t = set::<3, false>();
    for (va, kind, d) in [
        (0, Kind::UserReadExecute, 0x20_0000_0000_0fc7),
        (0x1000, Kind::UserReadOnly, 0x60_0000_0000_1fc7),
        (0x2000, Kind::UserReadWrite, 0x60_0000_0000_2f47),
    ] {
        map(&mut t, va, va, kind, BASE, BITS).unwrap();
        assert_eq!(t.lookup_page(va, BASE, BITS), Ok(d));
    }
    assert_eq!(descriptor(Kind::ReadExecute, 0), 0x40_0000_0000_0787);
    assert_eq!(descriptor(Kind::ReadOnly, 0), 0x60_0000_0000_0787);
    assert_eq!(descriptor(Kind::ReadWrite, 0), 0x60_0000_0000_0707);
    assert_eq!(descriptor(Kind::Device, 0), 0x60_0000_0000_0403);
}

/// `pt-07`.
#[test]
fn cloned_kernel_tables_are_private_and_keep_global_physical_leaves() {
    let mut source = set::<10, false>();
    let mut target = set::<10, false>();
    let target_base = 0x1_0000_a000;
    for (va, pa, kind) in [
        (0x4000, 0x4000_0000, Kind::ReadExecute),
        (0x900_0000, 0x900_0000, Kind::Device),
        (0x4000_0000, 0x2_0000_0000, Kind::ReadWrite),
    ] {
        map(&mut source, va, pa, kind, BASE, BITS).unwrap();
    }
    map(
        &mut target,
        0x8000_0000,
        0,
        Kind::ReadWrite,
        target_base,
        BITS,
    )
    .unwrap();
    let original = source.pool;
    copy(&mut target, &source, BASE, target_base, BITS).unwrap();
    assert!(source.pool == original);
    assert_eq!((target.used(), source.used()), (6, 6));
    // Each leaf under table descriptors of the target's tables of the
    // source's indices: (table, entry, descriptor).
    for (va, d, path) in [
        (
            0x4000,
            0x40_0000_4000_0787,
            [(0, 0, 0x1_0000_b003), (1, 0, 0x1_0000_c003)],
        ),
        (
            0x900_0000,
            0x60_0000_0900_0403,
            [(0, 0, 0x1_0000_b003), (1, 72, 0x1_0000_d003)],
        ),
        (
            0x4000_0000,
            0x60_0002_0000_0707,
            [(0, 1, 0x1_0000_e003), (4, 0, 0x1_0000_f003)],
        ),
    ] {
        assert_eq!(target.lookup_page(va, target_base, BITS), Ok(d));
        assert_eq!(source.lookup_page(va, BASE, BITS), Ok(d));
        for (table, index, entry) in path {
            assert_eq!(target.pool[table][index], entry);
        }
    }
    let old = target.lookup_page(0x8000_0000, target_base, BITS);
    assert_eq!(old, Err(TableError::NotMapped));
    map(
        &mut target,
        0x8000,
        0x6000,
        Kind::UserReadWrite,
        target_base,
        BITS,
    )
    .unwrap();
    let own = source.lookup_page(0x8000, BASE, BITS);
    assert_eq!(own, Err(TableError::NotMapped));
    assert_eq!(unmap(&mut source, 0x4000, BASE, BITS), Ok(0x4000_0000));
    let kept = target.lookup_page(0x4000, target_base, BITS);
    assert_eq!(kept, Ok(0x40_0000_4000_0787));
}

/// A copy that `clone_kernel_from` refuses with `error`, leaving the
/// target's tables and record unchanged.
fn refused<const N: usize, const UPPER: bool>(
    target: &mut Tables<N, UPPER>,
    source: &Tables<N, UPPER>,
    (source_base, base, bits): (u64, u64, u8),
    error: TableError,
) {
    let (pool, used) = (target.pool, target.used);
    let plan = target.clone_kernel_from(source, source_base, base, bits);
    assert_eq!(plan.err(), Some(error));
    assert!(target.pool == pool && target.used == used);
}

/// `pt-08`.
#[test]
fn kernel_clone_errors_preserve_the_destination() {
    let mut source = set::<6, false>();
    let mut target = set::<6, false>();
    let target_base = 0x1_0000_6000;
    map(&mut source, 0, 0x4000, Kind::ReadOnly, BASE, BITS).unwrap();
    map(
        &mut target,
        0x1000,
        0x8000,
        Kind::ReadWrite,
        target_base,
        BITS,
    )
    .unwrap();
    for (bases, error) in [
        ((BASE, BASE, BITS), TableError::TableBacking),
        ((BASE, BASE + 0x1000, BITS), TableError::TableBacking),
        ((BASE + 1, target_base, BITS), TableError::Alignment),
        ((BASE, target_base + 1, BITS), TableError::Alignment),
        ((BASE, target_base, 31), TableError::AddressWidth),
        ((BASE, 0xff_ffff_f000, BITS), TableError::TableBacking),
    ] {
        refused(&mut target, &source, bases, error);
    }
    let bases = (BASE, target_base, BITS);
    let root = source.pool[0][0];
    for (entry, error) in [
        (BASE | 3, TableError::TableBacking),
        ((BASE + 0x5000) | 3, TableError::TableBacking),
        (root | 1 << 6, TableError::InvalidDescriptor),
    ] {
        source.pool[0][0] = entry;
        refused(&mut target, &source, bases, error);
    }
    source.pool[0][0] = root;
    // Two parents of one table.
    source.pool[0][1] = root;
    refused(&mut target, &source, bases, TableError::TableBacking);
    source.pool[0][1] = 0;
    // A table in use that no entry reaches.
    source.used += 1;
    refused(&mut target, &source, bases, TableError::TableBacking);
    source.used -= 1;
    assert_eq!(unmap(&mut source, 0, BASE, BITS), Ok(0x4000));
    map(&mut source, 0, 0x4000, Kind::UserReadOnly, BASE, BITS).unwrap();
    refused(&mut target, &source, bases, TableError::InvalidDescriptor);
}

/// `pt-09`.
#[test]
fn whole_address_space_reset_reclaims_intermediate_tables() {
    let mut t = set::<4, false>();
    map(&mut t, 0, 0x1000, Kind::ReadWrite, BASE, BITS).unwrap();
    map(&mut t, 0x20_0000, 0x2000, Kind::UserReadWrite, BASE, BITS).unwrap();
    assert_eq!(unmap(&mut t, 0, BASE, BITS), Ok(0x1000));
    assert_eq!(t.used(), 4);
    let plan = t.reset();
    apply(&mut t, plan);
    assert!(t.pool.iter().flatten().all(|entry| *entry == 0));
    assert_eq!(t.used(), 1);
    let gone = t.lookup_page(0x20_0000, BASE, BITS);
    assert_eq!(gone, Err(TableError::NotMapped));
    map(
        &mut t,
        0x4000_0000,
        0x8000,
        Kind::UserReadExecute,
        BASE,
        BITS,
    )
    .unwrap();
    assert_eq!(t.used(), 3);
    let d = t.lookup_page(0x4000_0000, BASE, BITS);
    assert_eq!(d, Ok(0x20_0000_0000_8fc7));
}

/// `pt-10`.
#[test]
fn kernel_clone_rejects_leaf_physical_addresses_outside_the_profile() {
    let mut source = set::<3, false>();
    let mut target = set::<3, false>();
    map(&mut source, 0, 1 << 40, Kind::ReadOnly, BASE, 48).unwrap();
    let bases = (BASE, 0x1_0000_3000, BITS);
    refused(&mut target, &source, bases, TableError::InvalidDescriptor);
    assert_eq!(target.used(), 1);
    assert!(target.pool.iter().flatten().all(|entry| *entry == 0));
}

/// `pt-11`.
#[test]
fn private_kernel_stacks_are_privileged_non_executable_and_asid_scoped() {
    let mut first = set::<6, false>();
    let mut second = set::<6, false>();
    let second_base = 0x1_0000_7000;
    let stack = 0x2000_1000;
    let kind = Kind::KernelPrivateReadWrite;
    map(&mut first, stack, 0x4100_0000, kind, BASE, BITS).unwrap();
    assert_eq!(
        first.lookup_page(stack, BASE, BITS),
        Ok(0x60_0000_4100_0f07)
    );
    let guard = first.lookup_page(0x2000_0000, BASE, BITS);
    assert_eq!(guard, Err(TableError::NotMapped));
    map(&mut second, stack, 0x4200_0000, kind, second_base, BITS).unwrap();
    let d = second.lookup_page(stack, second_base, BITS);
    assert_eq!(d, Ok(0x60_0000_4200_0f07));
    let guard = second.lookup_page(0x2000_0000, second_base, BITS);
    assert_eq!(guard, Err(TableError::NotMapped));
    assert_eq!(
        first.lookup_page(stack, BASE, BITS),
        Ok(0x60_0000_4100_0f07)
    );
    assert_eq!(unmap(&mut first, stack, BASE, BITS), Ok(0x4100_0000));
    assert_eq!(second.lookup_page(stack, second_base, BITS), d);
}

/// `pt-12`.
#[test]
fn kernel_template_clone_rejects_private_privileged_stack_mappings() {
    let mut source = set::<3, false>();
    let mut target = set::<3, false>();
    let target_base = 0x1_0000_4000;
    let kind = Kind::KernelPrivateReadWrite;
    map(&mut source, 0x2000_1000, 0x4100_0000, kind, BASE, BITS).unwrap();
    map(
        &mut target,
        0x4000_0000,
        0x4000_0000,
        Kind::ReadWrite,
        target_base,
        BITS,
    )
    .unwrap();
    let bases = (BASE, target_base, BITS);
    refused(&mut target, &source, bases, TableError::InvalidDescriptor);
    assert_eq!(target.used(), 3);
}

/// `pt-13`.
#[test]
fn zeroed_table_storage_can_be_initialized_in_place() {
    let mut t = Tables::<3, false> {
        pool: [[0; ENTRIES]; 3],
        used: 0,
    };
    let plan = t.reset();
    apply(&mut t, plan);
    assert_eq!(t.used(), 1);
    let kind = Kind::KernelPrivateReadWrite;
    map(&mut t, 0x2000_1000, 0x4100_0000, kind, BASE, BITS).unwrap();
    let d = t.lookup_page(0x2000_1000, BASE, BITS);
    assert_eq!(d, Ok(0x60_0000_4100_0f07));
}

/// `pt-14`.
#[test]
fn lower_and_upper_tables_reject_each_others_canonical_addresses() {
    let mut lower = set::<3, false>();
    let mut upper = set::<3, true>();
    let width = Err(TableError::AddressWidth);
    for va in [0, 0x1000, 0x7f_ffff_f000] {
        assert_eq!(map(&mut upper, va, 0, Kind::ReadWrite, BASE, BITS), width);
    }
    for va in [DIRECT_BASE, DIRECT_BASE + 0x1000, 0xffff_ffff_ffff_f000] {
        assert_eq!(map(&mut lower, va, 0, Kind::ReadWrite, BASE, BITS), width);
    }
    for va in [1 << 39, DIRECT_BASE - 0x1000] {
        assert_eq!(map(&mut lower, va, 0, Kind::ReadWrite, BASE, BITS), width);
        assert_eq!(map(&mut upper, va, 0, Kind::ReadWrite, BASE, BITS), width);
    }
    map(
        &mut upper,
        DIRECT_BASE,
        1 << 32,
        Kind::ReadWrite,
        BASE,
        BITS,
    )
    .unwrap();
    let d = upper.lookup_page(DIRECT_BASE, BASE, BITS);
    assert_eq!(d, Ok(0x60_0001_0000_0707));
    assert_eq!(lower.used(), 1);
}

/// `pt-15`.
#[test]
fn blocks_are_privileged_global_nx_and_cannot_be_removed_as_pages() {
    let mut t = set::<3, true>();
    let va = DIRECT_BASE + (1 << 32);
    block(&mut t, va, 1 << 32, BASE, BITS).unwrap();
    let d = t.lookup_block(va, BASE, BITS);
    assert_eq!(d, Ok(0x60_0001_0000_0705));
    for offset in [0, 0x1000, 0x1f_f000] {
        let page = unmap(&mut t, va + offset, BASE, BITS);
        assert_eq!(page, Err(TableError::NotMapped));
        let again = map(&mut t, va + offset, 0, Kind::ReadWrite, BASE, BITS);
        assert_eq!(again, Err(TableError::AlreadyMapped));
    }
    assert_eq!(t.lookup_block(va, BASE, BITS), d);
    assert_eq!(t.used(), 2);
}

/// `pt-16`.
#[test]
fn block_errors_preserve_existing_storage_and_do_not_promote_page_tables() {
    let mut t = set::<3, false>();
    map(&mut t, 0, 0, Kind::ReadOnly, BASE, BITS).unwrap();
    let before = t.pool;
    for (va, pa, error) in [
        (0, 0, TableError::AlreadyMapped),
        (0x1000, 0, TableError::Alignment),
        (0x20_0000, 0x1000, TableError::Alignment),
        (0x20_0000, 1 << 40, TableError::AddressWidth),
        (1 << 39, 0, TableError::AddressWidth),
        (1 << 30, 0, TableError::OutOfTables),
    ] {
        assert_eq!(block(&mut t, va, pa, BASE, BITS), Err(error));
        assert_eq!(t.pool, before);
        assert_eq!(t.used(), 3);
    }
    assert_eq!(unmap(&mut t, 0, BASE, BITS), Ok(0));
    let block = block(&mut t, 0, 0, BASE, BITS);
    assert_eq!(block, Err(TableError::AlreadyMapped));
}

/// `pt-17`.
#[test]
fn eight_gib_of_blocks_use_nine_tables_and_cross_root_boundaries() {
    let mut t = set::<9, true>();
    for pa in (0..8 << 30).step_by(0x20_0000) {
        block(&mut t, DIRECT_BASE | pa, pa, BASE, BITS).unwrap();
    }
    assert_eq!(t.used(), 9);
    for pa in [0, 0x3fe0_0000, 0x4000_0000, 0x1_0000_0000, 0x1_ffe0_0000] {
        let d = t.lookup_block(DIRECT_BASE | pa, BASE, BITS);
        assert_eq!(d, Ok(0x60_0000_0000_0705 | pa));
    }
    let beyond = block(&mut t, DIRECT_BASE | 8 << 30, 8 << 30, BASE, BITS);
    assert_eq!(beyond, Err(TableError::OutOfTables));
}

/// `pt-18`.
#[test]
fn cloning_a_block_map_is_rejected_without_changing_the_destination() {
    let mut source = set::<3, true>();
    let mut target = set::<3, true>();
    let target_base = 0x1_0000_4000;
    block(&mut source, DIRECT_BASE, 0, BASE, BITS).unwrap();
    let page = DIRECT_BASE + 0x1000;
    map(&mut target, page, 0x1000, Kind::ReadOnly, target_base, BITS).unwrap();
    let bases = (BASE, target_base, BITS);
    refused(&mut target, &source, bases, TableError::InvalidDescriptor);
    assert_eq!(target.used(), 3);
}

/// `pt-21`.
#[test]
fn delegated_device_pages_are_rw_nx_non_global_with_device_attributes() {
    assert_eq!(descriptor(Kind::UserDevice, 0), 0x60_0000_0000_0c43);
}
