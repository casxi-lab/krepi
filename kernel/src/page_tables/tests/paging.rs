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

/// `pt-21`.
#[test]
fn delegated_device_pages_are_rw_nx_non_global_with_device_attributes() {
    assert_eq!(descriptor(Kind::UserDevice, 0), 0x60_0000_0000_0c43);
}
