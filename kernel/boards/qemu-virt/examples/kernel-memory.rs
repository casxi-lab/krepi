//! The test image of kernel memory on QEMU virt: with the kernel tables of
//! the boot wiring and the MMU on, it reads and writes the edge pages of
//! the usable ranges of the boot memory map through the direct map, reads
//! two pages that the map excludes, and probes the attributes of the lower
//! kernel set and of the direct map.
//!
//! Feature: krepi.kernel.kernel-memory
//!
//! The image writes its start record with the MMU off and runs the boot
//! wiring of the board, which turns the MMU on with the caches off. It
//! takes every address from the boot memory map and the link symbols: with
//! `T` the end of the pages of the tree, the second span of the boot
//! storage, `E` the end of the image and `B` the first 2 MiB boundary above
//! `E`, the pages P1 to P6 are `T`, the page below `__text_start`, `E`,
//! the page below `B`, `B` and the last page of the last managed bank. Each
//! must lie in a usable range; the image writes it, zeroes it with
//! `mmu::zero_frames`, reads it back as zero, writes it with a pattern of
//! its physical address and reads the pattern back, through the direct
//! map. The pages P7 and P8, below `T` and at `__text_start`, are excluded,
//! and a read of each through the direct map is a translation fault at
//! level 3. A write to `__rodata_start` is a permission fault at level 3; a
//! branch to the direct-map page below P6, which must equal the absolute
//! symbol `krepi_test_execute_never`, is an instruction abort with a
//! permission fault at level 2; a read of `__stack_guard` is a translation
//! fault at level 3. For each fault the image arms the address of the
//! faulting instruction and the label at which its code resumes, and its
//! dispatch reports the exception and resumes there; any other exception
//! halts. Last, `AT S1E1W` of the PL011 gives Device-nGnRnE memory at its
//! address. Every record after the start record goes through that `Device`
//! page. The image then writes one self-check for each of the twelve items
//! and `CASXI_RESUMED`. On the host it is an empty program.

#![cfg_attr(all(target_arch = "aarch64", target_os = "none"), no_std, no_main)]

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod common;
#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod memory;

#[cfg(all(target_arch = "aarch64", target_os = "none"))]
mod image {
    use core::arch::{asm, global_asm};
    use core::ptr;

    use crate::{common, memory};
    use krepi_arch::exception::{Frame, SYNC, exception_class};
    use krepi_arch::mmu;
    use krepi_kernel::fdt::MemoryPlan;
    use krepi_kernel::page_tables::{DIRECT_BASE, PhysRange};
    use krepi_qemu_virt::{UART_BASE, uart};

    /// A page, 4 KiB.
    const PAGE: u64 = 0x1000;
    /// A block of the direct map, 2 MiB.
    const BLOCK: u64 = 0x20_0000;
    /// The words of a page.
    const WORDS: u64 = PAGE / 8;
    /// The exception class of a data abort at EL1.
    const DATA_ABORT: u64 = 0x25;
    /// The exception class of an instruction abort at EL1.
    const INSTRUCTION_ABORT: u64 = 0x21;
    /// The fault status code of a translation fault at level 3.
    const TRANSLATION_LEVEL_3: u64 = 0x07;
    /// The fault status code of a permission fault at level 2.
    const PERMISSION_LEVEL_2: u64 = 0x0e;
    /// The fault status code of a permission fault at level 3.
    const PERMISSION_LEVEL_3: u64 = 0x0f;
    /// The fault status code, bits 0 to 5 of the syndrome.
    const FSC: u64 = 0x3f;
    /// The write bit `WnR` of the syndrome of a data abort.
    const WRITE: u64 = 1 << 6;
    /// `RET`, which the image writes into the page of its branch, so that a
    /// page that ran would return at once.
    const RET: u32 = 0xd65f_03c0;
    /// The failure bit `F` of `PAR_EL1`, bit 0.
    const PAR_FAILED: u64 = 1;
    /// The physical address of a translation in `PAR_EL1`, bits 12 to 47.
    const PAR_ADDRESS: u64 = 0x0000_ffff_ffff_f000;
    /// The first bit of the memory attribute of a translation in
    /// `PAR_EL1`, bits 56 to 63, in the encoding of `MAIR_EL1`: `0x00` for
    /// Device-nGnRnE memory.
    const PAR_ATTRIBUTE_SHIFT: u64 = 56;

    /// A fault that the next probe must take: the address of the faulting
    /// instruction, and the label at which the code resumes. A site of 0
    /// arms nothing.
    #[derive(Clone, Copy)]
    struct Armed {
        site: u64,
        resume: u64,
    }

    /// What the dispatch saw of the faults of a probe: their number, and
    /// the syndrome and the fault address of the last.
    #[derive(Clone, Copy)]
    struct Taken {
        count: u64,
        esr: u64,
        far: u64,
    }

    const DISARMED: Armed = Armed { site: 0, resume: 0 };
    const NOTHING: Taken = Taken {
        count: 0,
        esr: 0,
        far: 0,
    };

    /// The armed fault.
    static mut ARMED: Armed = DISARMED;
    /// The faults that the dispatch took since the last probe began.
    static mut TAKEN: Taken = NOTHING;

    unsafe extern "C" {
        /// Reads the word at `address` into `x1`.
        fn krepi_test_load(address: u64);
        /// Writes `value` to the word at `address`.
        fn krepi_test_store(address: u64, value: u64);
        /// Branches to `target` with the link register set, so that code at
        /// `target` that returns resumes after the branch.
        fn krepi_test_execute(target: u64);
        /// The return of `krepi_test_load`.
        static krepi_test_load_resume: u8;
        /// The return of `krepi_test_store`.
        static krepi_test_store_resume: u8;
        /// The code after the branch of `krepi_test_execute`.
        static krepi_test_execute_resume: u8;
        /// The value of the absolute symbol `krepi_test_execute_never`, the
        /// direct-map address of the page of the branch.
        static krepi_test_execute_never_word: u64;
    }

    // The entry of the image, the cold entry; the probes, whose first
    // instruction is the one that faults; the absolute symbol of the page of
    // the branch, the direct-map address of the second-last page of the RAM
    // that the runner gives QEMU virt, `[0x4000_0000, 0x4800_0000)`, and a
    // word that holds its value.
    global_asm!(
        r#"
        .section .text.krepi_test, "ax"
        .global krepi_test_entry
        .type krepi_test_entry, %function
    krepi_test_entry:
        b _start
        .size krepi_test_entry, . - krepi_test_entry

        .global krepi_test_load
        .type krepi_test_load, %function
    krepi_test_load:
        ldr x1, [x0]
        .global krepi_test_load_resume
    krepi_test_load_resume:
        ret
        .size krepi_test_load, . - krepi_test_load

        .global krepi_test_store
        .type krepi_test_store, %function
    krepi_test_store:
        str x1, [x0]
        .global krepi_test_store_resume
    krepi_test_store_resume:
        ret
        .size krepi_test_store, . - krepi_test_store

        .global krepi_test_execute
        .type krepi_test_execute, %function
    krepi_test_execute:
        stp x29, x30, [sp, #-16]!
        blr x0
        .global krepi_test_execute_resume
    krepi_test_execute_resume:
        ldp x29, x30, [sp], #16
        ret
        .size krepi_test_execute, . - krepi_test_execute

        .global krepi_test_execute_never
        .set krepi_test_execute_never, 0xffffff8047ffe000

        .section .rodata.krepi_test, "a"
        .balign 8
        .global krepi_test_execute_never_word
    krepi_test_execute_never_word:
        .quad krepi_test_execute_never
        "#
    );

    /// Reads a static of the image.
    fn load<T: Copy>(source: *const T) -> T {
        // SAFETY: `source` is a static of this image, aligned and
        // initialized; only CPU 0 runs, and the dispatch, the only other code
        // that accesses it, does not run during the read.
        unsafe { ptr::read_volatile(source) }
    }

    /// Writes a static of the image.
    fn store<T>(destination: *mut T, value: T) {
        // SAFETY: as in `load`: an aligned static of this image that no other
        // code accesses during the write.
        unsafe { ptr::write_volatile(destination, value) }
    }

    /// Reads word `index` of the usable page `page` through the direct map.
    fn read_word(page: u64, index: u64) -> u64 {
        // SAFETY: `page` is a page of a usable range of the boot memory map,
        // which the direct map maps `ReadWrite` at `DIRECT_BASE | page` and
        // which nothing else uses at boot; it belongs to no allocation of the
        // Rust program, so the pointer needs the provenance of none, and the
        // word is aligned and lies in the page.
        unsafe {
            ptr::with_exposed_provenance::<u64>((DIRECT_BASE | page) as usize + 8 * index as usize)
                .read_volatile()
        }
    }

    /// Writes word `index` of the usable page `page` through the direct map.
    fn write_word(page: u64, index: u64, value: u64) {
        // SAFETY: as in `read_word`.
        unsafe {
            ptr::with_exposed_provenance_mut::<u64>(
                (DIRECT_BASE | page) as usize + 8 * index as usize,
            )
            .write_volatile(value)
        }
    }

    /// The pattern of word `word` of the page at the physical address `pa`.
    fn pattern(pa: u64, word: u64) -> u64 {
        pa.rotate_left(17) ^ word.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ 0x4341_5358_49a5_5a5a
    }

    /// Whether the page at `page` lies in a usable range of `map`.
    fn usable(map: &MemoryPlan, page: u64) -> bool {
        let mut ranges = map.available_ranges();
        while let Some(range) = ranges.next() {
            if range.start <= page && page + PAGE <= range.start + range.size {
                return true;
            }
        }
        false
    }

    /// The checks of the edge page `page`: it lies in a usable range of
    /// `map`; after the complement of its pattern and `zero_frames`, every
    /// word reads 0; and after its pattern, every word reads it back. A page
    /// that is not usable is not touched.
    fn edge(map: &MemoryPlan, page: u64) -> [bool; 3] {
        if !usable(map, page) {
            return [false; 3];
        }
        for word in 0..WORDS {
            write_word(page, word, !pattern(page, word));
        }
        let Ok(range) = PhysRange::new(page, PAGE) else {
            return [true, false, false];
        };
        // SAFETY: the MMU is on with the direct map, which maps the usable
        // page `range` `ReadWrite`; at boot nothing else uses it, and no
        // reference to its bytes exists.
        unsafe { mmu::zero_frames(range) };
        let zero = (0..WORDS).all(|word| read_word(page, word) == 0);
        for word in 0..WORDS {
            write_word(page, word, pattern(page, word));
        }
        let back = (0..WORDS).all(|word| read_word(page, word) == pattern(page, word));
        [true, zero, back]
    }

    /// Runs `probe` with the fault at `site` armed, resuming at `resume`;
    /// what the dispatch saw.
    fn probe(site: u64, resume: u64, probe: impl FnOnce()) -> Taken {
        store(&raw mut TAKEN, NOTHING);
        store(&raw mut ARMED, Armed { site, resume });
        probe();
        store(&raw mut ARMED, DISARMED);
        load(&raw const TAKEN)
    }

    /// The checks of a fault that `taken` saw: one fault, at `address`, of
    /// the exception class `class` and the fault status code `fsc`, with the
    /// write bit `write`.
    fn fault(taken: Taken, address: u64, class: u64, fsc: u64, write: bool) -> [bool; 5] {
        [
            taken.count == 1,
            taken.far == address,
            exception_class(taken.esr) == class,
            taken.esr & FSC == fsc,
            (taken.esr & WRITE != 0) == write,
        ]
    }

    /// Reads `address` with `krepi_test_load`, which must fault: the checks
    /// of a read with a translation fault at level 3.
    fn unmapped(address: u64) -> [bool; 5] {
        let site = (krepi_test_load as *const ()).addr() as u64;
        let resume = (&raw const krepi_test_load_resume).addr() as u64;
        // SAFETY: the load reads `address` into `x1` and returns, or faults;
        // the dispatch of this image resumes a fault at its return.
        let taken = probe(site, resume, || unsafe { krepi_test_load(address) });
        fault(taken, address, DATA_ABORT, TRANSLATION_LEVEL_3, false)
    }

    /// Writes to `address`, read-only data of the image, with
    /// `krepi_test_store`, which must fault: the checks of a write with a
    /// permission fault at level 3.
    fn read_only(address: u64) -> [bool; 5] {
        let site = (krepi_test_store as *const ()).addr() as u64;
        let resume = (&raw const krepi_test_store_resume).addr() as u64;
        // SAFETY: the store faults where the kernel tables map `address`
        // read-only, as the check expects; were it mapped writable, it would
        // change one word of the image's read-only data, which nothing reads
        // afterwards. The dispatch resumes a fault at its return.
        let taken = probe(site, resume, || unsafe { krepi_test_store(address, 0) });
        fault(taken, address, DATA_ABORT, PERMISSION_LEVEL_3, true)
    }

    /// Branches to the direct-map address of the usable page `page` of
    /// `map`, which must fault: the checks that the address is the absolute
    /// symbol of the image and the page usable, and those of an instruction
    /// abort with a permission fault at level 2. Without the first two the
    /// image does not branch.
    fn execute_never(map: &MemoryPlan, page: u64) -> [bool; 7] {
        let target = DIRECT_BASE | page;
        // SAFETY: the word is the static of this image that holds the value
        // of the symbol, aligned and initialized, and nothing writes it.
        let named =
            target == unsafe { ptr::read_volatile(&raw const krepi_test_execute_never_word) };
        let usable = usable(map, page);
        let mut taken = NOTHING;
        if named && usable {
            // SAFETY: as in `write_word`; the page is usable, and the direct
            // map maps it `ReadWrite` and never executable.
            unsafe { ptr::with_exposed_provenance_mut::<u32>(target as usize).write_volatile(RET) };
            let resume = (&raw const krepi_test_execute_resume).addr() as u64;
            // SAFETY: the branch faults where the direct map does not let EL1
            // execute; were it executable, its first instruction, `RET`,
            // would return after the branch. The dispatch resumes a fault
            // there.
            taken = probe(target, resume, || unsafe { krepi_test_execute(target) });
        }
        let [one, far, class, fsc, read] =
            fault(taken, target, INSTRUCTION_ABORT, PERMISSION_LEVEL_2, false);
        [named, usable, one, far, class, fsc, read]
    }

    /// The checks of `AT S1E1W` of the registers of the PL011: the
    /// translation succeeds, to their own address, with the attribute of
    /// Device-nGnRnE memory.
    fn device_console() -> [bool; 3] {
        let par: u64;
        // SAFETY: `AT S1E1W` translates the address as a write at EL1 would,
        // with the tables of the current regime, without accessing it, and
        // writes only `PAR_EL1`, which the `ISB` completes before the read;
        // the asm touches no stack and no flags.
        unsafe {
            asm!(
                "at s1e1w, {address}",
                "isb",
                "mrs {par}, par_el1",
                address = in(reg) UART_BASE as u64,
                par = out(reg) par,
                options(nostack, preserves_flags)
            )
        };
        [
            par & PAR_FAILED == 0,
            par & PAR_ADDRESS == UART_BASE as u64,
            par >> PAR_ATTRIBUTE_SHIFT == 0x00,
        ]
    }

    /// The Rust entry of the image, which `_start` calls once on CPU 0.
    #[unsafe(no_mangle)]
    extern "C" fn kernel_main() -> ! {
        common::start("kernel-memory");
        let wired = memory::wire();
        let map = wired.memory;
        let image = wired.image;
        let tree = map.boot_ranges()[1];
        let tree_end = tree.start + tree.size;
        let block = image.image_end.next_multiple_of(BLOCK);
        let ram_end = map
            .managed_banks()
            .last()
            .map_or(0, |bank| bank.start + bank.size);
        let edges = [
            tree_end,
            image.text_start - PAGE,
            image.image_end,
            block - PAGE,
            block,
            ram_end - PAGE,
        ]
        .map(|page| edge(map, page));
        let tree_last = unmapped(DIRECT_BASE | (tree_end - PAGE));
        let image_first = unmapped(DIRECT_BASE | image.text_start);
        let rodata = read_only(image.rodata_start);
        let direct = execute_never(map, ram_end - 2 * PAGE);
        let guard = unmapped(image.stack_guard);
        let console = device_console();
        let names = [
            "p1-tree-end",
            "p2-below-image",
            "p3-above-image",
            "p4-below-block",
            "p5-first-block",
            "p6-ram-end",
        ];
        for (name, checks) in names.into_iter().zip(edges) {
            common::check(name, &checks);
        }
        common::check("p7-tree-last", &tree_last);
        common::check("p8-image-first", &image_first);
        common::check("a1-read-only", &rodata);
        common::check("a2-execute-never", &direct);
        common::check("a3-stack-guard", &guard);
        common::check("a4-device-console", &console);
        common::finish()
    }

    /// The exception dispatch of the image: a synchronous exception at the
    /// armed site is recorded and reported, and the code resumes at the
    /// armed label, once; any other exception is reported and halts, which
    /// fails the case.
    #[unsafe(no_mangle)]
    extern "C" fn exception_dispatch(frame: &mut Frame) {
        let armed = load(&raw const ARMED);
        if frame.vector != SYNC || armed.site == 0 || frame.elr != armed.site {
            uart::report_fatal(frame);
        }
        store(&raw mut ARMED, DISARMED);
        let taken = load(&raw const TAKEN);
        store(
            &raw mut TAKEN,
            Taken {
                count: taken.count + 1,
                esr: frame.esr,
                far: frame.far,
            },
        );
        uart::report_exception(frame);
        frame.elr = armed.resume;
    }
}

#[cfg(not(all(target_arch = "aarch64", target_os = "none")))]
fn main() {}
