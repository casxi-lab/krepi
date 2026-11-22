//! The QEMU boot suite of the kernel, the command `cargo xtask qemu-boot`:
//! it builds the QEMU virt default image and the test images of the kernel
//! workspace, runs its cases on QEMU virt through the QEMU runner of
//! [`crate::qemu_run`] and judges the receipt and the transcript of every
//! run against fixed expected records.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! ```sh
//! cargo xtask qemu-boot [--qemu PATH] [--output-dir OUTPUT_DIR]
//! ```
//!
//! The suite builds the images with one command,
//! `cargo build --locked --release --target aarch64-unknown-none-softfloat
//! -p krepi-qemu-virt --bin krepi-qemu-virt --example <image>...
//! --message-format=json-render-diagnostics` in `kernel/`, with an
//! `--example` for each test image of [`CASES`], with the Cargo that `CARGO`
//! names or else `cargo` from the search path, and takes each image from the
//! artifact message of its target. It records the output of `rustc -vV` in
//! `kernel/` as the toolchain. `--qemu` names the QEMU executable, as for
//! `cargo xtask qemu`.
//! The suite creates the output directory, which must not exist, with its
//! missing parents: by default `artifacts/qemu-boot/<%Y%m%dT%H%M%SZ>-<12
//! hex digits>` below the repository root. It holds `build.log`, the
//! standard error of the build, a directory `<case>-<n>` for each run, which
//! the runner fills, for the case `boot-memory` the device tree that QEMU
//! dumps, `boot-memory-tree.dtb`, with QEMU's standard error in
//! `boot-memory-tree.log`, and the suite receipt `summary.json`, with sorted
//! keys.
//!
//! The suite runs the cases of [`CASES`] in order, each run in a new QEMU
//! process with one Cortex-A76 and the host clock, on the runner's machine
//! `virt-8.2` without EL2 and EL3 or, for a test image that enters at EL2,
//! on the same machine with EL2. A run ends at its window of [`RUN_WINDOW`]
//! seconds, the platform parameter of QEMU virt for these cases, or at
//! [`RUN_MAX_BYTES`] bytes of output: no image stops by itself.
//!
//! The case `cold-boot-echo` boots the default image three times. Once the
//! transcript holds `CASXI_READY` and CR LF, the runner sends
//! `casxi-sim-check` and CR, 16 bytes. The case passes when every run shows
//! the boot records of the contract of the boot component in order, the
//! echo of the 16 bytes with a line feed after the carriage return and
//! nothing else, and when the three image digests are equal and the three
//! transcripts are identical byte for byte.
//!
//! The other cases boot a test image once each and hold its transcript
//! against an exact sequence of records: the start record of the image, the
//! exception records that the case expects, each with its vector, class,
//! syndrome and return address, and then either `CASXI_HALTED`, or the
//! self-checks of the image, each with no failure, and `CASXI_RESUMED`, or,
//! for an image whose vectors halt after its dispatch, those self-checks
//! alone; nothing else. The cases of the cache and TLB maintenance expect no
//! exception record: each passes with its start record, its self-check and
//! `CASXI_RESUMED`. The return address must be that of a symbol of the
//! image, among them an absolute symbol that names an address outside the
//! image, or lie between two of its symbols, which the suite reads from the
//! ELF file. The expected records are written here from the contract and
//! from the exception classes of the Arm Architecture Reference Manual, not
//! taken from an earlier run, and the suite judges no times.
//!
//! The case `kernel-memory` boots the test image that turns the MMU on with
//! the boot wiring of the board and expects the five faults of its probes
//! of kernel memory, each with the exception class, the fault status code
//! and the write bit of its syndrome, and then its twelve self-checks. It
//! also requires the image to start at `0x4020_0000` and to end on a page
//! boundary below `0x4040_0000`, the edge of the image that the addresses
//! of its probes assume.
//!
//! The case `boot-memory` boots the test image that writes the counts of the
//! boot wiring three times. Each transcript must hold the start record, the
//! two count records, the self-check of the stack with no failure and
//! `CASXI_RESUMED`, and the three must be identical byte for byte. The
//! counts must be those that the suite computes from the contracts of the
//! fdt and page-tables components for the runner's RAM, the link symbols of
//! the ELF file and the size of the device tree that QEMU builds for the
//! machine, which QEMU dumps with the machine option `dumpdtb` before the
//! runs, so that the expectation does not rest on the parse under test. A
//! dump that fails ends the case as an error.
//!
//! The suite exits with 0 for `PASS`, 1 for `FAIL`, 2 for `ERROR`, such as
//! a failed build or a run that could not start, and for a usage error, 130
//! for `INTERRUPTED` and 120 when it cannot write its own output, by the
//! rules of [`crate::console`]. SIGINT, SIGTERM and SIGHUP are caught from
//! immediately before the first QEMU starts, as by the runner.

use crate::console::{Console, Streams, with_process_console};
use crate::elf;
use crate::qemu::{Clock, Machine};
use crate::qemu_run::{self, Input, Options};
use crate::receipt;
use crate::report::{Value, to_json, utc_now};
use crate::serial_capture::{
    create_output, file_error, pure_path, render, run_directory, write_new,
};
use crate::timing::Timing;
use crate::{Failure, hex};
use clap::Arg;
use serde_json::json;
use sha2::{Digest, Sha256};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::atomic::AtomicI32;
use std::time::{Duration, Instant};

/// The bare-metal target of the kernel images.
pub const TARGET: &str = "aarch64-unknown-none-softfloat";
/// The board crate of QEMU virt, which holds the default image.
pub const PACKAGE: &str = "krepi-qemu-virt";
/// The binary of the QEMU virt default image.
pub const DEFAULT_IMAGE: &str = "krepi-qemu-virt";
/// The bytes that the case sends once the image is ready: the challenge of
/// the prototype's boot suite.
pub const CHALLENGE: &[u8] = b"casxi-sim-check\r";
/// The trigger of the challenge: the ready record with its CR LF.
pub const READY: &[u8] = b"CASXI_READY\r\n";
/// The cold boots of the case.
pub const RUNS: usize = 3;
/// The window of one run in seconds, a platform parameter of QEMU virt: a
/// boot to the echo takes well under a second there.
pub const RUN_WINDOW: f64 = 20.0;
/// The serial output limit of one run.
pub const RUN_MAX_BYTES: u64 = 4096;
/// The machine of the runner, which the receipt of every run of the case
/// `cold-boot-echo` must name.
pub const MACHINE: &str = "virt-8.2,secure=off,virtualization=off,gic-version=2";
/// The name of the case of the default image.
pub const CASE: &str = "cold-boot-echo";
/// The criterion of the case `cold-boot-echo`.
const CRITERION: &str = "The default image boots on QEMU virt with one Cortex-A76 into EL1, writes its CPU identity, boot and ready records, echoes the 16 bytes of the challenge with a line feed after the carriage return and nothing else, and three cold boots give equal image digests and identical transcripts";
/// The records that the transcript must hold after the CPU identity record,
/// each followed by CR LF, as the contract of the boot component writes
/// them.
const RECORDS: [&[u8]; 2] = [
    b"CASXI_BOOT kernel=krepi board=qemu-virt el=1",
    b"CASXI_READY",
];
/// The beginnings of records that no run of the case may hold.
const FATAL: [&[u8]; 4] = [
    b"CASXI_PANIC",
    b"CASXI_HALTED",
    b"CASXI_UART_FAIL",
    b"CASXI_EXCEPTION",
];
/// The variables of the environment that identify a GitHub Actions run.
const GITHUB: [&str; 5] = [
    "GITHUB_RUN_ID",
    "GITHUB_RUN_ATTEMPT",
    "GITHUB_EVENT_NAME",
    "GITHUB_REF",
    "GITHUB_SHA",
];
/// The run directories below the repository root.
const OUTPUT_DIR: &str = "artifacts/qemu-boot";
/// The standard error of the build in the output directory.
pub const BUILD_LOG: &str = "build.log";
/// The suite receipt in the output directory.
pub const SUMMARY_FILE: &str = "summary.json";
/// The name of the command in its usage and in the report of a failed
/// output write.
const PROG: &str = "cargo xtask qemu-boot";

/// What a command line asks for, apart from the help.
#[derive(Clone, Debug, PartialEq)]
pub struct SuiteOptions {
    /// `--qemu`.
    pub qemu: Option<PathBuf>,
    /// `--output-dir`.
    pub output: Option<PathBuf>,
}

fn cli() -> clap::Command {
    clap::Command::new("qemu-boot")
        .bin_name(PROG)
        .no_binary_name(true)
        .about(
            "Build the QEMU virt default image and test images and run the QEMU boot suite on them, judging every run against fixed expected records.",
        )
        .args_override_self(true)
        .arg(
            Arg::new("qemu")
                .long("qemu")
                .value_name("PATH")
                .help("QEMU executable; qemu-system-aarch64 on the search path without it"),
        )
        .arg(
            Arg::new("output-dir")
                .long("output-dir")
                .value_name("OUTPUT_DIR")
                .help("new suite directory; must not already exist"),
        )
}

/// The suite that a command line asks for, or clap's error: the help for
/// `-h` and `--help`, or a usage error.
pub fn parse(args: &[String]) -> Result<SuiteOptions, clap::Error> {
    let matches = cli().try_get_matches_from(args)?;
    let path = |name: &str| matches.get_one::<String>(name).map(PathBuf::from);
    Ok(SuiteOptions {
        qemu: path("qemu"),
        output: path("output-dir"),
    })
}

/// One check of a case: its name, whether it held and, when it did not,
/// why.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Check {
    pub name: String,
    pub failure: Option<String>,
}

impl Check {
    fn of(name: impl Into<String>, result: Result<(), Failure>) -> Self {
        Check {
            name: name.into(),
            failure: result.err().map(|Failure(message)| message),
        }
    }

    /// The entry of the suite receipt: `name`, `status` (`PASS` or `FAIL`)
    /// and, for a failed check, `detail`.
    fn report(&self) -> Value {
        match &self.failure {
            None => json!({"name": self.name, "status": "PASS"}),
            Some(detail) => json!({"name": self.name, "status": "FAIL", "detail": detail}),
        }
    }
}

/// One run of a case: the receipt that the runner returned and the bytes
/// of its transcript.
#[derive(Clone, Debug, PartialEq)]
pub struct Run {
    pub receipt: Value,
    pub transcript: Vec<u8>,
}

/// The SHA-256 digest of `bytes` in lowercase hexadecimal.
fn sha256(bytes: &[u8]) -> String {
    hex(&Sha256::digest(bytes))
}

fn require(condition: bool, message: impl FnOnce() -> String) -> Result<(), Failure> {
    if condition {
        Ok(())
    } else {
        Err(Failure::new(message()))
    }
}

/// Whether `haystack` holds `needle`.
fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    haystack
        .windows(needle.len())
        .any(|window| window == needle)
}

/// The receipt of one run of the case `cold-boot-echo` of an image with the
/// digest `image_sha256`: the checks of [`check_receipt`] on the runner's
/// machine, [`MACHINE`], and the challenge sent once after the ready record.
pub fn check_run_receipt(
    receipt: &Value,
    image_sha256: &str,
    transcript: &[u8],
) -> Result<(), Failure> {
    check_receipt(receipt, image_sha256, transcript, Machine::Virt)?;
    let input = &receipt["input"];
    let expected = json!([{
        "after": READY.escape_ascii().to_string(),
        "bytes": CHALLENGE.escape_ascii().to_string(),
    }]);
    let sent = input[0]["sent_at"].as_u64();
    let mut shown = input.clone();
    if let Some(entry) = shown.get_mut(0).and_then(Value::as_object_mut) {
        entry.remove("sent_at");
    }
    require(shown == expected && sent.is_some(), || {
        format!("the input is {input}, not the challenge sent after the ready record")
    })
}

/// The next line of `rest`, which must end in CR LF: the line without its
/// terminator and the rest after it.
fn take_line(rest: &[u8]) -> Result<(&[u8], &[u8]), Failure> {
    let Some(end) = rest.windows(2).position(|pair| pair == b"\r\n") else {
        return Err(Failure::new(format!(
            "no record line ending in CR LF in {}",
            rest.escape_ascii()
        )));
    };
    Ok((&rest[..end], &rest[end + 2..]))
}

/// The transcript of one run of the case `cold-boot-echo`, whose challenge
/// the runner sent once `sent_at` bytes of output had arrived: no fatal
/// record; the CPU identity record of a Cortex-A76, the boot record and the
/// ready record, each ending in CR LF; the challenge sent just after the
/// ready record; and after it exactly the echo of the challenge with a line
/// feed after its carriage return.
pub fn check_transcript(transcript: &[u8], sent_at: Option<u64>) -> Result<(), Failure> {
    for marker in FATAL {
        require(!contains(transcript, marker), || {
            format!(
                "the transcript holds the fatal record {}",
                marker.escape_ascii()
            )
        })?;
    }
    receipt::check_cpu_identity(transcript)?;
    let (cpu, mut rest) = take_line(transcript)?;
    require(cpu.starts_with(b"CASXI_CPU "), || {
        format!(
            "the first record is {}, not the CPU identity",
            cpu.escape_ascii()
        )
    })?;
    for expected in RECORDS {
        let (line, after) = take_line(rest)?;
        require(line == expected, || {
            format!(
                "the record {} is not {}",
                line.escape_ascii(),
                expected.escape_ascii()
            )
        })?;
        rest = after;
    }
    let ready_end = transcript.len() - rest.len();
    require(sent_at == u64::try_from(ready_end).ok(), || {
        format!(
            "the challenge was sent at byte {sent_at:?}, not just after the ready record at {ready_end}"
        )
    })?;
    let mut echo = CHALLENGE.to_vec();
    echo.push(b'\n');
    require(rest == echo.as_slice(), || {
        format!(
            "after the ready record the transcript holds {}, not {}",
            rest.escape_ascii(),
            echo.escape_ascii()
        )
    })
}

/// The checks of the case `cold-boot-echo` over its `runs` of an image with
/// the digest `image_sha256`: each run's receipt and transcript, the count of
/// runs, the equal image digests and the identical transcripts.
pub fn judge(image_sha256: &str, runs: &[Run]) -> Vec<Check> {
    let mut checks = Vec::new();
    for (index, run) in runs.iter().enumerate() {
        let number = index + 1;
        checks.push(Check::of(
            format!("run {number} receipt"),
            check_run_receipt(&run.receipt, image_sha256, &run.transcript),
        ));
        let sent_at = run.receipt["input"][0]["sent_at"].as_u64();
        checks.push(Check::of(
            format!("run {number} transcript"),
            check_transcript(&run.transcript, sent_at),
        ));
    }
    checks.push(Check::of(
        "runs",
        require(runs.len() == RUNS, || {
            format!("{} runs, not {RUNS}", runs.len())
        }),
    ));
    let digests: Vec<&Value> = runs
        .iter()
        .map(|run| &run.receipt["image"]["sha256"])
        .collect();
    checks.push(Check::of(
        "equal image digests",
        require(digests.windows(2).all(|pair| pair[0] == pair[1]), || {
            "the runs booted images with different digests".to_string()
        }),
    ));
    checks.push(Check::of(
        "identical transcripts",
        require(
            runs.windows(2)
                .all(|pair| pair[0].transcript == pair[1].transcript),
            || "the transcripts of the runs differ".to_string(),
        ),
    ));
    checks
}

/// The image that a case boots.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Image {
    /// The default image, the binary [`DEFAULT_IMAGE`].
    Default,
    /// The test image of the example with this name.
    Test(&'static str),
}

impl Image {
    /// The name of the image's Cargo target.
    pub fn target(self) -> &'static str {
        match self {
            Image::Default => DEFAULT_IMAGE,
            Image::Test(name) => name,
        }
    }
}

/// What the syndrome of an expected exception record must be.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Esr {
    /// Exactly this value.
    Exact(u64),
    /// Any value with this exception class, bits 26 to 31.
    Class(u64),
    /// Any value whose bits of the mask, the first value, are the second.
    Masked(u64, u64),
    /// Any value: the architecture does not define one.
    Any,
}

/// Where the return address of an expected exception record must be.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Elr {
    /// At the address of this symbol of the image.
    At(&'static str),
    /// At or above the first symbol and below the second.
    Within(&'static str, &'static str),
}

/// An exception record that a case expects.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Exception {
    /// The vector number.
    pub vector: u64,
    /// The class name.
    pub class: &'static str,
    /// The syndrome.
    pub esr: Esr,
    /// The return address.
    pub elr: Elr,
}

/// How the records of a test image end.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum End {
    /// `CASXI_HALTED` right after the last exception record.
    Halted,
    /// The self-checks of the image in order, then `CASXI_RESUMED`.
    Resumed(&'static [&'static str]),
    /// The self-checks of the image in order, which its dispatch writes
    /// before it returns, and nothing after them: the vectors halted.
    Silent(&'static [&'static str]),
}

/// How a case judges its runs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Judgment {
    /// The cold boots and the echo of the default image.
    ColdBootEcho,
    /// The records of a test image: the exception records in order and the
    /// end.
    Records(&'static [Exception], End),
    /// The records of the test image of kernel memory, as `Records`, and
    /// the edge of its image: `__text_start` at `0x4020_0000` and
    /// `__image_end` on a page boundary below `0x4040_0000`.
    KernelMemory(&'static [Exception], End),
    /// The records of the test image of the boot memory: its two count
    /// records, equal to the counts that the contracts give for the tree of
    /// the machine, the runner's RAM and the link symbols of the image, then
    /// the end; and the runs identical.
    BootMemory(End),
}

/// One case of the suite.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Case {
    /// The name, which also names the run directories.
    pub name: &'static str,
    /// What the case establishes.
    pub criterion: &'static str,
    /// The image that it boots.
    pub image: Image,
    /// The machine of its runs.
    pub machine: Machine,
    /// The cold boots.
    pub runs: usize,
    /// How its runs are judged.
    pub judgment: Judgment,
}

/// The cases of the suite, in the order in which it runs them.
pub const CASES: [Case; 14] = [
    Case {
        name: CASE,
        criterion: CRITERION,
        image: Image::Default,
        machine: Machine::Virt,
        runs: RUNS,
        judgment: Judgment::ColdBootEcho,
    },
    Case {
        name: "el1-brk",
        criterion: "A BRK #0xc5 at EL1 enters vector 4 and is reported with the class brk, the syndrome of EC 0x3c with the immediate and the address of the BRK; the dispatch returns past it, and the image's checks of the frame and of the return hold",
        image: Image::Test("el1-brk"),
        machine: Machine::Virt,
        runs: 1,
        judgment: Judgment::Records(
            &[Exception {
                vector: 4,
                class: "brk",
                esr: Esr::Exact(0xf200_00c5),
                elr: Elr::At("krepi_test_brk_site"),
            }],
            End::Resumed(&[
                "frame-records-interrupted-sp",
                "entry-saves-general-registers",
                "frame-records-system-registers",
                "return-restores-elr-and-pstate",
                "return-restores-sp",
            ]),
        ),
    },
    Case {
        name: "injected-serror",
        criterion: "On the machine with EL2, the virtual SError that the image's entry at EL2 makes pending through HCR_EL2.VSE enters vector 7 at EL1 once SErrors are unmasked, is reported with the class serror, a syndrome of EC 0x2f and an address in the code that unmasked it, and halts",
        image: Image::Test("injected-serror"),
        machine: Machine::VirtEl2,
        runs: 1,
        judgment: Judgment::Records(
            &[Exception {
                vector: 7,
                class: "serror",
                esr: Esr::Class(0x2f),
                elr: Elr::Within("krepi_test_serror", "krepi_test_serror_end"),
            }],
            End::Halted,
        ),
    },
    Case {
        name: "el1-fp-trap",
        criterion: "An FP/SIMD instruction at EL1 with CPACR_EL1.FPEN 0 traps to vector 4 and is reported with the class fp, a syndrome of EC 0x07 and the address of the instruction, and halts",
        image: Image::Test("el1-fp-trap"),
        machine: Machine::Virt,
        runs: 1,
        judgment: Judgment::Records(
            &[Exception {
                vector: 4,
                class: "fp",
                esr: Esr::Class(0x07),
                elr: Elr::At("krepi_test_fp_site"),
            }],
            End::Halted,
        ),
    },
    Case {
        name: "timer-irq",
        criterion: "The virtual timer interrupts through the GICv2 as interrupt 27, enters vector 5 twice while the image waits with IRQs unmasked, and is reported with the class irq and an address in the waiting code each time; the dispatch acknowledges and ends it and returns, and the image's checks of the interrupts and of the masking during the dispatch hold",
        image: Image::Test("timer-irq"),
        machine: Machine::Virt,
        runs: 1,
        judgment: Judgment::Records(
            &[WAIT_IRQ, WAIT_IRQ],
            End::Resumed(&["timer-irq", "dispatch-masks-daif"]),
        ),
    },
    Case {
        name: "irq-preserves-registers",
        criterion: "The timer interrupt taken at a known instruction is reported with the class irq and that instruction's address; after the return, x0 to x30, the stack pointer and NZCV are those of before the interrupt, and ELR_EL1 and SPSR_EL1 equal the frame's, as the image checks",
        image: Image::Test("irq-registers"),
        machine: Machine::Virt,
        runs: 1,
        judgment: Judgment::Records(
            &[Exception {
                vector: 5,
                class: "irq",
                esr: Esr::Any,
                elr: Elr::At("krepi_test_irq_resume"),
            }],
            End::Resumed(&["irq-preserves-registers"]),
        ),
    },
    Case {
        name: "sp-el0-brk",
        criterion: "A BRK #0x5e at EL1 with SP_EL0 selected enters vector 0 and is reported with the class sync, the syndrome of EC 0x3c with the immediate and the address of the BRK; the frame records the stack pointer above it on SP_EL1, as the image's check holds, and when the dispatch returns the vectors halt with nothing after its records",
        image: Image::Test("sp-el0-brk"),
        machine: Machine::Virt,
        runs: 1,
        judgment: Judgment::Records(
            &[Exception {
                vector: 0,
                class: "sync",
                esr: Esr::Exact(0xf200_005e),
                elr: Elr::At("krepi_test_sp0_site"),
            }],
            End::Silent(&["sp-el0-frame-records-sp-el1"]),
        ),
    },
    Case {
        name: "unexpected-irq",
        criterion: "The physical timer interrupts through the GICv2 as interrupt 30, which the board does not expect, enters vector 5 once while the image waits with IRQs unmasked and is reported with the class irq and an address in the waiting code; the board's handler disables and ends it, and the image's check that one interrupt came, that it was interrupt 30 and that it is disabled holds",
        image: Image::Test("unexpected-irq"),
        machine: Machine::Virt,
        runs: 1,
        judgment: Judgment::Records(&[WAIT_IRQ], End::Resumed(&["unexpected-irq-disabled"])),
    },
    Case {
        name: "clean-code-to-pou",
        criterion: "The clean of data cache lines to the point of unification runs at EL1 over a range whose ends lie inside lines of the size of CTR_EL0.DminLine and that touches more than one line, returns without an exception, and the buffer reads back unchanged, as the image checks",
        image: Image::Test("clean-code-to-pou"),
        machine: Machine::Virt,
        runs: 1,
        judgment: Judgment::Records(&[], End::Resumed(&["clean-keeps-data"])),
    },
    Case {
        name: "invalidate-to-poc",
        criterion: "With the MMU and the caches off, the invalidation of data cache lines to the point of coherency and of the instruction caches runs at EL1 over a range whose ends lie inside lines and that touches more than one line, returns without an exception, and the data written before it reads back unchanged, as the image checks",
        image: Image::Test("invalidate-to-poc"),
        machine: Machine::Virt,
        runs: 1,
        judgment: Judgment::Records(&[], End::Resumed(&["invalidate-keeps-data"])),
    },
    Case {
        name: "invalidate-tlb-page",
        criterion: "With translation tables of the image and the MMU on, a page read through a first frame is read through a second frame after its entry is replaced by break-before-make with the TLB invalidation of the page between the invalid and the new entry, without an exception, as the image checks",
        image: Image::Test("invalidate-tlb-page"),
        machine: Machine::Virt,
        runs: 1,
        judgment: Judgment::Records(&[], End::Resumed(&["remap-reads-new-frame"])),
    },
    Case {
        name: "code-publication",
        criterion: "Code written across the boundary of two instruction cache lines of the size of CTR_EL0.IminLine and published with the clean to the point of unification and the instruction cache invalidation runs and returns its value, and so does other code written and published at the same address, without an exception, as the image checks",
        image: Image::Test("code-publication"),
        machine: Machine::Virt,
        runs: 1,
        judgment: Judgment::Records(&[], End::Resumed(&["published-code-runs"])),
    },
    Case {
        name: "boot-memory",
        criterion: "Three cold boots of the test image that runs the boot wiring of the board give identical transcripts, whose count records hold the size of the device tree that QEMU dumps for the machine, one RAM bank, no firmware reservation, two spans of boot storage, one managed bank and two usable ranges, and the tables, blocks and pages that the page-tables contract gives for the lower kernel set and the direct map of the image and the tree, and whose self-check holds that the stack stayed within 48 KiB",
        image: Image::Test("boot-memory"),
        machine: Machine::Virt,
        runs: RUNS,
        judgment: Judgment::BootMemory(End::Resumed(&["stack-depth"])),
    },
    Case {
        name: "kernel-memory",
        criterion: "With the kernel tables of the boot wiring and the MMU on, the six edge pages of the usable ranges of the boot memory map read and write through the direct map, and the last page of the tree and the first page of the image are not mapped there; a write to read-only data, a branch into the direct map and a read of the guard page below the stack fault, each with the syndrome and return address of the Arm Architecture Reference Manual, and resume; the registers of the PL011 translate as Device-nGnRnE memory; the image checks each of the twelve",
        image: Image::Test("kernel-memory"),
        machine: Machine::Virt,
        runs: 1,
        judgment: Judgment::KernelMemory(
            &KERNEL_MEMORY,
            End::Resumed(&[
                "p1-tree-end",
                "p2-below-image",
                "p3-above-image",
                "p4-below-block",
                "p5-first-block",
                "p6-ram-end",
                "p7-tree-last",
                "p8-image-first",
                "a1-read-only",
                "a2-execute-never",
                "a3-stack-guard",
                "a4-device-console",
            ]),
        ),
    },
];

/// The exception record of an IRQ that a test image takes while it waits in
/// `krepi_test_wait`.
const WAIT_IRQ: Exception = Exception {
    vector: 5,
    class: "irq",
    esr: Esr::Any,
    elr: Elr::Within("krepi_test_wait", "krepi_test_wait_end"),
};

/// The bits of a syndrome that the faults of kernel memory fix: the
/// exception class, bits 26 to 31, `IL`, bit 25, `WnR`, bit 6, and the fault
/// status code, bits 0 to 5. The other bits of the ISS, such as `ISV` and
/// the register of the access, are left out: QEMU versions may fill them
/// differently.
const FAULT_BITS: u64 = 0xfe00_007f;

/// The syndrome of a data abort at EL1, EC `0x25`, with `IL` 1.
const DATA_ABORT: u64 = (0x25 << 26) | (1 << 25);

/// The syndrome of an instruction abort at EL1, EC `0x21`, with `IL` 1.
const INSTRUCTION_ABORT: u64 = (0x21 << 26) | (1 << 25);

/// A read through `krepi_test_load` of a page that no level 3 entry maps: a
/// data abort with `WnR` 0 and a translation fault at level 3, FSC `0x07`.
const UNMAPPED_READ: Exception = Exception {
    vector: 4,
    class: "sync",
    esr: Esr::Masked(FAULT_BITS, DATA_ABORT | 0x07),
    elr: Elr::At("krepi_test_load"),
};

/// The faults of the test image of kernel memory, in the order of its
/// probes: the last page of the tree and the first page of the image read
/// through the direct map; a write through `krepi_test_store` to read-only
/// data, a permission fault at level 3, FSC `0x0f`, with `WnR` 1; a branch
/// to a page of the direct map, an instruction abort with a permission fault
/// at level 2, FSC `0x0e`, whose return address is that page, the absolute
/// symbol `krepi_test_execute_never`; and the guard page below the stack.
const KERNEL_MEMORY: [Exception; 5] = [
    UNMAPPED_READ,
    UNMAPPED_READ,
    Exception {
        vector: 4,
        class: "sync",
        esr: Esr::Masked(FAULT_BITS, DATA_ABORT | (1 << 6) | 0x0f),
        elr: Elr::At("krepi_test_store"),
    },
    Exception {
        vector: 4,
        class: "sync",
        esr: Esr::Masked(FAULT_BITS, INSTRUCTION_ABORT | 0x0e),
        elr: Elr::At("krepi_test_execute_never"),
    },
    UNMAPPED_READ,
];

/// The start of the images, 2 MiB above the start of the RAM of QEMU virt,
/// where their link script puts them.
const IMAGE_BASE: u64 = 0x4020_0000;
/// A page, 4 KiB.
const PAGE: u64 = 0x1000;
/// A block of the translation tables, 2 MiB.
const BLOCK: u64 = 0x20_0000;
/// The link symbols that bound an image of kernel memory.
const EDGE_SYMBOLS: [&str; 2] = ["__text_start", "__image_end"];

/// Whether the image of `symbols` has the edge that the cases of kernel
/// memory assume: `__text_start` at [`IMAGE_BASE`] and `__image_end` on a
/// page boundary above it and below the next 2 MiB block, so that the image
/// lies in one block.
fn check_edges(symbols: &[(String, u64)]) -> Result<(), Failure> {
    let (start, end) = (
        address(symbols, EDGE_SYMBOLS[0])?,
        address(symbols, EDGE_SYMBOLS[1])?,
    );
    require(start == IMAGE_BASE, || {
        format!("the image starts at {start:#x}, not at {IMAGE_BASE:#x}")
    })?;
    require(
        end.is_multiple_of(PAGE) && start < end && end < IMAGE_BASE + BLOCK,
        || {
            format!(
                "the image ends at {end:#x}, not on a page below {:#x}",
                IMAGE_BASE + BLOCK
            )
        },
    )
}

/// The link symbols of the parts of an image, in the order of its link
/// script.
const LINK_SYMBOLS: [&str; 7] = [
    "__text_start",
    "__text_end",
    "__rodata_start",
    "__rodata_end",
    "__stack_guard",
    "__stack_bottom",
    "__image_end",
];
/// Where QEMU's loader places the device tree: the start of the RAM of
/// QEMU virt.
const TREE_BASE: u64 = 0x4000_0000;
/// The end of the 128 MiB of RAM that the runner gives QEMU virt.
const RAM_END: u64 = 0x4800_0000;
/// The largest device tree that the board takes, `MAX_BLOB_SIZE` of the
/// fdt component: 2 MiB, the room below the image.
const MAX_TREE: u64 = 0x20_0000;
/// The pages that the lower kernel set maps as Device memory: the register
/// frame of the PL011, and the distributor and the CPU interface of the
/// GICv2, 64 KiB each.
const DEVICE_PAGES: u64 = 1 + 32;
/// The count records of the test image of the boot memory.
const COUNT_RECORDS: [&str; 2] = ["CASXI_MEMORY", "CASXI_TABLES"];

/// The count records that the test image of the boot memory must write for
/// a device tree of `tree` bytes and an image with the link symbols of
/// `symbols`, by the boot memory map of the fdt contract and the table pool
/// and the direct map of the page-tables contract. The map holds the
/// runner's one RAM bank, no firmware reservation, the image and then the
/// tree as boot storage, one managed bank and two usable ranges: from the
/// end `T` of the tree's pages to the image, and from the end `E` of the
/// image to the end of RAM. The lower kernel set uses 6 tables and one for
/// each 2 MiB block that the image touches, and maps no block and the pages
/// of the image but its guard page, of the tree and of the devices. The
/// direct map uses the root, the level 2 table of the RAM and the level 3
/// tables of the blocks of `T` and of `E`, and maps the blocks from the
/// first 2 MiB boundary `B` above `E` to the end of RAM and the pages of
/// `[T, 0x4020_0000)` and `[E, B)`.
fn boot_counts(symbols: &[(String, u64)], tree: u64) -> Result<[String; 2], Failure> {
    check_edges(symbols)?;
    let mut at = [0; 7];
    for (slot, name) in at.iter_mut().zip(LINK_SYMBOLS) {
        *slot = address(symbols, name)?;
    }
    let [text, text_end, rodata, rodata_end, guard, stack, end] = at;
    require(
        at.windows(2).all(|pair| pair[0] <= pair[1])
            && guard < stack
            && at.iter().all(|bound| bound.is_multiple_of(PAGE)),
        || format!("the link symbols {at:x?} do not bound pages in the order of the link script"),
    )?;
    let tree_end = TREE_BASE + tree.next_multiple_of(PAGE);
    require((40..=MAX_TREE).contains(&tree) && tree_end < text, || {
        format!("a tree of {tree} bytes leaves no usable page below the image")
    })?;
    let pages = |start: u64, end: u64| (end - start) / PAGE;
    let block = end.next_multiple_of(BLOCK);
    let lower_tables = 6 + (text % BLOCK + end - text).div_ceil(BLOCK);
    let lower_pages = pages(text, text_end)
        + pages(rodata, rodata_end)
        + pages(rodata_end, guard)
        + pages(stack, end)
        + pages(TREE_BASE, tree_end)
        + DEVICE_PAGES;
    let direct_blocks = (RAM_END - block) / BLOCK;
    let direct_pages = pages(tree_end, text) + pages(end, block);
    Ok([
        format!("CASXI_MEMORY tree={tree} ram=1 reserved=0 boot=2 managed=1 usable=2"),
        format!(
            "CASXI_TABLES lower={lower_tables},0,{lower_pages} direct=4,{direct_blocks},{direct_pages}"
        ),
    ])
}

/// The common checks of the receipt of one run of an image with the digest
/// `image_sha256` on `machine`: no errors; ended at its window by the
/// runner; with one Cortex-A76, the host clock and no instruction count;
/// the image of the build; and a transcript of `transcript`.
pub fn check_receipt(
    receipt: &Value,
    image_sha256: &str,
    transcript: &[u8],
    machine: Machine,
) -> Result<(), Failure> {
    require(receipt.get("errors").is_none(), || {
        format!("the run has errors: {}", receipt["errors"])
    })?;
    require(receipt["exit_reason"] == "deadline", || {
        format!(
            "the run ended as {}, not at its window",
            receipt["exit_reason"]
        )
    })?;
    require(receipt["process"]["intentional_shutdown"] == true, || {
        "the runner did not stop QEMU at the window".to_string()
    })?;
    require(receipt["clock"] == "host", || {
        format!("the clock is {}, not host", receipt["clock"])
    })?;
    let command: Vec<&str> = receipt["qemu"]["command"]
        .as_array()
        .into_iter()
        .flatten()
        .filter_map(Value::as_str)
        .collect();
    let follows = |option: &str, value: &str| {
        command
            .windows(2)
            .any(|pair| pair[0] == option && pair[1] == value)
    };
    let machine = machine.option();
    require(follows("-machine", machine), || {
        format!("the QEMU command does not name the machine {machine}")
    })?;
    require(
        follows("-cpu", "cortex-a76") && follows("-smp", "1"),
        || "the QEMU command does not name one Cortex-A76".to_string(),
    )?;
    require(!command.iter().any(|arg| arg.contains("icount")), || {
        "the QEMU command holds an instruction count".to_string()
    })?;
    require(receipt["image"]["sha256"] == image_sha256, || {
        format!(
            "the image digest is {}, not that of the build, {image_sha256}",
            receipt["image"]["sha256"]
        )
    })?;
    require(
        receipt["transcript"]["sha256"] == sha256(transcript).as_str(),
        || "the receipt does not describe the transcript".to_string(),
    )
}

/// The fields of an exception record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Record {
    pub vector: u64,
    pub esr: u64,
    pub elr: u64,
    pub far: u64,
    pub spsr: u64,
    pub class: String,
}

/// The fields of the exception record `line`: `CASXI_EXCEPTION vector=<n>
/// ESR=0x<16> ELR=0x<16> FAR=0x<16> SPSR=0x<16> class=<name>`, the vector in
/// decimal without leading zeros and each register in 16 lowercase
/// hexadecimal digits.
pub fn parse_exception(line: &[u8]) -> Result<Record, Failure> {
    let wrong = || {
        Failure::new(format!(
            "{} is not an exception record of the contract's form",
            line.escape_ascii()
        ))
    };
    let text = std::str::from_utf8(line).map_err(|_| wrong())?;
    let words: Vec<&str> = text.split(' ').collect();
    let ["CASXI_EXCEPTION", vector, esr, elr, far, spsr, class] = words[..] else {
        return Err(wrong());
    };
    let decimal = |word: &str| {
        let digits = word.strip_prefix("vector=")?;
        let canonical = digits == "0" || !digits.starts_with('0');
        (canonical && !digits.is_empty() && digits.bytes().all(|b| b.is_ascii_digit()))
            .then(|| digits.parse().ok())
            .flatten()
    };
    let register = |word: &str, name: &str| {
        let digits = word.strip_prefix(name)?.strip_prefix("=0x")?;
        let lower = |b: u8| b.is_ascii_digit() || (b'a'..=b'f').contains(&b);
        (digits.len() == 16 && digits.bytes().all(lower))
            .then(|| u64::from_str_radix(digits, 16).ok())
            .flatten()
    };
    let class = class.strip_prefix("class=").filter(|name| !name.is_empty());
    Ok(Record {
        vector: decimal(vector).ok_or_else(wrong)?,
        esr: register(esr, "ESR").ok_or_else(wrong)?,
        elr: register(elr, "ELR").ok_or_else(wrong)?,
        far: register(far, "FAR").ok_or_else(wrong)?,
        spsr: register(spsr, "SPSR").ok_or_else(wrong)?,
        class: class.ok_or_else(wrong)?.to_string(),
    })
}

/// The symbols of the image that `exceptions` name, in the order of their
/// first appearance.
pub fn symbols_of(exceptions: &[Exception]) -> Vec<&'static str> {
    let mut names = Vec::new();
    for exception in exceptions {
        let pair = match exception.elr {
            Elr::At(name) => [Some(name), None],
            Elr::Within(low, high) => [Some(low), Some(high)],
        };
        for name in pair.into_iter().flatten() {
            if !names.contains(&name) {
                names.push(name);
            }
        }
    }
    names
}

/// The address of the symbol `name` in `symbols`.
fn address(symbols: &[(String, u64)], name: &str) -> Result<u64, Failure> {
    symbols
        .iter()
        .find(|(symbol, _)| symbol == name)
        .map(|(_, address)| *address)
        .ok_or_else(|| Failure::new(format!("the image has no symbol {name}")))
}

/// Whether the exception record `record` is the `expected` one of an image
/// with `symbols`: its vector, class, syndrome and return address.
pub fn check_exception(
    record: &Record,
    expected: &Exception,
    symbols: &[(String, u64)],
) -> Result<(), Failure> {
    require(record.vector == expected.vector, || {
        format!("the vector is {}, not {}", record.vector, expected.vector)
    })?;
    require(record.class == expected.class, || {
        format!("the class is {}, not {}", record.class, expected.class)
    })?;
    match expected.esr {
        Esr::Exact(esr) => require(record.esr == esr, || {
            format!("the syndrome is {:#018x}, not {esr:#018x}", record.esr)
        })?,
        Esr::Class(class) => require((record.esr >> 26) & 0x3f == class, || {
            format!(
                "the syndrome {:#018x} has not the exception class {class:#04x}",
                record.esr
            )
        })?,
        Esr::Masked(mask, value) => require(record.esr & mask == value, || {
            format!(
                "the syndrome {:#018x} has not the bits {value:#x} of the mask {mask:#x}",
                record.esr
            )
        })?,
        Esr::Any => {}
    }
    match expected.elr {
        Elr::At(name) => {
            let at = address(symbols, name)?;
            require(record.elr == at, || {
                format!(
                    "the return address is {:#018x}, not that of {name}, {at:#018x}",
                    record.elr
                )
            })
        }
        Elr::Within(low, high) => {
            let (from, to) = (address(symbols, low)?, address(symbols, high)?);
            require((from..to).contains(&record.elr), || {
                format!(
                    "the return address {:#018x} is not in [{low}, {high}) = [{from:#018x}, {to:#018x})",
                    record.elr
                )
            })
        }
    }
}

/// The lines of `transcript`, each of which must end in CR LF and hold no
/// other CR or LF.
fn record_lines(transcript: &[u8]) -> Result<Vec<&[u8]>, Failure> {
    let mut lines = Vec::new();
    let mut rest = transcript;
    while !rest.is_empty() {
        let (line, after) = take_line(rest)?;
        require(!line.contains(&b'\r') && !line.contains(&b'\n'), || {
            format!("the line {} holds a CR or an LF", line.escape_ascii())
        })?;
        lines.push(line);
        rest = after;
    }
    Ok(lines)
}

/// The count records, the exception records and the self-check records of
/// a transcript, in order, without their CR LF.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Records<'t> {
    pub counts: Vec<&'t [u8]>,
    pub exceptions: Vec<&'t [u8]>,
    pub checks: Vec<&'t [u8]>,
}

/// The count records, the exception records and the self-check records of
/// the transcript of a test image `image` that a case judges with the count
/// records `counts`, `exceptions` and `end`: the start record `CASXI_TEST
/// image=<image>`; a record of each name of `counts`, which begins with the
/// name and a space; for each expected exception an empty line and an
/// exception record; then, for [`End::Halted`], `CASXI_HALTED`, for
/// [`End::Resumed`] one `CASXI_CHECK` record of each self-check in order and
/// `CASXI_RESUMED`, or for [`End::Silent`] those self-check records alone;
/// and nothing else.
pub fn check_records<'t>(
    transcript: &'t [u8],
    image: &str,
    counts: &[&str],
    exceptions: &[Exception],
    end: End,
) -> Result<Records<'t>, Failure> {
    let lines = record_lines(transcript)?;
    let start = format!("CASXI_TEST image={image}");
    let (checks, last_record): (&[&str], Option<&[u8]>) = match end {
        End::Halted => (&[], Some(b"CASXI_HALTED")),
        End::Resumed(checks) => (checks, Some(b"CASXI_RESUMED")),
        End::Silent(checks) => (checks, None),
    };
    let expected =
        1 + counts.len() + 2 * exceptions.len() + checks.len() + usize::from(last_record.is_some());
    require(lines.len() == expected, || {
        format!(
            "the transcript has {} records, not {expected}: {}",
            lines.len(),
            transcript.escape_ascii()
        )
    })?;
    require(lines[0] == start.as_bytes(), || {
        format!(
            "the first record is {}, not {start}",
            lines[0].escape_ascii()
        )
    })?;
    let (count_lines, lines) = lines[1..].split_at(counts.len());
    for (line, name) in count_lines.iter().zip(counts) {
        require(line.starts_with(format!("{name} ").as_bytes()), || {
            format!("the record {} is not {name}", line.escape_ascii())
        })?;
    }
    let mut records = Vec::new();
    for pair in lines[..2 * exceptions.len()].chunks(2) {
        require(
            pair[0].is_empty() && pair[1].starts_with(b"CASXI_EXCEPTION "),
            || {
                format!(
                    "{} and {} are not a line break and an exception record",
                    pair[0].escape_ascii(),
                    pair[1].escape_ascii()
                )
            },
        )?;
        records.push(pair[1]);
    }
    let rest = &lines[2 * exceptions.len()..];
    let check_lines = &rest[..checks.len()];
    for (line, name) in check_lines.iter().zip(checks) {
        let prefix = format!("CASXI_CHECK name={name} failures=0x");
        require(line.starts_with(prefix.as_bytes()), || {
            format!("the record {} is not the check {name}", line.escape_ascii())
        })?;
    }
    if let Some(last_record) = last_record {
        let last = rest[checks.len()];
        require(last == last_record, || {
            format!(
                "the last record is {}, not {}",
                last.escape_ascii(),
                last_record.escape_ascii()
            )
        })?;
    }
    Ok(Records {
        counts: count_lines.to_vec(),
        exceptions: records,
        checks: check_lines.to_vec(),
    })
}

/// The checks of the runs of the test image of `case`, an image with the
/// digest `image_sha256` and `symbols` on a machine whose device tree has
/// `tree` bytes: for each run its receipt on the machine of the case,
/// without input; the records of its transcript; for the case of the boot
/// memory each count record, which must be that of [`boot_counts`]; each
/// expected exception record; and each self-check, which passes when the
/// image reports no failure; then the count of runs, for the case of kernel
/// memory the edge of its image, and for the case of the boot memory the
/// identity of the transcripts. A case of the default image is judged by
/// [`judge`].
pub fn judge_records(
    case: &Case,
    image_sha256: &str,
    symbols: &[(String, u64)],
    tree: Option<u64>,
    runs: &[Run],
) -> Vec<Check> {
    let (exceptions, end, counts) = match case.judgment {
        Judgment::ColdBootEcho => return judge(image_sha256, runs),
        Judgment::Records(exceptions, end) | Judgment::KernelMemory(exceptions, end) => {
            (exceptions, end, None)
        }
        Judgment::BootMemory(end) => {
            let unknown = || Failure::new("the size of the tree of the machine is not known");
            let expected = tree.ok_or_else(unknown);
            (
                &[][..],
                end,
                Some(expected.and_then(|tree| boot_counts(symbols, tree))),
            )
        }
    };
    let names: &[&str] = if counts.is_some() {
        &COUNT_RECORDS
    } else {
        &[]
    };
    let (image, machine) = (case.image.target(), case.machine);
    let mut checks = Vec::new();
    for (index, run) in runs.iter().enumerate() {
        let number = index + 1;
        let receipt =
            check_receipt(&run.receipt, image_sha256, &run.transcript, machine).and_then(|()| {
                require(run.receipt.get("input").is_none(), || {
                    "the run sent input to the image".to_string()
                })
            });
        checks.push(Check::of(format!("run {number} receipt"), receipt));
        let parsed = check_records(&run.transcript, image, names, exceptions, end);
        let missing = || Failure::new("the transcript does not have the record");
        checks.push(Check::of(
            format!("run {number} transcript"),
            parsed.as_ref().map(|_| ()).map_err(Clone::clone),
        ));
        if let Some(expected) = &counts {
            for (position, name) in ["memory counts", "table counts"].into_iter().enumerate() {
                let result = expected.clone().and_then(|lines| {
                    let records = parsed.as_ref().map_err(|_| missing())?;
                    let line = records.counts[position];
                    require(line == lines[position].as_bytes(), || {
                        format!(
                            "the image reports {}, not {}",
                            line.escape_ascii(),
                            lines[position]
                        )
                    })
                });
                checks.push(Check::of(format!("run {number} {name}"), result));
            }
        }
        for (position, expected) in exceptions.iter().enumerate() {
            let result = parsed
                .as_ref()
                .map_err(|_| missing())
                .and_then(|records| parse_exception(records.exceptions[position]))
                .and_then(|record| check_exception(&record, expected, symbols));
            checks.push(Check::of(
                format!("run {number} exception {}", position + 1),
                result,
            ));
        }
        if let End::Resumed(names) | End::Silent(names) = end {
            for (position, name) in names.iter().enumerate() {
                let result = parsed.as_ref().map_err(|_| missing()).and_then(|records| {
                    let line = records.checks[position];
                    let held = format!("CASXI_CHECK name={name} failures=0x{:016x}", 0);
                    require(line == held.as_bytes(), || {
                        format!("the image reports {}", line.escape_ascii())
                    })
                });
                checks.push(Check::of(format!("run {number} {name}"), result));
            }
        }
    }
    let expected = case.runs;
    checks.push(Check::of(
        "runs",
        require(runs.len() == expected, || {
            format!("{} runs, not {expected}", runs.len())
        }),
    ));
    match case.judgment {
        Judgment::KernelMemory(..) => checks.push(Check::of("image edges", check_edges(symbols))),
        Judgment::BootMemory(_) => checks.push(Check::of(
            "identical transcripts",
            require(
                runs.windows(2)
                    .all(|pair| pair[0].transcript == pair[1].transcript),
                || "the transcripts of the runs differ".to_string(),
            ),
        )),
        Judgment::ColdBootEcho | Judgment::Records(..) => {}
    }
    checks
}

/// The path of the executable of the target `target`, the default image or
/// a test image, in the messages that `cargo build
/// --message-format=json-render-diagnostics` printed: the last artifact
/// message of the target with an executable.
pub fn executable_from_messages(messages: &str, target: &str) -> Option<PathBuf> {
    messages
        .lines()
        .filter_map(|line| serde_json::from_str::<Value>(line).ok())
        .filter(|message| {
            message["reason"] == "compiler-artifact" && message["target"]["name"] == target
        })
        .filter_map(|message| message["executable"].as_str().map(PathBuf::from))
        .next_back()
}

/// The test images of [`CASES`], each once, in order.
pub fn test_images() -> Vec<&'static str> {
    let mut names = Vec::new();
    for case in &CASES {
        if let Image::Test(name) = case.image
            && !names.contains(&name)
        {
            names.push(name);
        }
    }
    names
}

/// The command that builds the default image and the test images, the
/// Cargo executable first. It selects the board crate with `-p`, the
/// default image with `--bin` and each test image with `--example`.
pub fn build_command() -> Vec<String> {
    let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());
    let mut command: Vec<String> = [
        cargo.as_str(),
        "build",
        "--locked",
        "--release",
        "--target",
        TARGET,
        "-p",
        PACKAGE,
        "--bin",
        DEFAULT_IMAGE,
    ]
    .map(str::to_string)
    .to_vec();
    for name in test_images() {
        command.extend(["--example".to_string(), name.to_string()]);
    }
    command.push("--message-format=json-render-diagnostics".to_string());
    command
}

/// Builds the images in `kernel`, writing the standard error of the build to
/// `log`: the record of the build and the messages of Cargo, or why the
/// build failed.
fn build(kernel: &Path, log: &Path) -> (Value, Result<String, Failure>) {
    let command = build_command();
    let mut record =
        json!({"command": command, "directory": "kernel", "log": BUILD_LOG, "exit_code": null});
    let output = Command::new(&command[0])
        .args(&command[1..])
        .current_dir(kernel)
        .stdin(Stdio::null())
        .output();
    let output = match output {
        Ok(output) => output,
        Err(error) => return (record, Err(file_error(Path::new(&command[0]), error))),
    };
    record["exit_code"] = output.status.code().into();
    if let Err(failure) = write_new(log, &output.stderr) {
        return (record, Err(failure));
    }
    if !output.status.success() {
        return (
            record,
            Err(Failure::new(format!(
                "the build of the images failed with {}; see {BUILD_LOG}",
                output.status
            ))),
        );
    }
    (
        record,
        Ok(String::from_utf8_lossy(&output.stdout).into_owned()),
    )
}

/// One built image: its path, size and digest.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Built {
    pub path: PathBuf,
    pub bytes: usize,
    pub sha256: String,
}

/// The image `target` of the build whose Cargo messages are `messages`.
fn built(messages: &str, target: &str) -> Result<Built, Failure> {
    let path = executable_from_messages(messages, target)
        .ok_or_else(|| Failure::new(format!("the build named no executable of {target}")))?;
    let bytes = std::fs::read(&path).map_err(|error| file_error(&path, error))?;
    Ok(Built {
        sha256: sha256(&bytes),
        bytes: bytes.len(),
        path,
    })
}

/// The lines of `rustc -vV` run in `kernel`, or null.
fn toolchain(kernel: &Path) -> Value {
    let output = Command::new("rustc")
        .arg("-vV")
        .current_dir(kernel)
        .stdin(Stdio::null())
        .output();
    match output {
        Ok(output) if output.status.success() => String::from_utf8_lossy(&output.stdout)
            .lines()
            .map(str::to_string)
            .collect::<Vec<_>>()
            .into(),
        _ => Value::Null,
    }
}

/// The commit that `git rev-parse HEAD` names in `root`, or null.
fn commit(root: &Path) -> Value {
    let output = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .current_dir(root)
        .stdin(Stdio::null())
        .output();
    match output {
        Ok(output) if output.status.success() => {
            String::from_utf8_lossy(&output.stdout).trim().into()
        }
        _ => Value::Null,
    }
}

/// How the runs of a case ended.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    /// Every run ran and every check held.
    Pass,
    /// Every run ran, and a check failed.
    Fail,
    /// A run could not run.
    Error,
    /// An interrupt ended a run.
    Interrupted,
}

impl Outcome {
    /// The status that the suite receipt records.
    pub fn name(self) -> &'static str {
        match self {
            Outcome::Pass => "PASS",
            Outcome::Fail => "FAIL",
            Outcome::Error => "ERROR",
            Outcome::Interrupted => "INTERRUPTED",
        }
    }

    /// The exit status of the suite.
    pub fn code(self) -> i32 {
        match self {
            Outcome::Pass => 0,
            Outcome::Fail => 1,
            Outcome::Error => 2,
            Outcome::Interrupted => 130,
        }
    }
}

/// The image that a case runs: its path, its digest and the addresses of
/// the symbols that the case needs.
#[derive(Clone, Copy, Debug)]
pub struct Subject<'s> {
    pub image: &'s Path,
    pub sha256: &'s str,
    pub symbols: &'s [(String, u64)],
    /// The size of the device tree of the machine of the case, which the
    /// case of the boot memory needs.
    pub tree: Option<u64>,
}

/// The input of each run of `case`: the challenge after the ready record
/// for the case of the default image, and none for the cases of the test
/// images.
pub fn case_inputs(case: &Case) -> Vec<Input> {
    match case.judgment {
        Judgment::ColdBootEcho => vec![Input {
            after: READY.to_vec(),
            bytes: CHALLENGE.to_vec(),
        }],
        Judgment::Records(..) | Judgment::KernelMemory(..) | Judgment::BootMemory(_) => Vec::new(),
    }
}

/// Runs `case` on the image of `subject` with the QEMU `qemu`, each run
/// into `<output>/<case>-<n>`; the entry of the case in the suite receipt
/// and its outcome. `progress` gets a line for each run. A run that the
/// runner cannot start ends the case as `Error`, and an interrupted run as
/// `Interrupted`, without the runs after it.
pub fn run_case<'a>(
    case: &Case,
    subject: Subject<'_>,
    qemu: Option<&Path>,
    output: &Path,
    timing: &Timing,
    arm: &mut dyn FnMut() -> Result<&'a AtomicI32, Failure>,
    progress: &mut dyn FnMut(&str),
) -> (Value, Outcome) {
    let options = Options {
        image: subject.image.to_path_buf(),
        timeout: RUN_WINDOW,
        max_bytes: RUN_MAX_BYTES,
        clock: Clock::Host,
        qemu: qemu.map(Path::to_path_buf),
        output: None,
    };
    let inputs = case_inputs(case);
    let mut runs = Vec::new();
    let mut entries = Vec::new();
    let mut stopped = None;
    for number in 1..=case.runs {
        let name = format!("{}-{number}", case.name);
        let directory = output.join(&name);
        let result =
            qemu_run::run_image_on(case.machine, &options, &inputs, &directory, timing, arm);
        let receipt = match result {
            Ok(receipt) => receipt,
            Err(Failure(error)) => {
                progress(&format!(
                    "{name}: the run could not start: {}",
                    render(&error)
                ));
                entries.push(json!({"directory": name, "error": error}));
                stopped = Some(Outcome::Error);
                break;
            }
        };
        let transcript =
            std::fs::read(directory.join(qemu_run::TRANSCRIPT_FILE)).unwrap_or_default();
        let reason = receipt["exit_reason"]
            .as_str()
            .unwrap_or("error")
            .to_string();
        progress(&format!(
            "{name}: {reason}, {} bytes of serial output",
            transcript.len()
        ));
        entries.push(json!({
            "directory": name,
            "exit_reason": reason,
            "receipt_sha256": sha256(to_json(&receipt).as_bytes()),
            "transcript_sha256": sha256(&transcript),
        }));
        runs.push(Run {
            receipt,
            transcript,
        });
        if reason == "interrupted" {
            stopped = Some(Outcome::Interrupted);
            break;
        }
    }
    let checks = judge_records(case, subject.sha256, subject.symbols, subject.tree, &runs);
    let outcome = stopped.unwrap_or(if checks.iter().all(|check| check.failure.is_none()) {
        Outcome::Pass
    } else {
        Outcome::Fail
    });
    let entry = json!({
        "name": case.name,
        "criterion": case.criterion,
        "image": case.image.target(),
        "machine": case.machine.option(),
        "status": outcome.name(),
        "runs": entries,
        "checks": checks.iter().map(Check::report).collect::<Vec<_>>(),
    });
    (entry, outcome)
}

/// The outcome of a suite whose cases ended as `outcomes`: `Interrupted`
/// if one was, else `Error` if one was, else `Fail` if one failed, else
/// `Pass`.
pub fn suite_outcome(outcomes: &[Outcome]) -> Outcome {
    [Outcome::Interrupted, Outcome::Error, Outcome::Fail]
        .into_iter()
        .find(|worst| outcomes.contains(worst))
        .unwrap_or(Outcome::Pass)
}

/// The size of the device tree that QEMU builds for the machine of `case`
/// with the image `image`: the QEMU `qemu`, run with the arguments of a run
/// of the case and with `dumpdtb=<directory>/<case>-tree.dtb` added to the
/// machine, writes the tree into that file and exits, its standard error in
/// `<case>-tree.log`; the size is the `totalsize` of the header of the tree.
/// The dump is no run of the case and has no receipt. QEMU must exit with 0
/// within [`RUN_WINDOW`] seconds and write a tree, or the dump fails.
pub fn machine_tree(
    case: &Case,
    image: &Path,
    qemu: Option<&Path>,
    directory: &Path,
) -> Result<u64, Failure> {
    let file = directory.join(format!("{}-tree.dtb", case.name));
    let log = directory.join(format!("{}-tree.log", case.name));
    let mut command = crate::qemu::build_command_on(image, qemu, Clock::Host, case.machine)?;
    let dump = format!("{},dumpdtb={}", case.machine.option(), file.display());
    for argument in command
        .iter_mut()
        .filter(|arg| *arg == case.machine.option())
    {
        argument.clone_from(&dump);
    }
    let stderr = std::fs::File::create_new(&log).map_err(|error| file_error(&log, error))?;
    let mut child = Command::new(&command[0])
        .args(&command[1..])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(stderr)
        .spawn()
        .map_err(|error| file_error(Path::new(&command[0]), error))?;
    let deadline = Instant::now() + Duration::from_secs_f64(RUN_WINDOW);
    let status = loop {
        if let Some(status) = child.try_wait()? {
            break status;
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            let _ = child.wait();
            return Err(Failure::new("QEMU did not exit after the dump of the tree"));
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    require(status.success(), || {
        format!(
            "the dump of the tree failed with {status}; see {}",
            log.display()
        )
    })?;
    let tree = std::fs::read(&file).map_err(|error| file_error(&file, error))?;
    require(
        tree.len() >= 8 && tree[..4] == [0xd0, 0x0d, 0xfe, 0xed],
        || format!("{} holds no device tree", file.display()),
    )?;
    let size = u64::from(u32::from_be_bytes([tree[4], tree[5], tree[6], tree[7]]));
    require(size <= tree.len() as u64, || {
        format!("the tree of {size} bytes is longer than its dump")
    })?;
    Ok(size)
}

/// A lookup of a symbol in an ELF file.
type Lookup = fn(&Path, &str) -> Result<u64, Failure>;

/// The symbols that `case` needs from its image, read from the ELF file
/// `image`: those of its exception records, each in its section or
/// absolute, and the link symbols of the edge of the image for the case of
/// kernel memory and of all its parts for the case of the boot memory, which
/// may end their section.
fn case_symbols(case: &Case, image: &Path) -> Result<Vec<(String, u64)>, Failure> {
    let (sites, bounds) = match case.judgment {
        Judgment::ColdBootEcho => (Vec::new(), Vec::new()),
        Judgment::Records(exceptions, _) => (symbols_of(exceptions), Vec::new()),
        Judgment::KernelMemory(exceptions, _) => (symbols_of(exceptions), EDGE_SYMBOLS.to_vec()),
        Judgment::BootMemory(_) => (Vec::new(), LINK_SYMBOLS.to_vec()),
    };
    let lookups: [(Vec<&str>, Lookup); 2] =
        [(sites, elf::symbol_address), (bounds, elf::bound_address)];
    let mut symbols = Vec::new();
    for (names, lookup) in lookups {
        for name in names {
            let address = lookup(image, name)
                .map_err(|Failure(error)| Failure::new(format!("{name}: {error}")))?;
            symbols.push((name.to_string(), address));
        }
    }
    Ok(symbols)
}

/// The command entry point: the lines go to the standard streams, the
/// interrupt handlers are installed immediately before the first QEMU
/// starts, and the runs wait as `Timing::QEMU_VIRT` gives. Returns the exit
/// status of the process.
pub fn main(root: &Path, args: &[String]) -> i32 {
    with_process_console(|console| run_with(root, args, &Timing::QEMU_VIRT, console))
}

/// [`main`] with the time values `timing` and the streams and interrupt
/// handlers of `console`.
pub fn run_with(root: &Path, args: &[String], timing: &Timing, console: &mut Console) -> i32 {
    let mut streams = Streams::new(PROG, console);
    let code = run(root, args, timing, &mut streams);
    streams.exit(code)
}

fn run(root: &Path, args: &[String], timing: &Timing, streams: &mut Streams) -> i32 {
    let options = match parse(args) {
        Ok(options) => options,
        Err(error) => return streams.clap_error(&error),
    };
    let output = pure_path(
        &options
            .output
            .clone()
            .unwrap_or_else(|| run_directory(root, OUTPUT_DIR)),
    );
    if let Err(Failure(error)) = create_output(&output) {
        streams.warn(&format!("QEMU boot suite failed: {}", render(&error)));
        return 2;
    }
    let started_at = utc_now();
    let kernel = root.join("kernel");
    let mut report = json!({
        "schema_version": 1,
        "started_at": started_at,
        "commit": commit(root),
        "github": GITHUB.iter().map(|name| (name.to_string(), std::env::var(name).ok().into())).collect::<serde_json::Map<String, Value>>(),
        "toolchain": toolchain(&kernel),
        "images": null,
        "cases": [],
    });
    let (build_record, messages) = build(&kernel, &output.join(BUILD_LOG));
    report["build"] = build_record;
    let targets = std::iter::once(DEFAULT_IMAGE).chain(test_images());
    let images = messages.and_then(|messages| {
        targets
            .map(|target| Ok((target, built(&messages, target)?)))
            .collect::<Result<Vec<_>, Failure>>()
    });
    let outcome = match images {
        Err(Failure(error)) => {
            streams.warn(&format!("QEMU boot suite failed: {}", render(&error)));
            report["errors"] = json!([error]);
            Outcome::Error
        }
        Ok(images) => {
            report["images"] = images
                .iter()
                .map(|(target, image)| {
                    let entry = json!({
                        "path": image.path.to_string_lossy(),
                        "bytes": image.bytes,
                        "sha256": image.sha256,
                    });
                    (target.to_string(), entry)
                })
                .collect::<serde_json::Map<String, Value>>()
                .into();
            let mut cases = Vec::new();
            let mut outcomes = Vec::new();
            for case in &CASES {
                let (_, image) = images
                    .iter()
                    .find(|(target, _)| *target == case.image.target())
                    .expect("every image of a case is built");
                let mut lines = Vec::new();
                let facts = case_symbols(case, &image.path).and_then(|symbols| {
                    let tree = match case.judgment {
                        Judgment::BootMemory(_) => Some(machine_tree(
                            case,
                            &image.path,
                            options.qemu.as_deref(),
                            &output,
                        )?),
                        _ => None,
                    };
                    Ok((symbols, tree))
                });
                let (entry, outcome) = match facts {
                    Err(Failure(error)) => {
                        lines.push(format!("{}: {}", case.name, render(&error)));
                        let entry = json!({
                            "name": case.name,
                            "criterion": case.criterion,
                            "status": Outcome::Error.name(),
                            "error": error,
                        });
                        (entry, Outcome::Error)
                    }
                    Ok((symbols, tree)) => run_case(
                        case,
                        Subject {
                            image: &image.path,
                            sha256: &image.sha256,
                            symbols: &symbols,
                            tree,
                        },
                        options.qemu.as_deref(),
                        &output,
                        timing,
                        streams.console.arm,
                        &mut |line| lines.push(line.to_string()),
                    ),
                };
                for line in &lines {
                    streams.print(line);
                }
                cases.push(entry);
                outcomes.push(outcome);
                if outcome == Outcome::Interrupted {
                    break;
                }
            }
            report["cases"] = cases.into();
            suite_outcome(&outcomes)
        }
    };
    report["status"] = outcome.name().into();
    report["finished_at"] = utc_now().into();
    report.sort_all_objects();
    if let Err(Failure(error)) = write_new(&output.join(SUMMARY_FILE), to_json(&report).as_bytes())
    {
        streams.warn(&format!("QEMU boot suite failed: {}", render(&error)));
        return 2;
    }
    for check in report["cases"]
        .as_array()
        .into_iter()
        .flatten()
        .flat_map(|case| case["checks"].as_array().into_iter().flatten())
        .filter(|check| check["status"] == "FAIL")
    {
        streams.print(&format!(
            "FAILED {}: {}",
            check["name"].as_str().unwrap_or_default(),
            check["detail"].as_str().unwrap_or_default()
        ));
    }
    let summary = std::fs::canonicalize(&output)
        .unwrap_or_else(|_| output.clone())
        .join(SUMMARY_FILE);
    streams.print(&format!("{}: {}", outcome.name(), summary.display()));
    outcome.code()
}

#[cfg(test)]
mod tests;
