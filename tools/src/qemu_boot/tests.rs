//! The tests of the QEMU boot suite: the checks of the cases against
//! hand-written receipts and transcripts, the images of the build, the
//! command line, and runs of a case with a fake QEMU.
//!
//! Feature: krepi.platform.qemu-virt-boot

use super::*;
use crate::TEST_WAIT;
use crate::qemu_run::seams::DEADLINE_AT;
use crate::scratch::Scratch;

/// The time values of a run under test: those of QEMU virt, with bounds for
/// the final collection and the end of the process that a slow host never
/// reaches.
const TIMING: Timing = Timing {
    guest_finish: TEST_WAIT,
    stop_grace: TEST_WAIT,
    kill_grace: TEST_WAIT,
    ..Timing::QEMU_VIRT
};

/// The CPU identity record of the Cortex-A76 r4p1 that QEMU models, whose
/// `MIDR_EL1` is `0x414fd0b1` (Cortex-A76 Technical Reference Manual).
const CPU: &[u8] = b"CASXI_CPU model=cortex-a76 midr=0x00000000414fd0b1\r\n";
/// The boot and ready records of the contract of the boot component.
const BOOT: &[u8] = b"CASXI_BOOT kernel=krepi board=qemu-virt el=1\r\n";
const READY_LINE: &[u8] = b"CASXI_READY\r\n";
/// The echo of the challenge: its 16 bytes and a line feed.
const ECHO: &[u8] = b"casxi-sim-check\r\n";
/// A digest that stands for that of the built image.
const IMAGE_SHA256: &str = "1111111111111111111111111111111111111111111111111111111111111111";

/// The transcript of a good run.
fn good_transcript() -> Vec<u8> {
    [CPU, BOOT, READY_LINE, ECHO].concat()
}

/// The output offset just after the ready record of a good run.
fn ready_end() -> u64 {
    (CPU.len() + BOOT.len() + READY_LINE.len()) as u64
}

/// The receipt that the runner gives for a good run with `transcript`.
fn good_receipt(transcript: &[u8]) -> Value {
    json!({
        "schema_version": 1,
        "exit_reason": "deadline",
        "clock": "host",
        "image": {"path": "/x/krepi-qemu-virt", "bytes": 4, "sha256": IMAGE_SHA256},
        "qemu": {
            "executable": "/usr/bin/qemu-system-aarch64",
            "version": "QEMU emulator version 8.2.2",
            "command": [
                "/usr/bin/qemu-system-aarch64", "-accel", "tcg,thread=single",
                "-machine", MACHINE, "-cpu", "cortex-a76", "-smp", "1", "-m", "128M",
                "-nic", "none", "-display", "none", "-serial", "stdio", "-monitor", "none",
                "-kernel", "/x/krepi-qemu-virt",
            ],
        },
        "process": {"exit_code": null, "forced_kill": false, "intentional_shutdown": true, "signal": 15},
        "transcript": {"file": "transcript.bin", "bytes": transcript.len(), "sha256": sha256(transcript)},
        "input": [{"after": "CASXI_READY\\r\\n", "bytes": "casxi-sim-check\\r", "sent_at": ready_end()}],
    })
}

fn good_run() -> Run {
    let transcript = good_transcript();
    Run {
        receipt: good_receipt(&transcript),
        transcript,
    }
}

/// The names of the checks that failed.
fn failed(checks: &[Check]) -> Vec<&str> {
    checks
        .iter()
        .filter(|check| check.failure.is_some())
        .map(|check| check.name.as_str())
        .collect()
}

mod receipts {
    use super::*;

    /// A change of a good receipt.
    type Change = fn(&mut Value);

    /// Three runs that each show the records and the echo, of the same image
    /// and with the same transcript, pass every check.
    #[test]
    fn three_good_runs_pass() {
        let checks = judge(IMAGE_SHA256, &[good_run(), good_run(), good_run()]);
        assert_eq!(failed(&checks), Vec::<&str>::new());
        let names: Vec<&str> = checks.iter().map(|check| check.name.as_str()).collect();
        assert_eq!(
            names,
            [
                "run 1 receipt",
                "run 1 transcript",
                "run 2 receipt",
                "run 2 transcript",
                "run 3 receipt",
                "run 3 transcript",
                "runs",
                "equal image digests",
                "identical transcripts",
            ]
        );
    }

    /// A transcript whose records are missing, reordered or changed fails.
    #[test]
    fn missing_reordered_or_changed_records_fail() {
        let el2 = b"CASXI_BOOT kernel=krepi board=qemu-virt el=2\r\n";
        let other_board = b"CASXI_BOOT kernel=krepi board=pi5 el=1\r\n";
        let a77 = b"CASXI_CPU model=cortex-a76 midr=0x00000000414fd0d1\r\n";
        for transcript in [
            [BOOT, READY_LINE, ECHO].concat(),
            [CPU, READY_LINE, ECHO].concat(),
            [CPU, BOOT, ECHO].concat(),
            [CPU, READY_LINE, BOOT, ECHO].concat(),
            [CPU, el2, READY_LINE, ECHO].concat(),
            [CPU, other_board, READY_LINE, ECHO].concat(),
            [a77, BOOT, READY_LINE, ECHO].concat(),
            [CPU, CPU, BOOT, READY_LINE, ECHO].concat(),
            [
                CPU,
                b"CASXI_BOOT kernel=krepi board=qemu-virt el=1\n",
                READY_LINE,
                ECHO,
            ]
            .concat(),
        ] {
            let sent_at = Some(ready_end());
            assert!(
                check_transcript(&transcript, sent_at).is_err(),
                "{}",
                transcript.escape_ascii()
            );
        }
    }

    /// A missing, partial or changed echo, an echo without the line feed and
    /// bytes beyond the echo fail.
    #[test]
    fn anything_but_the_exact_echo_fails() {
        for echo in [
            &b""[..],
            b"casxi-sim-check",
            b"casxi-sim-check\r",
            b"casxi-sim-chec\r\n",
            b"casxi-sim-check\n",
            b"casxi-sim-check\r\n\r\n",
            b"casxi-sim-check\r\nmore",
        ] {
            let transcript = [CPU, BOOT, READY_LINE, echo].concat();
            let result = check_transcript(&transcript, Some(ready_end()));
            assert!(result.is_err(), "{}", echo.escape_ascii());
        }
    }

    /// A fatal record anywhere in the transcript fails, also after the echo.
    #[test]
    fn a_fatal_record_fails() {
        for fatal in [
            &b"CASXI_PANIC BSS not initialized\r\n"[..],
            b"CASXI_HALTED\r\n",
            b"\r\nCASXI_UART_FAIL reason=stalled\r\n",
            b"CASXI_EXCEPTION vector=4\r\n",
        ] {
            let transcript = [CPU, BOOT, READY_LINE, ECHO, fatal].concat();
            let error = check_transcript(&transcript, Some(ready_end())).unwrap_err();
            assert!(error.0.contains("fatal record"), "{error}");
        }
    }

    /// The challenge must have been sent just after the ready record: one
    /// sent before or after it, or not at all, fails.
    #[test]
    fn a_challenge_sent_at_another_point_fails() {
        let transcript = good_transcript();
        for sent_at in [None, Some(0), Some(ready_end() - 1), Some(ready_end() + 1)] {
            assert!(
                check_transcript(&transcript, sent_at).is_err(),
                "{sent_at:?}"
            );
        }
        assert_eq!(check_transcript(&transcript, Some(ready_end())), Ok(()));
    }

    /// A receipt with errors, another exit reason, a run that the runner did
    /// not stop, another clock, machine or CPU, an instruction count, another
    /// image, a transcript that it does not describe or another input fails.
    #[test]
    fn weakened_or_misattributed_receipts_fail() {
        let transcript = good_transcript();
        let changes: [(&str, Change); 13] = [
            ("errors", |r| r["errors"] = json!(["send of input 1: x"])),
            ("guest_shutdown", |r| {
                r["exit_reason"] = json!("guest_shutdown")
            }),
            ("output_limit", |r| r["exit_reason"] = json!("output_limit")),
            ("not stopped", |r| {
                r["process"]["intentional_shutdown"] = json!(false)
            }),
            ("icount clock", |r| r["clock"] = json!("icount")),
            ("machine", |r| {
                r["qemu"]["command"][4] = json!("virt,secure=off,virtualization=on,gic-version=2")
            }),
            ("cpu", |r| r["qemu"]["command"][6] = json!("cortex-a72")),
            ("smp", |r| r["qemu"]["command"][8] = json!("2")),
            ("icount", |r| {
                let command = r["qemu"]["command"].as_array_mut().unwrap();
                command.insert(3, json!("-icount"));
                command.insert(4, json!("shift=3,align=off,sleep=off"));
            }),
            ("image", |r| r["image"]["sha256"] = json!("2".repeat(64))),
            ("transcript", |r| {
                r["transcript"]["sha256"] = json!("3".repeat(64))
            }),
            ("input bytes", |r| {
                r["input"][0]["bytes"] = json!("casxi-sim-check")
            }),
            ("not sent", |r| r["input"][0]["sent_at"] = Value::Null),
        ];
        assert_eq!(
            check_run_receipt(&good_receipt(&transcript), IMAGE_SHA256, &transcript),
            Ok(())
        );
        for (name, change) in changes {
            let mut receipt = good_receipt(&transcript);
            change(&mut receipt);
            assert!(
                check_run_receipt(&receipt, IMAGE_SHA256, &transcript).is_err(),
                "{name}"
            );
        }
        let mut receipt = good_receipt(&transcript);
        receipt.as_object_mut().unwrap().remove("input");
        assert!(check_run_receipt(&receipt, IMAGE_SHA256, &transcript).is_err());
    }

    /// Runs whose transcripts differ, whose images differ or that are too
    /// few fail the checks across the runs, even when each run passes alone.
    #[test]
    fn runs_that_differ_or_are_too_few_fail() {
        let mut other = good_run();
        other.transcript = [
            &b"CASXI_CPU model=cortex-a76 midr=0x00000000414fd0b2\r\n"[..],
            BOOT,
            READY_LINE,
            ECHO,
        ]
        .concat();
        other.receipt = good_receipt(&other.transcript);
        assert_eq!(
            check_transcript(&other.transcript, Some(ready_end())),
            Ok(())
        );
        let checks = judge(IMAGE_SHA256, &[good_run(), other, good_run()]);
        assert_eq!(failed(&checks), ["identical transcripts"]);

        let mut rebuilt = good_run();
        rebuilt.receipt["image"]["sha256"] = json!("4".repeat(64));
        let checks = judge(IMAGE_SHA256, &[good_run(), good_run(), rebuilt]);
        assert_eq!(failed(&checks), ["run 3 receipt", "equal image digests"]);

        let checks = judge(IMAGE_SHA256, &[good_run(), good_run()]);
        assert_eq!(failed(&checks), ["runs"]);
    }
}

/// The executable of an image is that of the last artifact message of its
/// target; other messages and lines are ignored.
#[test]
fn the_image_is_taken_from_the_artifact_message() {
    let messages = concat!(
        "{\"reason\":\"compiler-artifact\",\"target\":{\"name\":\"krepi_arch\"},\"executable\":null}\n",
        "not JSON\n",
        "{\"reason\":\"build-script-executed\",\"package_id\":\"x\"}\n",
        "{\"reason\":\"compiler-artifact\",\"target\":{\"name\":\"krepi-qemu-virt\"},\"executable\":\"/w/kernel/target/aarch64-unknown-none-softfloat/release/krepi-qemu-virt\"}\n",
        "{\"reason\":\"compiler-artifact\",\"target\":{\"name\":\"el1-brk\"},\"executable\":\"/w/kernel/target/aarch64-unknown-none-softfloat/release/examples/el1-brk\"}\n",
        "{\"reason\":\"build-finished\",\"success\":true}\n",
    );
    assert_eq!(
        executable_from_messages(messages, DEFAULT_IMAGE),
        Some(PathBuf::from(
            "/w/kernel/target/aarch64-unknown-none-softfloat/release/krepi-qemu-virt"
        ))
    );
    assert_eq!(
        executable_from_messages(messages, "el1-brk"),
        Some(PathBuf::from(
            "/w/kernel/target/aarch64-unknown-none-softfloat/release/examples/el1-brk"
        ))
    );
    assert_eq!(
        executable_from_messages("{\"reason\":\"build-finished\"}\n", DEFAULT_IMAGE),
        None
    );
}

/// The build command builds the default image and each test image of the
/// board crate once, from the lock and in release, for the bare-metal
/// target.
#[test]
fn the_build_command_names_the_images() {
    let command = build_command();
    assert_eq!(
        command[1..],
        [
            "build",
            "--locked",
            "--release",
            "--target",
            "aarch64-unknown-none-softfloat",
            "-p",
            "krepi-qemu-virt",
            "--bin",
            "krepi-qemu-virt",
            "--example",
            "el1-brk",
            "--example",
            "injected-serror",
            "--example",
            "el1-fp-trap",
            "--example",
            "timer-irq",
            "--example",
            "irq-registers",
            "--example",
            "sp-el0-brk",
            "--example",
            "unexpected-irq",
            "--example",
            "clean-code-to-pou",
            "--example",
            "invalidate-to-poc",
            "--example",
            "invalidate-tlb-page",
            "--example",
            "code-publication",
            "--message-format=json-render-diagnostics",
        ]
    );
}

/// The command line takes `--qemu` and `--output-dir`; `--help` is the
/// help, and an unknown option or an argument is a usage error.
#[test]
fn the_command_line_takes_its_two_options() {
    let args = |args: &[&str]| args.iter().map(|arg| arg.to_string()).collect::<Vec<_>>();
    assert_eq!(
        parse(&args(&["--qemu", "/q", "--output-dir=out"])).unwrap(),
        SuiteOptions {
            qemu: Some(PathBuf::from("/q")),
            output: Some(PathBuf::from("out")),
        }
    );
    assert_eq!(
        parse(&[]).unwrap(),
        SuiteOptions {
            qemu: None,
            output: None,
        }
    );
    let help = parse(&args(&["--help"])).unwrap_err();
    assert_eq!(help.kind(), clap::error::ErrorKind::DisplayHelp);
    assert!(help.to_string().contains("Usage: cargo xtask qemu-boot"));
    for wrong in [&["--timeout", "5"][..], &["image.elf"]] {
        assert_ne!(
            parse(&args(wrong)).unwrap_err().kind(),
            clap::error::ErrorKind::DisplayHelp
        );
    }
}

/// Restores the deadline of the runs of this thread.
struct DeadlineAt;

impl DeadlineAt {
    fn new(marker: &'static [u8]) -> Self {
        DEADLINE_AT.set(Some(marker));
        DeadlineAt
    }
}

impl Drop for DeadlineAt {
    fn drop(&mut self) {
        DEADLINE_AT.set(None);
    }
}

/// A fake QEMU that answers `--version` and otherwise writes the records
/// with `boot` in place of the boot record, then echoes the 16 bytes that
/// it reads and a line feed, and runs until it is stopped.
fn fake_qemu(scratch: &Scratch, boot: &str) -> PathBuf {
    scratch.script(
        "qemu",
        &format!(
            "#!/bin/sh\nif [ \"$1\" = --version ]; then\n  echo 'QEMU emulator version 0.0.0'\n  exit 0\nfi\n\
             printf 'CASXI_CPU model=cortex-a76 midr=0x00000000414fd0b1\\r\\n'\n\
             printf '{boot}\\r\\n'\nprintf 'CASXI_READY\\r\\n'\n\
             input=$(dd bs=1 count=16 2>/dev/null)\nprintf '%s\\n' \"$input\"\nexec cat\n"
        ),
    )
}

/// The case runs the image three times through the runner, each run into
/// a directory of its own, and passes with a QEMU that behaves as the
/// default image should. The deadline of each run passes once the echo has
/// arrived, in place of the window.
#[test]
fn the_case_passes_with_a_guest_that_boots_and_echoes() {
    let scratch = Scratch::new("qemu-boot-pass");
    let qemu = fake_qemu(&scratch, "CASXI_BOOT kernel=krepi board=qemu-virt el=1");
    let image = scratch.write("image.elf", b"not an ELF image\n");
    let digest = sha256(b"not an ELF image\n");
    let output = scratch.path("suite");
    std::fs::create_dir(&output).unwrap();
    let _deadline = DeadlineAt::new(ECHO);
    let mut lines = Vec::new();
    let flag: &'static AtomicI32 = Box::leak(Box::new(AtomicI32::new(0)));
    let (entry, outcome) = run_case(
        &CASES[0],
        Subject {
            image: &image,
            sha256: &digest,
            symbols: &[],
        },
        Some(&qemu),
        &output,
        &TIMING,
        &mut || Ok(flag),
        &mut |line| lines.push(line.to_string()),
    );
    assert_eq!(outcome, Outcome::Pass, "{entry}");
    assert_eq!(entry["status"], "PASS");
    assert_eq!(entry["runs"].as_array().unwrap().len(), RUNS);
    for number in 1..=RUNS {
        let directory = output.join(format!("{CASE}-{number}"));
        assert_eq!(
            std::fs::read(directory.join(qemu_run::TRANSCRIPT_FILE)).unwrap(),
            good_transcript()
        );
        assert!(directory.join(qemu_run::SUMMARY_FILE).is_file());
    }
    assert_eq!(
        lines,
        (1..=RUNS)
            .map(|n| format!(
                "{CASE}-{n}: deadline, {} bytes of serial output",
                good_transcript().len()
            ))
            .collect::<Vec<_>>()
    );
}

/// A guest that reports another exception level fails the case, and the
/// failed check names the transcript of the first run.
#[test]
fn the_case_fails_with_a_guest_at_another_level() {
    let scratch = Scratch::new("qemu-boot-fail");
    let qemu = fake_qemu(&scratch, "CASXI_BOOT kernel=krepi board=qemu-virt el=2");
    let image = scratch.write("image.elf", b"image\n");
    let output = scratch.path("suite");
    std::fs::create_dir(&output).unwrap();
    let _deadline = DeadlineAt::new(ECHO);
    let flag: &'static AtomicI32 = Box::leak(Box::new(AtomicI32::new(0)));
    let (entry, outcome) = run_case(
        &CASES[0],
        Subject {
            image: &image,
            sha256: &sha256(b"image\n"),
            symbols: &[],
        },
        Some(&qemu),
        &output,
        &TIMING,
        &mut || Ok(flag),
        &mut |_| {},
    );
    assert_eq!(outcome, Outcome::Fail);
    let failed: Vec<&str> = entry["checks"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|check| check["status"] == "FAIL")
        .map(|check| check["name"].as_str().unwrap())
        .collect();
    assert_eq!(
        failed,
        ["run 1 transcript", "run 2 transcript", "run 3 transcript"]
    );
}

/// A run that cannot start, here for a missing QEMU, ends the case as an
/// error without the runs after it.
#[test]
fn a_run_that_cannot_start_is_an_error() {
    let scratch = Scratch::new("qemu-boot-error");
    let image = scratch.write("image.elf", b"image\n");
    let output = scratch.path("suite");
    std::fs::create_dir(&output).unwrap();
    let flag: &'static AtomicI32 = Box::leak(Box::new(AtomicI32::new(0)));
    let (entry, outcome) = run_case(
        &CASES[0],
        Subject {
            image: &image,
            sha256: &sha256(b"image\n"),
            symbols: &[],
        },
        Some(&scratch.path("no-qemu")),
        &output,
        &TIMING,
        &mut || Ok(flag),
        &mut |_| {},
    );
    assert_eq!(outcome, Outcome::Error);
    assert_eq!(outcome.code(), 2);
    let runs = entry["runs"].as_array().unwrap();
    assert_eq!(runs.len(), 1);
    assert!(
        runs[0]["error"]
            .as_str()
            .unwrap()
            .starts_with("QEMU executable not found"),
        "{entry}"
    );
}

/// The addresses that the test images of the tests have for the symbols of
/// the cases.
fn symbols() -> Vec<(String, u64)> {
    [
        ("krepi_test_brk_site", 0x4020_1288),
        ("krepi_test_serror", 0x4020_11a0),
        ("krepi_test_serror_end", 0x4020_11b0),
        ("krepi_test_fp_site", 0x4020_1160),
        ("krepi_test_wait", 0x4020_1160),
        ("krepi_test_wait_end", 0x4020_1188),
        ("krepi_test_irq_resume", 0x4020_1258),
        ("krepi_test_sp0_site", 0x4020_1178),
    ]
    .map(|(name, address)| (name.to_string(), address))
    .to_vec()
}

/// The case `name` of the suite.
fn case(name: &str) -> &'static Case {
    CASES.iter().find(|case| case.name == name).unwrap()
}

/// The receipt that the runner gives for a good run of a test image on
/// `machine` with `transcript`.
fn image_receipt(transcript: &[u8], machine: Machine) -> Value {
    let mut receipt = good_receipt(transcript);
    receipt["qemu"]["command"][4] = json!(machine.option());
    receipt.as_object_mut().unwrap().remove("input");
    receipt
}

/// The transcript of `lines`, each followed by CR LF.
fn lines(lines: &[&[u8]]) -> Vec<u8> {
    lines
        .iter()
        .flat_map(|line| [*line, b"\r\n"].concat())
        .collect()
}

/// The exception record of a good run of `el1-brk`.
const BRK_RECORD: &[u8] = b"CASXI_EXCEPTION vector=4 ESR=0x00000000f20000c5 ELR=0x0000000040201288 FAR=0x0000000000000000 SPSR=0x00000000a0000285 class=brk";

/// The self-checks of `el1-brk` with no failure.
const BRK_CHECKS: [&[u8]; 5] = [
    b"CASXI_CHECK name=frame-records-interrupted-sp failures=0x0000000000000000",
    b"CASXI_CHECK name=entry-saves-general-registers failures=0x0000000000000000",
    b"CASXI_CHECK name=frame-records-system-registers failures=0x0000000000000000",
    b"CASXI_CHECK name=return-restores-elr-and-pstate failures=0x0000000000000000",
    b"CASXI_CHECK name=return-restores-sp failures=0x0000000000000000",
];

/// The transcript of a good run of `el1-brk` with the exception record
/// `record`.
fn brk_transcript(record: &[u8]) -> Vec<u8> {
    let mut all: Vec<&[u8]> = vec![b"CASXI_TEST image=el1-brk", b"", record];
    all.extend(BRK_CHECKS);
    all.push(b"CASXI_RESUMED");
    lines(&all)
}

/// The transcript of a good run of `injected-serror` with the exception
/// record `record`.
fn serror_transcript(record: &[u8]) -> Vec<u8> {
    lines(&[
        b"CASXI_TEST image=injected-serror",
        b"",
        record,
        b"CASXI_HALTED",
    ])
}

/// The exception record of a good run of `injected-serror`.
const SERROR_RECORD: &[u8] = b"CASXI_EXCEPTION vector=7 ESR=0x00000000be000000 ELR=0x00000000402011a4 FAR=0x0000000000000000 SPSR=0x00000000600002c5 class=serror";

/// The transcript of a good run of `el1-fp-trap`.
fn fp_transcript() -> Vec<u8> {
    lines(&[
        b"CASXI_TEST image=el1-fp-trap",
        b"",
        b"CASXI_EXCEPTION vector=4 ESR=0x000000001fe00000 ELR=0x0000000040201160 FAR=0x0000000000000000 SPSR=0x00000000600003c5 class=fp",
        b"CASXI_HALTED",
    ])
}

/// The exception record of an IRQ with the return address `elr`.
fn irq_record(elr: u64) -> String {
    format!(
        "CASXI_EXCEPTION vector=5 ESR=0x0000000000000000 ELR={elr:#018x} FAR=0x0000000000000000 SPSR=0x0000000000000345 class=irq"
    )
}

/// The transcript of a run of `timer-irq` whose interrupts returned to
/// `elrs`, with checks that report no failure.
fn timer_transcript(elrs: &[u64]) -> Vec<u8> {
    let records: Vec<String> = elrs.iter().map(|&elr| irq_record(elr)).collect();
    let mut all: Vec<&[u8]> = vec![b"CASXI_TEST image=timer-irq"];
    for record in &records {
        all.extend([&b""[..], record.as_bytes()]);
    }
    all.extend([
        &b"CASXI_CHECK name=timer-irq failures=0x0000000000000000"[..],
        b"CASXI_CHECK name=dispatch-masks-daif failures=0x0000000000000000",
        b"CASXI_RESUMED",
    ]);
    lines(&all)
}

/// The transcript of a good run of `irq-registers` whose interrupt returned
/// to `elr`.
fn registers_transcript(elr: u64) -> Vec<u8> {
    let record = irq_record(elr);
    lines(&[
        b"CASXI_TEST image=irq-registers",
        b"",
        record.as_bytes(),
        b"CASXI_CHECK name=irq-preserves-registers failures=0x0000000000000000",
        b"CASXI_RESUMED",
    ])
}

/// The exception record of a good run of `sp-el0-brk`.
const SP0_RECORD: &[u8] = b"CASXI_EXCEPTION vector=0 ESR=0x00000000f200005e ELR=0x0000000040201178 FAR=0x0000000000000000 SPSR=0x00000000600003c4 class=sync";

/// The transcript of a good run of `sp-el0-brk`, whose vectors halted after
/// its dispatch.
fn sp0_transcript() -> Vec<u8> {
    lines(&[
        b"CASXI_TEST image=sp-el0-brk",
        b"",
        SP0_RECORD,
        b"CASXI_CHECK name=sp-el0-frame-records-sp-el1 failures=0x0000000000000000",
    ])
}

/// The transcript of a good run of `unexpected-irq` whose interrupt
/// returned to `elr`.
fn unexpected_transcript(elr: u64) -> Vec<u8> {
    let record = irq_record(elr);
    lines(&[
        b"CASXI_TEST image=unexpected-irq",
        b"",
        record.as_bytes(),
        b"CASXI_CHECK name=unexpected-irq-disabled failures=0x0000000000000000",
        b"CASXI_RESUMED",
    ])
}

/// The cases of the cache and TLB maintenance, each with its self-check.
const MAINTENANCE: [(&str, &str); 4] = [
    ("clean-code-to-pou", "clean-keeps-data"),
    ("invalidate-to-poc", "invalidate-keeps-data"),
    ("invalidate-tlb-page", "remap-reads-new-frame"),
    ("code-publication", "published-code-runs"),
];

/// The transcript of a run of the test image `image` that takes no
/// exception and reports its self-check `check` with the mask `failures`.
fn maintenance_transcript(image: &str, check: &str, failures: u64) -> Vec<u8> {
    let start = format!("CASXI_TEST image={image}");
    let record = format!("CASXI_CHECK name={check} failures={failures:#018x}");
    lines(&[start.as_bytes(), record.as_bytes(), b"CASXI_RESUMED"])
}

/// The checks of one run of the case `name` with `transcript` on `machine`.
fn judge_one(name: &str, transcript: Vec<u8>, machine: Machine) -> Vec<Check> {
    let run = Run {
        receipt: image_receipt(&transcript, machine),
        transcript,
    };
    judge_records(case(name), IMAGE_SHA256, &symbols(), &[run])
}

mod records {
    use super::*;

    /// A good run of each test image passes every check, and each record
    /// and self-check is a check of its own.
    #[test]
    fn good_runs_of_the_test_images_pass() {
        let checks = judge_one("el1-brk", brk_transcript(BRK_RECORD), Machine::Virt);
        assert_eq!(failed(&checks), Vec::<&str>::new());
        let names: Vec<&str> = checks.iter().map(|check| check.name.as_str()).collect();
        assert_eq!(
            names,
            [
                "run 1 receipt",
                "run 1 transcript",
                "run 1 exception 1",
                "run 1 frame-records-interrupted-sp",
                "run 1 entry-saves-general-registers",
                "run 1 frame-records-system-registers",
                "run 1 return-restores-elr-and-pstate",
                "run 1 return-restores-sp",
                "runs",
            ]
        );
        let checks = judge_one(
            "injected-serror",
            serror_transcript(SERROR_RECORD),
            Machine::VirtEl2,
        );
        assert_eq!(failed(&checks), Vec::<&str>::new());
        let checks = judge_one("el1-fp-trap", fp_transcript(), Machine::Virt);
        assert_eq!(failed(&checks), Vec::<&str>::new());
        let checks = judge_one(
            "timer-irq",
            timer_transcript(&[0x4020_1164, 0x4020_1170]),
            Machine::Virt,
        );
        assert_eq!(failed(&checks), Vec::<&str>::new());
        let names: Vec<&str> = checks.iter().map(|check| check.name.as_str()).collect();
        assert_eq!(
            names,
            [
                "run 1 receipt",
                "run 1 transcript",
                "run 1 exception 1",
                "run 1 exception 2",
                "run 1 timer-irq",
                "run 1 dispatch-masks-daif",
                "runs",
            ]
        );
        let checks = judge_one(
            "irq-preserves-registers",
            registers_transcript(0x4020_1258),
            Machine::Virt,
        );
        assert_eq!(failed(&checks), Vec::<&str>::new());
        let checks = judge_one("sp-el0-brk", sp0_transcript(), Machine::Virt);
        assert_eq!(failed(&checks), Vec::<&str>::new());
        let names: Vec<&str> = checks.iter().map(|check| check.name.as_str()).collect();
        assert_eq!(
            names,
            [
                "run 1 receipt",
                "run 1 transcript",
                "run 1 exception 1",
                "run 1 sp-el0-frame-records-sp-el1",
                "runs",
            ]
        );
        let checks = judge_one(
            "unexpected-irq",
            unexpected_transcript(0x4020_1170),
            Machine::Virt,
        );
        assert_eq!(failed(&checks), Vec::<&str>::new());
        for (name, self_check) in MAINTENANCE {
            let checks = judge_one(
                name,
                maintenance_transcript(name, self_check, 0),
                Machine::Virt,
            );
            assert_eq!(failed(&checks), Vec::<&str>::new(), "{name}");
            let names: Vec<&str> = checks.iter().map(|check| check.name.as_str()).collect();
            let own = format!("run 1 {self_check}");
            assert_eq!(
                names,
                ["run 1 receipt", "run 1 transcript", own.as_str(), "runs"],
                "{name}"
            );
        }
    }

    /// A case of the cache and TLB maintenance expects no exception record:
    /// an exception record with its halt fails the transcript and the
    /// self-check, which the record displaces, and a self-check with a
    /// failure, a missing end or another image fails as well.
    #[test]
    fn a_case_without_exceptions_fails_with_an_exception_record() {
        let record = irq_record(0x4020_1170);
        let with_exception = lines(&[
            b"CASXI_TEST image=invalidate-tlb-page",
            b"",
            record.as_bytes(),
            b"CASXI_HALTED",
        ]);
        let checks = judge_one("invalidate-tlb-page", with_exception, Machine::Virt);
        assert_eq!(
            failed(&checks),
            ["run 1 transcript", "run 1 remap-reads-new-frame"]
        );
        let fatal = lines(&[
            b"CASXI_TEST image=code-publication",
            b"",
            b"CASXI_EXCEPTION vector=4 ESR=0x0000000086000010 ELR=0x0000000040203000 FAR=0x0000000040203000 SPSR=0x00000000000003c5 class=sync",
            b"CASXI_HALTED",
        ]);
        let checks = judge_one("code-publication", fatal, Machine::Virt);
        assert_eq!(
            failed(&checks),
            ["run 1 transcript", "run 1 published-code-runs"]
        );
        for (name, self_check) in MAINTENANCE {
            let failing = maintenance_transcript(name, self_check, 0b100);
            let checks = judge_one(name, failing, Machine::Virt);
            let own = format!("run 1 {self_check}");
            assert_eq!(failed(&checks), [own.as_str()], "{name}");
            let good = maintenance_transcript(name, self_check, 0);
            let without_end = good[..good.len() - b"CASXI_RESUMED\r\n".len()].to_vec();
            let checks = judge_one(name, without_end, Machine::Virt);
            assert_eq!(
                failed(&checks),
                ["run 1 transcript", own.as_str()],
                "{name}"
            );
        }
        let other = maintenance_transcript("clean-code-to-pou", "clean-keeps-data", 0);
        let checks = judge_one("invalidate-to-poc", other, Machine::Virt);
        assert_eq!(
            failed(&checks),
            ["run 1 transcript", "run 1 invalidate-keeps-data"]
        );
    }

    /// The timer interrupts must return into the waiting code, two of them,
    /// and the interrupt of the register check at the instruction after the
    /// unmask; a missing interrupt, a third one or another address fails.
    #[test]
    fn the_interrupts_must_return_where_the_cases_expect() {
        let one = |elrs: &[u64]| {
            failed(&judge_one(
                "timer-irq",
                timer_transcript(elrs),
                Machine::Virt,
            ))
            .len()
        };
        assert_eq!(one(&[0x4020_1160, 0x4020_1184]), 0);
        assert_eq!(one(&[0x4020_1164, 0x4020_1188]), 1);
        assert_eq!(one(&[0x4020_115c, 0x4020_1170]), 1);
        assert!(one(&[0x4020_1164]) > 0);
        assert!(one(&[0x4020_1164, 0x4020_1168, 0x4020_116c]) > 0);
        let at = |elr: u64| {
            failed(&judge_one(
                "irq-preserves-registers",
                registers_transcript(elr),
                Machine::Virt,
            ))
            .len()
        };
        assert_eq!(at(0x4020_1258), 0);
        assert_eq!(at(0x4020_125c), 1);
        assert_eq!(at(0x4020_1254), 1);
    }

    /// A record of another exception class, syndrome, return address, class
    /// name or vector fails the check of the record alone.
    #[test]
    fn a_record_with_other_fields_fails() {
        let good = std::str::from_utf8(BRK_RECORD).unwrap();
        for (what, from, to) in [
            (
                "exception class",
                "ESR=0x00000000f20000c5",
                "ESR=0x00000000f40000c5",
            ),
            (
                "immediate",
                "ESR=0x00000000f20000c5",
                "ESR=0x00000000f20000c6",
            ),
            (
                "address",
                "ELR=0x0000000040201288",
                "ELR=0x000000004020128c",
            ),
            ("class", "class=brk", "class=sync"),
            ("vector", "vector=4", "vector=5"),
        ] {
            let record = good.replace(from, to);
            let checks = judge_one("el1-brk", brk_transcript(record.as_bytes()), Machine::Virt);
            assert_eq!(failed(&checks), ["run 1 exception 1"], "{what}");
        }
        let fp = String::from_utf8(fp_transcript()).unwrap();
        let other = fp.replace("ESR=0x000000001fe00000", "ESR=0x0000000096000010");
        let checks = judge_one("el1-fp-trap", other.into_bytes(), Machine::Virt);
        assert_eq!(failed(&checks), ["run 1 exception 1"]);
    }

    /// The return address of the SError must lie in the code that unmasked
    /// it: its start is in, the end symbol is not.
    #[test]
    fn the_serror_must_return_into_the_unmasking_code() {
        let good = std::str::from_utf8(SERROR_RECORD).unwrap();
        let at = |elr: &str| {
            let record = good.replace("ELR=0x00000000402011a4", elr);
            failed(&judge_one(
                "injected-serror",
                serror_transcript(record.as_bytes()),
                Machine::VirtEl2,
            ))
            .len()
        };
        assert_eq!(at("ELR=0x00000000402011a0"), 0);
        assert_eq!(at("ELR=0x00000000402011b0"), 1);
        assert_eq!(at("ELR=0x000000004020119c"), 1);
    }

    /// A record whose fields are malformed, missing or extra is refused.
    #[test]
    fn malformed_records_are_refused() {
        let good = std::str::from_utf8(BRK_RECORD).unwrap();
        assert_eq!(
            parse_exception(BRK_RECORD),
            Ok(Record {
                vector: 4,
                esr: 0xf200_00c5,
                elr: 0x4020_1288,
                far: 0,
                spsr: 0xa000_0285,
                class: "brk".to_string(),
            })
        );
        for (from, to) in [
            ("ESR=0x00000000f20000c5", "ESR=0x00000000F20000C5"),
            ("ESR=0x00000000f20000c5", "ESR=0x0000000f20000c5"),
            ("ESR=0x00000000f20000c5", "ESR=00000000f20000c5"),
            ("vector=4", "vector=04"),
            ("vector=4", "vector="),
            ("class=brk", "class="),
            (" FAR=0x0000000000000000", ""),
            ("class=brk", "class=brk extra"),
            ("CASXI_EXCEPTION", "CASXI_EXCEPTIONS"),
            ("SPSR", "PSR"),
        ] {
            let line = good.replace(from, to);
            assert!(parse_exception(line.as_bytes()).is_err(), "{line}");
        }
    }

    /// A self-check that reports a failure fails that check alone.
    #[test]
    fn a_failed_self_check_fails() {
        let mut transcript = brk_transcript(BRK_RECORD);
        let text = String::from_utf8(transcript).unwrap().replace(
            "name=return-restores-sp failures=0x0000000000000000",
            "name=return-restores-sp failures=0x0000000000000001",
        );
        transcript = text.into_bytes();
        let checks = judge_one("el1-brk", transcript, Machine::Virt);
        assert_eq!(failed(&checks), ["run 1 return-restores-sp"]);
    }

    /// A halting case fails with any output after `CASXI_HALTED`, and a
    /// returning case fails without `CASXI_RESUMED` or with `CASXI_HALTED`;
    /// so do a missing, extra or reordered record and a line not ending in
    /// CR LF. Each makes every record check fail with the transcript.
    #[test]
    fn a_wrong_end_or_order_of_records_fails() {
        let halted = serror_transcript(SERROR_RECORD);
        for extra in [&b"CASXI_RESUMED\r\n"[..], b"x\r\n", b"\r\n"] {
            let transcript = [halted.as_slice(), extra].concat();
            let checks = judge_one("injected-serror", transcript, Machine::VirtEl2);
            assert_eq!(
                failed(&checks),
                ["run 1 transcript", "run 1 exception 1"],
                "{}",
                extra.escape_ascii()
            );
        }
        let resumed = brk_transcript(BRK_RECORD);
        let without_end = resumed[..resumed.len() - b"CASXI_RESUMED\r\n".len()].to_vec();
        let mut all: Vec<&[u8]> = vec![b"CASXI_TEST image=el1-brk", b"", BRK_RECORD];
        all.extend(BRK_CHECKS);
        all.push(b"CASXI_HALTED");
        let with_halt = lines(&all);
        let mut swapped: Vec<&[u8]> = vec![b"CASXI_TEST image=el1-brk", b"", BRK_RECORD];
        swapped.extend(BRK_CHECKS.iter().rev());
        swapped.push(b"CASXI_RESUMED");
        let reordered = lines(&swapped);
        let no_break = lines(&[
            b"CASXI_TEST image=el1-brk",
            BRK_RECORD,
            BRK_CHECKS[0],
            BRK_CHECKS[1],
            BRK_CHECKS[2],
            BRK_CHECKS[3],
            BRK_CHECKS[4],
            b"CASXI_RESUMED",
        ]);
        let other_image = String::from_utf8(resumed.clone())
            .unwrap()
            .replace("image=el1-brk", "image=el1-fp-trap")
            .into_bytes();
        let bare_lf = String::from_utf8(resumed.clone())
            .unwrap()
            .replacen("\r\n", "\n", 1)
            .into_bytes();
        let all_failed = [
            "run 1 transcript",
            "run 1 exception 1",
            "run 1 frame-records-interrupted-sp",
            "run 1 entry-saves-general-registers",
            "run 1 frame-records-system-registers",
            "run 1 return-restores-elr-and-pstate",
            "run 1 return-restores-sp",
        ];
        for (what, transcript) in [
            ("without the end", without_end),
            ("with a halt", with_halt),
            ("reordered", reordered),
            ("without the line break", no_break),
            ("another image", other_image),
            ("a bare LF", bare_lf),
        ] {
            let checks = judge_one("el1-brk", transcript, Machine::Virt);
            assert_eq!(failed(&checks), all_failed, "{what}");
        }
    }

    /// The case whose vectors halt after its dispatch fails with any record
    /// after its self-check, such as `CASXI_RESUMED` when the vectors
    /// returned, and without the self-check; a failed self-check or another
    /// vector fails that check alone. The unexpected interrupt fails when it
    /// came twice.
    #[test]
    fn a_case_that_halts_after_its_dispatch_fails_with_more_or_less() {
        let good = sp0_transcript();
        let all_failed = [
            "run 1 transcript",
            "run 1 exception 1",
            "run 1 sp-el0-frame-records-sp-el1",
        ];
        for extra in [&b"CASXI_RESUMED\r\n"[..], b"CASXI_HALTED\r\n", b"\r\n"] {
            let transcript = [good.as_slice(), extra].concat();
            let checks = judge_one("sp-el0-brk", transcript, Machine::Virt);
            assert_eq!(failed(&checks), all_failed, "{}", extra.escape_ascii());
        }
        let without_check = lines(&[b"CASXI_TEST image=sp-el0-brk", b"", SP0_RECORD]);
        let checks = judge_one("sp-el0-brk", without_check, Machine::Virt);
        assert_eq!(failed(&checks), all_failed);
        let text = String::from_utf8(good).unwrap();
        let failing = text.replace("failures=0x0000000000000000", "failures=0x0000000000000004");
        let checks = judge_one("sp-el0-brk", failing.into_bytes(), Machine::Virt);
        assert_eq!(failed(&checks), ["run 1 sp-el0-frame-records-sp-el1"]);
        let other_vector = text.replace("vector=0", "vector=4");
        let checks = judge_one("sp-el0-brk", other_vector.into_bytes(), Machine::Virt);
        assert_eq!(failed(&checks), ["run 1 exception 1"]);
        let record = irq_record(0x4020_1170);
        let twice = lines(&[
            b"CASXI_TEST image=unexpected-irq",
            b"",
            record.as_bytes(),
            b"",
            record.as_bytes(),
            b"CASXI_CHECK name=unexpected-irq-disabled failures=0x0000000000000000",
            b"CASXI_RESUMED",
        ]);
        let checks = judge_one("unexpected-irq", twice, Machine::Virt);
        assert_eq!(
            failed(&checks),
            [
                "run 1 transcript",
                "run 1 exception 1",
                "run 1 unexpected-irq-disabled"
            ]
        );
        let outside = unexpected_transcript(0x4020_1188);
        let checks = judge_one("unexpected-irq", outside, Machine::Virt);
        assert_eq!(failed(&checks), ["run 1 exception 1"]);
    }

    /// The receipt of a test image must name the machine of its case, so
    /// the SError case fails without EL2 and the breakpoint case with it;
    /// a run with input, an instruction count or another image fails too.
    #[test]
    fn a_receipt_of_another_machine_or_with_input_fails() {
        let checks = judge_one(
            "injected-serror",
            serror_transcript(SERROR_RECORD),
            Machine::Virt,
        );
        assert_eq!(failed(&checks), ["run 1 receipt"]);
        let checks = judge_one("el1-brk", brk_transcript(BRK_RECORD), Machine::VirtEl2);
        assert_eq!(failed(&checks), ["run 1 receipt"]);
        let transcript = brk_transcript(BRK_RECORD);
        let changes: [fn(&mut Value); 3] = [
            |r| r["input"] = good_receipt(b"")["input"].clone(),
            |r| {
                let command = r["qemu"]["command"].as_array_mut().unwrap();
                command.insert(3, json!("-icount"));
                command.insert(4, json!("shift=3"));
            },
            |r| r["image"]["sha256"] = json!("2".repeat(64)),
        ];
        for change in changes {
            let mut receipt = image_receipt(&transcript, Machine::Virt);
            change(&mut receipt);
            let run = Run {
                receipt,
                transcript: transcript.clone(),
            };
            let checks = judge_records(case("el1-brk"), IMAGE_SHA256, &symbols(), &[run]);
            assert_eq!(failed(&checks), ["run 1 receipt"]);
        }
    }

    /// A symbol that the image lacks fails the check of the record, and a
    /// case of one run fails with none.
    #[test]
    fn a_missing_symbol_or_run_fails() {
        let transcript = brk_transcript(BRK_RECORD);
        let run = Run {
            receipt: image_receipt(&transcript, Machine::Virt),
            transcript,
        };
        let checks = judge_records(case("el1-brk"), IMAGE_SHA256, &[], &[run]);
        assert_eq!(failed(&checks), ["run 1 exception 1"]);
        let checks = judge_records(case("el1-brk"), IMAGE_SHA256, &symbols(), &[]);
        assert_eq!(failed(&checks), ["runs"]);
    }
}

/// The cases name each symbol once, the test images once each, and the
/// suite takes the worst outcome of its cases.
#[test]
fn the_cases_name_their_symbols_images_and_outcome() {
    let Judgment::Records(exceptions, _) = case("injected-serror").judgment else {
        panic!("a case of records");
    };
    assert_eq!(
        symbols_of(exceptions),
        ["krepi_test_serror", "krepi_test_serror_end"]
    );
    assert_eq!(
        test_images(),
        [
            "el1-brk",
            "injected-serror",
            "el1-fp-trap",
            "timer-irq",
            "irq-registers",
            "sp-el0-brk",
            "unexpected-irq",
            "clean-code-to-pou",
            "invalidate-to-poc",
            "invalidate-tlb-page",
            "code-publication"
        ]
    );
    let all = |outcomes: &[Outcome]| suite_outcome(outcomes);
    assert_eq!(all(&[Outcome::Pass, Outcome::Pass]), Outcome::Pass);
    assert_eq!(all(&[Outcome::Pass, Outcome::Fail]), Outcome::Fail);
    assert_eq!(all(&[Outcome::Fail, Outcome::Error]), Outcome::Error);
    assert_eq!(
        all(&[Outcome::Error, Outcome::Interrupted]),
        Outcome::Interrupted
    );
    assert_eq!(all(&[]), Outcome::Pass);
}
