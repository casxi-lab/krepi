//! The tests of the QEMU boot suite: the checks of the case against
//! hand-written receipts and transcripts, the image of the build, the
//! command line, and runs of the case with a fake QEMU.
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

/// The executable of the default image is that of the last artifact
/// message of its binary; other messages and lines are ignored.
#[test]
fn the_image_is_taken_from_the_artifact_message() {
    let messages = concat!(
        "{\"reason\":\"compiler-artifact\",\"target\":{\"name\":\"krepi_arch\"},\"executable\":null}\n",
        "not JSON\n",
        "{\"reason\":\"build-script-executed\",\"package_id\":\"x\"}\n",
        "{\"reason\":\"compiler-artifact\",\"target\":{\"name\":\"krepi-qemu-virt\"},\"executable\":\"/w/kernel/target/aarch64-unknown-none-softfloat/release/krepi-qemu-virt\"}\n",
        "{\"reason\":\"build-finished\",\"success\":true}\n",
    );
    assert_eq!(
        executable_from_messages(messages),
        Some(PathBuf::from(
            "/w/kernel/target/aarch64-unknown-none-softfloat/release/krepi-qemu-virt"
        ))
    );
    assert_eq!(
        executable_from_messages("{\"reason\":\"build-finished\"}\n"),
        None
    );
}

/// The build command builds only the default image of the board crate, from
/// the lock and in release, for the bare-metal target.
#[test]
fn the_build_command_names_the_default_image() {
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
        &image,
        &digest,
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
        &image,
        &sha256(b"image\n"),
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
        &image,
        &sha256(b"image\n"),
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
