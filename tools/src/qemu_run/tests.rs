use super::*;
use crate::TEST_WAIT;
use crate::scratch::Scratch;
use std::os::unix::fs::PermissionsExt;

/// The time values of a run under test: those of QEMU virt, with bounds for
/// the final collection and the end of the process that a slow host never
/// reaches.
const TIMING: Timing = Timing {
    guest_finish: TEST_WAIT,
    stop_grace: TEST_WAIT,
    kill_grace: TEST_WAIT,
    ..Timing::QEMU_VIRT
};
/// The image of a run under test, which a fake QEMU does not read.
const IMAGE: &[u8] = b"not an ELF image\n";
/// The SHA-256 digest of [`IMAGE`], from `shasum -a 256`.
const IMAGE_SHA256: &str = "d7106734913c428a1b8abd0a15afd3ad14084c4bd0c03bf06fff5803403823e0";
/// The SHA-256 digest of no bytes.
const EMPTY_SHA256: &str = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
/// The start of the usage line of clap, which names the command.
const USAGE: &str = "Usage: cargo xtask qemu ";

/// An interrupt flag that holds no signal, for one test.
fn fresh_flag() -> &'static AtomicI32 {
    Box::leak(Box::new(AtomicI32::new(0)))
}

fn arguments(args: &[&str]) -> Vec<String> {
    args.iter().map(|arg| arg.to_string()).collect()
}

/// A fake QEMU: a shell script that answers `--version` with the two lines
/// of QEMU and runs `body` otherwise.
#[track_caller]
fn fake_qemu(scratch: &Scratch, body: &str) -> PathBuf {
    scratch.script(
        "qemu",
        &format!(
            "#!/bin/sh\nif [ \"$1\" = --version ]; then\n  printf 'QEMU emulator version 0.0.0\\nCopyright (c) 2003-2026 Fabrice Bellard and the QEMU Project developers\\n'\n  exit 0\nfi\n{body}\n"
        ),
    )
}

/// A run directory with a fake QEMU and an image.
struct Bench {
    scratch: Scratch,
    qemu: PathBuf,
    image: PathBuf,
}

impl Bench {
    #[track_caller]
    fn new(label: &str, body: &str) -> Self {
        let scratch = Scratch::new(label);
        let qemu = fake_qemu(&scratch, body);
        let image = scratch.write("image.elf", IMAGE);
        Bench {
            scratch,
            qemu,
            image,
        }
    }

    /// The output directory of the run.
    fn output(&self) -> PathBuf {
        self.scratch.path("run")
    }

    /// The arguments of a run of the image with the fake QEMU into
    /// [`Bench::output`], with a timeout that a run which another event
    /// ends never reaches, followed by `more`, which may replace it.
    fn args(&self, more: &[&str]) -> Vec<String> {
        let mut args = vec![
            self.image.to_str().unwrap().to_string(),
            "--qemu".to_string(),
            self.qemu.to_str().unwrap().to_string(),
            "--output-dir".to_string(),
            self.output().to_str().unwrap().to_string(),
            "--timeout".to_string(),
            "120".to_string(),
        ];
        args.extend(more.iter().map(|arg| arg.to_string()));
        args
    }

    /// The receipt of the run as `summary.json` holds it, which is the JSON
    /// text of its value with sorted keys.
    #[track_caller]
    fn receipt(&self) -> Value {
        let text = std::fs::read_to_string(self.output().join(SUMMARY_FILE)).unwrap();
        let receipt: Value = serde_json::from_str(&text).unwrap();
        assert_eq!(to_json(&receipt), text);
        let mut sorted = receipt.clone();
        sorted.sort_all_objects();
        assert_eq!(
            serde_json::to_string(&sorted).unwrap(),
            serde_json::to_string(&receipt).unwrap(),
            "the keys are sorted"
        );
        receipt
    }

    /// The bytes of `name` in the run directory.
    fn file(&self, name: &str) -> Vec<u8> {
        std::fs::read(self.output().join(name)).unwrap()
    }
}

/// The exit status and the lines on each stream of a run of the command
/// with `args`, whose interrupt flag is `interrupt`.
fn command(
    root: &Path,
    args: &[String],
    interrupt: &AtomicI32,
    timing: &Timing,
) -> (i32, Vec<String>, Vec<String>) {
    let (mut out, mut err) = (Vec::new(), Vec::new());
    let code = run_with(
        root,
        args,
        timing,
        &mut Console {
            print: &mut |line| {
                out.push(line.to_string());
                Ok(())
            },
            warn: &mut |line| {
                err.push(line.to_string());
                Ok(())
            },
            arm: &mut || Ok(interrupt),
        },
    );
    (code, out, err)
}

/// The QEMU command line of a run of `image` with `qemu`, both canonical.
fn qemu_command(qemu: &Path, image: &Path) -> Vec<String> {
    let mut command = vec![
        std::fs::canonicalize(qemu)
            .unwrap()
            .to_str()
            .unwrap()
            .to_string(),
    ];
    command.extend(
        [
            "-accel",
            "tcg,thread=single",
            "-machine",
            "virt-8.2,secure=off,virtualization=off,gic-version=2",
            "-cpu",
            "cortex-a76",
            "-smp",
            "1",
            "-m",
            "128M",
            "-nic",
            "none",
            "-display",
            "none",
            "-serial",
            "stdio",
            "-monitor",
            "none",
            "-kernel",
        ]
        .map(String::from),
    );
    command.push(
        std::fs::canonicalize(image)
            .unwrap()
            .to_str()
            .unwrap()
            .to_string(),
    );
    command
}

/// Requires a time stamp in the form of `report::utc_now`.
#[track_caller]
fn assert_stamp(value: &Value) {
    let stamp = value.as_str().expect("a time stamp");
    assert_eq!(stamp.len(), "2026-10-14T07:45:17.123456Z".len(), "{stamp}");
    assert!(
        stamp.ends_with('Z') && stamp.as_bytes()[10] == b'T',
        "{stamp}"
    );
}

/// The lines that a run prints.
fn printed(reason: &str, bytes: usize, output: &Path) -> Vec<String> {
    let summary = std::fs::canonicalize(output).unwrap().join(SUMMARY_FILE);
    vec![
        format!("{reason}: {bytes} bytes of serial output; the output is not evaluated."),
        format!("Receipt: {}", summary.display()),
    ]
}

/// The names in the run directory, sorted.
fn listing(output: &Path) -> Vec<String> {
    let mut names: Vec<String> = std::fs::read_dir(output)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .collect();
    names.sort();
    names
}

/// A QEMU that writes to its serial port and its standard error and exits
/// with status 0, as one does whose guest powers the machine off, ends the
/// run as `guest_shutdown` with status 0. The receipt describes the image,
/// QEMU, the run and both files as they are on disk; the run directory
/// holds those files and the receipt and nothing else.
#[test]
fn a_guest_that_powers_off_ends_the_run() {
    let bench = Bench::new(
        "qemu-run-shutdown",
        "printf 'hello\\r\\n'\nprintf 'note\\n' >&2\nexit 0",
    );
    let (code, out, err) = command(
        bench.scratch.root(),
        &bench.args(&[]),
        fresh_flag(),
        &TIMING,
    );
    assert_eq!((code, err), (0, Vec::<String>::new()));
    assert_eq!(out, printed("guest_shutdown", 7, &bench.output()));
    assert_eq!(
        listing(&bench.output()),
        [STDERR_FILE, SUMMARY_FILE, TRANSCRIPT_FILE]
    );
    assert_eq!(bench.file(TRANSCRIPT_FILE), b"hello\r\n");
    assert_eq!(bench.file(STDERR_FILE), b"note\n");
    let receipt = bench.receipt();
    let mut timed = receipt.clone();
    let object = timed.as_object_mut().unwrap();
    for key in ["started_at", "finished_at"] {
        assert_stamp(&object.remove(key).unwrap());
    }
    assert!(receipt["started_at"].as_str() <= receipt["finished_at"].as_str());
    let elapsed = object.remove("elapsed_seconds").unwrap();
    assert!(elapsed.as_f64().is_some_and(|seconds| seconds >= 0.0));
    let image = std::fs::canonicalize(&bench.image).unwrap();
    assert_eq!(
        timed,
        json!({
            "clock": "host",
            "exit_reason": "guest_shutdown",
            "image": {
                "bytes": IMAGE.len(),
                "path": image.to_str().unwrap(),
                "sha256": IMAGE_SHA256,
            },
            "max_bytes": 262144,
            "process": {
                "exit_code": 0,
                "forced_kill": false,
                "intentional_shutdown": false,
                "signal": null,
            },
            "qemu": {
                "command": qemu_command(&bench.qemu, &bench.image),
                "executable": std::fs::canonicalize(&bench.qemu).unwrap().to_str().unwrap(),
                "version": "QEMU emulator version 0.0.0",
            },
            "schema_version": 1,
            "stderr": {
                "bytes": 5,
                "file": "qemu-stderr.txt",
                "sha256": "389ed6887e49a315f706f6c2b931b1dcf0d797c91437124f32eb98555c669758",
            },
            "timeout_seconds": 120.0,
            "transcript": {
                "bytes": 7,
                "file": "transcript.bin",
                "sha256": "cd2eca3535741f27a8ae40c31b0c41d4057a7a7b912b33b9aed86485d1c84676",
            },
        })
    );
}

/// A QEMU that exits by itself with another status ends the run as
/// `qemu_exit` with status 1, and the receipt keeps the status.
#[test]
fn qemu_that_fails_ends_the_run_with_its_status() {
    let bench = Bench::new("qemu-run-exit", "exit 3");
    let (code, out, err) = command(
        bench.scratch.root(),
        &bench.args(&["--clock", "icount"]),
        fresh_flag(),
        &TIMING,
    );
    assert_eq!((code, err), (1, Vec::<String>::new()));
    assert_eq!(out, printed("qemu_exit", 0, &bench.output()));
    let receipt = bench.receipt();
    assert_eq!(receipt["exit_reason"], "qemu_exit");
    assert_eq!(
        receipt["process"],
        json!({"exit_code": 3, "forced_kill": false, "intentional_shutdown": false, "signal": null})
    );
    assert_eq!(receipt["clock"], "icount");
    let command = receipt["qemu"]["command"].as_array().unwrap();
    assert_eq!(
        command[3..5],
        [json!("-icount"), json!("shift=3,align=off,sleep=off")]
    );
    assert_eq!(
        receipt["transcript"],
        json!({"bytes": 0, "file": "transcript.bin", "sha256": EMPTY_SHA256})
    );
    assert_eq!(
        receipt["stderr"],
        json!({"bytes": 0, "file": "qemu-stderr.txt", "sha256": EMPTY_SHA256})
    );
}

/// A QEMU that a signal from another process ended exits with status 0 too,
/// once it has reported the signal on its standard error, with the sender
/// when it knows it: the run ends as `qemu_exit` with status 1, not as
/// `guest_shutdown`. The fake QEMU writes the report as QEMU does and exits
/// with status 0, without a signal.
#[test]
fn a_qemu_that_a_signal_from_elsewhere_ended_is_not_a_guest_shutdown() {
    for report in [
        "qemu-system-aarch64: terminating on signal 15 from pid 4242 (kill)",
        "qemu-system-aarch64: terminating on signal 2",
    ] {
        let bench = Bench::new(
            "qemu-run-signalled",
            &format!("printf 'boot\\r\\n'\necho '{report}' >&2\nexit 0"),
        );
        let (code, out, err) = command(
            bench.scratch.root(),
            &bench.args(&[]),
            fresh_flag(),
            &TIMING,
        );
        assert_eq!((code, err), (1, Vec::<String>::new()), "{report}");
        assert_eq!(out, printed("qemu_exit", 6, &bench.output()));
        assert_eq!(bench.file(STDERR_FILE), format!("{report}\n").as_bytes());
        let receipt = bench.receipt();
        assert_eq!(receipt["exit_reason"], "qemu_exit");
        assert_eq!(
            receipt["process"],
            json!({"exit_code": 0, "forced_kill": false, "intentional_shutdown": false, "signal": null})
        );
    }
}

/// A QEMU that still runs at the timeout is stopped with SIGTERM: the run
/// ends as `deadline` with status 1. The shell ends by the signal before or
/// after it has started `cat`, which never ends by itself.
#[test]
fn a_run_past_its_timeout_is_stopped() {
    let bench = Bench::new("qemu-run-deadline", "exec cat");
    let (code, out, err) = command(
        bench.scratch.root(),
        &bench.args(&["--timeout", "0.1"]),
        fresh_flag(),
        &TIMING,
    );
    assert_eq!((code, err), (1, Vec::<String>::new()));
    assert_eq!(out, printed("deadline", 0, &bench.output()));
    let receipt = bench.receipt();
    assert_eq!(receipt["exit_reason"], "deadline");
    assert_eq!(receipt["timeout_seconds"], 0.1);
    assert_eq!(
        receipt["process"],
        json!({"exit_code": null, "forced_kill": false, "intentional_shutdown": true, "signal": 15})
    );
}

/// Restores the deadline of the runs of this thread.
struct DeadlineAt;

impl DeadlineAt {
    fn new(marker: &'static [u8]) -> Self {
        seams::DEADLINE_AT.set(Some(marker));
        DeadlineAt
    }
}

impl Drop for DeadlineAt {
    fn drop(&mut self) {
        seams::DEADLINE_AT.set(None);
    }
}

/// A QEMU that exits with status 0 when SIGTERM stops it, as QEMU 11 does
/// with a line on its standard error, still ran past its timeout: the run
/// ends as `deadline`, not `guest_shutdown`. The deadline passes once the
/// shell has installed its trap and said so, in place of a time, so that
/// the signal never reaches a shell without the trap; the shell runs the
/// trap once its current `sleep` has ended.
#[test]
fn a_qemu_that_exits_0_when_stopped_still_ran_past_its_timeout() {
    let bench = Bench::new(
        "qemu-run-term",
        "trap 'echo \"terminating on signal 15\" >&2; exit 0' TERM\nprintf 'ready\\n'\nwhile :; do sleep 1; done",
    );
    let _deadline = DeadlineAt::new(b"ready\n");
    let (code, out, err) = command(
        bench.scratch.root(),
        &bench.args(&[]),
        fresh_flag(),
        &TIMING,
    );
    assert_eq!((code, err), (1, Vec::<String>::new()));
    assert_eq!(out, printed("deadline", 6, &bench.output()));
    let receipt = bench.receipt();
    assert_eq!(receipt["exit_reason"], "deadline");
    assert_eq!(
        receipt["process"],
        json!({"exit_code": 0, "forced_kill": false, "intentional_shutdown": true, "signal": null})
    );
    assert_eq!(bench.file(STDERR_FILE), b"terminating on signal 15\n");
    assert_eq!(
        receipt["stderr"],
        json!({
            "bytes": 25,
            "file": "qemu-stderr.txt",
            "sha256": "484cbf3bf8ac1001075d3522500e760b13f8e65f0c1b1708ac465b23b9802599",
        })
    );
}

/// The 100 bytes that the fake QEMUs below print, ten times `0123456789`.
const HUNDRED: &str = "printf '0123456789%.0s' 1 2 3 4 5 6 7 8 9 10";

/// Requires a transcript that holds a prefix of [`HUNDRED`] longer than the
/// limit of 10 bytes, which the receipt describes.
#[track_caller]
fn assert_past_the_limit(bench: &Bench, receipt: &Value) {
    let transcript = bench.file(TRANSCRIPT_FILE);
    assert!(transcript.len() > 10, "{transcript:?}");
    assert_eq!(
        transcript,
        &"0123456789".repeat(10).as_bytes()[..transcript.len()]
    );
    assert_eq!(
        receipt["transcript"],
        json!({
            "bytes": transcript.len(),
            "file": "transcript.bin",
            "sha256": hex(&Sha256::digest(&transcript)),
        })
    );
}

/// Output past `--max-bytes` stops a QEMU that still runs: the run ends as
/// `output_limit` with status 1, and the transcript keeps the read that
/// passed the limit whole.
#[test]
fn output_past_the_limit_stops_the_run() {
    let bench = Bench::new("qemu-run-limit", &format!("{HUNDRED}\nexec cat"));
    let (code, out, err) = command(
        bench.scratch.root(),
        &bench.args(&["--max-bytes", "10"]),
        fresh_flag(),
        &TIMING,
    );
    assert_eq!((code, err), (1, Vec::<String>::new()));
    let receipt = bench.receipt();
    assert_eq!(receipt["exit_reason"], "output_limit");
    assert_eq!(receipt["max_bytes"], 10);
    assert_eq!(
        receipt["process"],
        json!({"exit_code": null, "forced_kill": false, "intentional_shutdown": true, "signal": 15})
    );
    assert_past_the_limit(&bench, &receipt);
    let bytes = bench.file(TRANSCRIPT_FILE).len();
    assert_eq!(out, printed("output_limit", bytes, &bench.output()));
}

/// Output past the limit ends the run as `output_limit` also when QEMU has
/// ended by itself with status 0 before the runner read it all, while the
/// rest is collected; which of the two happens depends on scheduling, and
/// both give the same reason and transcript.
#[test]
fn output_past_the_limit_is_not_a_guest_shutdown() {
    let bench = Bench::new("qemu-run-limit-exit", &format!("{HUNDRED}\nexit 0"));
    let (code, _, err) = command(
        bench.scratch.root(),
        &bench.args(&["--max-bytes", "10"]),
        fresh_flag(),
        &TIMING,
    );
    assert_eq!((code, err), (1, Vec::<String>::new()));
    let receipt = bench.receipt();
    assert_eq!(receipt["exit_reason"], "output_limit");
    assert_past_the_limit(&bench, &receipt);
}

/// Output that reaches the limit exactly before QEMU ends by itself does not
/// end the run, and the collection of the rest looks past it: a byte that
/// follows, here from a process that QEMU left behind, passes the limit, and
/// the run ends as `output_limit` with every byte in the transcript. Whether
/// the runner sees QEMU end before it reads the line or after, or the byte
/// only arrives once a slow host has looked at QEMU, the outcome is the
/// same.
#[test]
fn output_that_follows_the_limit_after_qemu_ended_is_collected() {
    let bench = Bench::new(
        "qemu-run-limit-after",
        "printf '0123456789'\n(sleep 1; printf 'x') &\nexit 0",
    );
    let (code, out, err) = command(
        bench.scratch.root(),
        &bench.args(&["--max-bytes", "10"]),
        fresh_flag(),
        &TIMING,
    );
    assert_eq!((code, err), (1, Vec::<String>::new()));
    assert_eq!(out, printed("output_limit", 11, &bench.output()));
    assert_eq!(bench.file(TRANSCRIPT_FILE), b"0123456789x");
    let receipt = bench.receipt();
    assert_eq!(receipt["exit_reason"], "output_limit");
    assert_eq!(
        receipt["process"],
        json!({"exit_code": 0, "forced_kill": false, "intentional_shutdown": false, "signal": null})
    );
}

/// An interrupt stops a QEMU that still runs: the run ends as `interrupted`
/// with status 130 and the receipt written. The flag holds the signal when
/// the handlers are installed, so the first look at it ends the run.
#[test]
fn an_interrupt_stops_the_run_and_keeps_the_receipt() {
    let bench = Bench::new("qemu-run-interrupt", "exec cat");
    let interrupt = fresh_flag();
    interrupt.store(libc::SIGINT, Ordering::SeqCst);
    let (code, out, err) = command(bench.scratch.root(), &bench.args(&[]), interrupt, &TIMING);
    assert_eq!((code, err), (130, Vec::<String>::new()));
    assert_eq!(out, printed("interrupted", 0, &bench.output()));
    let receipt = bench.receipt();
    assert_eq!(receipt["exit_reason"], "interrupted");
    assert_eq!(
        receipt["process"],
        json!({"exit_code": null, "forced_kill": false, "intentional_shutdown": true, "signal": 15})
    );
}

/// A QEMU that cannot be started, here one that removes itself once it has
/// answered the version query, and interrupt handlers that cannot be
/// installed end the run as `error` with status 2 and the error in the
/// receipt, which has no stop report.
#[test]
fn a_qemu_that_cannot_start_ends_the_run_as_an_error() {
    let scratch = Scratch::new("qemu-run-start");
    let qemu = scratch.script(
        "qemu",
        "#!/bin/sh\nif [ \"$1\" = --version ]; then\n  printf 'QEMU emulator version 0.0.0\\n'\n  if [ -e \"$0.armed\" ]; then rm -f -- \"$0\"; fi\n  exit 0\nfi\nexit 0\n",
    );
    let canonical = std::fs::canonicalize(&qemu).unwrap();
    scratch.write("qemu.armed", b"");
    let image = scratch.write("image.elf", IMAGE);
    let output = scratch.path("run");
    let args = arguments(&[
        image.to_str().unwrap(),
        "--qemu",
        qemu.to_str().unwrap(),
        "--output-dir",
        output.to_str().unwrap(),
    ]);
    let (code, out, err) = command(scratch.root(), &args, fresh_flag(), &TIMING);
    assert_eq!((code, err), (2, Vec::<String>::new()));
    assert_eq!(out, printed("error", 0, &output));
    let text = std::fs::read_to_string(output.join(SUMMARY_FILE)).unwrap();
    let receipt: Value = serde_json::from_str(&text).unwrap();
    assert_eq!(receipt["exit_reason"], "error");
    assert_eq!(
        receipt["errors"],
        json!([format!(
            "{canonical:?}: No such file or directory (os error 2)"
        )])
    );
    assert_eq!(receipt["process"], Value::Null);
    assert_eq!(
        receipt["transcript"],
        json!({"bytes": 0, "file": "transcript.bin", "sha256": EMPTY_SHA256})
    );

    let bench = Bench::new("qemu-run-arm", "exit 0");
    let options = parse(&bench.args(&[])).unwrap();
    let receipt = run_image(&options, &bench.output(), &TIMING, &mut || {
        Err(Failure::new("cannot install the handlers"))
    })
    .unwrap();
    assert_eq!(receipt["exit_reason"], "error");
    assert_eq!(receipt["errors"], json!(["cannot install the handlers"]));
    assert_eq!(receipt["process"], Value::Null);
    assert_eq!(exit_code(&receipt), 2);
}

/// A run that fails before QEMU starts prints `QEMU run failed: <error>` with
/// status 2 and creates no run directory: a missing image, a QEMU that is
/// missing, not executable or fails its version query, and an output
/// directory that exists, which is left as it is.
#[test]
fn problems_before_qemu_starts_leave_no_directory() {
    let bench = Bench::new("qemu-run-before", "exit 0");
    let unrunnable = bench.scratch.write("unrunnable", b"#!/bin/sh\nexit 0\n");
    std::fs::set_permissions(&unrunnable, std::fs::Permissions::from_mode(0o644)).unwrap();
    let failing = bench.scratch.script("failing", "#!/bin/sh\nexit 1\n");
    let missing = bench.scratch.path("missing.elf");
    let run = |args: Vec<String>, expected: String| {
        let (code, out, err) = command(bench.scratch.root(), &args, fresh_flag(), &TIMING);
        assert_eq!(code, 2, "{args:?}");
        assert!(out.is_empty(), "{out:?}");
        assert_eq!(err, [format!("QEMU run failed: {expected}")]);
        assert!(!bench.output().exists());
    };
    let mut args = bench.args(&[]);
    args[0] = missing.to_str().unwrap().to_string();
    run(
        args,
        format!(
            "ELF image not found: {}. Build the image first.",
            missing.display()
        ),
    );
    for qemu in [Path::new("/nonexistent/qemu"), unrunnable.as_path()] {
        let mut args = bench.args(&[]);
        args[2] = qemu.to_str().unwrap().to_string();
        run(
            args,
            format!(
                "QEMU executable not found or not executable: {qemu:?}. Install qemu-system-aarch64 or pass its path with --qemu."
            ),
        );
    }
    let mut args = bench.args(&[]);
    args[2] = failing.to_str().unwrap().to_string();
    run(
        args,
        "QEMU version query failed with exit status: 1".to_string(),
    );
    std::fs::create_dir(bench.output()).unwrap();
    let (code, out, err) = command(
        bench.scratch.root(),
        &bench.args(&[]),
        fresh_flag(),
        &TIMING,
    );
    assert_eq!((code, out), (2, Vec::<String>::new()));
    assert_eq!(
        err,
        [format!(
            "QEMU run failed: {:?}: File exists (os error 17)",
            bench.output()
        )]
    );
    assert!(listing(&bench.output()).is_empty());
}

/// Clap reads the command line: the help names the command, the image and
/// the options with their defaults, without colour; a missing or second
/// image, a clock that is not one of the two and limits out of bounds are
/// usage errors; a repeated option keeps its last value, and the limits take
/// a sign.
#[test]
fn the_command_line_takes_the_image_and_its_options() {
    let root = Scratch::new("qemu-run-cli");
    let (code, out, err) = command(root.root(), &arguments(&["--help"]), fresh_flag(), &TIMING);
    assert_eq!((code, err), (0, Vec::<String>::new()));
    let help = out.join("\n");
    for text in [
        "Usage: cargo xtask qemu [OPTIONS] <ELF>",
        "<ELF>",
        "--timeout <SECONDS>",
        "[default: 60]",
        "--max-bytes <MAX_BYTES>",
        "[default: 262144]",
        "--clock <CLOCK>",
        "[default: host]",
        "[possible values: host, icount]",
        "--qemu <PATH>",
        "--output-dir <OUTPUT_DIR>",
        "-h, --help",
    ] {
        assert!(help.contains(text), "{text}: {help}");
    }
    assert!(!help.contains('\x1b'), "{help}");
    // A value that its parser refuses is an error about that option alone,
    // without the usage; the others repeat it.
    for (args, message, usage) in [
        (
            &[][..],
            "the following required arguments were not provided",
            true,
        ),
        (&["a", "b"][..], "unexpected argument 'b'", true),
        (
            &["a", "--clock", "other"][..],
            "invalid value 'other'",
            false,
        ),
        (&["a", "--timeout", "0"][..], TIMEOUT_BOUND, true),
        (&["a", "--timeout", "601"][..], TIMEOUT_BOUND, true),
        (&["a", "--timeout", "nan"][..], TIMEOUT_BOUND, true),
        (&["a", "--timeout", "-1"][..], TIMEOUT_BOUND, true),
        (&["a", "--timeout", "1s"][..], "invalid value '1s'", false),
        (&["a", "--max-bytes", "0"][..], BYTES_BOUND, true),
        (&["a", "--max-bytes", "16777217"][..], BYTES_BOUND, true),
        (
            &["a", "--max-bytes", "1e3"][..],
            "invalid value '1e3'",
            false,
        ),
    ] {
        let (code, out, err) = command(root.root(), &arguments(args), fresh_flag(), &TIMING);
        assert_eq!(code, 2, "{args:?}");
        assert!(out.is_empty(), "{args:?}: {out:?}");
        let text = err.join("\n");
        assert!(text.starts_with("error: "), "{args:?}: {text}");
        assert!(text.contains(message), "{args:?}: {text}");
        assert_eq!(text.contains(USAGE), usage, "{args:?}: {text}");
        assert!(!text.contains('\x1b'), "{text}");
    }
    assert_eq!(listing(root.root()), Vec::<String>::new());
    assert_eq!(
        parse(&arguments(&["image"])).unwrap(),
        Options {
            image: PathBuf::from("image"),
            timeout: DEFAULT_TIMEOUT,
            max_bytes: DEFAULT_MAX_BYTES,
            clock: Clock::Host,
            qemu: None,
            output: None,
        }
    );
    assert_eq!(
        parse(&arguments(&[
            "--timeout",
            "5",
            "--timeout=600",
            "--max-bytes",
            "+16777216",
            "--clock",
            "icount",
            "--clock=host",
            "--clock",
            "icount",
            "--qemu=q",
            "--output-dir",
            "o",
            "--output-dir",
            "p",
            "image",
        ]))
        .unwrap(),
        Options {
            image: PathBuf::from("image"),
            timeout: 600.0,
            max_bytes: 16_777_216,
            clock: Clock::Icount,
            qemu: Some(PathBuf::from("q")),
            output: Some(PathBuf::from("p")),
        }
    );
}

/// Without `--output-dir` the run creates
/// `artifacts/qemu/<%Y%m%dT%H%M%SZ>-<12 hex digits>` below the repository
/// root, with its missing parents.
#[test]
fn the_default_run_directory_is_a_utc_stamp_and_12_hex_digits() {
    let output = default_output(Path::new("/r"));
    assert_eq!(output.parent().unwrap(), Path::new("/r/artifacts/qemu"));
    let name = output.file_name().unwrap().to_str().unwrap();
    let (stamp, suffix) = name.split_once('-').unwrap();
    assert_eq!(stamp.len(), "20261101T120000Z".len(), "{name}");
    assert!(
        stamp.ends_with('Z') && stamp.as_bytes()[8] == b'T',
        "{name}"
    );
    assert!(
        stamp[..8]
            .bytes()
            .chain(stamp[9..15].bytes())
            .all(|byte| byte.is_ascii_digit()),
        "{name}"
    );
    assert_eq!(suffix.len(), 12, "{name}");
    assert!(
        suffix
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
        "{name}"
    );

    let bench = Bench::new("qemu-run-default", "exit 0");
    let root = bench.scratch.path("root");
    let args = arguments(&[
        bench.image.to_str().unwrap(),
        "--qemu",
        bench.qemu.to_str().unwrap(),
        "--timeout",
        "120",
    ]);
    let (code, out, _) = command(&root, &args, fresh_flag(), &TIMING);
    assert_eq!(code, 0);
    let runs: Vec<PathBuf> = std::fs::read_dir(root.join("artifacts/qemu"))
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect();
    assert_eq!(runs.len(), 1);
    assert_eq!(out, printed("guest_shutdown", 0, &runs[0]));
}

/// A failed write on standard output is reported on standard error and
/// makes the status 120; the run itself is complete.
#[test]
fn a_failed_write_of_the_output_gives_status_120() {
    let bench = Bench::new("qemu-run-stdout", "exit 0");
    let mut err = Vec::new();
    let interrupt = fresh_flag();
    let code = run_with(
        bench.scratch.root(),
        &bench.args(&[]),
        &TIMING,
        &mut Console {
            print: &mut |_| Err(io::Error::from_raw_os_error(libc::EPIPE)),
            warn: &mut |line| {
                err.push(line.to_string());
                Ok(())
            },
            arm: &mut || Ok(interrupt),
        },
    );
    assert_eq!(code, 120);
    assert_eq!(
        err,
        ["cargo xtask qemu: cannot write standard output: Broken pipe (os error 32)"]
    );
    assert_eq!(bench.receipt()["exit_reason"], "guest_shutdown");
}

/// The exit status follows the reason, and any error makes it 2.
#[test]
fn the_exit_status_follows_the_reason() {
    for (reason, code) in [
        (ExitReason::GuestShutdown, 0),
        (ExitReason::QemuExit, 1),
        (ExitReason::Deadline, 1),
        (ExitReason::OutputLimit, 1),
        (ExitReason::Interrupted, 130),
        (ExitReason::Error, 2),
    ] {
        let mut receipt = json!({ "exit_reason": reason.name() });
        assert_eq!(exit_code(&receipt), code, "{reason:?}");
        receipt["errors"] = json!(["\"transcript.bin\": Incomplete serial log write"]);
        assert_eq!(exit_code(&receipt), 2, "{reason:?}");
    }
}

/// The options of a library run of the bench's image with its fake QEMU
/// into [`Bench::output`], with a timeout that the run never reaches.
fn library_options(bench: &Bench) -> Options {
    Options {
        image: bench.image.clone(),
        timeout: 120.0,
        max_bytes: DEFAULT_MAX_BYTES,
        clock: Clock::Host,
        qemu: Some(bench.qemu.clone()),
        output: None,
    }
}

/// An input whose trigger is `after` and whose bytes are `bytes`.
fn input(after: &[u8], bytes: &[u8]) -> Input {
    Input {
        after: after.to_vec(),
        bytes: bytes.to_vec(),
    }
}

/// An input of a library run is sent once its trigger has arrived, and
/// what the guest does with it reaches the transcript. The receipt lists
/// the input with its trigger, its bytes, escaped, and the count of output
/// bytes when it was sent, which is that of the trigger line here, as the
/// guest writes nothing more until the input arrives. The deadline passes
/// once the guest has answered.
#[test]
fn an_input_is_sent_once_its_trigger_has_arrived() {
    let bench = Bench::new(
        "qemu-run-input",
        "printf 'READY\\r\\n'\nIFS= read -r line\nprintf 'got:%s\\r\\n' \"$line\"\nexec cat",
    );
    let _deadline = DeadlineAt::new(b"got:abc\r\n");
    let receipt = run_image_with(
        &library_options(&bench),
        &[input(b"READY\r\n", b"abc\n")],
        &bench.output(),
        &TIMING,
        &mut || Ok(fresh_flag()),
    )
    .unwrap();
    assert_eq!(bench.file(TRANSCRIPT_FILE), b"READY\r\ngot:abc\r\n");
    assert_eq!(receipt, bench.receipt());
    assert_eq!(receipt["exit_reason"], "deadline");
    assert!(receipt.get("errors").is_none(), "{receipt}");
    assert_eq!(
        receipt["input"],
        json!([{"after": "READY\\r\\n", "bytes": "abc\\n", "sent_at": 7}])
    );
}

/// The inputs of a run are sent in order, and each waits for its trigger in
/// the output that follows the trigger of the input before it: two inputs
/// with the same trigger need it twice.
#[test]
fn each_input_waits_for_its_trigger_after_the_previous_one() {
    let bench = Bench::new(
        "qemu-run-inputs",
        "printf 'A\\n'\nIFS= read -r one\nprintf 'A\\n'\nIFS= read -r two\nprintf '%s%s\\n' \"$one\" \"$two\"\nexec cat",
    );
    let _deadline = DeadlineAt::new(b"12\n");
    let receipt = run_image_with(
        &library_options(&bench),
        &[input(b"A\n", b"1\n"), input(b"A\n", b"2\n")],
        &bench.output(),
        &TIMING,
        &mut || Ok(fresh_flag()),
    )
    .unwrap();
    assert_eq!(bench.file(TRANSCRIPT_FILE), b"A\nA\n12\n");
    assert_eq!(
        receipt["input"],
        json!([
            {"after": "A\\n", "bytes": "1\\n", "sent_at": 2},
            {"after": "A\\n", "bytes": "2\\n", "sent_at": 4},
        ])
    );
}

/// An input whose trigger never arrives is not sent, and the receipt
/// records it with `sent_at` null; the run ends as it would without it.
#[test]
fn an_input_whose_trigger_never_arrives_is_not_sent() {
    let bench = Bench::new("qemu-run-no-trigger", "printf 'boot\\n'\nexec cat");
    let _deadline = DeadlineAt::new(b"boot\n");
    let receipt = run_image_with(
        &library_options(&bench),
        &[input(b"READY", b"x")],
        &bench.output(),
        &TIMING,
        &mut || Ok(fresh_flag()),
    )
    .unwrap();
    assert_eq!(bench.file(TRANSCRIPT_FILE), b"boot\n");
    assert_eq!(receipt["exit_reason"], "deadline");
    assert_eq!(
        receipt["input"],
        json!([{"after": "READY", "bytes": "x", "sent_at": null}])
    );
}

/// A library run without inputs is the run of `run_image`: its receipt has
/// no `input` key, as that of `cargo xtask qemu` has none.
#[test]
fn a_run_without_inputs_has_no_input_key() {
    let bench = Bench::new("qemu-run-no-input", "printf 'hello\\r\\n'\nexit 0");
    let receipt = run_image_with(
        &library_options(&bench),
        &[],
        &bench.output(),
        &TIMING,
        &mut || Ok(fresh_flag()),
    )
    .unwrap();
    assert_eq!(receipt["exit_reason"], "guest_shutdown");
    assert!(receipt.get("input").is_none(), "{receipt}");
}
