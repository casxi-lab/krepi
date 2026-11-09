//! The QEMU boot suite of the kernel, the command `cargo xtask qemu-boot`:
//! it builds the QEMU virt default image of the kernel workspace, runs its
//! cases on QEMU virt through the QEMU runner of [`crate::qemu_run`] and
//! judges the receipt and the transcript of every run against fixed
//! expected records.
//!
//! Feature: krepi.platform.qemu-virt-boot
//!
//! ```sh
//! cargo xtask qemu-boot [--qemu PATH] [--output-dir OUTPUT_DIR]
//! ```
//!
//! The suite builds the image with
//! `cargo build --locked --release --target aarch64-unknown-none-softfloat
//! -p krepi-qemu-virt --bin krepi-qemu-virt
//! --message-format=json-render-diagnostics` in `kernel/`, with the Cargo
//! that `CARGO` names or else `cargo` from the search path, and takes the
//! image from the artifact message of the binary. It records the output of
//! `rustc -vV` in `kernel/` as the toolchain. `--qemu` names the QEMU
//! executable, as for `cargo xtask qemu`.
//! The suite creates the output directory, which must not exist, with its
//! missing parents: by default `artifacts/qemu-boot/<%Y%m%dT%H%M%SZ>-<12
//! hex digits>` below the repository root. It holds `build.log`, the
//! standard error of the build, a directory `<case>-<n>` for each run, which
//! the runner fills, and the suite receipt `summary.json`, with sorted keys.
//!
//! The one case, `cold-boot-echo`, boots the default image three times, each
//! time in a new QEMU process on the runner's machine, `virt-8.2` without
//! EL2 and EL3 with one Cortex-A76 and the host clock. Once the transcript
//! holds `CASXI_READY` and CR LF, the runner sends `casxi-sim-check` and CR,
//! 16 bytes. The image never stops by itself, so a run ends at its window of
//! [`RUN_WINDOW`] seconds, the platform parameter of QEMU virt for this case,
//! or at [`RUN_MAX_BYTES`] bytes of output. The case passes when every run
//! shows the boot records of the contract of the boot component in order,
//! the echo of the 16 bytes with a line feed after the carriage return and
//! nothing else, and when the three image digests are equal and the three
//! transcripts are identical byte for byte. The expected records are written
//! here from the contract, not taken from an earlier run, and the suite
//! judges no times.
//!
//! The suite exits with 0 for `PASS`, 1 for `FAIL`, 2 for `ERROR`, such as
//! a failed build or a run that could not start, and for a usage error, 130
//! for `INTERRUPTED` and 120 when it cannot write its own output, by the
//! rules of [`crate::console`]. SIGINT, SIGTERM and SIGHUP are caught from
//! immediately before the first QEMU starts, as by the runner.

use crate::console::{Console, Streams, with_process_console};
use crate::qemu::Clock;
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
/// The machine of the runner, which the receipt of every run must name.
pub const MACHINE: &str = "virt-8.2,secure=off,virtualization=off,gic-version=2";
/// The name of the case.
pub const CASE: &str = "cold-boot-echo";
/// The criterion of the case.
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
            "Build the QEMU virt default image and run the QEMU boot suite on it, judging every run against fixed expected records.",
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
/// digest `image_sha256`: no errors; ended at its window by the runner;
/// on the runner's machine with one Cortex-A76, the host clock and no
/// instruction count; the image of the build; a transcript of `transcript`;
/// and the challenge sent once after the ready record.
pub fn check_run_receipt(
    receipt: &Value,
    image_sha256: &str,
    transcript: &[u8],
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
    require(follows("-machine", MACHINE), || {
        format!("the QEMU command does not name the machine {MACHINE}")
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
    )?;
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

/// The path of the executable of the binary [`DEFAULT_IMAGE`] in the
/// messages that `cargo build --message-format=json-render-diagnostics`
/// printed: the last artifact message of the binary with an executable.
pub fn executable_from_messages(messages: &str) -> Option<PathBuf> {
    messages
        .lines()
        .filter_map(|line| serde_json::from_str::<Value>(line).ok())
        .filter(|message| {
            message["reason"] == "compiler-artifact" && message["target"]["name"] == DEFAULT_IMAGE
        })
        .filter_map(|message| message["executable"].as_str().map(PathBuf::from))
        .next_back()
}

/// The command that builds the default image, the Cargo executable first.
/// It selects the board crate with `-p` and the image with `--bin`.
pub fn build_command() -> Vec<String> {
    let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".to_string());
    [
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
        "--message-format=json-render-diagnostics",
    ]
    .map(str::to_string)
    .to_vec()
}

/// Builds the default image in `kernel`, writing the standard error of the
/// build to `log`: the record of the build and the path of the image, or
/// why there is none.
fn build(kernel: &Path, log: &Path) -> (Value, Result<PathBuf, Failure>) {
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
                "the build of the default image failed with {}; see {BUILD_LOG}",
                output.status
            ))),
        );
    }
    let messages = String::from_utf8_lossy(&output.stdout);
    let image = executable_from_messages(&messages)
        .ok_or_else(|| Failure::new("the build named no executable of the default image"));
    (record, image)
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

/// Runs the case `cold-boot-echo` on `image`, whose digest is
/// `image_sha256`, with the QEMU `qemu`, each run into `<output>/<case>-<n>`;
/// the entry of the case in the suite receipt and its outcome. `progress`
/// gets a line for each run. A run that the runner cannot start ends the
/// case as `Error`, and an interrupted run as `Interrupted`, without the
/// runs after it.
pub fn run_case<'a>(
    image: &Path,
    image_sha256: &str,
    qemu: Option<&Path>,
    output: &Path,
    timing: &Timing,
    arm: &mut dyn FnMut() -> Result<&'a AtomicI32, Failure>,
    progress: &mut dyn FnMut(&str),
) -> (Value, Outcome) {
    let options = Options {
        image: image.to_path_buf(),
        timeout: RUN_WINDOW,
        max_bytes: RUN_MAX_BYTES,
        clock: Clock::Host,
        qemu: qemu.map(Path::to_path_buf),
        output: None,
    };
    let inputs = [Input {
        after: READY.to_vec(),
        bytes: CHALLENGE.to_vec(),
    }];
    let mut runs = Vec::new();
    let mut entries = Vec::new();
    let mut stopped = None;
    for number in 1..=RUNS {
        let name = format!("{CASE}-{number}");
        let directory = output.join(&name);
        let receipt = match qemu_run::run_image_with(&options, &inputs, &directory, timing, arm) {
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
    let checks = judge(image_sha256, &runs);
    let outcome = stopped.unwrap_or(if checks.iter().all(|check| check.failure.is_none()) {
        Outcome::Pass
    } else {
        Outcome::Fail
    });
    let entry = json!({
        "name": CASE,
        "criterion": CRITERION,
        "status": outcome.name(),
        "runs": entries,
        "checks": checks.iter().map(Check::report).collect::<Vec<_>>(),
    });
    (entry, outcome)
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
        "image": null,
        "cases": [],
    });
    let (build_record, image) = build(&kernel, &output.join(BUILD_LOG));
    report["build"] = build_record;
    let outcome = match image.and_then(|image| {
        let bytes = std::fs::read(&image).map_err(|error| file_error(&image, error))?;
        Ok((image, bytes))
    }) {
        Err(Failure(error)) => {
            streams.warn(&format!("QEMU boot suite failed: {}", render(&error)));
            report["errors"] = json!([error]);
            Outcome::Error
        }
        Ok((image, bytes)) => {
            let digest = sha256(&bytes);
            report["image"] = json!({
                "path": image.to_string_lossy(),
                "bytes": bytes.len(),
                "sha256": digest,
            });
            let mut lines = Vec::new();
            let (entry, outcome) = run_case(
                &image,
                &digest,
                options.qemu.as_deref(),
                &output,
                timing,
                streams.console.arm,
                &mut |line| lines.push(line.to_string()),
            );
            for line in &lines {
                streams.print(line);
            }
            report["cases"] = json!([entry]);
            outcome
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
