//! A bounded run of an ELF image on QEMU virt, which records the guest's
//! serial output and does not evaluate it: the command `cargo xtask qemu`.
//!
//! ```sh
//! cargo xtask qemu [--timeout SECONDS] [--max-bytes MAX_BYTES] \
//!     [--clock CLOCK] [--qemu PATH] [--output-dir OUTPUT_DIR] <ELF>
//! ```
//!
//! The run starts QEMU with the command line of [`qemu::build_command`]: one
//! Cortex-A76 on the machine `virt-8.2` without EL2 and EL3 under
//! single-threaded TCG, 128 MiB, no network card, the image `<ELF>` loaded
//! with `-kernel` and the PL011 on QEMU's standard streams. `--clock` chooses
//! the guest's time source, `host` (the default) or `icount`; `--qemu` names
//! the executable, by default `qemu-system-aarch64` on the search path. The
//! run creates the output directory, which must not exist, with its missing
//! parents: by default `artifacts/qemu/<%Y%m%dT%H%M%SZ>-<12 hex digits>`
//! below the repository root. QEMU's standard error goes to
//! `qemu-stderr.txt` in it, never into the serial output, and its standard
//! input is a pipe that stays open: `cargo xtask qemu` sends nothing on it,
//! and a run through [`run_image_with`] sends its inputs.
//!
//! The run ends when QEMU ends by itself, when it has run for `--timeout`
//! seconds (default 60, greater than 0 and at most 600), when more than
//! `--max-bytes` bytes of serial output (default 262144, at most 16777216)
//! have arrived, or at an interrupt; in the last three cases the runner stops
//! QEMU with SIGTERM, and with a kill if it has not ended within the stop
//! grace. The runner then collects the rest of the output, writes it to
//! `transcript.bin` and writes the receipt `summary.json`, with sorted keys.
//! The exit reason follows from what the runner did and from QEMU's report
//! of a signal, not from QEMU's exit status alone, as QEMU exits with status
//! 0 when SIGINT, SIGTERM or SIGHUP ends it, from the runner or from another
//! process, and reports the signal on its standard error as
//! `<program>: terminating on signal <N>`:
//!
//! - `guest_shutdown`: QEMU ended by itself with status 0 and reported no
//!   signal, which a guest that powers the machine off causes;
//! - `qemu_exit`: QEMU ended by itself with another status, by a signal that
//!   the runner did not send, or with status 0 after it reported such a
//!   signal;
//! - `deadline`: QEMU still ran at the timeout, and the runner stopped it;
//! - `output_limit`: more than `--max-bytes` bytes of serial output arrived,
//!   while QEMU ran or while the runner collected the rest, and the runner
//!   stopped QEMU if it still ran;
//! - `interrupted`: SIGINT, SIGTERM or SIGHUP reached the runner, which
//!   stopped QEMU if it still ran;
//! - `error`: QEMU did not start, as it or the interrupt handlers could not
//!   be started or installed.
//!
//! `interrupted` takes precedence over `output_limit`, and `output_limit`
//! over the others. The transcript holds every byte that the guest wrote to
//! its UART up to the read that passed the limit, which is kept whole, so
//! that it may hold up to 64 KiB more than the limit. The receipt describes
//! `transcript.bin` and `qemu-stderr.txt` as they are on disk once the run
//! has ended; a step that failed, such as a write of the transcript, adds
//! its error to `errors`.
//!
//! The command prints `<exit reason>: <bytes> bytes of serial output; the
//! output is not evaluated.` and `Receipt: <summary.json>`, and exits with 0
//! for `guest_shutdown`, 1 for `qemu_exit`, `deadline` and `output_limit`,
//! 130 for `interrupted`, and 2 for `error`, for a receipt with `errors`,
//! for a usage error and for a run that fails before QEMU starts, which
//! writes no receipt and is reported as `QEMU run failed: <error>` on
//! standard error, such as a missing or unreadable image, a missing QEMU
//! executable, a failed version query or an output directory that exists or
//! cannot be created. The output streams follow the rules of
//! [`crate::console`], which give status 120 for a failed write.
//!
//! A suite that drives a guest runs it through [`run_image_with`], the same
//! run with a list of [`Input`]s: each sends its bytes once to the guest's
//! serial input, as soon as the output that follows the previous input's
//! trigger holds its own trigger. The receipt of such a run has one more
//! key, `input`, which lists each input with its trigger, its bytes and the
//! count of output bytes when it was sent; a failed send adds its error to
//! `errors`. The command `cargo xtask qemu` sends nothing, and its receipt
//! has no `input` key.
//!
//! `clap` reads the command line as it reads that of `cargo xtask
//! serial-capture`: an option with a value takes it as `--option=value` or
//! as the next argument, a repeated option keeps its last value,
//! `--timeout` and `--max-bytes` take a negative number as the next argument
//! too, and the limits are checked once clap has read the command line. The
//! help goes to standard output with status 0 and a usage error to standard
//! error with status 2, both without colour.
//!
//! SIGINT, SIGTERM and SIGHUP are caught from immediately before QEMU starts
//! and end the run as `interrupted`, with the receipt written; before that,
//! they keep the dispositions that the process started with. QEMU stays in
//! the runner's process group, so a terminal's interrupt reaches both; the
//! runner looks at its interrupt flag once more after QEMU has ended by
//! itself, so that such an interrupt counts as `interrupted`.

use crate::console::{Console, Streams, with_process_console};
use crate::qemu::{self, Clock, SerialCapture};
use crate::report::{Value, to_json, utc_now};
use crate::serial_capture::{
    BYTES_BOUND, DEFAULT_MAX_BYTES, MAX_BYTES, create_output, file_error, pure_path,
    read_max_bytes, render, render_name, run_directory, write_new,
};
use crate::timing::Timing;
use crate::{Failure, hex};
use clap::Arg;
use clap::builder::PossibleValuesParser;
use clap::error::ErrorKind;
use serde_json::json;
use sha2::{Digest, Sha256};
use std::fs::File;
use std::io::{self, BufRead, BufReader, Read};
use std::path::{Path, PathBuf};
use std::process::Child;
use std::sync::atomic::{AtomicI32, Ordering};
use std::time::{Duration, Instant};

/// The timeout in seconds without `--timeout`.
pub const DEFAULT_TIMEOUT: f64 = 60.0;
/// The longest timeout in seconds.
pub const MAX_TIMEOUT: f64 = 600.0;
/// The message of a timeout out of bounds.
pub const TIMEOUT_BOUND: &str = "timeout must be finite and greater than 0, at most 600";
/// The serial output in the run directory.
pub const TRANSCRIPT_FILE: &str = "transcript.bin";
/// QEMU's standard error in the run directory.
pub const STDERR_FILE: &str = "qemu-stderr.txt";
/// The receipt in the run directory.
pub const SUMMARY_FILE: &str = "summary.json";
/// The run directories below the repository root.
const OUTPUT_DIR: &str = "artifacts/qemu";
/// The name that the usage, the help, a usage error and the report of a
/// failed output write give the command.
const PROG: &str = "cargo xtask qemu";

/// The limits of a run: `timeout` finite, greater than 0 and at most
/// [`MAX_TIMEOUT`] seconds, and `max_bytes` from 1 to [`MAX_BYTES`].
pub fn check_limits(timeout: f64, max_bytes: u64) -> Result<(), Failure> {
    if !(timeout.is_finite() && timeout > 0.0 && timeout <= MAX_TIMEOUT) {
        return Err(Failure::new(TIMEOUT_BOUND));
    }
    if !(1..=MAX_BYTES).contains(&max_bytes) {
        return Err(Failure::new(BYTES_BOUND));
    }
    Ok(())
}

/// What a command line asks for, apart from the help.
#[derive(Clone, Debug, PartialEq)]
pub struct Options {
    /// `<ELF>`, the image that QEMU loads.
    pub image: PathBuf,
    /// `--timeout`, in seconds.
    pub timeout: f64,
    /// `--max-bytes`.
    pub max_bytes: u64,
    /// `--clock`.
    pub clock: Clock,
    /// `--qemu`.
    pub qemu: Option<PathBuf>,
    /// `--output-dir`.
    pub output: Option<PathBuf>,
}

/// The command line as clap reads it: the image and the five options with
/// [`DEFAULT_TIMEOUT`], [`DEFAULT_MAX_BYTES`] and the host clock written out
/// as their defaults. The help and the usage name the command [`PROG`].
fn cli() -> clap::Command {
    clap::Command::new("qemu")
        .bin_name(PROG)
        .no_binary_name(true)
        .about(
            "Run an ELF image on QEMU virt until the guest powers off or a limit ends the run, recording its serial output without evaluating it.",
        )
        .args_override_self(true)
        .arg(
            Arg::new("elf")
                .value_name("ELF")
                .required(true)
                .help("image that QEMU loads with -kernel"),
        )
        .arg(
            Arg::new("timeout")
                .long("timeout")
                .value_name("SECONDS")
                .value_parser(clap::value_parser!(f64))
                .allow_negative_numbers(true)
                .default_value("60")
                .help("longest run before QEMU is stopped, greater than 0 and at most 600"),
        )
        .arg(
            Arg::new("max-bytes")
                .long("max-bytes")
                .value_name("MAX_BYTES")
                .value_parser(read_max_bytes)
                .allow_negative_numbers(true)
                .default_value("262144")
                .help("serial output limit, at most 16777216"),
        )
        .arg(
            Arg::new("clock")
                .long("clock")
                .value_name("CLOCK")
                .value_parser(PossibleValuesParser::new(["host", "icount"]))
                .default_value("host")
                .help("guest time source: the host clock or a fixed instruction count"),
        )
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
                .help("new run directory; must not already exist"),
        )
}

/// The run that a command line asks for, or clap's error: the help for `-h`
/// and `--help`, or a usage error, which a limit outside [`check_limits`] is
/// too, with the bound as its message.
pub fn parse(args: &[String]) -> Result<Options, clap::Error> {
    let mut cli = cli();
    let matches = cli.try_get_matches_from_mut(args)?;
    // These always have a value, their own or the default, and the clock is
    // one of the possible values.
    let timeout = *matches.get_one("timeout").unwrap_or(&DEFAULT_TIMEOUT);
    let max_bytes = *matches.get_one("max-bytes").unwrap_or(&DEFAULT_MAX_BYTES);
    let clock = matches
        .get_one::<String>("clock")
        .and_then(|name| Clock::parse(name))
        .unwrap_or(Clock::Host);
    check_limits(timeout, max_bytes)
        .map_err(|Failure(bound)| cli.error(ErrorKind::ValueValidation, bound))?;
    let path = |name: &str| matches.get_one::<String>(name).map(PathBuf::from);
    Ok(Options {
        image: path("elf").unwrap_or_default(),
        timeout,
        max_bytes,
        clock,
        qemu: path("qemu"),
        output: path("output-dir"),
    })
}

/// `artifacts/qemu/<%Y%m%dT%H%M%SZ>-<12 hex digits>` below `root`.
fn default_output(root: &Path) -> PathBuf {
    run_directory(root, OUTPUT_DIR)
}

/// Why a run ended; the module documentation describes each.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ExitReason {
    GuestShutdown,
    QemuExit,
    Deadline,
    OutputLimit,
    Interrupted,
    Error,
}

impl ExitReason {
    /// The name that the receipt records.
    pub fn name(self) -> &'static str {
        match self {
            ExitReason::GuestShutdown => "guest_shutdown",
            ExitReason::QemuExit => "qemu_exit",
            ExitReason::Deadline => "deadline",
            ExitReason::OutputLimit => "output_limit",
            ExitReason::Interrupted => "interrupted",
            ExitReason::Error => "error",
        }
    }
}

/// The exit status of a run with the receipt `report`: 2 when it has
/// `errors`, else 0 for `guest_shutdown`, 130 for `interrupted`, 2 for
/// `error` and 1 otherwise.
fn exit_code(report: &Value) -> i32 {
    if report.get("errors").is_some() {
        return 2;
    }
    match report["exit_reason"].as_str() {
        Some("guest_shutdown") => 0,
        Some("interrupted") => 130,
        Some("qemu_exit" | "deadline" | "output_limit") => 1,
        _ => 2,
    }
}

/// A fault that the unit tests inject on their own thread: a deadline that
/// the guest's output, not the clock, decides.
#[cfg(test)]
pub(crate) mod seams {
    use std::cell::Cell;

    thread_local! {
        /// Bytes whose arrival stands for the timeout: the deadline of a run
        /// counts as passed once its output holds them, and not before.
        pub static DEADLINE_AT: Cell<Option<&'static [u8]>> = const { Cell::new(None) };
    }
}

/// Whether the deadline of a run has passed at `now`.
fn deadline_passed(deadline: Option<Instant>, now: Instant, received: &[u8]) -> bool {
    #[cfg(test)]
    if let Some(marker) = seams::DEADLINE_AT.get() {
        return received
            .windows(marker.len())
            .any(|window| window == marker);
    }
    let _ = received;
    deadline.is_some_and(|deadline| now >= deadline)
}

fn interrupted(flag: &AtomicI32) -> bool {
    flag.load(Ordering::SeqCst) != 0
}

/// The text of QEMU's report on its standard error that a signal ended it,
/// `<program>: terminating on signal <N>`, followed by the sending process
/// when QEMU knows it. QEMU writes it at SIGINT, SIGTERM or SIGHUP and then
/// exits with status 0.
const SIGNAL_REPORT: &[u8] = b": terminating on signal ";

/// Whether the file `path`, QEMU's standard error, holds a line with
/// [`SIGNAL_REPORT`]. A file that cannot be read holds none; the receipt
/// reports it in `errors`.
fn signal_reported(path: &Path) -> bool {
    let Ok(file) = File::open(path) else {
        return false;
    };
    BufReader::new(file)
        .split(b'\n')
        .map_while(Result::ok)
        .any(|line| {
            line.windows(SIGNAL_REPORT.len())
                .any(|window| window == SIGNAL_REPORT)
        })
}

/// The count of bytes of the file `path` and their SHA-256 digest, read in
/// pieces.
fn digest_file(path: &Path) -> io::Result<(u64, String)> {
    let mut file = File::open(path)?;
    let mut digest = Sha256::new();
    let mut buffer = vec![0u8; 65536];
    let mut bytes = 0u64;
    loop {
        match file.read(&mut buffer) {
            Ok(0) => break,
            Ok(count) => {
                digest.update(&buffer[..count]);
                bytes += count as u64;
            }
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) => return Err(error),
        }
    }
    Ok((bytes, hex(&digest.finalize())))
}

/// The entry of the receipt for the file `name` in `output` as it is on
/// disk: its name, its count of bytes and their SHA-256 digest; null, with
/// the error in `errors`, for a file that cannot be read.
fn describe(output: &Path, name: &str, errors: &mut Vec<String>) -> Value {
    let path = output.join(name);
    match digest_file(&path) {
        Ok((bytes, sha256)) => json!({ "file": name, "bytes": bytes, "sha256": sha256 }),
        Err(error) => {
            errors.push(file_error(&path, error).0);
            Value::Null
        }
    }
}

/// Bytes that a run sends to the guest's serial input once its output holds
/// a trigger.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Input {
    /// The trigger: bytes that must arrive in the output after the trigger of
    /// the previous input, or from the start for the first input.
    pub after: Vec<u8>,
    /// The bytes sent once the trigger has arrived.
    pub bytes: Vec<u8>,
}

/// The inputs of a run and how far each got: the output offset just after
/// the latest trigger found, for each input the count of output bytes when
/// it was sent, and the errors of failed sends.
struct Inputs<'a> {
    inputs: &'a [Input],
    from: usize,
    sent_at: Vec<Option<usize>>,
    errors: Vec<String>,
}

impl<'a> Inputs<'a> {
    fn new(inputs: &'a [Input]) -> Self {
        Inputs {
            inputs,
            from: 0,
            sent_at: vec![None; inputs.len()],
            errors: Vec::new(),
        }
    }

    /// Sends every input, in order, whose trigger the output of `capture`
    /// holds after the trigger of the input before it. A failed send keeps
    /// its error and still counts as sent, so that it is not repeated.
    fn send_due(&mut self, child: &mut Child, capture: &mut SerialCapture) {
        while let Some(index) = self.sent_at.iter().position(Option::is_none) {
            let input = &self.inputs[index];
            let rest = &capture.received[self.from.min(capture.received.len())..];
            let Some(found) = find(rest, &input.after) else {
                return;
            };
            self.from += found + input.after.len();
            self.sent_at[index] = Some(capture.received.len());
            if let Err(Failure(error)) = capture.send(child, &input.bytes) {
                self.errors
                    .push(format!("send of input {}: {error}", index + 1));
            }
        }
    }

    /// The entry of the receipt: each input with `after` and `bytes` in the
    /// escapes of `<[u8]>::escape_ascii` and `sent_at`, null for an input
    /// that was not sent.
    fn report(&self) -> Value {
        let entries = self.inputs.iter().zip(&self.sent_at);
        Value::Array(
            entries
                .map(|(input, sent_at)| {
                    json!({
                        "after": input.after.escape_ascii().to_string(),
                        "bytes": input.bytes.escape_ascii().to_string(),
                        "sent_at": sent_at,
                    })
                })
                .collect(),
        )
    }
}

/// The offset of the first occurrence of `needle`, which is not empty, in
/// `haystack`; an empty `needle` occurs at 0.
fn find(haystack: &[u8], needle: &[u8]) -> Option<usize> {
    if needle.is_empty() {
        return Some(0);
    }
    haystack
        .windows(needle.len())
        .position(|window| window == needle)
}

/// Why the loop of [`supervise`] ended.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Stop {
    Interrupted,
    OutputLimit,
    Ended,
    Deadline,
}

/// Supervises the started `child`, whose output `capture` reads, until it
/// ends, `deadline` passes, its output passes `limit` or `interrupt` holds a
/// signal, sending `inputs` as their triggers arrive, and stops it: the exit
/// reason and the stop report of [`qemu::stop_process`].
fn supervise(
    child: &mut Child,
    capture: &mut SerialCapture,
    limit: usize,
    deadline: Option<Instant>,
    interrupt: &AtomicI32,
    timing: &Timing,
    inputs: &mut Inputs,
) -> (ExitReason, Value) {
    let stop = loop {
        if interrupted(interrupt) {
            break Stop::Interrupted;
        }
        if capture.received.len() > limit {
            break Stop::OutputLimit;
        }
        if matches!(child.try_wait(), Ok(Some(_))) {
            break Stop::Ended;
        }
        let now = Instant::now();
        if deadline_passed(deadline, now, &capture.received) {
            break Stop::Deadline;
        }
        inputs.send_due(child, capture);
        let left = deadline.map_or(timing.guest_slice, |deadline| {
            deadline.saturating_duration_since(now)
        });
        if capture.ended() {
            std::thread::sleep(timing.reap_poll.min(left));
        } else {
            capture.read(timing.guest_slice.min(left));
        }
    };
    let process = qemu::stop_process(child, timing);
    let signalled = process["intentional_shutdown"] == true;
    let reason = match stop {
        Stop::Interrupted => ExitReason::Interrupted,
        Stop::OutputLimit => ExitReason::OutputLimit,
        // An interrupt from a terminal reaches QEMU as well, which may end
        // by it before the runner looks at its flag.
        _ if interrupted(interrupt) => ExitReason::Interrupted,
        Stop::Deadline if signalled => ExitReason::Deadline,
        _ if process["exit_code"] == 0 => ExitReason::GuestShutdown,
        _ => ExitReason::QemuExit,
    };
    (reason, process)
}

/// Collects the rest of the output of a stopped QEMU into the transcript at
/// `transcript_path` and writes it: the exit reason `reason`, or
/// `output_limit` in place of any but `interrupted` when the output passed
/// `limit` meanwhile. A failed write adds its error to `errors`.
fn collect_rest(
    capture: &mut SerialCapture,
    reason: ExitReason,
    limit: usize,
    timing: &Timing,
    transcript_path: &Path,
    errors: &mut Vec<String>,
) -> ExitReason {
    let over = capture.received.len() > limit;
    // The collection, the look past the limit below included, lasts at most
    // `timing.guest_finish`. It ends with the stream, once the output reaches
    // the limit, or with a failure once it passes the limit, without writing
    // the transcript then.
    let finish = Instant::now().checked_add(timing.guest_finish);
    let collected = capture.finish_guarded();
    if collected.is_ok() && capture.received.len() == limit && !capture.ended() {
        // Output that stopped the collection exactly at the limit may have
        // more behind it, which the rest of the collection's time may bring.
        let left = finish.map_or(timing.guest_finish, |finish| {
            finish.saturating_duration_since(Instant::now())
        });
        capture.read(left);
    }
    let passed = !over && capture.received.len() > limit;
    // Writing the transcript again writes only the bytes not yet written.
    let written = if collected.is_ok() || passed {
        capture.write_deferred_log()
    } else {
        collected
    };
    if let Err(Failure(error)) = written {
        errors.push(format!("{transcript_path:?}: {error}"));
    }
    if passed && reason != ExitReason::Interrupted {
        ExitReason::OutputLimit
    } else {
        reason
    }
}

/// One run of `options.image` on QEMU into the new directory `output`, which
/// returns the receipt that `summary.json` holds with sorted keys; the
/// supervision waits as `timing` gives. `arm` is called immediately before
/// QEMU starts, to install the interrupt handlers; it returns the flag they
/// set, which ends the run as `interrupted`. Limits outside
/// [`check_limits`], a missing image or QEMU executable, a failed version
/// query, an output directory that exists or cannot be created and files
/// that cannot be created or written there are errors; a failed `arm` or
/// start of QEMU ends the run as `error`, with a receipt.
pub fn run_image<'a>(
    options: &Options,
    output: &Path,
    timing: &Timing,
    arm: &mut dyn FnMut() -> Result<&'a AtomicI32, Failure>,
) -> Result<Value, Failure> {
    run_image_with(options, &[], output, timing, arm)
}

/// [`run_image`] that sends `inputs` to the guest as their triggers arrive.
/// With inputs, the receipt has the key `input`; without them, the run and
/// its receipt are those of [`run_image`].
pub fn run_image_with<'a>(
    options: &Options,
    inputs: &[Input],
    output: &Path,
    timing: &Timing,
    arm: &mut dyn FnMut() -> Result<&'a AtomicI32, Failure>,
) -> Result<Value, Failure> {
    check_limits(options.timeout, options.max_bytes)?;
    let executable = qemu::resolve_qemu(options.qemu.as_deref())?;
    let command = qemu::build_command(&options.image, Some(&executable), options.clock)?;
    // The command ends with the canonical path of the image.
    let image = PathBuf::from(command.last().map_or("", String::as_str));
    let (image_bytes, image_sha256) =
        digest_file(&image).map_err(|error| file_error(&image, error))?;
    let version = qemu::version(&executable)?;
    create_output(output)?;
    let transcript_path = output.join(TRANSCRIPT_FILE);
    let transcript =
        File::create_new(&transcript_path).map_err(|error| file_error(&transcript_path, error))?;
    let stderr_path = output.join(STDERR_FILE);
    let stderr = File::create_new(&stderr_path).map_err(|error| file_error(&stderr_path, error))?;
    let limit = usize::try_from(options.max_bytes).unwrap_or(usize::MAX);
    let timeout = Duration::from_secs_f64(options.timeout);
    let mut errors: Vec<String> = Vec::new();
    let mut sent = Inputs::new(inputs);
    let started_at = utc_now();
    let started = Instant::now();
    let mut stopped = None;
    let (reason, process) = match arm() {
        Err(Failure(error)) => {
            errors.push(error);
            (ExitReason::Error, Value::Null)
        }
        Ok(interrupt) => match qemu::spawn_with_stderr(&command, stderr) {
            Err(error) => {
                errors.push(file_error(&executable, error).0);
                (ExitReason::Error, Value::Null)
            }
            Ok(mut child) => {
                match SerialCapture::guarded(&mut child, transcript, limit, &[], timing) {
                    Err(Failure(error)) => {
                        errors.push(error);
                        (ExitReason::Error, qemu::stop_process(&mut child, timing))
                    }
                    Ok(mut capture) => {
                        let deadline = started.checked_add(timeout);
                        let (reason, process) = supervise(
                            &mut child,
                            &mut capture,
                            limit,
                            deadline,
                            interrupt,
                            timing,
                            &mut sent,
                        );
                        errors.append(&mut sent.errors);
                        stopped = Some(started.elapsed());
                        let reason = match collect_rest(
                            &mut capture,
                            reason,
                            limit,
                            timing,
                            &transcript_path,
                            &mut errors,
                        ) {
                            // A signal from another process ends QEMU with
                            // status 0 too, which QEMU reports.
                            ExitReason::GuestShutdown if signal_reported(&stderr_path) => {
                                ExitReason::QemuExit
                            }
                            reason => reason,
                        };
                        (reason, process)
                    }
                }
            }
        },
    };
    let elapsed = stopped.unwrap_or_else(|| started.elapsed());
    let transcript = describe(output, TRANSCRIPT_FILE, &mut errors);
    let stderr = describe(output, STDERR_FILE, &mut errors);
    let mut report = json!({
        "schema_version": 1,
        "exit_reason": reason.name(),
        "started_at": started_at,
        "finished_at": utc_now(),
        "elapsed_seconds": elapsed.as_secs_f64(),
        "timeout_seconds": options.timeout,
        "max_bytes": options.max_bytes,
        "clock": options.clock.name(),
        "image": {
            "path": image.to_string_lossy(),
            "bytes": image_bytes,
            "sha256": image_sha256,
        },
        "qemu": {
            "executable": executable.to_string_lossy(),
            "version": version,
            "command": command,
        },
        "process": process,
        "transcript": transcript,
        "stderr": stderr,
    });
    if !inputs.is_empty() {
        report["input"] = sent.report();
    }
    if !errors.is_empty() {
        report["errors"] = errors.into();
    }
    report.sort_all_objects();
    write_new(&output.join(SUMMARY_FILE), to_json(&report).as_bytes())?;
    Ok(report)
}

/// The command entry point: the lines go to the standard streams, the
/// interrupt handlers are installed immediately before QEMU starts, and the
/// run waits as `Timing::QEMU_VIRT` gives. Returns the exit status of the
/// process.
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

/// One run over `streams`: the exit status of its work.
fn run(root: &Path, args: &[String], timing: &Timing, streams: &mut Streams) -> i32 {
    let options = match parse(args) {
        Ok(options) => options,
        Err(error) => return streams.clap_error(&error),
    };
    let output = pure_path(
        &options
            .output
            .clone()
            .unwrap_or_else(|| default_output(root)),
    );
    let report = match run_image(&options, &output, timing, streams.console.arm) {
        Ok(report) => report,
        Err(Failure(message)) => {
            streams.warn(&format!("QEMU run failed: {}", render(&message)));
            return 2;
        }
    };
    let reason = report["exit_reason"].as_str().unwrap_or("error");
    let bytes = report["transcript"]["bytes"].as_u64().unwrap_or(0);
    streams.print(&format!(
        "{reason}: {bytes} bytes of serial output; the output is not evaluated."
    ));
    let resolved = std::fs::canonicalize(&output)
        .or_else(|_| std::path::absolute(&output))
        .unwrap_or_else(|_| output.clone());
    let summary = resolved.join(SUMMARY_FILE);
    streams.print(&format!("Receipt: {}", render_name(summary.as_os_str())));
    exit_code(&report)
}

#[cfg(test)]
mod tests;
