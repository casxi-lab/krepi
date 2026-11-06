//! A bounded capture of what a board sends over a serial port, which does
//! not evaluate the board's boot: the command `cargo xtask serial-capture`.
//!
//! ```sh
//! cargo xtask serial-capture --list
//! cargo xtask serial-capture --port <tty> [--seconds SECONDS] \
//!     [--max-bytes MAX_BYTES] [--output-dir OUTPUT_DIR]
//! ```
//!
//! `--list` prints the likely USB serial devices below `/dev`, the entries of
//! any type whose names start with `cu.usb`, `ttyUSB` or `ttyACM`, in the
//! byte order of their names, without opening them. `--port` names the tty
//! to capture; no device is chosen automatically. The capture creates the
//! output directory, which must not exist, with its missing parents: by
//! default `artifacts/hardware-uart/<%Y%m%dT%H%M%SZ>-<12 hex digits>` below
//! the repository root. It opens the port read-only with a [`Receiver`],
//! which holds it exclusively with raw 115200 8N1 attributes and sends
//! nothing, and receives for `--seconds` (default 30, greater than 0 and at
//! most 300) or until `--max-bytes` (default 262144, at most 16777216) have
//! arrived, reading never more than the limit leaves room for, so that later
//! input stays queued, or until the device ends. It restores the port's
//! attributes and writes `raw.bin`, the bytes received; `preview.txt`, the
//! first 16 KiB decoded as UTF-8 with replacement characters and rendered for
//! a terminal (see [`render`]); and `summary.json`, the receipt, with sorted
//! keys. The command prints the preview, `<status>: <bytes> bytes; board boot
//! is not evaluated.` and `Receipt: <summary.json>`.
//!
//! The command exits with 0 for `CAPTURED` and `NO_DATA`, 130 for
//! `INTERRUPTED`, and 2 for `FAIL`, for a usage error and for a capture that
//! cannot create or write its files, which is reported as `UART capture
//! failed: <error>` on standard error. After a failed write on standard
//! output it writes nothing more there and ends with `cargo xtask
//! serial-capture: cannot write standard output: <error>` on standard error
//! and status 120; a failed write on standard error makes the status 120 as
//! well.
//!
//! `clap` reads the command line, which takes the seven options `-h`,
//! `--help`, `--list`, `--port`, `--seconds`, `--max-bytes` and
//! `--output-dir` and exactly one of `--list` and `--port`. An option with a
//! value takes it as `--option=value` or as the next argument, a repeated
//! option keeps its last value, and `--seconds` and `--max-bytes` take a
//! negative number as the next argument too. `--seconds` is a number as
//! Rust's `f64` reads it, and `--max-bytes` a decimal integer as Rust's
//! `u64` reads it, where an integer too large for 64 bits is out of bounds.
//! The limits are checked once clap has read the command line. The help, the
//! usage and the usage errors are clap's texts, without colour and not
//! wrapped to the terminal: the help goes to standard output with status 0,
//! a usage error to standard error with status 2.
//!
//! SIGINT, SIGTERM and SIGHUP are caught from immediately before the port
//! opens and end the capture as `INTERRUPTED`, with the port restored and the
//! receipt written; the handlers replace an inherited `SIG_IGN`, so that a
//! signal left ignored, as `nohup` leaves SIGHUP, ends the capture too.
//! Before the port opens, the three keep the dispositions that the process
//! started with. A signal caught once the capture has ended, while the port
//! is restored and the files are written, leaves the outcome as it is.
//! `raw.bin` is written unbuffered, so that a failed write ends the capture
//! with the error in the read that fails it; the bytes that reached the file
//! before the failure are counted in the receipt. A write past a file-size
//! limit raises SIGXFSZ, whose default action ends the process without a
//! receipt and with the port left raw.

use crate::report::{Map, Value, to_json, utc_now, utc_stamp};
use crate::timing::Timing;
use crate::tty::{self, Receiver};
use crate::{Failure, hex};
use clap::error::ErrorKind;
use clap::{Arg, ArgAction, ArgGroup, value_parser};
use sha2::{Digest, Sha256};
use std::ffi::OsStr;
use std::fs::File;
use std::io::{self, Write};
use std::os::unix::ffi::OsStrExt;
use std::path::{Component, Path, PathBuf};
use std::sync::atomic::{AtomicI32, Ordering};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

/// The line rate that the receipt records.
pub const BAUD: u32 = 115_200;
/// The byte limit without `--max-bytes`.
pub const DEFAULT_MAX_BYTES: u64 = 256 * 1024;
/// The largest byte limit.
pub const MAX_BYTES: u64 = 16 * 1024 * 1024;
/// The bytes of the capture that `preview.txt` renders.
pub const PREVIEW_BYTES: usize = 16 * 1024;
/// The duration in seconds without `--seconds`.
pub const DEFAULT_SECONDS: f64 = 30.0;
/// The longest duration in seconds.
pub const MAX_SECONDS: f64 = 300.0;
/// The run directories below the repository root.
const OUTPUT_DIR: &str = "artifacts/hardware-uart";
/// The most bytes one read takes.
const READ_CHUNK: usize = 65536;
/// The message of a duration out of bounds.
pub const SECONDS_BOUND: &str = "seconds must be finite and greater than 0, at most 300";
/// The message of a byte limit out of bounds.
pub const BYTES_BOUND: &str = "max-bytes must be an integer between 1 and 16777216";

/// The name that the usage, the help, a usage error and the report of a
/// failed output write give the command.
const PROG: &str = "cargo xtask serial-capture";

/// The limits of a capture: `seconds` finite, greater than 0 and at most
/// [`MAX_SECONDS`], and `max_bytes` from 1 to [`MAX_BYTES`].
pub fn check_limits(seconds: f64, max_bytes: u64) -> Result<(), Failure> {
    if !(seconds.is_finite() && seconds > 0.0 && seconds <= MAX_SECONDS) {
        return Err(Failure::new(SECONDS_BOUND));
    }
    if !(1..=MAX_BYTES).contains(&max_bytes) {
        return Err(Failure::new(BYTES_BOUND));
    }
    Ok(())
}

/// The characters that [`render`] writes as they are, although
/// `str::escape_debug` escapes them.
const KEPT: [char; 5] = ['\n', '\t', '\\', '"', '\''];

/// Appends `text` to `out` as [`render`] writes it.
fn render_into(text: &str, out: &mut String) {
    for piece in text.split_inclusive(KEPT) {
        let (run, kept) = match piece.chars().next_back() {
            Some(last) if KEPT.contains(&last) => {
                (&piece[..piece.len() - last.len_utf8()], Some(last))
            }
            _ => (piece, None),
        };
        out.extend(run.escape_debug());
        out.extend(kept);
    }
}

/// `text` rendered for a terminal: newline, tab, backslash and both quotes
/// stay as they are, and each run of text between them is written as
/// `str::escape_debug` writes it. That escapes, by the Unicode tables of the
/// toolchain, control, format, private-use, default-ignorable and
/// unassigned characters and white space other than the space, such as ESC
/// as `\u{1b}`, carriage return as `\r`, NUL as `\0` and the bidirectional
/// and zero-width format characters, and a grapheme extender, such as a
/// combining mark, only at the start of a run.
pub fn render(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    render_into(text, &mut out);
    out
}

/// The name `name` rendered for a terminal: its text as [`render`] writes
/// it, and each byte that does not decode as UTF-8 as `\xNN`.
pub fn render_name(name: &OsStr) -> String {
    let mut out = String::new();
    for chunk in name.as_bytes().utf8_chunks() {
        render_into(chunk.valid(), &mut out);
        for byte in chunk.invalid() {
            out.push_str(&format!("\\x{byte:02x}"));
        }
    }
    out
}

/// The entries of `directory` of any type whose names start with `cu.usb`,
/// `ttyUSB` or `ttyACM`, case-sensitively, in the byte order of their
/// names; none for a directory that cannot be read. Nothing is opened.
pub fn list_ports(directory: &Path) -> Vec<PathBuf> {
    let Ok(entries) = std::fs::read_dir(directory) else {
        return Vec::new();
    };
    let mut names: Vec<_> = entries
        .flatten()
        .map(|entry| entry.file_name())
        .filter(|name| {
            let name = name.as_bytes();
            [&b"cu.usb"[..], b"ttyUSB", b"ttyACM"]
                .iter()
                .any(|prefix| name.starts_with(prefix))
        })
        .collect();
    names.sort_by(|a, b| a.as_bytes().cmp(b.as_bytes()));
    names.into_iter().map(|name| directory.join(name)).collect()
}

fn interrupted(flag: &AtomicI32) -> bool {
    flag.load(Ordering::SeqCst) != 0
}

/// The failure of an operation on `path`: the path in Rust's debug form and
/// the error, `"<path>": strerror (os error N)`.
fn file_error(path: &Path, error: io::Error) -> Failure {
    Failure::new(format!("{path:?}: {error}"))
}

/// `path` without `.` components and without repeated or trailing
/// separators, `.` when nothing remains.
fn pure_path(path: &Path) -> PathBuf {
    let pure: PathBuf = path
        .components()
        .filter(|component| *component != Component::CurDir)
        .collect();
    if pure.as_os_str().is_empty() {
        PathBuf::from(".")
    } else {
        pure
    }
}

/// Creates the new directory `output`, which must not exist, and, when a
/// parent is missing, its missing parents first. An error names the path
/// that its step was given: `output` itself, or its parent while the
/// parents are created.
fn create_output(output: &Path) -> Result<(), Failure> {
    match std::fs::create_dir(output) {
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            if let Some(parent) = output.parent() {
                std::fs::create_dir_all(parent).map_err(|error| file_error(parent, error))?;
            }
            std::fs::create_dir(output).map_err(|error| file_error(output, error))
        }
        created => created.map_err(|error| file_error(output, error)),
    }
}

/// A new file `path` with `data`, which must not exist.
fn write_new(path: &Path, data: &[u8]) -> Result<(), Failure> {
    File::create_new(path)
        .and_then(|mut file| file.write_all(data))
        .map_err(|error| file_error(path, error))
}

/// `len` lowercase hexadecimal digits that tell runs apart: the SHA-256
/// digest of the process, the wall clock and the monotonic clock, followed
/// by the digests of the digits so far until there are enough.
fn random_hex(len: usize) -> String {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|since| since.as_nanos())
        .unwrap_or(0);
    let seed = format!("{}-{nanos}-{:?}", std::process::id(), Instant::now());
    let mut digits = hex(&Sha256::digest(seed.as_bytes()));
    while digits.len() < len {
        let more = hex(&Sha256::digest(digits.as_bytes()));
        digits.push_str(&more);
    }
    digits.truncate(len);
    digits
}

/// Faults that the unit tests inject on their own thread: a write of
/// `raw.bin` that takes a given count of bytes and then fails, and an
/// interrupt caught while `raw.bin` is written.
#[cfg(test)]
mod seams {
    use std::cell::Cell;
    use std::sync::atomic::AtomicI32;

    thread_local! {
        /// The errno with which a write of `raw.bin` fails once it has taken
        /// [`RAW_TAKES`] bytes.
        pub static RAW_ERRNO: Cell<Option<i32>> = const { Cell::new(None) };
        /// The bytes that the writes of `raw.bin` still take before they fail
        /// with [`RAW_ERRNO`].
        pub static RAW_TAKES: Cell<usize> = const { Cell::new(0) };
        /// The interrupt flag that a write of `raw.bin` sets, as a signal
        /// caught there would set it.
        pub static INTERRUPT_AT_WRITE: Cell<Option<&'static AtomicI32>> =
            const { Cell::new(None) };
    }
}

/// One write of `data` to `raw.bin`: the count written, or the error.
fn write_some(raw: &mut File, data: &[u8]) -> io::Result<usize> {
    #[cfg(test)]
    if let Some(errno) = seams::RAW_ERRNO.get() {
        let takes = seams::RAW_TAKES.get().min(data.len());
        if takes == 0 {
            return Err(io::Error::from_raw_os_error(errno));
        }
        seams::RAW_TAKES.set(seams::RAW_TAKES.get() - takes);
        return raw.write(&data[..takes]);
    }
    raw.write(data)
}

/// Writes `chunk` to `raw.bin` unbuffered: the count of bytes that reached
/// the file, all of them unless a write failed, and the failure.
fn write_raw(raw: &mut File, chunk: &[u8]) -> (usize, Option<Failure>) {
    #[cfg(test)]
    if let Some(flag) = seams::INTERRUPT_AT_WRITE.get() {
        flag.store(libc::SIGINT, Ordering::SeqCst);
    }
    let mut written = 0;
    while written < chunk.len() {
        match write_some(raw, &chunk[written..]) {
            Ok(0) => {
                return (
                    written,
                    Some(Failure::from(io::Error::from(io::ErrorKind::WriteZero))),
                );
            }
            Ok(count) => written += count,
            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
            Err(error) => return (written, Some(Failure::from(error))),
        }
    }
    (written, None)
}

/// [`capture_with`] whose interrupt handlers are already installed and set
/// `interrupt`.
pub fn capture(
    port: &str,
    output: &Path,
    seconds: f64,
    max_bytes: u64,
    interrupt: &AtomicI32,
    timing: &Timing,
) -> Result<Value, Failure> {
    capture_with(port, output, seconds, max_bytes, timing, &mut || {
        Ok(interrupt)
    })
}

/// One bounded capture of `port` into the new directory `output`, which
/// returns the receipt that `summary.json` holds with sorted keys. The
/// capture waits for input at most `timing.capture_slice` at a time between
/// two looks at its interrupt flag. `arm` is called immediately before the
/// port opens, to install the interrupt handlers; it returns the flag they
/// set, which ends the capture as `INTERRUPTED`. Limits outside
/// [`check_limits`], an empty port name, an output directory that exists or
/// cannot be created and files that cannot be written are errors; a port
/// that cannot be opened, configured, read or restored, a failed write of
/// `raw.bin` and a failed `arm` fail the receipt with their texts.
pub fn capture_with<'a>(
    port: &str,
    output: &Path,
    seconds: f64,
    max_bytes: u64,
    timing: &Timing,
    arm: &mut dyn FnMut() -> Result<&'a AtomicI32, Failure>,
) -> Result<Value, Failure> {
    check_limits(seconds, max_bytes)?;
    if port.is_empty() {
        return Err(Failure::new("an explicit port is required"));
    }
    create_output(output)?;
    let started = Instant::now();
    let mut report = Map::new();
    let mut set = |key: &str, value: Value| {
        report.insert(key.to_string(), value);
    };
    set("schema_version", 1.into());
    set("status", "FAIL".into());
    set("reason", "error".into());
    set("started_at", utc_now().into());
    set("port", port.into());
    set("baud", BAUD.into());
    set("data_bits", 8.into());
    set("parity", "none".into());
    set("stop_bits", 1.into());
    set("flow_control", "none".into());
    set("requested_seconds", seconds.into());
    set("max_bytes", max_bytes.into());
    set("bytes", 0.into());
    set("exclusive", false.into());
    set("attributes_restored", false.into());
    set("raw_file", "raw.bin".into());
    set("preview_file", "preview.txt".into());
    set("boot_acceptance", "NOT_EVALUATED".into());
    let raw_path = output.join("raw.bin");
    let mut raw = File::create_new(&raw_path).map_err(|error| file_error(&raw_path, error))?;
    let limit = usize::try_from(max_bytes).unwrap_or(usize::MAX);
    let mut digest = Sha256::new();
    let mut preview: Vec<u8> = Vec::new();
    let mut received = 0usize;
    let mut reason = "error";
    let mut status = "FAIL";
    let mut receiver: Option<Receiver> = None;
    let mut armed: Option<&AtomicI32> = None;
    let outcome: Result<(), Failure> = (|| {
        let interrupt = *armed.insert(arm()?);
        if interrupted(interrupt) {
            return Err(Failure::new(tty::INTERRUPTED));
        }
        let tty = receiver.insert(Receiver::open(port)?);
        tty.configure()?;
        let deadline = Instant::now() + Duration::from_secs_f64(seconds);
        reason = "deadline";
        while received < limit {
            if interrupted(interrupt) {
                return Err(Failure::new(tty::INTERRUPTED));
            }
            let now = Instant::now();
            if now >= deadline {
                break;
            }
            if !tty.wait((deadline - now).min(timing.capture_slice))? {
                continue;
            }
            let Some(chunk) = tty.read(READ_CHUNK.min(limit - received))? else {
                continue;
            };
            if chunk.is_empty() {
                reason = "end_of_stream";
                break;
            }
            let (written, failed) = write_raw(&mut raw, &chunk);
            let kept = &chunk[..written];
            digest.update(kept);
            received += written;
            let room = PREVIEW_BYTES.saturating_sub(preview.len());
            preview.extend_from_slice(&kept[..kept.len().min(room)]);
            if let Some(failure) = failed {
                return Err(failure);
            }
        }
        if received == limit {
            reason = "byte_limit";
        }
        status = if received > 0 { "CAPTURED" } else { "NO_DATA" };
        Ok(())
    })();
    let mut errors: Vec<String> = Vec::new();
    // An interrupt caught at any point of the capture, also in its last
    // read, ends it.
    if armed.is_some_and(interrupted) {
        status = "INTERRUPTED";
        reason = "interrupted";
    } else if let Err(Failure(error)) = outcome {
        errors.push(error);
        status = "FAIL";
        reason = "error";
    }
    let mut set = |key: &str, value: Value| {
        report.insert(key.to_string(), value);
    };
    if let Some(tty) = receiver.as_mut() {
        errors.extend(tty.close());
        set("exclusive", tty.exclusive.into());
        set("attributes_restored", tty.restored.into());
    }
    drop(raw);
    set("bytes", received.into());
    if !errors.is_empty() {
        status = "FAIL";
        reason = "error";
        set("errors", errors.into());
    }
    set("status", status.into());
    set("reason", reason.into());
    set("finished_at", utc_now().into());
    set("elapsed_seconds", started.elapsed().as_secs_f64().into());
    set("sha256", hex(&digest.finalize()).into());
    set("preview_bytes", preview.len().into());
    set("preview_truncated", (received > preview.len()).into());
    let text = render(&String::from_utf8_lossy(&preview));
    write_new(&output.join("preview.txt"), text.as_bytes())?;
    let mut report = Value::Object(report);
    report.sort_all_objects();
    write_new(&output.join("summary.json"), to_json(&report).as_bytes())?;
    Ok(report)
}

/// What a command line asks for, apart from the help.
#[derive(Clone, Debug, PartialEq)]
pub enum Command {
    /// `--list`.
    List,
    /// `--port`; `output` is `--output-dir`.
    Capture {
        port: String,
        seconds: f64,
        max_bytes: u64,
        output: Option<PathBuf>,
    },
}

/// The command line as clap reads it: the seven options, of which exactly one
/// of `--list` and `--port` is required, and the limits with
/// [`DEFAULT_SECONDS`] and [`DEFAULT_MAX_BYTES`] written out as their
/// defaults. The help and the usage name the command [`PROG`].
fn cli() -> clap::Command {
    clap::Command::new("serial-capture")
        .bin_name(PROG)
        .no_binary_name(true)
        .about("Record a bounded UART receive session without interpreting board boot success.")
        .args_override_self(true)
        .arg(
            Arg::new("list")
                .long("list")
                .action(ArgAction::SetTrue)
                .help("list likely USB ports without opening them"),
        )
        .arg(
            Arg::new("port")
                .long("port")
                .value_name("PORT")
                .help("explicit tty path; no automatic device selection"),
        )
        .group(ArgGroup::new("mode").args(["list", "port"]).required(true))
        .arg(
            Arg::new("seconds")
                .long("seconds")
                .value_name("SECONDS")
                .value_parser(value_parser!(f64))
                .allow_negative_numbers(true)
                .default_value("30")
                .help("capture duration, greater than 0 and at most 300"),
        )
        .arg(
            Arg::new("max-bytes")
                .long("max-bytes")
                .value_name("MAX_BYTES")
                .value_parser(read_max_bytes)
                .allow_negative_numbers(true)
                .default_value("262144")
                .help("receive limit, at most 16777216"),
        )
        .arg(
            Arg::new("output-dir")
                .long("output-dir")
                .value_name("OUTPUT_DIR")
                .help("new capture directory; must not already exist"),
        )
}

/// The value of `--max-bytes`: a decimal integer as Rust's `u64` reads it,
/// an optional `+` and ASCII digits. An integer too large for 64 bits is out
/// of bounds, whatever its length, and reads as `u64::MAX`.
fn read_max_bytes(value: &str) -> Result<u64, &'static str> {
    let digits = value.strip_prefix('+').unwrap_or(value);
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err("not a decimal integer");
    }
    // Digits alone fail to read only by overflow.
    Ok(digits.parse().unwrap_or(u64::MAX))
}

/// The command that a command line asks for, or clap's error: the help for
/// `-h` and `--help`, or a usage error, which a limit outside
/// [`check_limits`] is too, with the bound as its message.
pub fn parse(args: &[String]) -> Result<Command, clap::Error> {
    let mut cli = cli();
    let matches = cli.try_get_matches_from_mut(args)?;
    // Both always have a value, their own or the default.
    let seconds = *matches.get_one("seconds").unwrap_or(&DEFAULT_SECONDS);
    let max_bytes = *matches.get_one("max-bytes").unwrap_or(&DEFAULT_MAX_BYTES);
    check_limits(seconds, max_bytes)
        .map_err(|Failure(bound)| cli.error(ErrorKind::ValueValidation, bound))?;
    Ok(match matches.get_one::<String>("port") {
        Some(port) => Command::Capture {
            port: port.clone(),
            seconds,
            max_bytes,
            output: matches.get_one::<String>("output-dir").map(PathBuf::from),
        },
        None => Command::List,
    })
}

/// `artifacts/hardware-uart/<%Y%m%dT%H%M%SZ>-<12 hex digits>` below `root`.
fn default_output(root: &Path) -> PathBuf {
    let stamp = utc_stamp();
    root.join(OUTPUT_DIR).join(format!(
        "{}Z-{}",
        &stamp[.."YYYYmmddTHHMMSS".len()],
        random_hex(12)
    ))
}

/// The exit status of a capture with the receipt status `status`: 130 for
/// `INTERRUPTED`, 2 for `FAIL`, otherwise 0.
fn exit_code(status: &str) -> i32 {
    match status {
        "INTERRUPTED" => 130,
        "FAIL" => 2,
        _ => 0,
    }
}

/// The terminal of the command: its two output streams and the interrupt
/// handlers.
pub struct Console<'a> {
    /// Writes one text and a newline on standard output.
    pub print: &'a mut dyn FnMut(&str) -> io::Result<()>,
    /// Writes one text and a newline on standard error.
    pub warn: &'a mut dyn FnMut(&str) -> io::Result<()>,
    /// Called immediately before the port opens: installs the interrupt
    /// handlers and returns the flag they set.
    pub arm: &'a mut dyn FnMut() -> Result<&'a AtomicI32, Failure>,
}

/// The output streams of one run, with what failed on them.
struct Streams<'c, 'a> {
    console: &'c mut Console<'a>,
    /// The first write on standard output that failed; nothing more is
    /// written there after it.
    unwritten: Option<io::Error>,
    /// Whether a write on standard error failed.
    unwarned: bool,
}

impl Streams<'_, '_> {
    fn print(&mut self, text: &str) {
        if self.unwritten.is_none()
            && let Err(error) = (self.console.print)(text)
        {
            self.unwritten = Some(error);
        }
    }

    fn warn(&mut self, text: &str) {
        if (self.console.warn)(text).is_err() {
            self.unwarned = true;
        }
    }

    /// The exit status of a run whose work ended with `code`: 120 after a
    /// failed write, which on standard output is reported on standard error.
    fn exit(mut self, code: i32) -> i32 {
        if let Some(error) = self.unwritten.take() {
            self.warn(&format!("{PROG}: cannot write standard output: {error}"));
            return 120;
        }
        if self.unwarned { 120 } else { code }
    }
}

/// The command entry point: `--list` searches `/dev`, the lines go to the
/// standard streams, the interrupt handlers are installed immediately before
/// the port opens, and the capture waits as `Timing::PI5` gives. Returns the
/// exit status of the process.
pub fn main(root: &Path, args: &[String]) -> i32 {
    let console = &mut Console {
        print: &mut |text| {
            let mut stdout = io::stdout().lock();
            writeln!(stdout, "{text}").and_then(|()| stdout.flush())
        },
        warn: &mut |text| writeln!(io::stderr(), "{text}"),
        arm: &mut || tty::catch_interrupts(),
    };
    run_with(root, Path::new("/dev"), args, &Timing::PI5, console)
}

/// [`main`] with `devices` as the directory that `--list` searches, the
/// time values `timing` and the streams and interrupt handlers of `console`.
pub fn run_with(
    root: &Path,
    devices: &Path,
    args: &[String],
    timing: &Timing,
    console: &mut Console,
) -> i32 {
    let mut streams = Streams {
        console,
        unwritten: None,
        unwarned: false,
    };
    let code = run(root, devices, args, timing, &mut streams);
    streams.exit(code)
}

/// The text of `preview.txt` in `output`.
fn read_preview(output: &Path) -> Result<String, Failure> {
    let path = output.join("preview.txt");
    std::fs::read_to_string(&path).map_err(|error| file_error(&path, error))
}

/// One run over `streams`: the exit status of its work.
fn run(
    root: &Path,
    devices: &Path,
    args: &[String],
    timing: &Timing,
    streams: &mut Streams,
) -> i32 {
    let command = match parse(args) {
        Ok(command) => command,
        // Clap's text ends with a newline, which the streams add.
        Err(error) => {
            let text = error.render().to_string();
            let text = text.strip_suffix('\n').unwrap_or(&text);
            return if error.kind() == ErrorKind::DisplayHelp {
                streams.print(text);
                0
            } else {
                streams.warn(text);
                2
            };
        }
    };
    let (port, seconds, max_bytes, output) = match command {
        Command::List => {
            for port in list_ports(devices) {
                streams.print(&render_name(port.as_os_str()));
            }
            return 0;
        }
        Command::Capture {
            port,
            seconds,
            max_bytes,
            output,
        } => (port, seconds, max_bytes, output),
    };
    let output = pure_path(&output.unwrap_or_else(|| default_output(root)));
    let captured = capture_with(
        &port,
        &output,
        seconds,
        max_bytes,
        timing,
        streams.console.arm,
    )
    .and_then(|report| Ok((report, read_preview(&output)?)));
    let (report, preview) = match captured {
        Ok(captured) => captured,
        Err(Failure(message)) => {
            streams.warn(&format!("UART capture failed: {}", render(&message)));
            return 2;
        }
    };
    if !preview.is_empty() {
        streams.print(&preview);
    }
    let status = report["status"].as_str().unwrap_or("FAIL");
    let bytes = report["bytes"].as_u64().unwrap_or(0);
    streams.print(&format!(
        "{status}: {bytes} bytes; board boot is not evaluated."
    ));
    let resolved = std::fs::canonicalize(&output)
        .or_else(|_| std::path::absolute(&output))
        .unwrap_or_else(|_| output.clone());
    let summary = resolved.join("summary.json");
    streams.print(&format!("Receipt: {}", render_name(summary.as_os_str())));
    exit_code(status)
}

#[cfg(test)]
mod tests;
