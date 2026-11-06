use super::*;
use crate::TEST_WAIT;
use crate::child::{ChildTest, child_part};
use crate::pty::{Attributes, Master, Pty};
use crate::scratch::Scratch;
use crate::tty::{TtyPort, catch_interrupts, raw_attributes, seams as tty_seams};
use clap::error::ErrorKind;
use serde_json::json;
use std::cell::Cell;
use std::fmt::Debug;

/// A port that no open finds.
const MISSING_PORT: &str = "/nonexistent/krepi-port";
/// The digest of no bytes.
const EMPTY_SHA256: &str = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";
/// A capture deadline in seconds beyond [`TEST_WAIT`]. A capture that a
/// test ends by its byte limit, by the end of the stream or by an interrupt
/// never reaches it while the test waits, however slow the host.
const LONG: f64 = 120.0;
/// [`LONG`] as a command-line value.
const LONG_ARG: &str = "120";
/// The time values of the captures under test: those of the Pi 5.
const TIMING: Timing = Timing::PI5;

/// A fresh interrupt flag that lives as long as the test process; only the
/// test or a seam sets it.
fn fresh_flag() -> &'static AtomicI32 {
    Box::leak(Box::new(AtomicI32::new(0)))
}

fn arguments(args: &[&str]) -> Vec<String> {
    args.iter().map(|arg| arg.to_string()).collect()
}

/// Requires a rejection with exactly the message `expected`.
#[track_caller]
fn assert_rejects<T: Debug>(result: Result<T, Failure>, expected: &str) {
    match result {
        Err(Failure(message)) => assert_eq!(message, expected),
        Ok(value) => panic!("accepted: {value:?}"),
    }
}

/// The receipt's `errors`.
#[track_caller]
fn errors(report: &Value) -> Vec<&str> {
    report["errors"]
        .as_array()
        .map(|errors| errors.iter().map(|error| error.as_str().unwrap()).collect())
        .unwrap_or_default()
}

/// The keys of the receipt, in their order.
#[track_caller]
fn keys(report: &Value) -> Vec<&str> {
    report
        .as_object()
        .expect("a receipt object")
        .keys()
        .map(String::as_str)
        .collect()
}

/// The receipt that `bytes` hold.
#[track_caller]
fn parse_receipt(bytes: &[u8]) -> Value {
    serde_json::from_slice(bytes).expect("a JSON receipt")
}

/// The keys of every capture receipt in byte order, with `errors` after a
/// failure.
fn capture_keys(failed: bool) -> Vec<&'static str> {
    let mut keys = vec![
        "attributes_restored",
        "baud",
        "boot_acceptance",
        "bytes",
        "data_bits",
        "elapsed_seconds",
        "exclusive",
        "finished_at",
        "flow_control",
        "max_bytes",
        "parity",
        "port",
        "preview_bytes",
        "preview_file",
        "preview_truncated",
        "raw_file",
        "reason",
        "requested_seconds",
        "schema_version",
        "sha256",
        "started_at",
        "status",
        "stop_bits",
    ];
    if failed {
        keys.push("errors");
        keys.sort_unstable();
    }
    keys
}

/// The JSON escapes `\uXXXX` in the JSON text `written`: a backslash that
/// starts an escape and is followed by `u`.
fn unicode_escapes(written: &[u8]) -> usize {
    let mut count = 0;
    let mut bytes = written.iter();
    while let Some(&byte) = bytes.next() {
        if byte == b'\\' && bytes.next() == Some(&b'u') {
            count += 1;
        }
    }
    count
}

/// How often `needle` occurs in `haystack`.
fn occurrences(haystack: &[u8], needle: &[u8]) -> usize {
    haystack
        .windows(needle.len())
        .filter(|window| *window == needle)
        .count()
}

/// A pseudo-terminal whose master stands in for the board, the slave's
/// attributes that a capture must restore, and a scratch directory for the
/// output directory `capture`, which the capture creates.
struct Uart {
    pty: Pty,
    before: Attributes,
    scratch: Scratch,
}

impl Uart {
    #[track_caller]
    fn new() -> Self {
        let pty = Pty::open();
        Uart {
            before: pty.attributes(),
            pty,
            scratch: Scratch::new("serial-capture"),
        }
    }

    fn port(&self) -> &str {
        self.pty.path()
    }

    fn output(&self) -> PathBuf {
        self.scratch.path("capture")
    }

    /// Queues `bytes` before the capture opens the port, so that its first
    /// read finds them. Echo is turned off first, so that the line
    /// discipline writes nothing back to the master, and the attributes that
    /// the capture must restore are taken after that.
    #[track_caller]
    fn queue(&mut self, bytes: &[u8]) {
        let mut termios = self.pty.termios();
        termios.c_lflag &= !libc::ECHO;
        self.pty.set_termios(&termios);
        self.before = self.pty.attributes();
        self.pty.write(bytes);
    }

    /// A capture of the slave whose interrupt handlers set `interrupt`,
    /// while `script` plays the board on a thread of its own: the result and
    /// what the script returned.
    #[track_caller]
    fn run<T, F>(
        &self,
        seconds: f64,
        max_bytes: u64,
        interrupt: &'static AtomicI32,
        script: F,
    ) -> (Result<Value, Failure>, T)
    where
        F: FnOnce(&Master) -> T + Send + 'static,
        T: Send + 'static,
    {
        let board = self.pty.board(script);
        let result = capture(
            self.port(),
            &self.output(),
            seconds,
            max_bytes,
            interrupt,
            &TIMING,
        );
        (result, board.join())
    }

    /// The receipt of a capture while the board sends `payload` once the
    /// port is raw. The capture ends by its byte limit, the length of the
    /// payload.
    #[track_caller]
    fn receive(&self, payload: &'static [u8]) -> Value {
        let max_bytes = payload.len() as u64;
        let (result, ()) = self.run(LONG, max_bytes, fresh_flag(), sends(payload));
        self.receipt(result)
    }

    /// The receipt of a capture of `seconds` while the board sends nothing
    /// and waits for nothing.
    #[track_caller]
    fn quiet(&self, seconds: f64) -> Value {
        self.receipt(capture(
            self.port(),
            &self.output(),
            seconds,
            DEFAULT_MAX_BYTES,
            fresh_flag(),
            &TIMING,
        ))
    }

    /// The receipt of a capture, which `summary.json` holds byte for byte.
    #[track_caller]
    fn receipt(&self, result: Result<Value, Failure>) -> Value {
        let report = result.unwrap();
        assert_eq!(
            String::from_utf8(self.scratch.read("capture/summary.json")).unwrap(),
            to_json(&report)
        );
        report
    }

    #[track_caller]
    fn raw(&self) -> Vec<u8> {
        self.scratch.read("capture/raw.bin")
    }

    #[track_caller]
    fn preview(&self) -> String {
        String::from_utf8(self.scratch.read("capture/preview.txt")).unwrap()
    }

    /// Whether the capture has made the port raw.
    #[track_caller]
    fn is_raw(&self) -> bool {
        self.pty.attributes().lflag & libc::ICANON == 0
    }

    /// The slave has its attributes back. Darwin sets `PENDIN` when
    /// canonical mode is restored without flushing input, so that flag is
    /// left out.
    #[track_caller]
    fn assert_restored(&self) {
        let (mut actual, mut expected) = (self.pty.attributes(), self.before.clone());
        actual.lflag &= !libc::PENDIN;
        expected.lflag &= !libc::PENDIN;
        assert_eq!(actual, expected);
    }
}

/// A board that sends `payload` once the capture has made the port raw.
fn sends(payload: &'static [u8]) -> impl FnOnce(&Master) + Send + 'static {
    move |master| {
        master.await_raw();
        master.write(payload);
    }
}

/// One run of the command from `root`, whose `--list` searches `devices`:
/// the exit status and the lines written on standard output and on
/// standard error. Arming returns `interrupt` without installing a handler.
#[track_caller]
fn capture_command(
    root: &Path,
    devices: &Path,
    args: &[&str],
    interrupt: &AtomicI32,
) -> (i32, Vec<String>, Vec<String>) {
    let (code, out, err, _) = faulty_command(root, devices, args, interrupt, None, false);
    (code, out, err)
}

/// [`capture_command`] whose writes on standard output fail with `errno`,
/// when given, and whose writes on standard error fail when `unwritable` is
/// set: the exit status, the lines written on each stream and the count of
/// the writes tried on standard output.
#[track_caller]
fn faulty_command(
    root: &Path,
    devices: &Path,
    args: &[&str],
    interrupt: &AtomicI32,
    errno: Option<i32>,
    unwritable: bool,
) -> (i32, Vec<String>, Vec<String>, usize) {
    let (mut out, mut err, mut tried) = (Vec::new(), Vec::new(), 0);
    let code = run_with(
        root,
        devices,
        &arguments(args),
        &TIMING,
        &mut Console {
            print: &mut |line| {
                tried += 1;
                match errno {
                    Some(errno) => Err(io::Error::from_raw_os_error(errno)),
                    None => {
                        out.push(line.to_string());
                        Ok(())
                    }
                }
            },
            warn: &mut |line| {
                if unwritable {
                    return Err(io::Error::from_raw_os_error(libc::EPIPE));
                }
                err.push(line.to_string());
                Ok(())
            },
            arm: &mut || Ok(interrupt),
        },
    );
    (code, out, err, tried)
}

/// The start of the usage line of clap, which names the command; the help
/// and a usage error about the command line as a whole hold it.
const USAGE: &str = "Usage: cargo xtask serial-capture ";

/// Requires that clap ends the reading of `args` with an error of `kind`.
#[track_caller]
fn assert_error_kind(args: &[&str], kind: ErrorKind) {
    match parse(&arguments(args)) {
        Err(error) => assert_eq!(error.kind(), kind, "{args:?}: {error}"),
        Ok(command) => panic!("{args:?} accepted: {command:?}"),
    }
}

/// Requires a usage error for a value that `option` cannot read: clap's
/// error that names the option and quotes the value, which is no bound.
#[track_caller]
fn assert_invalid_value(result: Result<Command, clap::Error>, option: &str, value: &str) {
    let error = result.expect_err(value);
    assert_eq!(error.kind(), ErrorKind::ValueValidation, "{value:?}");
    let text = error.to_string();
    assert!(text.contains(&format!("'{value}'")), "{value:?}: {text}");
    assert!(text.contains(&format!("'{option} ")), "{option}: {text}");
    assert!(!text.contains(SECONDS_BOUND) && !text.contains(BYTES_BOUND));
}

/// Requires a usage error for a limit out of bounds, whose message is the
/// bound `bound`.
#[track_caller]
fn assert_out_of_bounds(result: Result<Command, clap::Error>, bound: &str) {
    let error = result.expect_err(bound);
    assert_eq!(error.kind(), ErrorKind::ValueValidation, "{error}");
    assert!(
        error.to_string().starts_with(&format!("error: {bound}\n")),
        "{error}"
    );
}

/// The report of a failed write on standard output with the error text
/// `error`.
fn unwritten(error: &str) -> String {
    format!("cargo xtask serial-capture: cannot write standard output: {error}")
}

/// A capture of `uart` into a directory of its own, with the faults that
/// the caller set on this thread, which it resets: the receipt, which
/// `summary.json` holds byte for byte, and `raw.bin`, whose length is the
/// receipt's `bytes`.
#[track_caller]
fn faulted(uart: &Uart, seconds: f64) -> (Value, Vec<u8>) {
    let scratch = Scratch::new("serial-capture-faulted");
    let output = scratch.path("capture");
    let flag = AtomicI32::new(0);
    let result = capture(
        uart.port(),
        &output,
        seconds,
        DEFAULT_MAX_BYTES,
        &flag,
        &TIMING,
    );
    tty_seams::WAIT_ERRNO.set(None);
    tty_seams::APPLY_ERRNO.set(None);
    tty_seams::RESTORE_ERRNO.set(None);
    seams::RAW_ERRNO.set(None);
    seams::RAW_TAKES.set(0);
    let report = result.unwrap();
    assert_eq!(
        String::from_utf8(scratch.read("capture/summary.json")).unwrap(),
        to_json(&report)
    );
    let raw = scratch.read("capture/raw.bin");
    assert_eq!(raw.len() as u64, report["bytes"].as_u64().unwrap());
    (report, raw)
}

/// A run of the command over `uart` whose arm returns `flag`, with the
/// faults that the caller set on this thread, which it resets: the exit
/// status, the lines on each stream before the `Receipt:` line, the receipt
/// and `raw.bin`.
#[track_caller]
fn commanded(
    uart: &Uart,
    seconds: &str,
    max_bytes: &str,
    flag: &'static AtomicI32,
) -> (i32, Vec<String>, Vec<String>, Value, Vec<u8>) {
    let output = uart.output();
    let args = [
        "--port",
        uart.port(),
        "--seconds",
        seconds,
        "--max-bytes",
        max_bytes,
        "--output-dir",
        output.to_str().unwrap(),
    ];
    let root = uart.scratch.root();
    let (code, mut out, err) = capture_command(root, root, &args, flag);
    tty_seams::WAIT_ERRNO.set(None);
    tty_seams::INTERRUPT_AT_RESTORE.set(None);
    seams::INTERRUPT_AT_WRITE.set(None);
    let summary = std::fs::canonicalize(&output).unwrap().join("summary.json");
    assert_eq!(out.pop(), Some(format!("Receipt: {}", summary.display())));
    let report = parse_receipt(&uart.scratch.read("capture/summary.json"));
    (code, out, err, report, uart.raw())
}

/// A wait that fails fails the receipt with its error text, and the port
/// is restored.
#[test]
fn a_failed_wait_fails_the_receipt_and_restores_the_port() {
    let uart = Uart::new();
    tty_seams::WAIT_ERRNO.set(Some(libc::EIO));
    let (report, _) = faulted(&uart, 1.0);
    assert_eq!(report["status"], "FAIL");
    assert_eq!(report["reason"], "error");
    assert_eq!(errors(&report), ["Input/output error (os error 5)"]);
    assert_eq!(report["exclusive"], true);
    assert_eq!(report["attributes_restored"], true);
    uart.assert_restored();
}

/// A restoration that fails fails the receipt with its label;
/// `tty::tests::a_receiver_closes_after_a_failed_restoration` shows that
/// the descriptor is still closed.
#[test]
fn a_failed_restoration_fails_the_receipt() {
    let uart = Uart::new();
    tty_seams::RESTORE_ERRNO.set(Some(libc::EIO));
    let (report, _) = faulted(&uart, 0.01);
    assert_eq!(report["status"], "FAIL");
    assert_eq!(report["reason"], "error");
    assert_eq!(
        errors(&report),
        ["attribute restoration failed: Input/output error (os error 5)"]
    );
    assert_eq!(report["attributes_restored"], false);
}

/// Raw attributes that the port refuses fail the receipt with their label,
/// and the original attributes are still restored; when the restoration
/// fails as well, both texts are recorded in that order.
#[test]
fn refused_raw_attributes_keep_the_restoration() {
    let uart = Uart::new();
    tty_seams::APPLY_ERRNO.set(Some(libc::EIO));
    let (report, _) = faulted(&uart, 0.01);
    assert_eq!(
        errors(&report),
        ["raw attributes refused: Input/output error (os error 5)"]
    );
    assert_eq!(report["exclusive"], true);
    assert_eq!(report["attributes_restored"], true);
    uart.assert_restored();
    tty_seams::APPLY_ERRNO.set(Some(libc::EIO));
    tty_seams::RESTORE_ERRNO.set(Some(libc::EIO));
    let (report, _) = faulted(&uart, 0.01);
    assert_eq!(
        errors(&report),
        [
            "raw attributes refused: Input/output error (os error 5)",
            "attribute restoration failed: Input/output error (os error 5)"
        ]
    );
    assert_eq!(report["attributes_restored"], false);
}

/// A signal caught once the capture has ended, while the port is restored
/// and the files are written, leaves the outcome as it is, with its exit
/// status. The seam sets the flag in the restoration, the first of those
/// steps, and a flag stays set, so that no look at it there or later could
/// miss it.
#[test]
fn an_interrupt_once_the_capture_has_ended_leaves_the_outcome() {
    for (queued, errno, seconds, max_bytes, status, reason, code) in [
        (
            &b"queued\n"[..],
            None,
            LONG_ARG,
            "7",
            "CAPTURED",
            "byte_limit",
            0,
        ),
        (b"", None, "0.05", "262144", "NO_DATA", "deadline", 0),
        (b"", Some(libc::EIO), LONG_ARG, "262144", "FAIL", "error", 2),
    ] {
        let mut uart = Uart::new();
        uart.queue(queued);
        let flag = fresh_flag();
        tty_seams::INTERRUPT_AT_RESTORE.set(Some(flag));
        tty_seams::WAIT_ERRNO.set(errno);
        let (exit, out, err, report, raw) = commanded(&uart, seconds, max_bytes, flag);
        assert_ne!(flag.load(Ordering::SeqCst), 0, "{status}");
        assert_eq!(exit, code, "{status}");
        let line = format!(
            "{status}: {} bytes; board boot is not evaluated.",
            queued.len()
        );
        if queued.is_empty() {
            assert_eq!(out, [line], "{status}");
        } else {
            assert_eq!(out, ["queued\n".to_string(), line], "{status}");
        }
        assert!(err.is_empty(), "{status}: {err:?}");
        assert_eq!(raw, queued, "{status}");
        assert_eq!(report["status"], status);
        assert_eq!(report["reason"], reason);
        assert_eq!(report["attributes_restored"], true);
        if errno.is_some() {
            assert_eq!(errors(&report), ["Input/output error (os error 5)"]);
        } else {
            assert!(report.get("errors").is_none(), "{status}: {report:?}");
        }
        uart.assert_restored();
    }
}

/// The other side of that boundary: a signal caught in the last read, after
/// which the loop does not look at the flag again, ends the capture as
/// `INTERRUPTED`, and the bytes received are kept.
#[test]
fn an_interrupt_in_the_last_read_ends_the_capture() {
    let mut uart = Uart::new();
    uart.queue(b"queued\n");
    let flag = fresh_flag();
    seams::INTERRUPT_AT_WRITE.set(Some(flag));
    let (exit, out, err, report, raw) = commanded(&uart, LONG_ARG, "7", flag);
    assert_ne!(flag.load(Ordering::SeqCst), 0);
    assert_eq!(exit, 130);
    assert_eq!(
        out,
        [
            "queued\n",
            "INTERRUPTED: 7 bytes; board boot is not evaluated."
        ]
    );
    assert!(err.is_empty(), "{err:?}");
    assert_eq!(raw, b"queued\n");
    assert_eq!(report["status"], "INTERRUPTED");
    assert_eq!(report["reason"], "interrupted");
    assert_eq!(report["bytes"], 7);
    assert_eq!(report["attributes_restored"], true);
    uart.assert_restored();
}

/// A write of `raw.bin` that fails fails the receipt with its error text in
/// the read whose bytes it could not keep, which are not counted, and the
/// port is restored.
#[test]
fn a_failed_write_of_the_capture_fails_the_receipt() {
    let mut uart = Uart::new();
    uart.queue(b"queued\n");
    seams::RAW_ERRNO.set(Some(libc::ENOSPC));
    let (report, raw) = faulted(&uart, LONG);
    assert_eq!(report["status"], "FAIL");
    assert_eq!(report["reason"], "error");
    assert_eq!(errors(&report), ["No space left on device (os error 28)"]);
    assert_eq!(report["bytes"], 0);
    assert_eq!(raw, b"");
    assert_eq!(report["preview_bytes"], 0);
    assert_eq!(report["sha256"], EMPTY_SHA256);
    assert_eq!(report["attributes_restored"], true);
    uart.assert_restored();
}

/// A write of `raw.bin` that takes part of a read and then fails leaves
/// those bytes in the file, and the receipt counts them: its `bytes`,
/// `sha256` and preview describe what `raw.bin` holds.
#[test]
fn a_partly_written_read_counts_what_raw_bin_holds() {
    let mut uart = Uart::new();
    uart.queue(b"queued\n");
    seams::RAW_ERRNO.set(Some(libc::ENOSPC));
    seams::RAW_TAKES.set(3);
    let (report, raw) = faulted(&uart, LONG);
    assert_eq!(report["status"], "FAIL");
    assert_eq!(errors(&report), ["No space left on device (os error 28)"]);
    assert_eq!(raw, b"que");
    assert_eq!(report["bytes"], 3);
    // `printf que | shasum -a 256`.
    assert_eq!(
        report["sha256"],
        "c57b7501cd843672550c711a346dd93e9bdc2c97a640874d54b4c9cf4b12ee81"
    );
    assert_eq!(report["preview_bytes"], 3);
    assert_eq!(report["preview_truncated"], false);
    uart.assert_restored();
}

#[test]
fn only_interrupted_and_fail_exit_with_another_code() {
    for (status, code) in [
        ("CAPTURED", 0),
        ("NO_DATA", 0),
        ("FAIL", 2),
        ("INTERRUPTED", 130),
    ] {
        assert_eq!(exit_code(status), code, "{status}");
    }
}

#[test]
fn the_default_run_directory_is_a_utc_stamp_and_12_hex_digits() {
    let output = default_output(Path::new("/r"));
    assert_eq!(
        output.parent().unwrap(),
        Path::new("/r/artifacts/hardware-uart")
    );
    let name = output.file_name().unwrap().to_str().unwrap();
    let (stamp, suffix) = name.split_once('-').unwrap();
    assert_eq!(stamp.len(), "20261101T120000Z".len());
    assert!(stamp.ends_with('Z') && stamp.as_bytes()[8] == b'T');
    assert!(
        stamp[..8]
            .bytes()
            .chain(stamp[9..15].bytes())
            .all(|b| b.is_ascii_digit())
    );
    assert_eq!(suffix.len(), 12);
    assert!(
        suffix
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    );
}

/// An output path loses its `.` components and its repeated and trailing
/// separators, and two leading separators become one.
#[test]
fn an_output_path_is_normalized_by_its_components() {
    for (path, pure) in [
        ("./a//b/./c/", "a/b/c"),
        ("a/../b", "a/../b"),
        (".", "."),
        ("./", "."),
        ("/x/./y//", "/x/y"),
        ("../a/.", "../a"),
        ("//x/./y", "/x/y"),
    ] {
        assert_eq!(pure_path(Path::new(path)), Path::new(pure), "{path:?}");
    }
}

mod properties {
    use super::*;

    /// The rendering escapes terminal controls, format characters such as
    /// the bidirectional and zero-width ones, white space other than the
    /// space, default-ignorable characters such as variation selectors and
    /// fillers, private-use, unassigned and noncharacter code points, and a
    /// combining mark at the start of a run; newline, tab, the quotes, the
    /// backslash, a combining mark after a character and the replacement
    /// character stay. The rows avoid code points that some Unicode version
    /// assigns and another does not.
    #[test]
    fn the_preview_escapes_controls_and_unprintable_characters() {
        assert_eq!(
            render("safe\n\t\x1b\r\x7f\u{9b}\u{202e}\u{200b}"),
            "safe\n\t\\u{1b}\\r\\u{7f}\\u{9b}\\u{202e}\\u{200b}"
        );
        for (text, rendered) in [
            (
                "\u{a0}\u{2028}\u{2029}\u{3000} \u{feff}\u{e0001}\u{fffd}",
                "\\u{a0}\\u{2028}\\u{2029}\\u{3000} \\u{feff}\\u{e0001}\u{fffd}",
            ),
            (
                "\u{34f}\u{fe0f}\u{115f}\u{3164}\u{ffa0}\u{e0100}",
                "\\u{34f}\\u{fe0f}\\u{115f}\\u{3164}\\u{ffa0}\\u{e0100}",
            ),
            ("x\n\u{301}e\u{301}", "x\n\\u{301}e\u{301}"),
            (
                "\u{e000}\u{f0000}\u{10fffd}",
                "\\u{e000}\\u{f0000}\\u{10fffd}",
            ),
            (
                "\u{85}\u{a0}\u{ad}\u{600}\u{61c}\u{180e}\u{2060}\u{2064}\u{2066}\u{110bd}\u{1bca0}\u{1d173}",
                "\\u{85}\\u{a0}\\u{ad}\\u{600}\\u{61c}\\u{180e}\\u{2060}\\u{2064}\\u{2066}\\u{110bd}\\u{1bca0}\\u{1d173}",
            ),
            ("\"'\\", "\"'\\"),
            ("\0a\u{1}", "\\0a\\u{1}"),
            (
                "\u{378}\u{fdd0}\u{ffff}\u{1ffff}\u{10ffff}",
                "\\u{378}\\u{fdd0}\\u{ffff}\\u{1ffff}\\u{10ffff}",
            ),
            ("e\u{301}", "e\u{301}"),
        ] {
            assert_eq!(render(text), rendered, "{text:?}");
        }
    }

    /// The names that `--list` prints: a byte that does not decode as UTF-8
    /// is written as `\xNN`.
    #[test]
    fn undecodable_name_bytes_are_rendered_as_hex_escapes() {
        let name = OsStr::from_bytes(b"cu.usb\xff\x1b-\xce\xa3");
        assert_eq!(render_name(name), "cu.usb\\xff\\u{1b}-\u{3a3}");
    }

    /// The preview decodes the capture with one replacement character for
    /// each maximal invalid sequence, the substitution that the Unicode
    /// standard recommends, and renders the byte order mark as a format
    /// character.
    #[test]
    fn the_preview_replaces_each_maximal_invalid_sequence() {
        const BYTES: &[u8] = b"\xe2\x82|\xe2\x82A|\xf0\x9f\x98|\xf0\x9f\x98\x80|\xed\xa0\x80|\xc0\xaf|\xf4\x90\x80\x80|\x80\xbf|\xe0\x80\xaf|\xf8\x88\x80\x80\x80|a\xffb\xfe|\xce\xa3\xce|\xef\xbb\xbfBOM";
        let uart = Uart::new();
        let report = uart.receive(BYTES);
        assert_eq!(report["status"], "CAPTURED");
        assert_eq!(uart.raw(), BYTES);
        let r = '\u{fffd}';
        assert_eq!(
            uart.preview(),
            format!(
                "{r}|{r}A|{r}|\u{1f600}|{r}{r}{r}|{r}{r}|{r}{r}{r}{r}|{r}{r}|{r}{r}{r}|\
                 {r}{r}{r}{r}{r}|a{r}b{r}|\u{3a3}{r}|\\u{{feff}}BOM"
            )
        );
    }

    /// On the port while the capture holds it: raw 115200 8N1 without any
    /// flow control, input or output processing or line discipline, and
    /// reads that return at once. The board reads the attributes and then
    /// sends the one byte that ends the capture. The original attributes are
    /// back afterwards.
    #[test]
    fn the_held_port_is_raw_8n1_without_flow_control() {
        let uart = Uart::new();
        let (result, held) = uart.run(LONG, 1, fresh_flag(), |master| {
            master.await_raw();
            let held = master.attributes();
            master.write(b"x");
            held
        });
        let report = uart.receipt(result);
        assert_eq!(report["status"], "CAPTURED");
        assert_eq!(report["reason"], "byte_limit");
        assert_eq!((held.iflag, held.oflag, held.lflag), (0, 0, 0));
        assert_eq!(held.cflag & libc::CSIZE, libc::CS8);
        assert_eq!(
            held.cflag & (libc::PARENB | libc::CSTOPB | libc::CRTSCTS),
            0
        );
        assert_eq!(
            held.cflag & (libc::CREAD | libc::CLOCAL),
            libc::CREAD | libc::CLOCAL
        );
        if cfg!(target_os = "macos") {
            // CCTS_OFLOW, CRTS_IFLOW, CDTR_IFLOW, CDSR_OFLOW, CCAR_OFLOW.
            assert_eq!(held.cflag & 0x001f_0000, 0);
        }
        assert_eq!((held.ispeed, held.ospeed), (libc::B115200, libc::B115200));
        assert_eq!((held.cc[libc::VMIN], held.cc[libc::VTIME]), (0, 0));
        uart.assert_restored();
    }

    /// `--seconds` and `--max-bytes` take what Rust's `f64` and `u64` read:
    /// decimal, scientific and leading-dot forms and a sign, and no white
    /// space, underscores or digits other than ASCII ones. A value that they
    /// cannot read is a usage error that names the option and the value. A
    /// value out of bounds, also one beyond 64 bits, fails the bound and not
    /// the reading. Each value follows `=`, so that clap takes it as it is.
    #[test]
    fn option_values_are_read_as_rust_numbers() {
        let capture = |seconds: f64, max_bytes: u64| Command::Capture {
            port: "p".to_string(),
            seconds,
            max_bytes,
            output: None,
        };
        let read = |option: &str, value: &str| {
            parse(&arguments(&["--port", "p", &format!("{option}={value}")]))
        };
        for (value, seconds) in [
            ("1e-5", 1e-5),
            ("300", 300.0),
            (".5", 0.5),
            ("5.", 5.0),
            ("+5", 5.0),
            ("1E2", 100.0),
        ] {
            assert_eq!(
                read("--seconds", value).unwrap(),
                capture(seconds, DEFAULT_MAX_BYTES),
                "{value:?}"
            );
        }
        for value in [
            " 5 ",
            "1_0",
            "\x0b5\x0c",
            "\u{a0}5",
            "\u{2000}5",
            "1_0.5_5",
            "\u{6f5}",
            "",
        ] {
            assert_invalid_value(read("--seconds", value), "--seconds", value);
        }
        for value in ["+inf", "iNfInItY", "-0", "1e400", "-1e-3", "NaN"] {
            assert_out_of_bounds(read("--seconds", value), SECONDS_BOUND);
        }
        for (value, max_bytes) in [("7", 7), ("+7", 7), ("007", 7), ("16777216", MAX_BYTES)] {
            assert_eq!(
                read("--max-bytes", value).unwrap(),
                capture(DEFAULT_SECONDS, max_bytes),
                "{value:?}"
            );
        }
        let long = "1_".repeat(2200) + "1";
        let negative = format!("-{}", "9".repeat(60));
        for value in [
            " 7",
            "0_7",
            "\u{a0}7\u{3000}",
            "\u{ff11}",
            "-0",
            "-1",
            "",
            "+",
            long.as_str(),
            negative.as_str(),
        ] {
            assert_invalid_value(read("--max-bytes", value), "--max-bytes", value);
        }
        assert_out_of_bounds(read("--max-bytes", "16777217"), BYTES_BOUND);
    }
}

mod boundaries {
    use super::*;

    /// Limits out of bounds are refused before the output directory exists
    /// and before the handlers are installed and the port is opened.
    #[test]
    fn invalid_limits_are_rejected_before_any_artifacts_or_port_open() {
        let uart = Uart::new();
        for (seconds, max_bytes, message) in [
            (0.0, 1, SECONDS_BOUND),
            (-1.0, 1, SECONDS_BOUND),
            (301.0, 1, SECONDS_BOUND),
            (f64::NAN, 1, SECONDS_BOUND),
            (f64::INFINITY, 1, SECONDS_BOUND),
            (1.0, 0, BYTES_BOUND),
            (1.0, MAX_BYTES + 1, BYTES_BOUND),
        ] {
            let armed = Cell::new(false);
            let result = capture_with(
                uart.port(),
                &uart.output(),
                seconds,
                max_bytes,
                &TIMING,
                &mut || {
                    armed.set(true);
                    Ok(fresh_flag())
                },
            );
            assert_rejects(result, message);
            assert!(!armed.get(), "{seconds:?} {max_bytes}");
        }
        assert!(!uart.output().exists());
        uart.assert_restored();
    }

    /// Each bound holds at its edge: `0 < seconds <= 300` for a finite
    /// number and `1 <= max_bytes <= 16777216`.
    #[test]
    fn the_limits_hold_at_their_edges() {
        for (seconds, max_bytes) in [
            (1.0, 1),
            (300.0, MAX_BYTES),
            (300.0, DEFAULT_MAX_BYTES),
            (f64::from_bits(1), 1),
        ] {
            check_limits(seconds, max_bytes).unwrap();
        }
        for seconds in [
            0.0,
            -0.0,
            f64::from_bits(300f64.to_bits() + 1),
            f64::NEG_INFINITY,
            f64::MIN,
        ] {
            assert_rejects(check_limits(seconds, 1), SECONDS_BOUND);
        }
        assert_rejects(check_limits(1.0, u64::MAX), BYTES_BOUND);
    }

    /// An existing output directory and its files stay as they were, and the
    /// port is never opened. The command reports the error as `UART capture
    /// failed` with exit status 2, also for `--output-dir ''`, which names
    /// the working directory, and names the directory without its `.`
    /// components and with repeated separators made one.
    #[test]
    fn an_existing_output_directory_is_never_overwritten() {
        let uart = Uart::new();
        std::fs::create_dir(uart.output()).unwrap();
        let sentinel = uart.scratch.write("capture/raw.bin", b"retain");
        let exists = format!("{:?}: File exists (os error 17)", uart.output());
        let armed = Cell::new(false);
        let result = capture_with(
            uart.port(),
            &uart.output(),
            0.01,
            DEFAULT_MAX_BYTES,
            &TIMING,
            &mut || {
                armed.set(true);
                Ok(fresh_flag())
            },
        );
        assert_rejects(result, &exists);
        assert!(!armed.get());
        assert_eq!(std::fs::read(&sentinel).unwrap(), b"retain");
        assert_eq!(std::fs::read_dir(uart.output()).unwrap().count(), 1);
        uart.assert_restored();
        let output = uart.output();
        let output = output.to_str().unwrap();
        let (twice, thrice) = (format!("/{output}"), format!("//{output}/./"));
        for (args, error) in [
            (
                &["--port", MISSING_PORT, "--output-dir", output][..],
                exists.clone(),
            ),
            (
                &["--port", MISSING_PORT, "--output-dir", ""],
                "\".\": File exists (os error 17)".to_string(),
            ),
            (
                &["--port", MISSING_PORT, "--output-dir", &twice],
                exists.clone(),
            ),
            (
                &["--port", MISSING_PORT, "--output-dir", &thrice],
                exists.clone(),
            ),
        ] {
            let root = uart.scratch.root();
            let (code, out, err) = capture_command(root, root, args, fresh_flag());
            assert_eq!(code, 2, "{args:?}");
            assert!(out.is_empty());
            assert_eq!(err, [format!("UART capture failed: {error}")]);
        }
        assert_eq!(std::fs::read(&sentinel).unwrap(), b"retain");
    }

    /// An empty port name is refused before the output directory exists;
    /// `--port=` gives it.
    #[test]
    fn an_empty_port_is_refused_before_the_output_directory() {
        let scratch = Scratch::new("serial-capture-empty");
        let output = scratch.path("capture");
        assert_rejects(
            capture(
                "",
                &output,
                DEFAULT_SECONDS,
                DEFAULT_MAX_BYTES,
                fresh_flag(),
                &TIMING,
            ),
            "an explicit port is required",
        );
        assert!(!output.exists());
        let output = output.to_str().unwrap();
        let (code, out, err) = capture_command(
            scratch.root(),
            scratch.root(),
            &["--port=", "--output-dir", output],
            fresh_flag(),
        );
        assert_eq!(code, 2);
        assert!(out.is_empty());
        assert_eq!(err, ["UART capture failed: an explicit port is required"]);
        assert_eq!(std::fs::read_dir(scratch.root()).unwrap().count(), 0);
    }

    /// A port that cannot be opened fails the receipt with the port's name
    /// and the error text.
    #[test]
    fn an_invalid_port_emits_a_failure_receipt() {
        let uart = Uart::new();
        let missing = uart.scratch.path("missing");
        let missing = missing.to_str().unwrap();
        let report = uart.receipt(capture(
            missing,
            &uart.output(),
            0.01,
            DEFAULT_MAX_BYTES,
            fresh_flag(),
            &TIMING,
        ));
        assert_eq!(keys(&report), capture_keys(true));
        assert_eq!(report["status"], "FAIL");
        assert_eq!(report["reason"], "error");
        assert_eq!(report["bytes"], 0);
        assert_eq!(report["exclusive"], false);
        assert_eq!(report["attributes_restored"], false);
        assert_eq!(
            errors(&report),
            [format!(
                "\"{missing}\": No such file or directory (os error 2)"
            )]
        );
        assert_eq!(report["sha256"], EMPTY_SHA256);
        assert_eq!(uart.raw(), b"");
        assert_eq!(uart.preview(), "");
    }

    /// A regular file, or a directory, is no tty; it stays as it was, and
    /// the port was neither held nor changed.
    #[test]
    fn a_regular_file_is_rejected_without_changing_it() {
        let scratch = Scratch::new("serial-capture-file");
        let file = scratch.write("not-a-port", b"unchanged");
        let directory = scratch.path("directory");
        std::fs::create_dir(&directory).unwrap();
        for (index, port) in [&file, &directory].into_iter().enumerate() {
            let output = scratch.path(&format!("capture-{index}"));
            let report = capture(
                port.to_str().unwrap(),
                &output,
                0.01,
                DEFAULT_MAX_BYTES,
                fresh_flag(),
                &TIMING,
            )
            .unwrap();
            assert_eq!(report["status"], "FAIL");
            assert_eq!(errors(&report), ["selected port is not a tty"]);
            assert_eq!(report["exclusive"], false);
            assert_eq!(report["attributes_restored"], false);
        }
        assert_eq!(std::fs::read(&file).unwrap(), b"unchanged");
        assert_eq!(std::fs::read_dir(&directory).unwrap().count(), 0);
    }

    /// The capture stops at its limit without reading past it, so the rest
    /// stays queued for the next reader of the tty.
    #[test]
    fn the_byte_limit_is_exact_and_never_discards_unread_input() {
        let uart = Uart::new();
        let (result, ()) = uart.run(LONG, 3, fresh_flag(), sends(b"abcdef"));
        let report = uart.receipt(result);
        assert_eq!(report["status"], "CAPTURED");
        assert_eq!(report["reason"], "byte_limit");
        assert_eq!(report["bytes"], 3);
        assert_eq!(uart.raw(), b"abc");
        uart.pty.set_termios(&raw_attributes(&uart.pty.termios()));
        assert_eq!(uart.pty.read_slave(3), b"def");
    }

    /// The preview renders the first 16 KiB, cutting a character that
    /// crosses the bound to a replacement character, while `raw.bin` keeps
    /// every byte.
    #[test]
    fn the_preview_is_bounded_separately_from_the_raw_capture() {
        static PAYLOAD: std::sync::OnceLock<Vec<u8>> = std::sync::OnceLock::new();
        let payload = PAYLOAD.get_or_init(|| {
            let mut payload = vec![b'x'; PREVIEW_BYTES - 1];
            payload.extend_from_slice("\u{39e}".as_bytes());
            payload.extend_from_slice(&[b'y'; 199]);
            payload
        });
        let uart = Uart::new();
        let report = uart.receive(payload);
        assert_eq!(report["bytes"], PREVIEW_BYTES as u64 + 200);
        assert_eq!(report["preview_truncated"], true);
        assert_eq!(report["preview_bytes"], PREVIEW_BYTES as u64);
        let preview = uart.preview();
        assert_eq!(preview.chars().count(), PREVIEW_BYTES);
        assert!(
            preview.ends_with("xx\u{fffd}"),
            "{:?}",
            &preview[preview.len() - 8..]
        );
        assert_eq!(&uart.raw(), payload);
    }

    /// Each of these command lines is a usage error of clap with exit status
    /// 2, and nothing is captured: no mode, both modes in either order, and
    /// limits out of bounds, also with `--list`. Standard error holds the
    /// error with the usage, a limit's with the bound as its message, and
    /// standard output nothing.
    #[test]
    fn the_command_line_requires_one_mode_and_valid_limits() {
        let root = Scratch::new("serial-capture-usage");
        for (args, kind, part) in [
            (&[][..], ErrorKind::MissingRequiredArgument, "--list|--port"),
            (
                &["--list", "--port", "fake"],
                ErrorKind::ArgumentConflict,
                "'--list'",
            ),
            (
                &["--port", "fake", "--list"],
                ErrorKind::ArgumentConflict,
                "'--list'",
            ),
            (
                &["--port", "fake", "--seconds", "nan"],
                ErrorKind::ValueValidation,
                SECONDS_BOUND,
            ),
            (
                &["--port", "fake", "--max-bytes", "0"],
                ErrorKind::ValueValidation,
                BYTES_BOUND,
            ),
            (
                &["--port", "fake", "--seconds", "301"],
                ErrorKind::ValueValidation,
                SECONDS_BOUND,
            ),
            (
                &["--list", "--seconds", "0"],
                ErrorKind::ValueValidation,
                SECONDS_BOUND,
            ),
            (
                &["--list", "--max-bytes", "0", "--seconds", "0"],
                ErrorKind::ValueValidation,
                SECONDS_BOUND,
            ),
        ] {
            assert_error_kind(args, kind);
            let (code, out, err) = capture_command(root.root(), root.root(), args, fresh_flag());
            assert_eq!(code, 2, "{args:?}");
            assert!(out.is_empty());
            assert_eq!(err.len(), 1, "{args:?}");
            assert!(err[0].starts_with("error: "), "{}", err[0]);
            for part in [USAGE, part] {
                assert!(err[0].contains(part), "{part:?}: {}", err[0]);
            }
        }
        assert_eq!(std::fs::read_dir(root.root()).unwrap().count(), 0);
    }

    /// The command line takes the seven options of the command and no other:
    /// `--list` or `--port`, `--seconds` and `--max-bytes` with their
    /// defaults, `--output-dir`, and `-h` and `--help`, which ask for the
    /// help also after other options. A value follows its option as the next
    /// argument or after `=`, a repeated option keeps its last value, and
    /// `--seconds` and `--max-bytes` take a negative number as the next
    /// argument, which then fails the bound or the reading. Anything else is
    /// a usage error that names it: a prefix of an option, an option or a
    /// word that the command does not have, an option without its value and
    /// a value for `--list`.
    #[test]
    fn the_command_line_takes_the_seven_options() {
        let capture =
            |port: &str, seconds: f64, max_bytes: u64, output: Option<&str>| Command::Capture {
                port: port.to_string(),
                seconds,
                max_bytes,
                output: output.map(PathBuf::from),
            };
        let defaults = |port: &str| capture(port, DEFAULT_SECONDS, DEFAULT_MAX_BYTES, None);
        for (args, command) in [
            (&["--list"][..], Command::List),
            (&["--list", "--list"], Command::List),
            (&["--output-dir", "x", "--list"], Command::List),
            (&["--port", "x"], defaults("x")),
            (&["--port=x"], defaults("x")),
            (&["--port=a=b"], defaults("a=b")),
            (&["--port", "a", "--port", "b"], defaults("b")),
            (
                &[
                    "--max-bytes=7",
                    "--port=p",
                    "--seconds",
                    "5",
                    "--output-dir",
                    "d",
                ],
                capture("p", 5.0, 7, Some("d")),
            ),
            (
                &[
                    "--seconds=1",
                    "--seconds",
                    "2",
                    "--max-bytes",
                    "3",
                    "--max-bytes=4",
                    "--output-dir",
                    "d",
                    "--output-dir=",
                    "--port",
                    "p",
                ],
                capture("p", 2.0, 4, Some("")),
            ),
        ] {
            assert_eq!(parse(&arguments(args)).unwrap(), command, "{args:?}");
        }
        for args in [
            &["-h"][..],
            &["--help"],
            &["--port", "p", "-h"],
            &["--list", "--port", "p", "--help"],
        ] {
            assert_error_kind(args, ErrorKind::DisplayHelp);
        }
        let read = |args: &[&str]| parse(&arguments(args));
        assert_out_of_bounds(read(&["--port", "p", "--seconds", "-1"]), SECONDS_BOUND);
        assert_invalid_value(
            read(&["--port", "p", "--max-bytes", "-1"]),
            "--max-bytes",
            "-1",
        );
        for (args, named) in [
            (&["--list", "--po", "x"][..], "'--po'"),
            (&["--list", "--bogus"], "'--bogus'"),
            (&["--list", "--version"], "'--version'"),
            (&["--list", "-V"], "'-V'"),
            (&["--list", "stray"], "'stray'"),
            (&["--port"], "'--port "),
            (&["--port", "--list"], "'--port "),
            (&["--list=1"], "'--list'"),
        ] {
            let error = read(args).expect_err(named);
            assert_ne!(error.kind(), ErrorKind::DisplayHelp, "{args:?}");
            let text = error.to_string();
            assert!(
                text.starts_with("error: ") && text.contains(named),
                "{text}"
            );
        }
    }

    /// Non-ASCII text is written in the receipt as UTF-8, without a JSON
    /// `\u` escape: a port name that holds a non-ASCII character, recorded
    /// as given and named in the open error, and a live capture of a port
    /// reached by such a name, where the name is the only such text. A DEL
    /// stays as it is in the port field; the error names the port in Rust's
    /// debug form, which writes it `\u{7f}`.
    #[test]
    fn the_receipt_keeps_non_ascii_text_as_utf8() {
        const PORT: &str = "/nonexistent/krepi-p\u{f6}rt";
        let scratch = Scratch::new("serial-capture-utf8");
        let output = scratch.path("capture");
        let args = [
            "--port",
            PORT,
            "--seconds",
            "0.01",
            "--output-dir",
            output.to_str().unwrap(),
        ];
        let (code, _, err) = capture_command(scratch.root(), scratch.root(), &args, fresh_flag());
        assert_eq!(code, 2);
        assert!(err.is_empty());
        let written = scratch.read("capture/summary.json");
        let report = parse_receipt(&written);
        assert_eq!(report["port"], PORT);
        assert_eq!(
            errors(&report),
            ["\"/nonexistent/krepi-p\u{f6}rt\": No such file or directory (os error 2)"]
        );
        assert_eq!(occurrences(&written, b"p\xc3\xb6rt"), 2);
        assert_eq!(unicode_escapes(&written), 0);

        let uart = Uart::new();
        let link = uart.scratch.path("p\u{f6}rt");
        std::os::unix::fs::symlink(uart.port(), &link).unwrap();
        let link = link.to_str().unwrap();
        let report = uart.receipt(capture(
            link,
            &uart.output(),
            0.01,
            DEFAULT_MAX_BYTES,
            fresh_flag(),
            &TIMING,
        ));
        assert_eq!(keys(&report), capture_keys(false));
        assert_eq!(report["status"], "NO_DATA");
        assert_eq!(report["port"], link);
        let written = uart.scratch.read("capture/summary.json");
        assert_eq!(occurrences(&written, b"p\xc3\xb6rt"), 1);
        assert_eq!(unicode_escapes(&written), 0);
        uart.assert_restored();

        let scratch = Scratch::new("serial-capture-del");
        let output = scratch.path("capture");
        let args = [
            "--port",
            "/nonexistent/krepi-\u{7f}",
            "--seconds",
            "0.01",
            "--output-dir",
            output.to_str().unwrap(),
        ];
        let (code, _, err) = capture_command(scratch.root(), scratch.root(), &args, fresh_flag());
        assert_eq!(code, 2);
        assert!(err.is_empty());
        let written = scratch.read("capture/summary.json");
        assert_eq!(occurrences(&written, b"krepi-\x7f\""), 1);
        assert_eq!(occurrences(&written, b"krepi-\\\\u{7f}\\\": No such"), 1);
        assert_eq!(unicode_escapes(&written), 0);
    }

    /// A write that fails on standard output makes the exit status 120 once
    /// the command's work is done; nothing more is written there, and the
    /// failure is reported on standard error. A write that fails on
    /// standard error makes the status 120 as well. An empty listing writes
    /// nothing and exits with 0. After a capture, no `UART capture failed`
    /// line follows the failed write.
    #[test]
    fn a_failed_write_makes_the_exit_status_120() {
        let root = Scratch::new("serial-capture-root");
        let devices = Scratch::new("serial-capture-devices");
        let broken = unwritten("Broken pipe (os error 32)");
        for (errno, report) in [
            (libc::EPIPE, broken.clone()),
            (libc::EIO, unwritten("Input/output error (os error 5)")),
        ] {
            let (code, out, err, tried) = faulty_command(
                root.root(),
                devices.root(),
                &["--help"],
                fresh_flag(),
                Some(errno),
                false,
            );
            assert_eq!((code, tried), (120, 1));
            assert!(out.is_empty());
            assert_eq!(err, [report]);
        }
        let (code, _, err, tried) = faulty_command(
            root.root(),
            devices.root(),
            &["--list"],
            fresh_flag(),
            Some(libc::EPIPE),
            false,
        );
        assert_eq!((code, tried), (0, 0));
        assert!(err.is_empty());
        devices.write("cu.usbA", b"");
        devices.write("ttyACM0", b"");
        let (code, _, err, tried) = faulty_command(
            root.root(),
            devices.root(),
            &["--list"],
            fresh_flag(),
            Some(libc::EPIPE),
            false,
        );
        assert_eq!((code, tried), (120, 1));
        assert_eq!(err, [broken.as_str()]);
        let output = root.path("failed");
        let output = output.to_str().unwrap();
        let capture = [
            "--port",
            MISSING_PORT,
            "--seconds",
            "0.01",
            "--output-dir",
            output,
        ];
        let (code, _, err, tried) = faulty_command(
            root.root(),
            devices.root(),
            &capture,
            fresh_flag(),
            Some(libc::EPIPE),
            false,
        );
        assert_eq!((code, tried), (120, 1));
        assert_eq!(err, [broken.as_str()]);
        assert!(root.path("failed/summary.json").is_file());
        for args in [&["--bogus"][..], &capture] {
            let (code, out, err, _) =
                faulty_command(root.root(), devices.root(), args, fresh_flag(), None, true);
            assert_eq!(code, 120, "{args:?}");
            assert!(out.is_empty() && err.is_empty());
        }
    }

    /// Characters that are no ASCII digit are no part of a number, and a
    /// `--max-bytes` literal is read whatever its length: leading zeros are
    /// allowed, and a value beyond 64 bits fails the bound. A value with
    /// another character is an invalid value also where its digits before
    /// that character are already beyond 64 bits.
    #[test]
    fn other_numerics_and_overlong_literals_are_refused() {
        let read = |option: &str, value: &str| {
            parse(&arguments(&["--port", "p", &format!("{option}={value}")]))
        };
        for value in ["\u{b2}", "\u{ff0e}5"] {
            assert_invalid_value(read("--seconds", value), "--seconds", value);
        }
        let zeros = "0".repeat(4300);
        let refused = [
            "\u{b2}".to_string(),
            "\u{2167}".to_string(),
            "\u{3007}".to_string(),
            "\u{9f4}".to_string(),
            "\u{fe0f}1".to_string(),
            "1\u{300}".to_string(),
            format!(" {} ", "0".repeat(4301)),
            format!("{}_7", vec!["0"; 4300].join("_")),
            format!("-{}", "0".repeat(4301)),
            "\u{661}".repeat(4301),
            "99999999999999999999x".to_string(),
            "18446744073709551616 ".to_string(),
            format!("+{}+", "9".repeat(20)),
        ];
        for value in &refused {
            assert_invalid_value(read("--max-bytes", value), "--max-bytes", value);
        }
        for value in [
            zeros.clone(),
            "0".repeat(4301),
            "1".repeat(4301),
            "18446744073709551615".to_string(),
            "18446744073709551616".to_string(),
        ] {
            assert_out_of_bounds(read("--max-bytes", &value), BYTES_BOUND);
        }
        for (value, max_bytes) in [
            (format!("{zeros}1"), 1),
            (format!("+{}07", "0".repeat(4299)), 7),
        ] {
            assert_eq!(
                read("--max-bytes", &value).unwrap(),
                Command::Capture {
                    port: "p".to_string(),
                    seconds: DEFAULT_SECONDS,
                    max_bytes,
                    output: None,
                }
            );
        }
    }

    /// An output directory that cannot be created is named in the error,
    /// also below a regular file, which is no directory. A missing parent
    /// that cannot be created is named by the parent of the output
    /// directory, the path that its creation was given, not by the ancestor
    /// that failed: here a symbolic link to nothing, which exists and is no
    /// directory, two levels up. Nothing is captured.
    #[test]
    fn an_output_directory_that_cannot_be_created_is_named() {
        let scratch = Scratch::new("serial-capture-uncreatable");
        let file = scratch.write("file", b"");
        let link = scratch.path("link");
        std::os::unix::fs::symlink(scratch.path("nothing"), &link).unwrap();
        let below_link = link.join("sub");
        for (output, error) in [
            (
                file.join("sub").join("run"),
                format!(
                    "{:?}: Not a directory (os error 20)",
                    file.join("sub").join("run")
                ),
            ),
            (
                file.join("run"),
                format!("{:?}: Not a directory (os error 20)", file.join("run")),
            ),
            (file.clone(), format!("{file:?}: File exists (os error 17)")),
            (
                below_link.join("run"),
                format!("{below_link:?}: File exists (os error 17)"),
            ),
        ] {
            assert_rejects(
                capture(
                    MISSING_PORT,
                    &output,
                    1.0,
                    DEFAULT_MAX_BYTES,
                    fresh_flag(),
                    &TIMING,
                ),
                &error,
            );
            let (code, out, err) = capture_command(
                scratch.root(),
                scratch.root(),
                &[
                    "--port",
                    MISSING_PORT,
                    "--output-dir",
                    output.to_str().unwrap(),
                ],
                fresh_flag(),
            );
            assert_eq!(code, 2, "{output:?}");
            assert!(out.is_empty());
            assert_eq!(err, [format!("UART capture failed: {error}")]);
        }
        let mut names: Vec<_> = std::fs::read_dir(scratch.root())
            .unwrap()
            .map(|entry| entry.unwrap().file_name())
            .collect();
        names.sort();
        assert_eq!(names, ["file", "link"]);
    }
}

mod resources {
    use super::*;

    /// Gives SIGINT, SIGTERM and SIGHUP the default dispositions of a fresh
    /// process: a test runner started in the background or under `nohup`
    /// passes SIGINT or SIGHUP on ignored.
    fn default_dispositions() {
        for signal in [libc::SIGINT, libc::SIGTERM, libc::SIGHUP] {
            // SAFETY: signal takes a signal number and a disposition and
            // touches no memory of this process; SIG_DFL is a valid
            // disposition for the three signals, and the child runs this
            // test alone.
            let previous = unsafe { libc::signal(signal, libc::SIG_DFL) };
            assert_ne!(previous, libc::SIG_ERR, "signal {signal}");
        }
    }

    /// Limits the files that this process writes to `bytes`. A limit belongs
    /// to the whole process, which is why only a child sets it.
    #[track_caller]
    fn limit_file_size(bytes: usize) {
        let mut limit = libc::rlimit {
            rlim_cur: 0,
            rlim_max: 0,
        };
        // SAFETY: `limit` is one initialized, properly aligned rlimit on this
        // frame, exclusively borrowed for the call, which writes it.
        let status = unsafe { libc::getrlimit(libc::RLIMIT_FSIZE, &mut limit) };
        assert_eq!(status, 0);
        limit.rlim_cur = bytes as libc::rlim_t;
        // SAFETY: `limit` is an initialized rlimit that the call only reads;
        // it lowers the soft limit and raises nothing.
        let status = unsafe { libc::setrlimit(libc::RLIMIT_FSIZE, &limit) };
        assert_eq!(status, 0);
    }

    /// Whether this process runs with the user ID of root, which file
    /// permissions do not restrict.
    fn is_root() -> bool {
        // SAFETY: geteuid takes no arguments, touches no memory of this
        // process and always succeeds.
        unsafe { libc::geteuid() == 0 }
    }

    /// The bytes are kept as received and hashed, the preview renders the
    /// terminal controls as text, the port gets its attributes back and is
    /// released, so that a new opener can use it.
    #[test]
    fn raw_hash_preview_and_restoration() {
        const PAYLOAD: &[u8] = b"CAS\xce\x9e\r\n\x00\x1b[2J\xff";
        let uart = Uart::new();
        let report = uart.receive(PAYLOAD);
        assert_eq!(report["status"], "CAPTURED");
        assert_eq!(report["reason"], "byte_limit");
        assert_eq!(uart.raw(), PAYLOAD);
        // `shasum -a 256` of the payload.
        assert_eq!(
            report["sha256"],
            "0b09f83d84d6efd1fa3d3bfc6ccbfa89d66bae0052e67ebef896fb5f1f5bf5c2"
        );
        assert_eq!(uart.preview(), "CAS\u{39e}\\r\n\\0\\u{1b}[2J\u{fffd}");
        assert_eq!(report["attributes_restored"], true);
        assert_eq!(report["exclusive"], true);
        uart.assert_restored();
        assert_eq!(report["boot_acceptance"], "NOT_EVALUATED");
        assert!(report["started_at"].as_str().unwrap().ends_with('Z'));
        assert!(report["finished_at"].as_str().unwrap().ends_with('Z'));
        assert_eq!(report["baud"], 115200);
        TtyPort::open(uart.port()).unwrap().finish().unwrap();
    }

    /// A quiet board is `NO_DATA` at the deadline, neither a failure nor a
    /// success. The board sends nothing and waits for nothing, so that the
    /// outcome does not depend on when the test's threads run.
    #[test]
    fn no_data_is_neither_boot_failure_nor_success() {
        let uart = Uart::new();
        let report = uart.quiet(0.03);
        assert_eq!(report["status"], "NO_DATA");
        assert_eq!(report["bytes"], 0);
        assert_eq!(report["reason"], "deadline");
        assert_eq!(report["sha256"], EMPTY_SHA256);
        let elapsed = report["elapsed_seconds"].as_f64().unwrap();
        assert!(elapsed >= 0.03, "{elapsed}");
        assert_eq!(uart.preview(), "");
        uart.assert_restored();
    }

    /// The quiet capture of [`no_data_is_neither_boot_failure_nor_success`]
    /// passes at the lowest scheduling priority: the test binary runs that
    /// test alone under `nice -n 19`, or on macOS under
    /// `taskpolicy -c background`.
    #[test]
    fn the_quiet_capture_passes_at_the_lowest_priority() {
        let prefix: &[&str] = if cfg!(target_os = "macos") {
            &["taskpolicy", "-c", "background"]
        } else {
            &["nice", "-n", "19"]
        };
        let test = "no_data_is_neither_boot_failure_nor_success";
        let ended = ChildTest::spawn_under(prefix, module_path!(), test, "").finish();
        assert!(ended.passed(), "{prefix:?}: {ended:?}");
    }

    /// Input that was queued before the capture opened the port is
    /// captured, so nothing flushed it; the slave's mode admits only
    /// reading, so the capture opened it read-only; and nothing reaches the
    /// board, which the test reads once the capture has ended.
    #[test]
    fn queued_input_is_preserved_and_the_port_is_read_only() {
        use std::os::unix::fs::PermissionsExt;
        let uart = Uart::new();
        uart.pty.set_termios(&raw_attributes(&uart.pty.termios()));
        uart.pty.write(b"queued");
        std::fs::set_permissions(uart.port(), std::fs::Permissions::from_mode(0o400)).unwrap();
        let report = uart.receipt(capture(
            uart.port(),
            &uart.output(),
            LONG,
            6,
            fresh_flag(),
            &TIMING,
        ));
        assert_eq!(report["status"], "CAPTURED");
        assert_eq!(uart.raw(), b"queued");
        assert_eq!(uart.pty.received(Duration::from_millis(300)), b"");
        if !is_root() {
            assert_rejects(
                TtyPort::open(uart.port()).map(drop),
                &format!("\"{}\": Permission denied (os error 13)", uart.port()),
            );
        }
    }

    /// An interrupt while the capture waits for input ends it as
    /// `INTERRUPTED`, the port restored and the receipt written.
    #[test]
    fn an_interrupted_capture_restores_the_port_and_records_its_receipt() {
        let uart = Uart::new();
        let flag = fresh_flag();
        let (result, ()) = uart.run(LONG, DEFAULT_MAX_BYTES, flag, |master| {
            master.await_raw();
            flag.store(libc::SIGINT, Ordering::SeqCst);
        });
        let report = uart.receipt(result);
        assert_eq!(keys(&report), capture_keys(false));
        assert_eq!(report["status"], "INTERRUPTED");
        assert_eq!(report["reason"], "interrupted");
        assert_eq!(report["exclusive"], true);
        assert_eq!(report["attributes_restored"], true);
        assert_eq!(report["requested_seconds"], json!(LONG));
        uart.assert_restored();
    }

    /// A device that closes ends the capture at once. On Darwin a slave
    /// whose master has closed reads empty, so the capture ends with the
    /// reason `end_of_stream`, and its attributes are restored. Linux hangs
    /// the slave up when its master closes: a read fails with `EIO` until
    /// the hang-up completes and reads empty after it, and every terminal
    /// request after it fails with `EIO`, so the capture fails with those
    /// errors alone.
    #[test]
    fn the_end_of_the_stream_ends_the_capture() {
        let mut uart = Uart::new();
        let board = uart.pty.board(|master| master.await_raw());
        uart.pty.close_master();
        let report = uart.receipt(capture(
            uart.port(),
            &uart.output(),
            LONG,
            DEFAULT_MAX_BYTES,
            fresh_flag(),
            &TIMING,
        ));
        board.join();
        assert_eq!(report["bytes"], 0);
        if cfg!(target_os = "linux") {
            assert_eq!(report["status"], "FAIL");
            assert_eq!(report["reason"], "error");
            let errors = errors(&report);
            assert!(!errors.is_empty());
            assert!(
                errors
                    .iter()
                    .all(|error| error.ends_with("Input/output error (os error 5)")),
                "{errors:?}"
            );
        } else {
            assert_eq!(report["status"], "NO_DATA");
            assert_eq!(report["reason"], "end_of_stream");
            assert_eq!(report["attributes_restored"], true);
        }
    }

    /// An interrupt caught once the handlers are installed and before the
    /// port opens ends the capture without opening the port.
    #[test]
    fn an_interrupt_before_the_port_opens_leaves_it_alone() {
        let uart = Uart::new();
        let flag = fresh_flag();
        flag.store(libc::SIGTERM, Ordering::SeqCst);
        let report = uart.receipt(capture(
            uart.port(),
            &uart.output(),
            1.0,
            DEFAULT_MAX_BYTES,
            flag,
            &TIMING,
        ));
        assert_eq!(keys(&report), capture_keys(false));
        assert_eq!(report["status"], "INTERRUPTED");
        assert_eq!(report["reason"], "interrupted");
        assert_eq!(report["exclusive"], false);
        assert_eq!(report["attributes_restored"], false);
        uart.assert_restored();
    }

    /// The handlers are installed immediately before the port opens, so that
    /// a signal before it ends the process by its start disposition: not for
    /// a capture refused before its receipt exists, and only once `raw.bin`
    /// exists. A failure to install them fails the receipt.
    #[test]
    fn the_handlers_are_installed_immediately_before_the_port_opens() {
        let scratch = Scratch::new("serial-capture-arm");
        let existing = scratch.path("existing");
        std::fs::create_dir(&existing).unwrap();
        let exists = format!("{existing:?}: File exists (os error 17)");
        for (output, seconds, refusal) in [
            (scratch.path("bounded"), 0.0, Some(SECONDS_BOUND)),
            (existing, 1.0, Some(exists.as_str())),
            (scratch.path("run"), 1.0, None),
        ] {
            let installed = Cell::new(0);
            let log = output.join("raw.bin");
            let result = capture_with(
                MISSING_PORT,
                &output,
                seconds,
                DEFAULT_MAX_BYTES,
                &TIMING,
                &mut || {
                    assert!(log.is_file(), "the handlers came before raw.bin");
                    installed.set(installed.get() + 1);
                    Ok(fresh_flag())
                },
            );
            match refusal {
                Some(message) => {
                    assert_rejects(result, message);
                    assert_eq!(installed.get(), 0, "{output:?}");
                }
                None => {
                    let report = result.unwrap();
                    assert_eq!(
                        errors(&report),
                        ["\"/nonexistent/krepi-port\": No such file or directory (os error 2)"]
                    );
                    assert_eq!(installed.get(), 1, "{output:?}");
                }
            }
        }
        let output = scratch.path("unarmed");
        let report = capture_with(
            MISSING_PORT,
            &output,
            1.0,
            DEFAULT_MAX_BYTES,
            &TIMING,
            &mut || Err(Failure::new("Invalid argument (os error 22)")),
        )
        .unwrap();
        assert_eq!(report["status"], "FAIL");
        assert_eq!(errors(&report), ["Invalid argument (os error 22)"]);
    }

    /// An interrupt during the capture of the command: the receipt is
    /// written, and the command prints its status and receipt lines and
    /// exits with 130.
    #[test]
    fn an_interrupted_command_prints_its_receipt_and_exits_with_130() {
        let uart = Uart::new();
        let flag = fresh_flag();
        let board = uart.pty.board(move |master| {
            master.await_raw();
            flag.store(libc::SIGINT, Ordering::SeqCst);
        });
        let output = uart.output();
        let (code, out, err) = capture_command(
            uart.scratch.root(),
            uart.scratch.root(),
            &[
                "--port",
                uart.port(),
                "--seconds",
                LONG_ARG,
                "--output-dir",
                output.to_str().unwrap(),
            ],
            flag,
        );
        board.join();
        assert_eq!(code, 130);
        let summary = std::fs::canonicalize(&output).unwrap().join("summary.json");
        assert_eq!(
            out,
            [
                "INTERRUPTED: 0 bytes; board boot is not evaluated.".to_string(),
                format!("Receipt: {}", summary.display())
            ]
        );
        assert!(err.is_empty());
        let report = parse_receipt(&uart.scratch.read("capture/summary.json"));
        assert_eq!(report["reason"], "interrupted");
        assert_eq!(report["requested_seconds"], json!(LONG));
        uart.assert_restored();
    }

    /// A real SIGINT, SIGTERM or SIGHUP once the port is open is caught by
    /// the handlers that the command installs and ends the capture: the
    /// command prints its status and receipt lines and exits with 130, the
    /// receipt says `INTERRUPTED`, and the port has its attributes back. A
    /// signal that the child inherits ignored ends the capture the same way,
    /// as the handlers replace `SIG_IGN`. The command runs in a child
    /// process, which the test signals once the port is raw.
    #[test]
    fn a_signal_once_the_port_is_open_is_caught_and_the_port_restored() {
        if let Some(part) = child_part() {
            let mut part = part.splitn(3, '\n');
            let ignored: libc::c_int = part.next().unwrap().parse().unwrap();
            let (port, output) = (part.next().unwrap(), part.next().unwrap());
            default_dispositions();
            if ignored != 0 {
                // SAFETY: signal takes a signal number and a disposition and
                // touches no memory of this process; SIG_IGN is a valid
                // disposition for this signal, and the child runs this test
                // alone.
                let previous = unsafe { libc::signal(ignored, libc::SIG_IGN) };
                assert_ne!(previous, libc::SIG_ERR);
            }
            let scratch = Scratch::new("serial-capture-signalled");
            let args = [
                "--port",
                port,
                "--seconds",
                LONG_ARG,
                "--output-dir",
                output,
            ];
            assert_eq!(main(scratch.root(), &arguments(&args)), 130);
            return;
        }
        // The first number is a signal that the child inherits ignored, as
        // under `nohup` or in a background job of a script.
        for (ignored, signal) in [
            (0, libc::SIGINT),
            (0, libc::SIGTERM),
            (0, libc::SIGHUP),
            (libc::SIGINT, libc::SIGINT),
            (libc::SIGTERM, libc::SIGTERM),
            (libc::SIGHUP, libc::SIGHUP),
        ] {
            let uart = Uart::new();
            let output = uart.output();
            let part = format!("{ignored}\n{}\n{}", uart.port(), output.display());
            let test = "a_signal_once_the_port_is_open_is_caught_and_the_port_restored";
            let mut child = ChildTest::spawn(module_path!(), test, &part);
            child.await_state("raw", || uart.is_raw());
            child.signal(signal);
            let ended = child.finish();
            assert!(ended.passed(), "signal {signal}: {ended:?}");
            let summary = std::fs::canonicalize(&output).unwrap().join("summary.json");
            assert_eq!(
                ended.printed(),
                [
                    "INTERRUPTED: 0 bytes; board boot is not evaluated.",
                    format!("Receipt: {}", summary.display()).as_str()
                ],
                "{ended:?}"
            );
            let report = parse_receipt(&uart.scratch.read("capture/summary.json"));
            assert_eq!(keys(&report), capture_keys(false));
            assert_eq!(report["status"], "INTERRUPTED", "{signal}");
            assert_eq!(report["reason"], "interrupted");
            assert_eq!(report["exclusive"], true);
            assert_eq!(report["attributes_restored"], true);
            uart.assert_restored();
        }
    }

    /// Before the port opens, SIGINT, SIGTERM and SIGHUP end the command's
    /// process by their default action: a child process runs what ends
    /// before the arm, the help, the listing, a usage error, limits out of
    /// bounds, an empty port name, an existing output directory and, unless
    /// the test runs as root, which permissions do not restrict, one that
    /// cannot hold `raw.bin`, with the default dispositions, and then raises
    /// the signal. A handler, once installed, stays, so none of those runs
    /// installed one.
    #[test]
    fn a_signal_before_the_port_opens_ends_the_process() {
        use std::os::unix::process::ExitStatusExt;
        const MARKER: &str = "the refusals returned, without a newline";
        if let Some(signal) = child_part() {
            let signal: libc::c_int = signal.parse().unwrap();
            default_dispositions();
            let scratch = Scratch::new("serial-capture-unarmed");
            let existing = scratch.path("existing");
            std::fs::create_dir(&existing).unwrap();
            let (new, unwritable) = (scratch.path("new"), scratch.path("unwritable"));
            let (root, existing_dir) = (scratch.root(), existing.to_str().unwrap());
            let (new_dir, unwritable_dir) = (new.to_str().unwrap(), unwritable.to_str().unwrap());
            let missing = ["--port", MISSING_PORT];
            let rows: [(&[&str], i32); 6] = [
                (&["--help"], 0),
                (&["--list"], 0),
                (&["--bogus"], 2),
                (&[missing[0], missing[1], "--seconds", "0"], 2),
                (&["--port=", "--output-dir", new_dir], 2),
                (&[missing[0], missing[1], "--output-dir", existing_dir], 2),
            ];
            for (args, code) in rows {
                assert_eq!(main(root, &arguments(args)), code, "{args:?}");
            }
            assert!(!new.exists());
            assert_eq!(std::fs::read_dir(&existing).unwrap().count(), 0);
            // The capture creates this directory without write permission
            // and so cannot create raw.bin in it: a refusal after the
            // directory and before the arm. The mask belongs to the whole
            // process, which is why only a child changes it.
            if !is_root() {
                let args = [missing[0], missing[1], "--output-dir", unwritable_dir];
                // SAFETY: umask takes a mask, touches no memory of this
                // process and always succeeds.
                let mask = unsafe { libc::umask(0o222) };
                let code = main(root, &arguments(&args));
                // SAFETY: as above; the process has its own mask back.
                unsafe { libc::umask(mask) };
                assert_eq!(code, 2);
                assert_eq!(std::fs::read_dir(&unwritable).unwrap().count(), 0);
            }
            // The tree goes now: the signal ends the process without
            // dropping it.
            drop(scratch);
            // Straight to standard output, which the test runner does not
            // capture in the child.
            let mut stdout = io::stdout();
            stdout.write_all(MARKER.as_bytes()).unwrap();
            stdout.flush().unwrap();
            // SAFETY: raise takes only a signal number and touches no memory
            // of this process; the child runs this test alone.
            unsafe { libc::raise(signal) };
            panic!("the process survived signal {signal}");
        }
        for signal in [libc::SIGINT, libc::SIGTERM, libc::SIGHUP] {
            let test = "a_signal_before_the_port_opens_ends_the_process";
            let ended = ChildTest::spawn(module_path!(), test, &signal.to_string()).finish();
            assert_eq!(ended.status.signal(), Some(signal), "{ended:?}");
            assert!(!ended.status.core_dumped());
            assert_eq!(
                ended.lines.last().map(String::as_str),
                Some(MARKER),
                "{ended:?}"
            );
        }
    }

    /// The handlers stay installed once the capture has ended: a real
    /// SIGINT, SIGTERM or SIGHUP at each line that the command prints after
    /// it is caught and leaves the outcome and the exit status as they are,
    /// the port restored. The unit test
    /// `an_interrupt_once_the_capture_has_ended_leaves_the_outcome` sets the
    /// flag during the restoration. The command runs in a child process with
    /// the real handlers; the board sends nothing and waits for nothing.
    #[test]
    fn a_signal_once_the_capture_has_ended_is_caught() {
        if let Some(signal) = child_part() {
            let signal: libc::c_int = signal.parse().unwrap();
            default_dispositions();
            let uart = Uart::new();
            let output = uart.output();
            let args = arguments(&[
                "--port",
                uart.port(),
                "--seconds",
                "0.05",
                "--output-dir",
                output.to_str().unwrap(),
            ]);
            let root = uart.scratch.root();
            let mut lines = Vec::new();
            let code = run_with(
                root,
                root,
                &args,
                &TIMING,
                &mut Console {
                    print: &mut |line| {
                        lines.push(line.to_string());
                        // SAFETY: raise takes only a signal number and
                        // touches no memory of this process; the child runs
                        // this test alone.
                        assert_eq!(unsafe { libc::raise(signal) }, 0);
                        Ok(())
                    },
                    warn: &mut |line| panic!("{line}"),
                    arm: &mut || catch_interrupts(),
                },
            );
            assert_eq!(code, 0);
            let summary = std::fs::canonicalize(&output).unwrap().join("summary.json");
            assert_eq!(
                lines,
                [
                    "NO_DATA: 0 bytes; board boot is not evaluated.".to_string(),
                    format!("Receipt: {}", summary.display())
                ]
            );
            let report = parse_receipt(&uart.scratch.read("capture/summary.json"));
            assert_eq!(report["status"], "NO_DATA");
            uart.assert_restored();
            return;
        }
        for signal in [libc::SIGINT, libc::SIGTERM, libc::SIGHUP] {
            let test = "a_signal_once_the_capture_has_ended_is_caught";
            let ended = ChildTest::spawn(module_path!(), test, &signal.to_string()).finish();
            assert!(ended.passed(), "signal {signal}: {ended:?}");
        }
    }

    /// `raw.bin` is written unbuffered, so that it holds a read before the
    /// next one, and a write that fails is an error of the capture in the
    /// read that fails it. A real failure, past a file-size limit, in a
    /// child process, as a limit and a signal disposition belong to the
    /// whole process: the board sends exactly the limit, waits until the
    /// file holds it, and sends one byte more, whose write fails. The child
    /// ignores SIGXFSZ, so that the write fails with `EFBIG`. The capture
    /// ends at once with the error in the receipt, whose `bytes` is the
    /// length of `raw.bin`, and the port restored.
    #[test]
    fn a_failed_write_of_raw_bin_ends_the_capture_in_that_read() {
        const LIMIT: usize = 4096;
        if child_part().is_some() {
            // SAFETY: signal takes a signal number and a disposition and
            // touches no memory of this process; SIG_IGN is a valid
            // disposition for SIGXFSZ, and the child runs this test alone.
            let previous = unsafe { libc::signal(libc::SIGXFSZ, libc::SIG_IGN) };
            assert_ne!(previous, libc::SIG_ERR);
            limit_file_size(LIMIT);
            let uart = Uart::new();
            let output = uart.output();
            let raw = output.join("raw.bin");
            let board = uart.pty.board(move |master| {
                master.await_raw();
                master.write(&[b'a'; LIMIT]);
                let deadline = Instant::now() + TEST_WAIT;
                while std::fs::metadata(&raw).map_or(0, |file| file.len()) < LIMIT as u64 {
                    assert!(Instant::now() < deadline, "raw.bin kept its bytes back");
                    std::thread::sleep(Duration::from_millis(2));
                }
                master.write(b"b");
            });
            let (code, out, err) = capture_command(
                uart.scratch.root(),
                uart.scratch.root(),
                &[
                    "--port",
                    uart.port(),
                    "--seconds",
                    LONG_ARG,
                    "--output-dir",
                    output.to_str().unwrap(),
                ],
                fresh_flag(),
            );
            board.join();
            assert_eq!(code, 2);
            let summary = std::fs::canonicalize(&output).unwrap().join("summary.json");
            assert_eq!(
                out,
                [
                    "a".repeat(LIMIT),
                    format!("FAIL: {LIMIT} bytes; board boot is not evaluated."),
                    format!("Receipt: {}", summary.display())
                ]
            );
            assert!(err.is_empty(), "{err:?}");
            let report = parse_receipt(&uart.scratch.read("capture/summary.json"));
            assert_eq!(keys(&report), capture_keys(true));
            assert_eq!(report["status"], "FAIL");
            assert_eq!(report["reason"], "error");
            assert_eq!(errors(&report), ["File too large (os error 27)"]);
            assert_eq!(report["bytes"], LIMIT as u64);
            assert_eq!(report["preview_bytes"], LIMIT as u64);
            // `shasum -a 256` of 4096 bytes `a`.
            assert_eq!(
                report["sha256"],
                "c93eee2d0db02f10acc7460d9576e122dcf8cd53c4bf8dfcae1b3e74ebcfff5a"
            );
            assert_eq!(report["attributes_restored"], true);
            assert_eq!(uart.raw().len(), LIMIT);
            uart.assert_restored();
            return;
        }
        let test = "a_failed_write_of_raw_bin_ends_the_capture_in_that_read";
        let ended = ChildTest::spawn(module_path!(), test, "limit").finish();
        assert!(ended.passed(), "{ended:?}");
    }

    /// With SIGXFSZ at its default action, a write past a file-size limit
    /// does not fail: the signal ends the process in that write, without a
    /// receipt and with the port left raw. The parent owns the port and
    /// plays the board, as a process that dies takes its descriptors with
    /// it. The child forks for the command, as the signal goes to the
    /// process: of the test runner's threads another one could take it and
    /// leave this one to restore the port, and a fork has only the calling
    /// thread, as the command's process has.
    #[test]
    fn a_write_past_a_file_size_limit_ends_the_process_by_its_signal() {
        const LIMIT: usize = 4096;
        if let Some(part) = child_part() {
            let (port, output) = part.split_once('\n').unwrap();
            // SAFETY: fork takes no arguments and touches no memory of this
            // process. The new process has only this thread, and it runs the
            // whole command, which allocates, locks standard output and
            // writes files, not only async-signal-safe calls. That is sound
            // because no lock it needs can be held at the fork: the only
            // other thread is the test runner's main thread, which runs this
            // one test alone and waits for its result on a channel without
            // holding a lock, and the C libraries of Linux and Darwin keep
            // their allocator usable in the child of a fork. The new process
            // ends with _exit, so it runs no destructor of the parent's state.
            let pid = unsafe { libc::fork() };
            assert!(pid >= 0, "{}", io::Error::last_os_error());
            if pid == 0 {
                // SAFETY: signal takes a signal number and a disposition and
                // touches no memory of this process; SIG_DFL is a valid
                // disposition for SIGXFSZ.
                let previous = unsafe { libc::signal(libc::SIGXFSZ, libc::SIG_DFL) };
                assert_ne!(previous, libc::SIG_ERR);
                limit_file_size(LIMIT);
                let args = [
                    "--port",
                    port,
                    "--seconds",
                    LONG_ARG,
                    "--output-dir",
                    output,
                ];
                // The output directory is named, so the root stays unused.
                let code = main(Path::new("/nonexistent"), &arguments(&args));
                // SAFETY: _exit takes a status and ends this process at once.
                unsafe { libc::_exit(code) };
            }
            let mut status = 0;
            // SAFETY: `status` is one initialized integer on this frame,
            // exclusively borrowed for the call, which writes it.
            assert_eq!(unsafe { libc::waitpid(pid, &mut status, 0) }, pid);
            assert!(libc::WIFSIGNALED(status), "{status:#x}");
            assert_eq!(libc::WTERMSIG(status), libc::SIGXFSZ);
            return;
        }
        let uart = Uart::new();
        let output = uart.output();
        let raw = output.join("raw.bin");
        let part = format!("{}\n{}", uart.port(), output.display());
        let test = "a_write_past_a_file_size_limit_ends_the_process_by_its_signal";
        let mut child = ChildTest::spawn(module_path!(), test, &part);
        child.await_state("raw", || uart.is_raw());
        // The port's input queue holds less than the limit, so this write
        // waits for the command's reads. It runs on the board's thread, so
        // that a command that stops reading fails the wait below, which has
        // a deadline, instead of holding this thread; once the file holds
        // the limit, the write is done and one byte more fits.
        let board = uart.pty.board(|master| master.write(&[b'a'; LIMIT]));
        child.await_state("full", || {
            std::fs::metadata(&raw).is_ok_and(|file| file.len() == LIMIT as u64)
        });
        board.join();
        uart.pty.write(b"b");
        let ended = child.finish();
        assert!(ended.passed(), "{ended:?}");
        assert_eq!(uart.raw().len(), LIMIT);
        assert!(!output.join("summary.json").exists());
        assert!(uart.is_raw(), "the port has its attributes back");
    }
}

mod receipts {
    use super::*;

    /// The receipt has its keys in byte order, the fixed line and file
    /// fields, UTC time stamps with six fraction digits, and
    /// `requested_seconds` as a JSON number with a fraction: `30.0` for the
    /// default, `1.0` for `--seconds 1`, `0.00001` for `--seconds 1e-5`.
    #[test]
    fn the_receipt_has_its_keys_and_values() {
        let uart = Uart::new();
        let report = uart.receive(b"ok");
        assert_eq!(keys(&report), capture_keys(false));
        for (key, value) in [
            ("schema_version", json!(1)),
            ("status", json!("CAPTURED")),
            ("reason", json!("byte_limit")),
            ("port", json!(uart.port())),
            ("baud", json!(115200)),
            ("data_bits", json!(8)),
            ("parity", json!("none")),
            ("stop_bits", json!(1)),
            ("flow_control", json!("none")),
            ("requested_seconds", json!(LONG)),
            ("max_bytes", json!(2)),
            ("bytes", json!(2)),
            ("exclusive", json!(true)),
            ("attributes_restored", json!(true)),
            ("raw_file", json!("raw.bin")),
            ("preview_file", json!("preview.txt")),
            ("boot_acceptance", json!("NOT_EVALUATED")),
            ("preview_bytes", json!(2)),
            ("preview_truncated", json!(false)),
        ] {
            assert_eq!(report[key], value, "{key}");
        }
        assert!(report["elapsed_seconds"].is_f64());
        // The times of `report::utc_now`, with six fraction digits.
        for key in ["started_at", "finished_at"] {
            let at = report[key].as_str().unwrap();
            assert_eq!(at.len(), "2026-10-14T07:45:17.123456Z".len(), "{at}");
            assert_eq!((&at[10..11], &at[19..20]), ("T", "."), "{at}");
            assert!(at.ends_with('Z'), "{at}");
        }
        let root = Scratch::new("serial-capture-seconds");
        for (seconds, text) in [
            (None, "30.0"),
            (Some("1"), "1.0"),
            (Some("1e-5"), "0.00001"),
        ] {
            let output = root.path(&format!("run-{text}"));
            let mut args = vec![
                "--port",
                MISSING_PORT,
                "--output-dir",
                output.to_str().unwrap(),
            ];
            if let Some(seconds) = seconds {
                args.extend(["--seconds", seconds]);
            }
            let (code, _, _) = capture_command(root.root(), root.root(), &args, fresh_flag());
            assert_eq!(code, 2);
            let summary =
                String::from_utf8(std::fs::read(output.join("summary.json")).unwrap()).unwrap();
            assert!(
                summary.contains(&format!("\n  \"requested_seconds\": {text},\n")),
                "{summary}"
            );
        }
    }

    /// After a capture the command prints the preview, the status line and
    /// the resolved receipt path, and exits with 0 for `CAPTURED` and
    /// `NO_DATA`, whose empty preview is not printed, and with 2 for
    /// `FAIL`. The quiet board sends nothing and waits for nothing.
    #[test]
    fn the_command_prints_the_preview_status_and_receipt() {
        let uart = Uart::new();
        let board = uart.pty.board(sends(b"CAS\xce\x9e\r\n\x00\x1b[2J\xff"));
        let output = uart.output();
        let output_dir = output.to_str().unwrap();
        let (code, out, err) = capture_command(
            uart.scratch.root(),
            uart.scratch.root(),
            &[
                "--port",
                uart.port(),
                "--seconds",
                LONG_ARG,
                "--max-bytes",
                "13",
                "--output-dir",
                output_dir,
            ],
            fresh_flag(),
        );
        board.join();
        let summary = std::fs::canonicalize(&output).unwrap().join("summary.json");
        assert_eq!(code, 0);
        assert_eq!(
            out,
            [
                "CAS\u{39e}\\r\n\\0\\u{1b}[2J\u{fffd}".to_string(),
                "CAPTURED: 13 bytes; board boot is not evaluated.".to_string(),
                format!("Receipt: {}", summary.display()),
            ]
        );
        assert!(err.is_empty());
        let quiet = uart.scratch.path("quiet");
        let (code, out, _) = capture_command(
            uart.scratch.root(),
            uart.scratch.root(),
            &[
                "--port",
                uart.port(),
                "--seconds",
                "0.05",
                "--output-dir",
                quiet.to_str().unwrap(),
            ],
            fresh_flag(),
        );
        assert_eq!(code, 0);
        assert_eq!(out[0], "NO_DATA: 0 bytes; board boot is not evaluated.");
        assert_eq!(out.len(), 2);
        let failed = uart.scratch.path("failed");
        let (code, out, _) = capture_command(
            uart.scratch.root(),
            uart.scratch.root(),
            &[
                "--port",
                MISSING_PORT,
                "--seconds",
                "0.01",
                "--output-dir",
                failed.to_str().unwrap(),
            ],
            fresh_flag(),
        );
        assert_eq!(code, 2);
        assert_eq!(out[0], "FAIL: 0 bytes; board boot is not evaluated.");
        uart.assert_restored();
    }

    /// `-h` and `--help` print the same help on standard output, also after
    /// other options, and exit with 0 without capturing anything. The help is
    /// clap's: it describes the command, gives its usage and lists the seven
    /// options, one to a line, with the defaults of the limits.
    #[test]
    fn the_help_lists_the_options_and_their_defaults() {
        let root = Scratch::new("serial-capture-help");
        let (code, help, err) =
            capture_command(root.root(), root.root(), &["--help"], fresh_flag());
        assert_eq!(code, 0);
        assert!(err.is_empty());
        assert_eq!(help.len(), 1);
        for args in [&["-h"][..], &["--port", "p", "-h"]] {
            let (code, out, err) = capture_command(root.root(), root.root(), args, fresh_flag());
            assert_eq!(code, 0, "{args:?}");
            assert_eq!(out, help, "{args:?}");
            assert!(err.is_empty());
        }
        let help = &help[0];
        assert!(
            help.starts_with(
                "Record a bounded UART receive session without interpreting board boot success.\n"
            ),
            "{help}"
        );
        assert!(help.contains(&format!("\n{USAGE}")), "{help}");
        let options: Vec<&str> = help
            .lines()
            .map(str::trim_start)
            .filter(|line| line.starts_with('-'))
            .collect();
        for (line, (option, default)) in options.iter().zip([
            ("--list ", None),
            ("--port <PORT> ", None),
            ("--seconds <SECONDS> ", Some("[default: 30]")),
            ("--max-bytes <MAX_BYTES> ", Some("[default: 262144]")),
            ("--output-dir <OUTPUT_DIR> ", None),
            ("-h, --help ", None),
        ]) {
            assert!(line.starts_with(option), "{line}");
            assert_eq!(line.contains("[default:"), default.is_some(), "{line}");
            assert!(
                default.is_none_or(|default| line.ends_with(default)),
                "{line}"
            );
        }
        assert_eq!(options.len(), 6, "{help}");
        assert_eq!(std::fs::read_dir(root.root()).unwrap().count(), 0);
    }

    /// The help and the usage keep their text on a terminal: not wrapped to
    /// the window or `COLUMNS` and without colour, whatever the colour
    /// variables say. `main` writes on the real streams, the slave of a pair
    /// with a window of 120 columns, in a child process, as the streams and
    /// the environment belong to the whole process; the parent reads from
    /// the master exactly the text that the command writes into a buffer in
    /// this process, with the line discipline's `\r\n`, and no escape byte.
    #[test]
    fn the_help_and_the_usage_keep_their_text_on_a_terminal() {
        if let Some(part) = child_part() {
            let mut part = part.splitn(3, '\n');
            let code: i32 = part.next().unwrap().parse().unwrap();
            let slave = std::ffi::CString::new(part.next().unwrap()).unwrap();
            let arg = part.next().unwrap();
            // SAFETY: `slave` is a NUL-terminated string that lives until the
            // call returns, and the call only reads it.
            let fd = unsafe { libc::open(slave.as_ptr(), libc::O_RDWR | libc::O_NOCTTY) };
            assert!(fd >= 0, "{}", io::Error::last_os_error());
            let window = libc::winsize {
                ws_row: 40,
                ws_col: 120,
                ws_xpixel: 0,
                ws_ypixel: 0,
            };
            // SAFETY: TIOCSWINSZ reads one winsize, and `window` is an
            // initialized, properly aligned winsize on this frame that the
            // borrow keeps alive during the call; `fd` is an open terminal.
            assert_eq!(unsafe { libc::ioctl(fd, libc::TIOCSWINSZ, &window) }, 0);
            let scratch = Scratch::new("serial-capture-terminal");
            // SAFETY: dup takes a descriptor and touches no memory of this
            // process; the standard streams are open.
            let streams = unsafe { (libc::dup(1), libc::dup(2)) };
            assert!(streams.0 >= 0 && streams.1 >= 0);
            // SAFETY: dup2 takes descriptors and touches no memory of this
            // process; `fd` is open, and the test runner's streams wait
            // aside in their duplicates.
            let moved = unsafe { (libc::dup2(fd, 1), libc::dup2(fd, 2)) };
            assert_eq!(moved, (1, 2));
            let returned = main(scratch.root(), &arguments(&[arg]));
            // SAFETY: as above; the test runner has its streams back.
            let moved = unsafe { (libc::dup2(streams.0, 1), libc::dup2(streams.1, 2)) };
            assert_eq!(moved, (1, 2));
            assert_eq!(returned, code);
            return;
        }
        let test = "the_help_and_the_usage_keep_their_text_on_a_terminal";
        let root = Scratch::new("serial-capture-buffered");
        let (_, help, _) = capture_command(root.root(), root.root(), &["--help"], fresh_flag());
        let (_, _, usage) = capture_command(root.root(), root.root(), &["--bogus"], fresh_flag());
        for environment in [
            [
                ("COLUMNS", Some("40")),
                ("FORCE_COLOR", None),
                ("PYTHON_COLORS", None),
                ("CLICOLOR_FORCE", None),
            ],
            [
                ("COLUMNS", None),
                ("FORCE_COLOR", Some("1")),
                ("PYTHON_COLORS", Some("1")),
                ("CLICOLOR_FORCE", Some("1")),
            ],
        ] {
            let mut environment = environment.to_vec();
            environment.extend([
                ("TERM", Some("xterm-256color")),
                ("LINES", None),
                ("NO_COLOR", None),
            ]);
            for (arg, code, text) in [("--help", 0, &help), ("--bogus", 2, &usage)] {
                assert_eq!(text.len(), 1, "{arg}");
                assert!(text[0].contains(USAGE), "{arg}: {text:?}");
                let pty = Pty::open();
                let part = format!("{code}\n{}\n{arg}", pty.path());
                let child = ChildTest::spawn_with(module_path!(), test, &part, &environment);
                let expected = format!("{}\n", text[0]).replace('\n', "\r\n");
                let received = pty.read(expected.len());
                assert!(!received.contains(&0x1b), "{arg}: {received:?}");
                assert_eq!(String::from_utf8_lossy(&received), expected, "{arg}");
                let ended = child.finish();
                assert!(ended.passed(), "{arg}: {ended:?}");
                assert_eq!(pty.received(Duration::from_millis(50)), b"", "{arg}");
            }
        }
    }

    /// Without `--output-dir` the capture creates
    /// `artifacts/hardware-uart/<%Y%m%dT%H%M%SZ>-<12 hex digits>` below the
    /// repository root, with its missing parents.
    #[test]
    fn the_default_output_is_a_new_run_below_the_root() {
        let root = Scratch::new("serial-capture-default");
        let (code, out, _) = capture_command(
            root.root(),
            root.root(),
            &["--port", MISSING_PORT],
            fresh_flag(),
        );
        assert_eq!(code, 2);
        let runs: Vec<PathBuf> = std::fs::read_dir(root.path("artifacts/hardware-uart"))
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .collect();
        assert_eq!(runs.len(), 1);
        let name = runs[0].file_name().unwrap().to_str().unwrap();
        assert_eq!(name.len(), "20261101T120000Z-".len() + 12, "{name}");
        assert!(runs[0].join("summary.json").is_file());
        let summary = std::fs::canonicalize(&runs[0])
            .unwrap()
            .join("summary.json");
        assert_eq!(out[1], format!("Receipt: {}", summary.display()));
    }

    /// `--list` prints the entries of any type whose names start with
    /// `cu.usb`, `ttyUSB` or `ttyACM`, case-sensitively, in the byte order
    /// of their names, rendered, and captures nothing.
    #[test]
    fn the_list_filters_usb_candidates_without_opening_them() {
        let devices = Scratch::new("serial-capture-list");
        for name in [
            "cu.usbserial-test",
            "cu.usbmodem-test",
            "ttyUSB0",
            "ttyACM0",
            "cu.Bluetooth-Incoming-Port",
            "tty",
            "console",
            "ttyUSB",
            "cu.usb",
            "CU.USBX",
            "ttyusb1",
            "xttyACM0",
            "cu.usb\x1bodd",
            "ttyACM\u{e9}",
        ] {
            devices.write(name, b"");
        }
        std::fs::create_dir(devices.path("ttyUSBdir")).unwrap();
        std::os::unix::fs::symlink(devices.path("nowhere"), devices.path("ttyACM9")).unwrap();
        let names: Vec<String> = list_ports(devices.root())
            .iter()
            .map(|path| {
                assert_eq!(path.parent(), Some(devices.root()));
                path.file_name().unwrap().to_str().unwrap().to_string()
            })
            .collect();
        let listed = [
            "cu.usb",
            "cu.usb\x1bodd",
            "cu.usbmodem-test",
            "cu.usbserial-test",
            "ttyACM0",
            "ttyACM9",
            "ttyACM\u{e9}",
            "ttyUSB",
            "ttyUSB0",
            "ttyUSBdir",
        ];
        assert_eq!(names, listed);
        let root = Scratch::new("serial-capture-list-root");
        let (code, out, err) =
            capture_command(root.root(), devices.root(), &["--list"], fresh_flag());
        assert_eq!(code, 0);
        let rendered: Vec<String> = listed
            .iter()
            .map(|name| {
                format!(
                    "{}/{}",
                    devices.root().display(),
                    name.replace('\x1b', "\\u{1b}")
                )
            })
            .collect();
        assert_eq!(out, rendered);
        assert!(err.is_empty());
        assert_eq!(std::fs::read_dir(root.root()).unwrap().count(), 0);
        assert!(list_ports(&devices.path("missing")).is_empty());
    }
}
