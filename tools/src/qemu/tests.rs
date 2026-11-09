use super::*;
use crate::TEST_WAIT;
use crate::pty::{Attributes, Pty, exclusive_open_refused, lock_refused};
use crate::receipt::ready_line_named;
use crate::scratch::Scratch;
use crate::tty::INTERRUPTED;
use std::fmt::Debug;
use std::io::{self, BufRead, BufReader};
use std::sync::atomic::{AtomicI32, Ordering};

/// The serial output that a guarded capture of a prototype guest kept at
/// most, 256 KiB.
const MAX_SERIAL_BYTES: usize = 256 * 1024;
/// The records of the prototype kernel that end a check wherever they
/// appear in its output.
const FATAL: [&[u8]; 3] = [b"CASXI_PANIC", b"CASXI_EXCEPTION", b"CASXI_HALTED"];
/// The records that end a board session of the prototype kernel: those of
/// [`FATAL`] and the failures of its PCIe and RP1 bring-up.
const FAILURE_MARKERS: [&[u8]; 5] = [
    FATAL[0],
    FATAL[1],
    FATAL[2],
    b"CASXI_PCIE_INIT_FAIL",
    b"CASXI_RP1_MMIO_FAIL",
];
/// The failure of a board capture whose output holds a fatal record.
const FATAL_TEXT: &str = "kernel fault or halt during serial validation";
/// A small output limit, which the tests of the limit pass.
const LIMIT: usize = 8;
/// The failure of output past [`LIMIT`].
const EXCEEDED: &str = "serial output exceeded 8 bytes";
/// A board session that a test never reaches the end of while it waits.
const SESSION: Duration = TEST_WAIT.saturating_mul(2);
/// The longest failure tail, for a tail that a test ends by `CASXI_HALTED`
/// or by an error, which a slow host never ends by its duration.
const TAIL: Duration = Duration::from_secs(120);
/// The time values of a board capture under test: those of the Pi 5, with a
/// request transmit time that a slow host never exceeds.
const TIMING: Timing = Timing {
    request_transmit: TEST_WAIT,
    ..Timing::PI5
};
/// The time values of a capture of a child process under test: those of QEMU
/// virt, with bounds for the final collection and the end of the process
/// that a slow host never reaches.
const GUEST: Timing = Timing {
    guest_finish: TEST_WAIT,
    stop_grace: TEST_WAIT,
    kill_grace: TEST_WAIT,
    ..Timing::QEMU_VIRT
};

/// Requires a rejection with exactly the message `expected`.
#[track_caller]
fn assert_rejects<T: Debug>(result: Result<T, Failure>, expected: &str) {
    match result {
        Err(Failure(message)) => assert_eq!(message, expected),
        Ok(value) => panic!("accepted: {value:?}"),
    }
}

/// The keys of `value`, an object, in their order.
#[track_caller]
fn keys(value: &Value) -> Vec<&str> {
    value
        .as_object()
        .expect("an object")
        .keys()
        .map(String::as_str)
        .collect()
}

/// A matcher for the first occurrence of `needle`, anywhere in the bytes.
fn bytes(needle: &'static [u8]) -> impl Fn(&[u8]) -> Option<Match> {
    move |buffer| {
        buffer
            .windows(needle.len())
            .position(|window| window == needle)
            .map(|start| Match {
                start,
                end: start + needle.len(),
                captures: Vec::new(),
            })
    }
}

/// A fake QEMU: a shell script that answers `--version` with the two lines
/// of QEMU, the first ending in `\r\n`, and runs `body` otherwise.
#[track_caller]
fn fake_qemu(scratch: &Scratch, name: &str, body: &str) -> PathBuf {
    scratch.script(
        name,
        &format!(
            "#!/bin/sh\nif [ \"$1\" = --version ]; then\n  printf 'QEMU emulator version 0.0.0\\r\\nCopyright (c) 2003-2026 Fabrice Bellard and the QEMU Project developers\\n'\n  exit 0\nfi\n{body}\n"
        ),
    )
}

/// A child process that runs the shell command `script` with all three
/// standard streams piped, as a guest.
#[track_caller]
fn shell_guest(script: &str) -> Child {
    Command::new("sh")
        .args(["-c", script])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("start sh")
}

/// A child that has exited with code 3 is reported with its exit code and no
/// signal; one that SIGTERM ends with that signal; and one that ignores
/// SIGTERM is killed and reported with SIGKILL. A grace that a slow host
/// never exceeds keeps the first two from being killed; the third waits its
/// whole stop grace, so that one is short.
#[test]
fn the_stop_report_gives_the_exit_code_or_the_signal() {
    let generous = Timing {
        stop_grace: TEST_WAIT,
        kill_grace: TEST_WAIT,
        ..Timing::QEMU_VIRT
    };
    let mut exited = Command::new("sh")
        .args(["-c", "exit 3"])
        .stdin(Stdio::null())
        .spawn()
        .unwrap();
    exited.wait().unwrap();
    assert_eq!(
        stop_process(&mut exited, &generous),
        json!({
            "intentional_shutdown": false,
            "forced_kill": false,
            "exit_code": 3,
            "signal": null,
        })
    );

    // `cat` waits for input on a pipe that stays open until it ends.
    let mut waiting = Command::new("cat")
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .spawn()
        .unwrap();
    let report = stop_process(&mut waiting, &generous);
    assert_eq!(
        report,
        json!({
            "intentional_shutdown": true,
            "forced_kill": false,
            "exit_code": null,
            "signal": libc::SIGTERM,
        })
    );
    assert_eq!(
        keys(&report),
        ["intentional_shutdown", "forced_kill", "exit_code", "signal"]
    );

    // The shell ignores SIGTERM, prints a line once it does, and hands the
    // ignored disposition on to `cat`, which waits for input.
    let mut ignoring = Command::new("sh")
        .args(["-c", "trap '' TERM; echo ignored; exec cat"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    let mut line = String::new();
    BufReader::new(ignoring.stdout.as_mut().unwrap())
        .read_line(&mut line)
        .unwrap();
    assert_eq!(line, "ignored\n");
    let short = Timing {
        stop_grace: Duration::from_millis(10),
        ..generous
    };
    assert_eq!(
        stop_process(&mut ignoring, &short),
        json!({
            "intentional_shutdown": true,
            "forced_kill": true,
            "exit_code": null,
            "signal": libc::SIGKILL,
        })
    );
}

/// A stream whose reads give its steps in turn, each a chunk or an error,
/// and then the end of the stream.
struct Steps(std::vec::IntoIter<io::Result<&'static [u8]>>);

impl Read for Steps {
    fn read(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
        match self.0.next() {
            None => Ok(0),
            Some(Ok(chunk)) => {
                buffer[..chunk.len()].copy_from_slice(chunk);
                Ok(chunk.len())
            }
            Some(Err(error)) => Err(error),
        }
    }
}

/// The reader of a child's output repeats a read that a caught signal
/// interrupted, as handlers without `SA_RESTART` make a blocked read fail
/// with `EINTR`, and ends the stream at any other failed read. The steps of
/// the stream stand for the reads, so that no signal has to reach the
/// reader's thread at the right moment.
#[test]
fn a_read_that_a_signal_interrupted_does_not_end_the_stream() {
    let drained = |steps: Vec<io::Result<&'static [u8]>>| {
        let (sender, receiver) = channel();
        spawn_reader(Steps(steps.into_iter()), sender);
        let mut bytes = Vec::new();
        loop {
            match receiver.recv_timeout(TEST_WAIT) {
                Ok(chunk) => bytes.extend(chunk),
                Err(RecvTimeoutError::Disconnected) => break bytes,
                Err(RecvTimeoutError::Timeout) => panic!("the stream did not end"),
            }
        }
    };
    let interrupted = || io::Error::from(io::ErrorKind::Interrupted);
    assert_eq!(
        drained(vec![
            Ok(&b"before"[..]),
            Err(interrupted()),
            Err(interrupted()),
            Ok(&b"after"[..]),
        ]),
        b"beforeafter"
    );
    assert_eq!(
        drained(vec![
            Ok(&b"before"[..]),
            Err(io::Error::from_raw_os_error(libc::EIO)),
            Ok(&b"after"[..]),
        ]),
        b"before"
    );
}

/// The whole command line for both clocks, with the executable as given and
/// the image by its canonical path; an image that does not exist, or is not
/// a regular file, is refused.
#[test]
fn the_command_follows_the_fixed_profile() {
    let scratch = Scratch::new("qemu-command");
    let elf = scratch.write("image.elf", b"ELF");
    let image = elf.canonicalize().unwrap().to_string_lossy().into_owned();
    let machine = [
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
        image.as_str(),
    ];
    let qemu = Path::new("/fixture/qemu");
    let accel = ["/fixture/qemu", "-accel", "tcg,thread=single"];
    let icount = ["-icount", "shift=3,align=off,sleep=off"];
    assert_eq!(
        build_command(&elf, Some(qemu), Clock::Host).unwrap(),
        [&accel[..], &machine].concat()
    );
    assert_eq!(
        build_command(&elf, Some(qemu), Clock::Icount).unwrap(),
        [&accel[..], &icount, &machine].concat()
    );
    let missing = scratch.path("missing.elf");
    assert_rejects(
        build_command(&missing, Some(qemu), Clock::Icount),
        &format!(
            "ELF image not found: {}. Build the image first.",
            missing.display()
        ),
    );
    let directory = scratch.root().canonicalize().unwrap();
    assert_rejects(
        build_command(scratch.root(), Some(qemu), Clock::Host),
        &format!(
            "ELF image not found: {}. Build the image first.",
            directory.display()
        ),
    );
}

/// The command on the machine with EL2 differs from the default command only
/// in the value of `-machine`, for both clocks, and the default command is
/// the one on the machine without EL2.
#[test]
fn the_el2_machine_differs_only_in_the_machine() {
    let scratch = Scratch::new("qemu-machine");
    let elf = scratch.write("image.elf", b"ELF");
    let qemu = Some(Path::new("/fixture/qemu"));
    for clock in [Clock::Host, Clock::Icount] {
        let default = build_command(&elf, qemu, clock).unwrap();
        assert_eq!(
            build_command_on(&elf, qemu, clock, Machine::Virt).unwrap(),
            default
        );
        let machine = default.iter().position(|arg| arg == "-machine").unwrap();
        let mut expected = default.clone();
        expected[machine + 1] = "virt-8.2,secure=off,virtualization=on,gic-version=2".to_string();
        assert_eq!(
            build_command_on(&elf, qemu, clock, Machine::VirtEl2).unwrap(),
            expected
        );
    }
}

/// A timeout is written in seconds as Rust writes an `f64`, which never uses
/// an exponent.
#[test]
fn a_timeout_is_written_in_seconds() {
    let cases = [
        (Duration::from_secs(8), "8"),
        (Duration::from_millis(2500), "2.5"),
        (Duration::from_millis(10), "0.01"),
        (Duration::from_micros(10), "0.00001"),
        (
            Duration::from_secs(10_000_000_000_000_000),
            "10000000000000000",
        ),
    ];
    for (duration, text) in cases {
        assert_eq!(seconds_text(duration), text, "{duration:?}");
    }
}

/// A QEMU process as the guest of a capture: running with its output open,
/// it is alive; with its output closed, it is reported as still running; and
/// once it has exited, with its exit status.
#[test]
fn a_child_guest_reports_how_it_ended() {
    let mut running = Command::new("cat")
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .spawn()
        .unwrap();
    assert_eq!(running.check_alive(false), Ok(()));
    assert_rejects(
        running.check_alive(true),
        "QEMU exited or closed serial output early (still running)",
    );
    stop_process(&mut running, &GUEST);

    let mut exited = Command::new("sh")
        .args(["-c", "exit 3"])
        .stdin(Stdio::null())
        .spawn()
        .unwrap();
    exited.wait().unwrap();
    assert_rejects(
        exited.check_alive(false),
        "QEMU exited or closed serial output early (exit status: 3)",
    );
}

/// The version is the first line that `--version` prints, without its line
/// terminator; a query that fails names its exit status.
#[test]
fn the_version_is_the_first_line_of_the_version_output() {
    let scratch = Scratch::new("qemu-version");
    let qemu = fake_qemu(&scratch, "qemu", "exit 0");
    assert_eq!(
        version(&qemu),
        Ok("QEMU emulator version 0.0.0".to_string())
    );
    let failing = scratch.script("failing", "#!/bin/sh\necho 'unknown option'\nexit 1\n");
    assert_rejects(
        version(&failing),
        "QEMU version query failed with exit status: 1",
    );
}

mod properties {
    use super::*;

    /// The clock decides only whether the instruction count is fixed; TCG
    /// stays single-threaded.
    #[test]
    fn clock_choice_does_not_change_tcg_threading() {
        let scratch = Scratch::new("qemu-clock");
        let elf = scratch.write("image.elf", b"ELF");
        for clock in [Clock::Icount, Clock::Host] {
            let command = build_command(&elf, Some(Path::new("/fixture/qemu")), clock).unwrap();
            let accel = command.iter().position(|arg| arg == "-accel").unwrap();
            assert_eq!(command[accel + 1], "tcg,thread=single");
            assert_eq!(
                command.contains(&"-icount".to_string()),
                clock == Clock::Icount
            );
        }
    }

    /// A guarded capture writes its log only after the guest stopped, keeps
    /// the complete output, writes each byte of it once, and reports fatal
    /// records.
    #[test]
    fn guarded_capture_defers_log_io_and_rejects_fatal_output() {
        let scratch = Scratch::new("guarded-capture");
        let mut child = shell_guest("echo READY; read x; echo DONE; read y");
        let log = File::create(scratch.path("guarded.log")).unwrap();
        let mut capture =
            SerialCapture::guarded(&mut child, log, MAX_SERIAL_BYTES, &FATAL, &GUEST).unwrap();
        capture
            .wait_for(&mut child, ready_line_named("READY"), 0, TEST_WAIT)
            .unwrap();
        assert_eq!(
            scratch.read("guarded.log"),
            b"",
            "log I/O before the guest stopped"
        );
        capture.send(&mut child, b"go\n").unwrap();
        capture
            .wait_for(&mut child, ready_line_named("DONE"), 0, TEST_WAIT)
            .unwrap();
        capture.send(&mut child, b"stop\n").unwrap();
        let cleanup = stop_process(&mut child, &GUEST);
        assert_eq!(cleanup["forced_kill"], false, "{cleanup}");
        assert!(
            cleanup["exit_code"] == 0 || cleanup["signal"] == libc::SIGTERM,
            "{cleanup}"
        );
        capture.finish_guarded().unwrap();
        assert_eq!(scratch.read("guarded.log"), capture.received);
        assert_eq!(capture.received, b"READY\nDONE\n");
        // The deferred log is written once.
        capture.write_deferred_log().unwrap();
        capture.finish_guarded().unwrap();
        assert_eq!(scratch.read("guarded.log"), b"READY\nDONE\n");

        let mut fatal_child = shell_guest("echo CASXI_PANIC; echo tail; read x");
        let log = File::create(scratch.path("fatal.log")).unwrap();
        let mut fatal =
            SerialCapture::guarded(&mut fatal_child, log, MAX_SERIAL_BYTES, &FATAL, &GUEST)
                .unwrap();
        assert_rejects(
            fatal.wait_for(&mut fatal_child, ready_line_named("NEVER"), 0, TEST_WAIT),
            "Kernel fault or halt during EL0 validation",
        );
        stop_process(&mut fatal_child, &GUEST);
        fatal.finish_guarded().unwrap();
        assert!(fatal.received.starts_with(b"CASXI_PANIC\n"));
        assert_eq!(scratch.read("fatal.log"), fatal.received);
    }

    /// Output past the limit of a guarded capture fails it with the limit,
    /// and the read that passed the limit is kept whole and logged; output
    /// that passes the limit during the cleanup fails the cleanup, which then
    /// writes no log.
    #[test]
    fn a_guarded_capture_stops_at_its_limit() {
        let scratch = Scratch::new("guarded-limit");
        let mut child = shell_guest("printf 0123456789; read x");
        let log = File::create(scratch.path("limit.log")).unwrap();
        let mut capture = SerialCapture::guarded(&mut child, log, LIMIT, &FATAL, &GUEST).unwrap();
        assert_rejects(
            capture.wait_for(&mut child, bytes(b"never"), 0, TEST_WAIT),
            EXCEEDED,
        );
        stop_process(&mut child, &GUEST);
        capture.finish_guarded().unwrap();
        assert_eq!(capture.received, b"0123456789");
        assert_eq!(scratch.read("limit.log"), b"0123456789");

        let mut child = shell_guest("printf 0123; read x; printf 456789; read y");
        let log = File::create(scratch.path("cleanup.log")).unwrap();
        let mut capture = SerialCapture::guarded(&mut child, log, LIMIT, &FATAL, &GUEST).unwrap();
        capture
            .wait_for(&mut child, bytes(b"0123"), 0, TEST_WAIT)
            .unwrap();
        capture.send(&mut child, b"go\n").unwrap();
        assert_rejects(
            capture.finish_guarded(),
            "serial output exceeded 8 bytes during cleanup",
        );
        assert_eq!(capture.received, b"0123456789");
        assert_eq!(scratch.read("cleanup.log"), b"");
        stop_process(&mut child, &GUEST);
    }
}

// --- Board serial capture -------------------------------------------------------
//
// The capture of a board session through a port, over a pseudo-terminal
// whose master end stands in for the board.

/// A board behind a port, as the guest of a board capture: there is no
/// process to look at. A session whose interrupt flag holds a signal ends
/// with [`INTERRUPTED`]; a stream that has ended ends it with the error that
/// the port's reader recorded, or `serial device closed`.
struct TestBoard<'a> {
    port: &'a TtyPort,
    interrupt: Option<&'a AtomicI32>,
}

impl<'a> TestBoard<'a> {
    /// A board whose session no interrupt ends.
    fn new(port: &'a TtyPort) -> Self {
        TestBoard {
            port,
            interrupt: None,
        }
    }

    /// A board whose session ends once `flag` holds a signal number.
    fn interruptible(port: &'a TtyPort, flag: &'a AtomicI32) -> Self {
        TestBoard {
            port,
            interrupt: Some(flag),
        }
    }
}

impl Guest for TestBoard<'_> {
    fn check_alive(&mut self, closed: bool) -> Result<(), Failure> {
        if self
            .interrupt
            .is_some_and(|flag| flag.load(Ordering::SeqCst) != 0)
        {
            return Err(Failure::new(INTERRUPTED));
        }
        if closed {
            return Err(Failure::new(
                self.port
                    .read_error()
                    .unwrap_or_else(|| "serial device closed".to_string()),
            ));
        }
        Ok(())
    }
}

/// A pseudo-terminal pair, the slave's attributes before the port opens, and
/// the slave opened as a board port with its capture, log and transmit
/// record. Fields drop in order, so the capture and then the port are
/// finished before the pair closes.
struct Serial {
    serial: SerialCapture,
    port: TtyPort,
    transmitted: Arc<Mutex<Vec<Value>>>,
    before: Attributes,
    pty: Pty,
    scratch: Scratch,
}

impl Serial {
    /// A port whose capture keeps 256 KiB and whose session a test never
    /// reaches the end of.
    #[track_caller]
    fn open() -> Self {
        Self::bounded(MAX_SERIAL_BYTES, SESSION)
    }

    /// A port whose capture keeps `limit` bytes and whose session ends after
    /// `session`.
    #[track_caller]
    fn bounded(limit: usize, session: Duration) -> Self {
        Self::logging(limit, session, |scratch| {
            File::create(scratch.path("raw.bin")).unwrap()
        })
    }

    /// A port whose log refuses every write: `raw.bin` opened read-only.
    #[track_caller]
    fn unwritable_log() -> Self {
        Self::logging(MAX_SERIAL_BYTES, SESSION, |scratch| {
            File::open(scratch.write("raw.bin", b"")).unwrap()
        })
    }

    /// A port whose capture logs to the file that `open` opens in the
    /// scratch directory.
    #[track_caller]
    fn logging(limit: usize, session: Duration, open: impl FnOnce(&Scratch) -> File) -> Self {
        let pty = Pty::open();
        let before = pty.attributes();
        let scratch = Scratch::new("board-serial");
        let log = open(&scratch);
        let port = TtyPort::open(pty.path()).unwrap();
        let transmitted = Arc::new(Mutex::new(Vec::new()));
        let serial = SerialCapture::from_tty(
            &port,
            log,
            limit,
            &FAILURE_MARKERS,
            Instant::now() + session,
            Arc::clone(&transmitted),
            &TIMING,
        )
        .unwrap();
        Serial {
            serial,
            port,
            transmitted,
            before,
            pty,
            scratch,
        }
    }

    /// The log as written so far.
    #[track_caller]
    fn log(&self) -> Vec<u8> {
        self.scratch.read("raw.bin")
    }

    /// Reads until `count` bytes were received in all. A test fails when
    /// they have not arrived within [`TEST_WAIT`] or the stream ends first.
    #[track_caller]
    fn take(&mut self, count: usize) {
        let deadline = Instant::now() + TEST_WAIT;
        while self.serial.received.len() < count {
            let now = Instant::now();
            assert!(
                now < deadline && !self.serial.eof,
                "{} of {count} bytes received",
                self.serial.received.len()
            );
            self.serial.read(deadline - now);
        }
    }

    /// `take` with checked reads, which stop at the first read that finds a
    /// failure.
    #[track_caller]
    fn checked_take(&mut self, count: usize) -> Result<(), Failure> {
        let deadline = Instant::now() + TEST_WAIT;
        while self.serial.received.len() < count {
            let now = Instant::now();
            assert!(
                now < deadline,
                "{} of {count} bytes received",
                self.serial.received.len()
            );
            self.serial
                .checked_read(&mut TestBoard::new(&self.port), deadline - now)?;
        }
        Ok(())
    }

    /// The checks after a read.
    fn check(&mut self) -> Result<(), Failure> {
        self.serial.ensure_running(&mut TestBoard::new(&self.port))
    }

    /// The failure tail of `tail`.
    fn collect_failure(&mut self, tail: Duration) -> Result<Value, Failure> {
        self.serial
            .collect_failure(&mut TestBoard::new(&self.port), tail)
    }

    /// The transmit record as `(hex, sent_bytes)` pairs.
    #[track_caller]
    fn transmitted(&self) -> Vec<(String, u64)> {
        self.transmitted
            .lock()
            .unwrap()
            .iter()
            .map(|entry| {
                (
                    entry["hex"].as_str().unwrap().to_string(),
                    entry["sent_bytes"].as_u64().unwrap(),
                )
            })
            .collect()
    }

    /// The slave has its attributes back. Darwin sets `PENDIN` when
    /// canonical mode is restored without flushing input, so that flag is
    /// left out.
    #[track_caller]
    fn assert_restored(&self) {
        assert!(self.port.restored);
        let (mut actual, mut expected) = (self.pty.attributes(), self.before.clone());
        actual.lflag &= !libc::PENDIN;
        expected.lflag &= !libc::PENDIN;
        assert_eq!(actual, expected);
    }
}

/// Requires `result` to fail as a board capture fails once the board end of
/// its port has closed. Darwin reads the slave empty, the end of the stream
/// without an error: `serial device closed`. Linux hangs the slave up: a
/// read that is under way when the master closes fails with `EIO`, which the
/// port's reader records and the capture reports, and a read that starts
/// once the hang-up has completed reads empty, as on Darwin. Which of the two
/// the reader makes depends on scheduling, so on Linux either is accepted,
/// with the error recorded exactly when the capture reports it.
#[track_caller]
fn assert_closed_device<T: Debug>(result: Result<T, Failure>, port: &TtyPort) {
    let message = match result {
        Err(Failure(message)) => message,
        Ok(value) => panic!("accepted: {value:?}"),
    };
    let failed_read = "Input/output error (os error 5)";
    if cfg!(target_os = "linux") && message == failed_read {
        assert_eq!(port.read_error(), Some(failed_read.to_string()));
    } else {
        assert_eq!(message, "serial device closed");
        assert_eq!(port.read_error(), None);
    }
}

mod boundaries {
    use super::*;

    /// A name with a `/` is taken as a path and must be an executable regular
    /// file; a name without one is looked for on the search path. A refusal
    /// names it in Rust's debug form.
    #[test]
    fn a_qemu_that_is_missing_or_not_executable_is_refused() {
        let refusal = |name: &Path| {
            format!(
                "QEMU executable not found or not executable: {name:?}. Install qemu-system-aarch64 or pass its path with --qemu."
            )
        };
        let scratch = Scratch::new("qemu-resolve");
        let missing = scratch.path("qemu-system-aarch64");
        assert_rejects(resolve_qemu(Some(&missing)), &refusal(&missing));
        let plain = scratch.write("plain", b"#!/bin/sh\n");
        assert_rejects(resolve_qemu(Some(&plain)), &refusal(&plain));
        assert_rejects(resolve_qemu(Some(scratch.root())), &refusal(scratch.root()));
        let unknown = Path::new("krepi-no-such-qemu");
        assert_rejects(resolve_qemu(Some(unknown)), &refusal(unknown));
        let quoted = scratch.path("it's \"qemu\"");
        assert_rejects(resolve_qemu(Some(&quoted)), &refusal(&quoted));

        let qemu = fake_qemu(&scratch, "qemu", "exit 0");
        assert_eq!(resolve_qemu(Some(&qemu)), Ok(qemu.canonicalize().unwrap()));
        // A name without a `/` is found on the search path, here the shell.
        let shell = resolve_qemu(Some(Path::new("sh"))).unwrap();
        assert!(shell.is_absolute(), "{shell:?}");
        let status = Command::new(&shell)
            .args(["-c", "exit 7"])
            .stdin(Stdio::null())
            .status()
            .unwrap();
        assert_eq!(status.code(), Some(7));
    }

    /// A wait whose end lies beyond the range of the clock has no end of its
    /// own: it lasts until the guest ends it, here by closing its output. The
    /// shell sends both output streams to `/dev/null` and becomes `cat`, which
    /// waits for input that the capture never sends.
    #[test]
    fn a_wait_beyond_the_range_of_the_clock_lasts_until_the_guest_ends() {
        let scratch = Scratch::new("endless-wait");
        let mut child = shell_guest("printf 'boot\\r\\n'; exec >/dev/null 2>&1; exec cat");
        let log = File::create(scratch.path("raw.bin")).unwrap();
        let mut capture = SerialCapture::new(&mut child, log, &GUEST).unwrap();
        assert_rejects(
            capture.wait_for(&mut child, bytes(b"never"), 0, Duration::MAX),
            "QEMU exited or closed serial output early (still running)",
        );
        assert_eq!(capture.received, b"boot\r\n");
        assert_eq!(scratch.read("raw.bin"), b"boot\r\n");
        stop_process(&mut child, &GUEST);
    }

    /// A capture of a process writes its log as the bytes arrive and ignores
    /// a failed write, where a board capture ends its session.
    #[test]
    fn a_capture_of_a_process_ignores_a_failed_log_write() {
        let scratch = Scratch::new("unwritable-log");
        let mut child = shell_guest("printf 'boot\\r\\n'; read x");
        let log = File::open(scratch.write("raw.bin", b"")).unwrap();
        let mut capture = SerialCapture::new(&mut child, log, &GUEST).unwrap();
        capture
            .wait_for(&mut child, bytes(b"boot\r\n"), 0, TEST_WAIT)
            .unwrap();
        assert_eq!(capture.ensure_running(&mut child), Ok(()));
        assert_eq!(capture.boundary(&mut child), Ok(6));
        assert_eq!(scratch.read("raw.bin"), b"");
        stop_process(&mut child, &GUEST);
    }

    /// At a boundary, a capture of a process reads past a guard error until
    /// no output is waiting and reports the error then, where a board capture
    /// stops at the first read after it; and output that keeps arriving for
    /// longer than its idle time fails the boundary. The output is handed to
    /// the capture through a channel of the test, so that the chunks wait for
    /// it before the boundary.
    #[test]
    fn a_capture_of_a_process_drains_past_a_guard_error_until_idle() {
        let scratch = Scratch::new("process-boundary");
        let mut child = Command::new("cat")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        let log = File::create(scratch.path("raw.bin")).unwrap();
        let patient = Timing {
            guest_idle: TEST_WAIT,
            ..GUEST
        };
        let mut capture =
            SerialCapture::guarded(&mut child, log, MAX_SERIAL_BYTES, &FATAL, &patient).unwrap();
        let (sender, receiver) = channel();
        capture.receiver = receiver;
        sender.send(b"CASXI_HALTED".to_vec()).unwrap();
        assert!(capture.read(Duration::ZERO));
        for chunk in [b"a", b"b", b"c"] {
            sender.send(chunk.to_vec()).unwrap();
        }
        assert_rejects(
            capture.boundary(&mut child),
            "Kernel fault or halt during EL0 validation",
        );
        assert_eq!(capture.received, b"CASXI_HALTEDabc");
        stop_process(&mut child, &GUEST);

        let mut child = Command::new("cat")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        let log = File::create(scratch.path("idle.bin")).unwrap();
        let hasty = Timing {
            guest_idle: Duration::ZERO,
            ..GUEST
        };
        let mut capture = SerialCapture::new(&mut child, log, &hasty).unwrap();
        let (sender, receiver) = channel();
        capture.receiver = receiver;
        sender.send(b"x".to_vec()).unwrap();
        assert_rejects(
            capture.boundary(&mut child),
            "UART output did not become idle before the next input",
        );
        stop_process(&mut child, &GUEST);
    }

    #[test]
    fn fatal_split_across_reads_is_retained_and_rejected() {
        let mut s = Serial::open();
        s.pty.write(b"CASXI_PA");
        s.take(8);
        s.check().unwrap();
        s.pty.write(b"NIC failure\r\n");
        s.take(21);
        assert_rejects(s.check(), FATAL_TEXT);
        assert_eq!(s.log(), b"CASXI_PANIC failure\r\n");
    }

    /// A board read keeps at most one byte past the limit, and that byte ends
    /// the stream: the tenth byte stays unread, and the failure tail finds
    /// the stream ended on every host, as the device is still open.
    #[test]
    fn output_is_bounded_at_limit_plus_one() {
        let mut s = Serial::bounded(LIMIT, SESSION);
        s.pty.write(b"0123456789");
        s.take(LIMIT + 1);
        assert_rejects(s.check(), EXCEEDED);
        assert_eq!(s.serial.received, b"012345678");
        assert_eq!(s.log(), b"012345678");
        assert_rejects(s.collect_failure(TAIL), "serial device closed");
        assert_eq!(s.serial.received, b"012345678");
    }

    /// A board capture fails `boundary` in the first read after a guard
    /// error and leaves the later output unread, where a capture of a QEMU
    /// process drains it until the guest goes idle. The fatal line comes
    /// through the port; the later output is handed to the capture through a
    /// channel of the test, so that three reads wait for the boundary
    /// whatever the pseudo-terminal buffers.
    #[test]
    fn boundary_stops_at_a_guard_error() {
        let mut s = Serial::open();
        let failure = b"CASXI_PANIC failure\r\n";
        s.pty.write(failure);
        s.take(failure.len());
        let (sender, receiver) = channel();
        s.serial.receiver = receiver;
        for _ in 0..3 {
            sender.send(b"late\r\n".to_vec()).unwrap();
        }
        assert_rejects(s.serial.boundary(&mut TestBoard::new(&s.port)), FATAL_TEXT);
        assert_eq!(s.serial.received, b"CASXI_PANIC failure\r\nlate\r\n");
        assert_eq!(s.log(), s.serial.received);
    }

    /// A checked read fails in the read that finds a fatal record, the output
    /// bound or the end of the stream, where `read` only records the failure.
    #[test]
    fn a_checked_read_fails_in_the_read_that_finds_a_failure() {
        let mut s = Serial::open();
        s.pty.write(b"boot\r\n");
        s.checked_take(6).unwrap();
        s.pty.write(b"CASXI_PANIC failure\r\n");
        assert_rejects(s.checked_take(27), FATAL_TEXT);
        let mut s = Serial::bounded(LIMIT, SESSION);
        s.pty.write(b"0123456789");
        assert_rejects(s.checked_take(10), EXCEEDED);
        assert_eq!(s.serial.received, b"012345678");
        let mut s = Serial::open();
        s.pty.close_master();
        let ended = s.checked_take(1);
        assert_closed_device(ended, &s.port);
    }

    /// A board capture writes each chunk to its log as it arrives, and a
    /// failed write ends the session in that read, before the fatal records
    /// are checked. A write that fails in the failure tail ends the tail the
    /// same way.
    #[test]
    fn a_failed_log_write_ends_the_session() {
        let refused = "Bad file descriptor (os error 9)";
        let mut s = Serial::unwritable_log();
        let failure = b"CASXI_PANIC failure\r\n";
        s.pty.write(failure);
        s.take(failure.len());
        assert_rejects(s.check(), refused);
        assert_rejects(s.serial.boundary(&mut TestBoard::new(&s.port)), refused);
        let halted = b"CASXI_HALTED\r\n";
        s.pty.write(halted);
        assert_rejects(s.collect_failure(TAIL), refused);
        assert_eq!(s.serial.received, [&failure[..], halted].concat());
        assert_eq!(s.log(), b"");
    }

    #[test]
    fn deadline_and_request_bound() {
        let mut s = Serial::open();
        assert_rejects(
            s.serial.send(&mut TestBoard::new(&s.port), &[b'x'; 129]),
            "invalid serial request size",
        );
        assert_rejects(
            s.serial.send(&mut TestBoard::new(&s.port), b""),
            "invalid serial request size",
        );
        assert!(s.transmitted().is_empty());
        assert_rejects(
            s.serial.wait_for(
                &mut TestBoard::new(&s.port),
                bytes(b"never"),
                0,
                Duration::from_millis(10),
            ),
            "Expected serial response not received within 0.01s",
        );
        let mut ended = Serial::bounded(MAX_SERIAL_BYTES, Duration::ZERO);
        ended.serial.read(Duration::ZERO);
        assert_rejects(
            ended.check(),
            "serial session closed or exceeded total deadline",
        );
    }

    /// A port that cannot be opened is named in Rust's debug form before the
    /// error. A request once the board end has closed and the device hung up
    /// fails with `EIO` on every host, after it was recorded with nothing
    /// sent. The stream then ends as the host ends it.
    #[test]
    fn open_and_write_errors_and_a_closed_device_are_reported() {
        assert_rejects(
            TtyPort::open("/nonexistent/krepi-board").map(drop),
            "\"/nonexistent/krepi-board\": No such file or directory (os error 2)",
        );
        assert_rejects(
            TtyPort::open("/nonexistent/krepi-board's").map(drop),
            "\"/nonexistent/krepi-board's\": No such file or directory (os error 2)",
        );
        let scratch = Scratch::new("board-not-a-tty");
        let file = scratch.write("not-a-tty", b"");
        assert_rejects(
            TtyPort::open(file.to_str().unwrap()).map(drop),
            "selected port is not a tty",
        );

        let mut s = Serial::open();
        s.pty.write(b"boot\r\n");
        s.serial
            .wait_for(
                &mut TestBoard::new(&s.port),
                bytes(b"boot\r\n"),
                0,
                TEST_WAIT,
            )
            .unwrap();
        s.pty.close_master();
        s.pty.await_hang_up();
        assert_rejects(
            s.serial.send(&mut TestBoard::new(&s.port), b":"),
            "Input/output error (os error 5)",
        );
        assert_eq!(s.transmitted(), [("3a".to_string(), 0)]);
        let ended = s
            .serial
            .wait_for(&mut TestBoard::new(&s.port), bytes(b"never"), 0, TEST_WAIT);
        assert_closed_device(ended, &s.port);
        assert_eq!(s.log(), b"boot\r\n");
    }

    /// A second port on a held terminal is refused, by the kernel where it
    /// refuses a new open of a terminal held with `TIOCEXCL`, elsewhere by
    /// the advisory lock; the held port keeps working, and once it is
    /// finished the terminal opens again while the capture still holds its
    /// descriptors.
    #[test]
    fn a_second_open_of_a_held_port_is_refused() {
        let mut s = Serial::open();
        let expected = if exclusive_open_refused() {
            Failure::new(format!(
                "{:?}: Device or resource busy (os error 16)",
                s.pty.path()
            ))
        } else {
            lock_refused()
        };
        assert_eq!(TtyPort::open(s.pty.path()).map(drop), Err(expected));
        s.pty.write(b"boot\r\n");
        s.serial
            .wait_for(
                &mut TestBoard::new(&s.port),
                bytes(b"boot\r\n"),
                0,
                TEST_WAIT,
            )
            .unwrap();
        s.serial.send(&mut TestBoard::new(&s.port), b":").unwrap();
        assert_eq!(s.pty.read(1), b":");
        s.port.finish().unwrap();
        assert!(s.port.restored);
        let mut again = TtyPort::open(s.pty.path()).unwrap();
        again.finish().unwrap();
        assert!(again.restored);
    }
}

mod resources {
    use super::*;

    #[test]
    fn bidirectional_bytes_and_restoration() {
        let mut s = Serial::open();
        s.pty.write(b"boot\r\n");
        s.serial
            .wait_for(
                &mut TestBoard::new(&s.port),
                bytes(b"boot\r\n"),
                0,
                TEST_WAIT,
            )
            .unwrap();
        assert_eq!(s.log(), b"boot\r\n");
        s.serial.send(&mut TestBoard::new(&s.port), b":").unwrap();
        assert_eq!(s.pty.read(1), b":");
        assert_eq!(s.transmitted()[0].1, 1);
        s.port.finish().unwrap();
        s.assert_restored();
    }

    /// A fatal record written in two parts, the diagnostics after it and
    /// `CASXI_HALTED`: the record is rejected once complete, and the failure
    /// tail keeps the rest without transmitting.
    #[track_caller]
    fn split_failure_keeps_its_diagnostics(head: &[u8], rest: &[u8]) {
        let mut s = Serial::open();
        s.pty.write(head);
        s.take(head.len());
        s.check().unwrap();
        s.pty.write(rest);
        s.take(head.len() + rest.len());
        assert_rejects(s.check(), FATAL_TEXT);
        let tail = b" error=Readback recovery=Failed\r\nCASXI_HALTED\r\n";
        s.pty.write(tail);
        let result = s.collect_failure(TAIL).unwrap();
        assert_eq!(result["terminal_halt"], true);
        assert!(s.log().ends_with(tail));
        assert!(s.transmitted().is_empty());
    }

    #[test]
    fn pcie_initialization_failure_keeps_split_diagnostics() {
        split_failure_keeps_its_diagnostics(b"CASXI_PCIE_INIT_", b"FAIL v=1 phase=Host");
    }

    #[test]
    fn rp1_mmio_failure_keeps_split_diagnostics() {
        split_failure_keeps_its_diagnostics(b"CASXI_RP1_MMIO_", b"FAIL v=1 phase=Restore");
    }

    #[test]
    fn failure_tail_keeps_the_fatal_tail_without_transmitting() {
        let mut s = Serial::open();
        let failure = b"CASXI_PANIC failure\r\n";
        s.pty.write(failure);
        s.take(failure.len());
        assert_rejects(s.check(), FATAL_TEXT);
        let tail = b"CASXI_PANIC_LOCATION file=fixture line=1\r\nCASXI_HALTED\r\n";
        s.pty.write(tail);
        let result = s.collect_failure(TAIL).unwrap();
        assert_eq!(
            keys(&result),
            ["additional_bytes", "elapsed_seconds", "terminal_halt"]
        );
        assert_eq!(result["terminal_halt"], true);
        assert_eq!(result["additional_bytes"], tail.len());
        assert!(s.transmitted().is_empty());
        assert!(s.log().ends_with(tail));
    }

    /// A tail of no time or of more than 120 s is refused, and output past
    /// the limit ends a tail.
    #[test]
    fn failure_tail_respects_its_limits() {
        let mut s = Serial::bounded(LIMIT, SESSION);
        for refused in [Duration::ZERO, Duration::from_secs(121)] {
            assert_rejects(
                s.collect_failure(refused),
                "invalid diagnostic capture duration",
            );
        }
        s.pty.write(b"0123456789");
        assert_rejects(s.collect_failure(TAIL), EXCEEDED);
        s.port.finish().unwrap();
        s.assert_restored();
    }

    /// A checked read checks the session deadline before it reads and waits
    /// for output no longer than the deadline: given far longer, the read
    /// ends with the session and not before its end. The session lasts 5 s,
    /// so the first read normally starts within it; on a host that stalls
    /// past the end before the read starts, the read fails as the second one
    /// does, which the test accepts as the end has passed then.
    #[test]
    fn a_checked_read_ends_at_the_session_deadline() {
        let mut s = Serial::bounded(MAX_SERIAL_BYTES, Duration::from_secs(5));
        let end = s.serial.deadline.expect("a board session has a deadline");
        let started = Instant::now();
        match s
            .serial
            .checked_read(&mut TestBoard::new(&s.port), TEST_WAIT * 2)
        {
            Ok(received) => assert!(!received),
            Err(Failure(message)) => {
                assert_eq!(message, "serial session closed or exceeded total deadline")
            }
        }
        assert!(Instant::now() >= end);
        assert!(started.elapsed() < TEST_WAIT);
        s.pty.write(b"late\r\n");
        assert_rejects(
            s.serial
                .checked_read(&mut TestBoard::new(&s.port), TEST_WAIT),
            "serial session closed or exceeded total deadline",
        );
        assert_eq!(s.serial.received, b"");
    }

    #[test]
    fn quiet_failure_tail_expires() {
        let mut s = Serial::open();
        let result = s.collect_failure(Duration::from_millis(10)).unwrap();
        assert_eq!(result["terminal_halt"], false);
        assert_eq!(result["additional_bytes"], 0);
        assert!(s.transmitted().is_empty());
    }

    /// The board takes the request and stays quiet; meanwhile the interrupt
    /// arrives, stored as the SIGINT handler stores it. The wait ends with
    /// it, and nothing more reaches the board.
    #[test]
    fn an_interrupt_flag_ends_the_board_session() {
        let mut s = Serial::open();
        let flag = Arc::new(AtomicI32::new(0));
        let caught = Arc::clone(&flag);
        let board = s.pty.board(move |master| {
            let request = master.read(1);
            caught.store(libc::SIGINT, Ordering::SeqCst);
            request
        });
        s.serial
            .send(&mut TestBoard::interruptible(&s.port, &flag), b"@")
            .unwrap();
        assert_rejects(
            s.serial.wait_for(
                &mut TestBoard::interruptible(&s.port, &flag),
                bytes(b"CASXI_SNAPSHOT"),
                0,
                TEST_WAIT,
            ),
            INTERRUPTED,
        );
        assert_eq!(board.join(), b"@");
        assert_rejects(
            s.serial
                .send(&mut TestBoard::interruptible(&s.port, &flag), b"+"),
            INTERRUPTED,
        );
        assert_eq!(s.transmitted(), [("40".to_string(), 1)]);
        assert_eq!(s.pty.received(Duration::from_millis(200)), b"");
        s.port.finish().unwrap();
        s.assert_restored();
    }

    /// Each read of the failure tail checks the guest, so an interrupt that
    /// was caught ends a tail of 120 s at once, with nothing transmitted.
    #[test]
    fn an_interrupt_ends_the_failure_tail() {
        let mut s = Serial::open();
        let failure = b"CASXI_PANIC failure\r\n";
        s.pty.write(failure);
        s.take(failure.len());
        assert_rejects(s.check(), FATAL_TEXT);
        let flag = AtomicI32::new(libc::SIGINT);
        assert_rejects(
            s.serial
                .collect_failure(&mut TestBoard::interruptible(&s.port, &flag), TAIL),
            INTERRUPTED,
        );
        assert!(s.transmitted().is_empty());
        s.port.finish().unwrap();
        s.assert_restored();
    }
}
