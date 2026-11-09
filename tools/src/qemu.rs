//! The QEMU virt command and the serial capture of a guest.
//!
//! [`build_command`] gives the command line of a guest on QEMU virt: one
//! Cortex-A76 under single-threaded TCG, GICv2, 128 MiB, no network, and the
//! PL011 on the standard streams of the QEMU process, with the host clock or
//! a fixed instruction count as the guest's time source. The machine has no
//! EL2; [`build_command_on`] gives the same command line on a [`Machine`],
//! which may instead be the variant with EL2 that test images entering at
//! EL2 use. [`Guest`] is the far end of a serial capture, which tells whether
//! the guest is still there.
//!
//! A [`SerialCapture`] keeps every byte that a guest wrote, lets each phase of
//! a check match from an offset of its own and sends input. It reads the
//! standard streams of a QEMU process, as a plain capture that logs what
//! arrives or a guarded one that bounds the output, rejects fatal records and
//! writes its log only after the guest has stopped; or it reads a board's
//! serial port through the transport of [`crate::tty`], as a session with a
//! deadline that bounds its output, rejects fatal records and stops at the
//! first failure. The process helpers stop a child and report how it ended.

use crate::Failure;
use crate::receipt::Match;
use crate::report::Value;
use crate::timing::Timing;
use crate::tty::TtyPort;
use serde_json::json;
use std::fs::File;
use std::io::{ErrorKind, Read, Write};
use std::os::unix::ffi::OsStrExt;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, ExitStatus, Stdio};
use std::sync::mpsc::{Receiver, RecvTimeoutError, Sender, channel};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

/// The bytes one read of [`spawn_reader`] takes at most.
const READ_BUFFER: usize = 65536;

/// The executable that [`resolve_qemu`] looks for on the search path.
const QEMU: &str = "qemu-system-aarch64";

/// The longest tail of diagnostics that [`SerialCapture::collect_failure`]
/// collects.
const LONGEST_TAIL: Duration = Duration::from_secs(120);

/// Guest time source: the host clock, or a fixed instruction count for a
/// functional reproduction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Clock {
    Icount,
    Host,
}

impl Clock {
    /// The clock named `icount` or `host`.
    pub fn parse(name: &str) -> Option<Self> {
        match name {
            "icount" => Some(Clock::Icount),
            "host" => Some(Clock::Host),
            _ => None,
        }
    }

    /// The name that [`Clock::parse`] reads: `icount` or `host`.
    pub fn name(self) -> &'static str {
        match self {
            Clock::Icount => "icount",
            Clock::Host => "host",
        }
    }
}

/// The machine of a guest on QEMU virt: the versioned `virt-8.2`, which
/// QEMU 8.2 and its later versions provide alike, without EL3, with GICv2.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Machine {
    /// Without EL2: the machine of `cargo xtask qemu`, on which the guest
    /// enters at EL1.
    Virt,
    /// With EL2, on which the guest enters at EL2: only for test images
    /// that drop to EL1 themselves, such as one that injects a virtual
    /// SError from EL2.
    VirtEl2,
}

impl Machine {
    /// The value of the `-machine` option.
    pub fn option(self) -> &'static str {
        match self {
            Machine::Virt => "virt-8.2,secure=off,virtualization=off,gic-version=2",
            Machine::VirtEl2 => "virt-8.2,secure=off,virtualization=on,gic-version=2",
        }
    }
}

/// The canonical path of the QEMU executable: `qemu`, the value of the
/// `--qemu` option, or `qemu-system-aarch64` without one. A name without a
/// `/` is looked for in the directories of `PATH`, in order, and a name with
/// one is taken as a path; either must be a regular file with an execute
/// bit. Otherwise the refusal names it in Rust's debug form:
/// `QEMU executable not found or not executable: "<name>". Install
/// qemu-system-aarch64 or pass its path with --qemu.`
pub fn resolve_qemu(qemu: Option<&Path>) -> Result<PathBuf, Failure> {
    let candidate = qemu.unwrap_or(Path::new(QEMU));
    let found = if candidate.as_os_str().as_bytes().contains(&b'/') {
        executable(candidate).then(|| candidate.to_path_buf())
    } else {
        std::env::var_os("PATH").and_then(|paths| {
            std::env::split_paths(&paths)
                .map(|dir| dir.join(candidate))
                .find(|path| executable(path))
        })
    };
    let Some(found) = found else {
        return Err(Failure::new(format!(
            "QEMU executable not found or not executable: {candidate:?}. Install {QEMU} or pass its path with --qemu."
        )));
    };
    Ok(found.canonicalize()?)
}

/// Whether `path` is a regular file, after symbolic links, with an execute
/// bit for anyone.
fn executable(path: &Path) -> bool {
    use std::os::unix::fs::PermissionsExt;
    std::fs::metadata(path).is_ok_and(|m| m.is_file() && m.permissions().mode() & 0o111 != 0)
}

/// The command line of a guest on QEMU virt with the image `elf`, which must
/// be a regular file and is given by its canonical path. `qemu` is the
/// executable, taken as it is; without one, [`resolve_qemu`] finds it. The
/// machine is [`Machine::Virt`], the versioned `virt-8.2` without EL2 and
/// EL3, with GICv2 and without a network card; one Cortex-A76 runs under
/// single-threaded TCG with 128 MiB, and the PL011 is on the standard
/// streams. [`Clock::Icount`] adds a fixed instruction count of 2^3 ns per
/// instruction.
pub fn build_command(
    elf: &Path,
    qemu: Option<&Path>,
    clock: Clock,
) -> Result<Vec<String>, Failure> {
    build_command_on(elf, qemu, clock, Machine::Virt)
}

/// The command line of [`build_command`] on `machine`: only the value of
/// `-machine` differs.
pub fn build_command_on(
    elf: &Path,
    qemu: Option<&Path>,
    clock: Clock,
    machine: Machine,
) -> Result<Vec<String>, Failure> {
    let image = elf.canonicalize().map_err(|_| {
        Failure::new(format!(
            "ELF image not found: {}. Build the image first.",
            elf.display()
        ))
    })?;
    if !image.is_file() {
        return Err(Failure::new(format!(
            "ELF image not found: {}. Build the image first.",
            image.display()
        )));
    }
    let qemu = match qemu {
        Some(path) => path.to_string_lossy().into_owned(),
        None => resolve_qemu(None)?.to_string_lossy().into_owned(),
    };
    let mut command = vec![qemu, "-accel".into(), "tcg,thread=single".into()];
    if clock == Clock::Icount {
        command.extend([
            "-icount".to_string(),
            "shift=3,align=off,sleep=off".to_string(),
        ]);
    }
    command.extend(
        [
            "-machine",
            machine.option(),
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
    command.push(image.to_string_lossy().into_owned());
    Ok(command)
}

/// The first line of the output of `qemu --version`, without the white space
/// around it, such as `QEMU emulator version 8.2.2`. A query that fails names
/// the standard library's text of its exit status.
pub fn version(qemu: &Path) -> Result<String, Failure> {
    let output = Command::new(qemu).arg("--version").output()?;
    if !output.status.success() {
        return Err(Failure::new(format!(
            "QEMU version query failed with {}",
            output.status
        )));
    }
    let text = String::from_utf8_lossy(&output.stdout);
    Ok(text.trim().lines().next().unwrap_or("").trim().to_string())
}

/// Starts `command`, the executable and its arguments, with piped standard
/// input and output and its standard error written to `stderr`, so that only
/// the guest's serial output reaches a capture.
pub fn spawn_with_stderr(command: &[String], stderr: File) -> std::io::Result<Child> {
    Command::new(&command[0])
        .args(&command[1..])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::from(stderr))
        .spawn()
}

/// Starts `command`, the executable and its arguments, with all three
/// standard streams piped, so that a capture reads its standard error with
/// its output.
pub fn spawn(command: &[String]) -> std::io::Result<Child> {
    Command::new(&command[0])
        .args(&command[1..])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
}

/// The far end of a serial capture: whether the guest behind the byte stream
/// is still there. `closed` reports whether the stream reached its end.
pub trait Guest {
    fn check_alive(&mut self, closed: bool) -> Result<(), Failure>;
}

/// A QEMU process: it fails once the process has exited or its output has
/// ended, with the standard library's text of its exit status, such as
/// `exit status: 1` or `signal: 15 (SIGTERM)`, or `still running` for a
/// process whose output ended first.
impl Guest for Child {
    fn check_alive(&mut self, closed: bool) -> Result<(), Failure> {
        let status = self.try_wait()?;
        if status.is_some() || closed {
            let end =
                status.map_or_else(|| "still running".to_string(), |status| status.to_string());
            return Err(Failure::new(format!(
                "QEMU exited or closed serial output early ({end})"
            )));
        }
        Ok(())
    }
}

/// Everything the guest wrote so far, with phase-relative matching.
///
/// A capture of a board's port follows rules of its own. Its reads keep at
/// most `limit + 1` bytes in all, and once a byte arrives past that bound
/// the stream counts as ended, the further bytes left unread. A failed write
/// of its log, which it writes as the bytes arrive, ends the session in the
/// read that failed, with the standard library's text of the error. And
/// [`SerialCapture::boundary`] and [`SerialCapture::checked_read`] stop at
/// the first read that finds a failure. A capture of a QEMU process instead
/// drains its output at a boundary until the guest is idle, and ignores a
/// failed write of its log.
pub struct SerialCapture {
    writer: Box<dyn Write + Send>,
    receiver: Receiver<Vec<u8>>,
    log: File,
    pub received: Vec<u8>,
    eof: bool,
    /// A guarded capture writes its log only once the guest has stopped, so
    /// that a slow file system cannot delay the guest's response to input.
    deferred_log: bool,
    /// The first received byte that a deferred log has not written yet.
    deferred_start: usize,
    limit: Option<usize>,
    fatal_markers: &'static [&'static [u8]],
    fatal_message: &'static str,
    guard_error: Option<Failure>,
    /// The failed log write of the latest read of a board capture, which the
    /// read keeps as its guard error and the failure tail reports at once.
    log_error: Option<Failure>,
    /// The deadline of a board session, which `ensure_running` reports.
    deadline: Option<Instant>,
    /// Whether the capture reads a board's port, with the rules of a board.
    board: bool,
    timing: Timing,
}

/// The failure of a guarded capture whose output holds a fatal record.
const FATAL_MESSAGE: &str = "Kernel fault or halt during EL0 validation";
/// The failure of a board capture whose output holds a fatal record.
const BOARD_FATAL_MESSAGE: &str = "kernel fault or halt during serial validation";
/// The failure of a board session past its deadline.
const SESSION_ENDED: &str = "serial session closed or exceeded total deadline";
/// The line that ends the failure tail.
const HALTED: &[u8] = b"CASXI_HALTED\r\n";

impl SerialCapture {
    /// Takes the child's standard streams; standard output and, when it is
    /// piped, standard error are drained by reader threads into one byte
    /// stream. The capture waits as `timing` gives.
    pub fn new(child: &mut Child, log: File, timing: &Timing) -> Result<Self, Failure> {
        let stdin = child
            .stdin
            .take()
            .ok_or_else(|| Failure::new("QEMU standard input is not piped"))?;
        let stdout = child
            .stdout
            .take()
            .ok_or_else(|| Failure::new("QEMU standard output is not piped"))?;
        let stderr = child.stderr.take();
        let (sender, receiver) = channel();
        spawn_reader(stdout, sender.clone());
        if let Some(stderr) = stderr {
            spawn_reader(stderr, sender);
        }
        Ok(SerialCapture {
            writer: Box::new(stdin),
            receiver,
            log,
            received: Vec::new(),
            eof: false,
            deferred_log: false,
            deferred_start: 0,
            limit: None,
            fatal_markers: &[],
            fatal_message: FATAL_MESSAGE,
            guard_error: None,
            log_error: None,
            deadline: None,
            board: false,
            timing: *timing,
        })
    }

    /// A capture of a board's port, which `port` holds exclusively: the
    /// port's reader thread feeds the byte stream, requests go through the
    /// port's bounded writer, which records them in `transmitted`, the log is
    /// written as the bytes arrive, the output is bounded by `limit` and
    /// guarded against `fatal_markers`, and the session ends at `deadline`.
    /// The capture follows the rules of a board; the port reads and writes
    /// as `timing` gives.
    pub fn from_tty(
        port: &TtyPort,
        log: File,
        limit: usize,
        fatal_markers: &'static [&'static [u8]],
        deadline: Instant,
        transmitted: Arc<Mutex<Vec<Value>>>,
        timing: &Timing,
    ) -> Result<Self, Failure> {
        let (sender, receiver) = channel();
        port.start_reader(sender, timing)?;
        let writer = port.writer(deadline, transmitted, timing)?;
        Ok(SerialCapture {
            writer: Box::new(writer),
            receiver,
            log,
            received: Vec::new(),
            eof: false,
            deferred_log: false,
            deferred_start: 0,
            limit: Some(limit),
            fatal_markers,
            fatal_message: BOARD_FATAL_MESSAGE,
            guard_error: None,
            log_error: None,
            deadline: Some(deadline),
            board: true,
            timing: *timing,
        })
    }

    /// A capture of the child's streams that rejects output holding one of
    /// `fatal_markers`, bounds the output by `limit` and writes the log only
    /// at [`SerialCapture::finish_guarded`], once the guest has stopped.
    pub fn guarded(
        child: &mut Child,
        log: File,
        limit: usize,
        fatal_markers: &'static [&'static [u8]],
        timing: &Timing,
    ) -> Result<Self, Failure> {
        let mut capture = Self::new(child, log, timing)?;
        capture.deferred_log = true;
        capture.limit = Some(limit);
        capture.fatal_markers = fatal_markers;
        Ok(capture)
    }

    /// Reads one chunk if it arrives within `timeout`; false at a timeout or
    /// at the end of the stream. A capture with a limit or fatal markers
    /// records output past the limit or holding a marker, and a board capture
    /// a failed log write before either, which the next `ensure_running`
    /// reports.
    pub fn read(&mut self, timeout: Duration) -> bool {
        let before = self.received.len();
        let received = self.read_raw(timeout);
        if let Some(error) = self.log_error.take() {
            self.guard_error.get_or_insert(error);
        }
        if received && self.guard_error.is_none() {
            if self.limit.is_some_and(|limit| self.received.len() > limit) {
                self.guard_error = Some(Failure::new(self.limit_message()));
            } else {
                let longest = self
                    .fatal_markers
                    .iter()
                    .map(|m| m.len())
                    .max()
                    .unwrap_or(0);
                let start = before.saturating_sub(longest.saturating_sub(1));
                let tail = &self.received[start..];
                if self
                    .fatal_markers
                    .iter()
                    .any(|marker| tail.windows(marker.len()).any(|w| w == *marker))
                {
                    self.guard_error = Some(Failure::new(self.fatal_message));
                }
            }
        }
        received
    }

    fn read_raw(&mut self, timeout: Duration) -> bool {
        if self.eof {
            return false;
        }
        match self.receiver.recv_timeout(timeout) {
            Ok(mut chunk) => {
                if let Some(room) = self.room() {
                    if chunk.len() > room {
                        // The bytes past the room stay unread, and with no
                        // room left the stream ends.
                        chunk.truncate(room);
                        self.eof = true;
                    }
                    if chunk.is_empty() {
                        return false;
                    }
                }
                self.received.extend_from_slice(&chunk);
                if !self.deferred_log {
                    let written = self.log.write_all(&chunk).and_then(|_| self.log.flush());
                    if self.board
                        && let Err(error) = written
                    {
                        self.log_error = Some(Failure::from(error));
                    }
                }
                true
            }
            Err(RecvTimeoutError::Timeout) => false,
            Err(RecvTimeoutError::Disconnected) => {
                self.eof = true;
                false
            }
        }
    }

    /// Whether the stream has ended: the guest closed it, or a board read
    /// reached the bound past the limit. A read then returns false at once.
    pub fn ended(&self) -> bool {
        self.eof
    }

    /// The bytes a board read may still keep, `limit + 1` in all; none for
    /// other captures.
    fn room(&self) -> Option<usize> {
        let limit = self.limit.filter(|_| self.board)?;
        Some(limit.saturating_add(1).saturating_sub(self.received.len()))
    }

    /// The failure of output past the limit, which names the limit.
    fn limit_message(&self) -> String {
        format!(
            "serial output exceeded {} bytes",
            self.limit.unwrap_or(usize::MAX)
        )
    }

    /// Cleanup of a guarded capture: collects the output that follows for up
    /// to `timing.guest_finish`, until the stream ends or the output reaches
    /// the limit, then writes the complete log. Output that passes the limit
    /// meanwhile fails with `serial output exceeded <limit> bytes during
    /// cleanup`.
    pub fn finish_guarded(&mut self) -> Result<(), Failure> {
        let limit = self.limit.unwrap_or(usize::MAX);
        let deadline = Instant::now().checked_add(self.timing.guest_finish);
        while !self.eof && self.received.len() < limit {
            let wait = match deadline {
                Some(deadline) => {
                    let now = Instant::now();
                    if now >= deadline {
                        break;
                    }
                    (deadline - now).min(self.timing.guest_finish_slice)
                }
                None => self.timing.guest_finish_slice,
            };
            self.read_raw(wait);
            if self.received.len() > limit {
                return Err(Failure::new(format!(
                    "{} during cleanup",
                    self.limit_message()
                )));
            }
        }
        self.write_deferred_log()
    }

    /// Writes the bytes that a deferred log has not written yet; each byte is
    /// written once, however often this or `finish_guarded` is called.
    pub fn write_deferred_log(&mut self) -> Result<(), Failure> {
        if !self.deferred_log {
            return Ok(());
        }
        self.log
            .write_all(&self.received[self.deferred_start..])
            .and_then(|_| self.log.flush())
            .map_err(|_| Failure::new("Incomplete serial log write"))?;
        self.deferred_start = self.received.len();
        Ok(())
    }

    /// Drains queued output, requiring the guest to go idle within
    /// `timing.guest_idle`, and returns the offset at which the next phase
    /// starts. A board capture reports a fatal record, the limit or a failed
    /// log write as soon as a read finds it.
    pub fn boundary(&mut self, guest: &mut dyn Guest) -> Result<usize, Failure> {
        let deadline = Instant::now().checked_add(self.timing.guest_idle);
        while self.read(Duration::ZERO) {
            if let Some(error) = self.guard_error.as_ref().filter(|_| self.board) {
                return Err(error.clone());
            }
            if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                return Err(Failure::new(
                    "UART output did not become idle before the next input",
                ));
            }
        }
        self.ensure_running(guest)?;
        Ok(self.received.len())
    }

    /// Fails with the recorded guard error, at the end of a board session or
    /// when the guest is gone.
    pub fn ensure_running(&mut self, guest: &mut dyn Guest) -> Result<(), Failure> {
        if let Some(error) = &self.guard_error {
            return Err(error.clone());
        }
        if self
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
        {
            return Err(Failure::new(SESSION_ENDED));
        }
        guest.check_alive(self.eof)
    }

    /// One read that fails at once on a board capture: the session is
    /// checked first, the read waits at most until the session deadline, and
    /// a failed log write, the limit, a fatal record or the end of the stream
    /// that it finds fails the read. Any other capture reads as `read` does.
    pub fn checked_read(
        &mut self,
        guest: &mut dyn Guest,
        timeout: Duration,
    ) -> Result<bool, Failure> {
        if !self.board {
            return Ok(self.read(timeout));
        }
        self.ensure_running(guest)?;
        let timeout = self.deadline.map_or(timeout, |deadline| {
            timeout.min(deadline.saturating_duration_since(Instant::now()))
        });
        let received = self.read(timeout);
        if let Some(error) = &self.guard_error {
            return Err(error.clone());
        }
        guest.check_alive(self.eof)?;
        Ok(received)
    }

    /// Sends `data` to the guest once the capture is running. A board
    /// request holds 1 to 128 bytes, else `invalid serial request size`.
    pub fn send(&mut self, guest: &mut dyn Guest, data: &[u8]) -> Result<(), Failure> {
        self.ensure_running(guest)?;
        // `write_all` does not call the writer for an empty request, so the
        // bound of a board request is checked here for it.
        if self.board && data.is_empty() {
            return Err(Failure::new("invalid serial request size"));
        }
        self.writer.write_all(data)?;
        self.writer.flush()?;
        Ok(())
    }

    /// Waits until `matcher` finds a line in the bytes received after `start`,
    /// reading at most `timing.guest_slice` at a time; the returned offsets
    /// are relative to `start`. A wait that ends first fails with `Expected
    /// serial response not received within <seconds>s`.
    pub fn wait_for<F>(
        &mut self,
        guest: &mut dyn Guest,
        matcher: F,
        start: usize,
        timeout: Duration,
    ) -> Result<Match, Failure>
    where
        F: Fn(&[u8]) -> Option<Match>,
    {
        let deadline = Instant::now().checked_add(timeout);
        loop {
            self.ensure_running(guest)?;
            if let Some(found) = matcher(&self.received[start..]) {
                return Ok(found);
            }
            let wait = match deadline {
                Some(deadline) => {
                    let now = Instant::now();
                    if now >= deadline {
                        return Err(Failure::new(format!(
                            "Expected serial response not received within {}s",
                            seconds_text(timeout)
                        )));
                    }
                    (deadline - now).min(self.timing.guest_slice)
                }
                None => self.timing.guest_slice,
            };
            self.read(wait);
        }
    }

    /// Keeps the late diagnostics of a failure without sending anything and
    /// without the fatal-record guard, so that the failure itself is not
    /// replaced. It receives for `tail` (more than zero and at most 120 s,
    /// else `invalid diagnostic capture duration`), within the session
    /// deadline, or until `CASXI_HALTED\r\n` was received, reading at most
    /// `timing.guest_slice` at a time. Each read checks the session deadline,
    /// a failed log write, the limit and the guest, which also reports the
    /// end of the stream, so that a caught interrupt ends the tail with its
    /// error at once. The result has the keys `additional_bytes`,
    /// `elapsed_seconds` and `terminal_halt`, in that order.
    pub fn collect_failure(
        &mut self,
        guest: &mut dyn Guest,
        tail: Duration,
    ) -> Result<Value, Failure> {
        if tail.is_zero() || tail > LONGEST_TAIL {
            return Err(Failure::new("invalid diagnostic capture duration"));
        }
        let started = Instant::now();
        let end = started + tail;
        let deadline = self.deadline.map_or(end, |session| session.min(end));
        let before = self.received.len();
        let mut halted = contains(&self.received, HALTED);
        while !halted && Instant::now() < deadline {
            let start = self.received.len();
            let wait = deadline.saturating_duration_since(Instant::now());
            self.receive(guest, wait.min(self.timing.guest_slice))?;
            halted = contains(
                &self.received[start.saturating_sub(HALTED.len() - 1)..],
                HALTED,
            );
        }
        Ok(json!({
            "additional_bytes": self.received.len() - before,
            "elapsed_seconds": started.elapsed().as_secs_f64(),
            "terminal_halt": halted,
        }))
    }

    /// One read of the failure tail, in this order: the session deadline,
    /// the read, the log write, the limit, then the guest, which reports a
    /// closed stream.
    fn receive(&mut self, guest: &mut dyn Guest, timeout: Duration) -> Result<(), Failure> {
        if self
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
        {
            return Err(Failure::new(SESSION_ENDED));
        }
        let received = self.read_raw(timeout);
        if let Some(error) = self.log_error.take() {
            return Err(error);
        }
        if received && self.limit.is_some_and(|limit| self.received.len() > limit) {
            return Err(Failure::new(self.limit_message()));
        }
        guest.check_alive(self.eof)
    }

    /// After the guest's process has been stopped, collects the remaining
    /// output for up to `timing.guest_finish`, until the stream ends.
    pub fn finish(&mut self) {
        let deadline = Instant::now().checked_add(self.timing.guest_finish);
        while !self.eof {
            let wait = match deadline {
                Some(deadline) => {
                    let now = Instant::now();
                    if now >= deadline {
                        break;
                    }
                    (deadline - now).min(self.timing.guest_finish_slice)
                }
                None => self.timing.guest_finish_slice,
            };
            self.read(wait);
        }
    }
}

/// Drains `stream` into `sender` on a thread of its own until the end of the
/// stream, a failed read or the receiver's end; the sender's drop marks the
/// end. A read that a caught signal interrupted is repeated: interrupt
/// handlers installed without `SA_RESTART`, such as those of
/// [`crate::tty::catch_interrupts`], make a blocked read fail with `EINTR`
/// when the signal is delivered to this thread.
pub(crate) fn spawn_reader<R: Read + Send + 'static>(mut stream: R, sender: Sender<Vec<u8>>) {
    std::thread::spawn(move || {
        let mut buffer = vec![0u8; READ_BUFFER];
        loop {
            match stream.read(&mut buffer) {
                Ok(0) => break,
                Ok(count) => {
                    if sender.send(buffer[..count].to_vec()).is_err() {
                        break;
                    }
                }
                Err(error) if error.kind() == ErrorKind::Interrupted => {}
                Err(_) => break,
            }
        }
    });
}

/// Whether `needle` occurs in `haystack`.
fn contains(haystack: &[u8], needle: &[u8]) -> bool {
    haystack
        .windows(needle.len())
        .any(|window| window == needle)
}

/// `duration` in seconds, as Rust writes an `f64`: `8`, `2.5`, `0.01`, and
/// never with an exponent.
fn seconds_text(duration: Duration) -> String {
    duration.as_secs_f64().to_string()
}

/// How `status` ended a process: the code it exited with, or the number of
/// the signal that ended it. Exactly one of the two is given.
pub fn exit_code(status: ExitStatus) -> (Option<i32>, Option<i32>) {
    (status.code(), status.signal())
}

/// Sends SIGTERM to `child`, which has not been reaped.
fn terminate(child: &Child) {
    let Ok(pid) = libc::pid_t::try_from(child.id()) else {
        return;
    };
    // SAFETY: kill takes a process number and a signal number and touches no
    // memory of this process. The caller holds the only handle of the child
    // and has not reaped it, so the number still names the child, or its
    // zombie, and no other process. A failure is ignored: the child has
    // ended meanwhile.
    unsafe { libc::kill(pid, libc::SIGTERM) };
}

/// The status of `child` once it has ended, looking every `poll` for at most
/// `timeout`; `None` if it still runs then.
fn wait_with_timeout(
    child: &mut Child,
    timeout: Duration,
    poll: Duration,
) -> std::io::Result<Option<ExitStatus>> {
    let deadline = Instant::now().checked_add(timeout);
    loop {
        if let Some(status) = child.try_wait()? {
            return Ok(Some(status));
        }
        if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
            return Ok(None);
        }
        std::thread::sleep(poll);
    }
}

/// Stops `child`: SIGTERM if it still runs, and a kill if it has not ended
/// within `timing.stop_grace`. The report says whether the child was still
/// running (`intentional_shutdown`), whether it was killed (`forced_kill`)
/// and how it ended, with the code it exited with (`exit_code`) or the
/// number of the signal that ended it (`signal`); the other one is null, and
/// both are when the child has not ended within `timing.kill_grace` of the
/// kill.
pub fn stop_process(child: &mut Child, timing: &Timing) -> Value {
    let was_running = matches!(child.try_wait(), Ok(None));
    let mut killed = false;
    if was_running {
        terminate(child);
    }
    let status = match wait_with_timeout(child, timing.stop_grace, timing.reap_poll) {
        Ok(Some(status)) => Some(status),
        _ => {
            killed = true;
            let _ = child.kill();
            wait_with_timeout(child, timing.kill_grace, timing.reap_poll)
                .ok()
                .flatten()
        }
    };
    let (code, signal) = status.map_or((None, None), exit_code);
    json!({
        "intentional_shutdown": was_running,
        "forced_kill": killed,
        "exit_code": code,
        "signal": signal,
    })
}

#[cfg(test)]
mod tests;
