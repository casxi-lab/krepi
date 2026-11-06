//! A bidirectional serial link to a guest over the standard streams of its
//! process.
//!
//! Reading and writing proceed independently so that neither direction of
//! the UART blocks the tool: reader threads drain the guest's output, and a
//! writer thread feeds scheduled input and counts how much the guest's pipe
//! accepted. The link keeps complete lines with the time they arrived and
//! the input count at that moment. Board serial ports are in [`crate::tty`].

use crate::Failure;
use crate::qemu::spawn_reader;
use crate::timing::Timing;
use std::collections::VecDeque;
use std::fs::File;
use std::io::Write;
use std::process::{Child, ChildStdin};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::mpsc::{Receiver, RecvTimeoutError, Sender, channel};
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

/// The longest unterminated line the link keeps before failing.
const LINE_LIMIT: usize = 65536;

/// The beginnings of the guest's records that end a wait for the ready line
/// with a failure.
const FATAL_RECORDS: [&[u8]; 3] = [b"CASXI_EXCEPTION", b"CASXI_PANIC", b"CASXI_HALTED"];

/// One complete serial line without its terminator and one trailing `\r`.
#[derive(Debug, Clone, PartialEq)]
pub struct Line {
    pub content: Vec<u8>,
    /// Seconds since the link opened when the line was received.
    pub received_seconds: f64,
    /// Input bytes the guest's pipe had accepted when the line was received.
    pub written_bytes: usize,
}

struct Writer {
    sender: Option<Sender<Vec<u8>>>,
    handle: Option<JoinHandle<()>>,
    written: Arc<AtomicUsize>,
    stopped: Arc<AtomicBool>,
    error: Arc<Mutex<Option<String>>>,
}

/// The guest's serial stream in both directions.
pub struct Link {
    receiver: Receiver<Vec<u8>>,
    output_log: File,
    writer: Writer,
    partial: Vec<u8>,
    timing: Timing,
    /// Complete lines not yet taken by the protocol.
    pub lines: VecDeque<Line>,
    /// Input bytes handed to the link so far.
    pub scheduled_bytes: usize,
    /// Output bytes received so far.
    pub received_bytes: usize,
    /// Both output streams reached their end.
    pub eof: bool,
    pub started: Instant,
}

impl Link {
    /// Takes the child's standard streams; output and diagnostics share one
    /// byte stream and `output_log`, and the input bytes that the guest
    /// accepted go to `input_log`. The link waits as `timing` gives.
    pub fn new(
        child: &mut Child,
        output_log: File,
        input_log: File,
        timing: &Timing,
    ) -> Result<Self, Failure> {
        let stdin = child
            .stdin
            .take()
            .ok_or_else(|| Failure::new("QEMU standard input is not piped"))?;
        let stdout = child
            .stdout
            .take()
            .ok_or_else(|| Failure::new("QEMU standard output is not piped"))?;
        let (sender, receiver) = channel();
        match child.stderr.take() {
            Some(stderr) => {
                spawn_reader(stdout, sender.clone());
                spawn_reader(stderr, sender);
            }
            None => spawn_reader(stdout, sender),
        }
        let written = Arc::new(AtomicUsize::new(0));
        let stopped = Arc::new(AtomicBool::new(false));
        let error = Arc::new(Mutex::new(None));
        let (input_sender, input_receiver) = channel();
        let handle = spawn_writer(
            stdin,
            input_log,
            input_receiver,
            Arc::clone(&written),
            Arc::clone(&stopped),
            Arc::clone(&error),
        );
        Ok(Link {
            receiver,
            output_log,
            writer: Writer {
                sender: Some(input_sender),
                handle: Some(handle),
                written,
                stopped,
                error,
            },
            partial: Vec::new(),
            timing: *timing,
            lines: VecDeque::new(),
            scheduled_bytes: 0,
            received_bytes: 0,
            eof: false,
            started: Instant::now(),
        })
    }

    /// Schedules `data` for transmission and returns the scheduled total.
    pub fn enqueue(&mut self, data: &[u8]) -> Result<usize, Failure> {
        let sender = self
            .writer
            .sender
            .as_ref()
            .ok_or_else(|| Failure::new("QEMU stdin is closed"))?;
        if sender.send(data.to_vec()).is_err() {
            return Err(Failure::new(
                self.writer_error()
                    .unwrap_or_else(|| "QEMU stdin is closed".to_string()),
            ));
        }
        self.scheduled_bytes += data.len();
        Ok(self.scheduled_bytes)
    }

    /// Input bytes the guest's pipe has accepted.
    pub fn written_bytes(&self) -> usize {
        self.writer.written.load(Ordering::SeqCst)
    }

    /// Scheduled bytes the pipe has not accepted yet.
    pub fn pending(&self) -> usize {
        self.scheduled_bytes.saturating_sub(self.written_bytes())
    }

    /// Bytes of an unterminated line received so far.
    pub fn partial_len(&self) -> usize {
        self.partial.len()
    }

    fn writer_error(&self) -> Option<String> {
        self.writer
            .error
            .lock()
            .ok()
            .and_then(|mut slot| slot.take())
    }

    /// Fails once the guest's process has exited or its output has ended,
    /// with the standard library's text of its exit status, such as
    /// `exit status: 1` or `signal: 15 (SIGTERM)`, or `still running` for a
    /// process whose output ended first.
    pub fn ensure_running(&mut self, child: &mut Child) -> Result<(), Failure> {
        let status = child.try_wait()?;
        if status.is_some() || self.eof {
            let end =
                status.map_or_else(|| "still running".to_string(), |status| status.to_string());
            return Err(Failure::new(format!(
                "QEMU exited or closed output early ({end})"
            )));
        }
        Ok(())
    }

    /// Waits up to `timeout` for output, then takes everything that is ready;
    /// a write failure surfaces here while writes are still wanted. Once the
    /// output has ended, it waits at most the link slice of its timing.
    pub fn poll(&mut self, timeout: Duration) -> Result<(), Failure> {
        if !self.writer.stopped.load(Ordering::SeqCst)
            && let Some(error) = self.writer_error()
        {
            return Err(Failure::new(error));
        }
        if self.eof {
            if !timeout.is_zero() {
                std::thread::sleep(timeout.min(self.timing.link_slice));
            }
            return Ok(());
        }
        let first = match self.receiver.recv_timeout(timeout) {
            Ok(chunk) => chunk,
            Err(RecvTimeoutError::Timeout) => return Ok(()),
            Err(RecvTimeoutError::Disconnected) => {
                self.eof = true;
                return Ok(());
            }
        };
        self.accept(first)?;
        while let Ok(chunk) = self.receiver.try_recv() {
            self.accept(chunk)?;
        }
        Ok(())
    }

    fn accept(&mut self, chunk: Vec<u8>) -> Result<(), Failure> {
        let _ = self
            .output_log
            .write_all(&chunk)
            .and_then(|_| self.output_log.flush());
        self.received_bytes += chunk.len();
        self.partial.extend_from_slice(&chunk);
        let written_bytes = self.written_bytes();
        let received_seconds = self.started.elapsed().as_secs_f64();
        while let Some(newline) = self.partial.iter().position(|&b| b == b'\n') {
            let tail = self.partial.split_off(newline + 1);
            self.partial.pop();
            if self.partial.last() == Some(&b'\r') {
                self.partial.pop();
            }
            let content = std::mem::replace(&mut self.partial, tail);
            self.lines.push_back(Line {
                content,
                received_seconds,
                written_bytes,
            });
        }
        if self.partial.len() > LINE_LIMIT {
            return Err(Failure::new("Unterminated serial line exceeds 64 KiB"));
        }
        Ok(())
    }

    /// Stops transmitting scheduled input; bytes already handed to the pipe
    /// are not recalled.
    pub fn stop_writes(&self) {
        self.writer.stopped.store(true, Ordering::SeqCst);
    }

    /// After a failure: stops input and collects, for the link drain of its
    /// timing, the diagnostics that may follow the first failing line.
    pub fn drain_failure(&mut self) -> Result<(), Failure> {
        self.stop_writes();
        let deadline = Instant::now() + self.timing.link_drain;
        while !self.eof {
            let now = Instant::now();
            if now >= deadline {
                break;
            }
            self.poll((deadline - now).min(self.timing.link_slice))?;
        }
        Ok(())
    }

    /// Never transmits leftover input during cleanup; reads until the output
    /// ends, for at most the link finish of its timing, then closes both
    /// directions.
    pub fn finish(&mut self) {
        self.stop_writes();
        self.writer.sender.take();
        let deadline = Instant::now() + self.timing.link_finish;
        while !self.eof {
            let now = Instant::now();
            if now >= deadline {
                break;
            }
            let _ = self.poll((deadline - now).min(self.timing.link_finish_slice));
        }
        if let Some(handle) = self.writer.handle.take() {
            let _ = handle.join();
        }
    }

    /// Waits at most `timeout` for the complete `CASXI_READY` line, failing
    /// on an earlier fatal record, whose bytes the message gives with the
    /// escapes of `<[u8]>::escape_ascii`.
    pub fn wait_ready(&mut self, child: &mut Child, timeout: Duration) -> Result<(), Failure> {
        let started = Instant::now();
        loop {
            self.ensure_running(child)?;
            while let Some(line) = self.lines.pop_front() {
                if line.content == b"CASXI_READY" {
                    return Ok(());
                }
                if FATAL_RECORDS
                    .iter()
                    .any(|prefix| line.content.starts_with(prefix))
                {
                    return Err(Failure::new(format!(
                        "Guest failed before ready: {}",
                        line.content.escape_ascii()
                    )));
                }
            }
            let remaining = timeout.saturating_sub(started.elapsed());
            if remaining.is_zero() {
                return Err(Failure::new(
                    "Timeout waiting for complete CASXI_READY line",
                ));
            }
            self.poll(remaining.min(self.timing.link_slice))?;
        }
    }
}

fn spawn_writer(
    mut stdin: ChildStdin,
    mut input_log: File,
    receiver: Receiver<Vec<u8>>,
    written: Arc<AtomicUsize>,
    stopped: Arc<AtomicBool>,
    error: Arc<Mutex<Option<String>>>,
) -> JoinHandle<()> {
    std::thread::spawn(move || {
        let fail = |message: String| {
            if let Ok(mut slot) = error.lock() {
                slot.get_or_insert(message);
            }
        };
        while let Ok(chunk) = receiver.recv() {
            let mut offset = 0;
            while offset < chunk.len() && !stopped.load(Ordering::SeqCst) {
                match stdin.write(&chunk[offset..]) {
                    Ok(0) => {
                        fail("QEMU stdin accepted zero bytes".to_string());
                        return;
                    }
                    Ok(count) => {
                        let _ = input_log
                            .write_all(&chunk[offset..offset + count])
                            .and_then(|_| input_log.flush());
                        offset += count;
                        written.fetch_add(count, Ordering::SeqCst);
                    }
                    Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
                    Err(e) => {
                        fail(e.to_string());
                        return;
                    }
                }
            }
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::TEST_WAIT;
    use crate::qemu::stop_process;
    use crate::scratch::Scratch;
    use serde_json::json;
    use std::process::{Command, Stdio};

    /// The time values of these tests: the slices of QEMU virt, and bounds
    /// that a slow host never reaches for the end of the output and of the
    /// process.
    const TIMING: Timing = Timing {
        link_finish: TEST_WAIT,
        stop_grace: TEST_WAIT,
        kill_grace: TEST_WAIT,
        ..Timing::QEMU_VIRT
    };

    /// `cat` as the guest: it echoes its input on its output.
    fn echo_guest() -> Child {
        Command::new("cat")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("start cat")
    }

    #[test]
    fn a_link_pairs_lines_with_input_progress() {
        let scratch = Scratch::new("serial-link");
        let mut child = echo_guest();
        let output_log = File::create(scratch.path("out.log")).unwrap();
        let input_log = File::create(scratch.path("in.bin")).unwrap();
        let mut link = Link::new(&mut child, output_log, input_log, &TIMING).unwrap();
        assert_eq!(link.enqueue(b"CASXI_READY\n").unwrap(), 12);
        link.wait_ready(&mut child, TEST_WAIT).unwrap();
        link.enqueue(b"hello\r\n").unwrap();
        let deadline = Instant::now() + TEST_WAIT;
        while link.lines.is_empty() && Instant::now() < deadline {
            link.poll(Duration::from_millis(50)).unwrap();
        }
        let line = link.lines.pop_front().expect("echoed line");
        assert_eq!(line.content, b"hello");
        assert!(line.written_bytes >= 12 && line.written_bytes <= 19);
        while link.pending() > 0 && Instant::now() < deadline {
            std::thread::sleep(Duration::from_millis(5));
        }
        assert_eq!(link.written_bytes(), 19);
        assert_eq!(link.scheduled_bytes, 19);
        assert_eq!(link.received_bytes, 19);
        let cleanup = stop_process(&mut child, &TIMING);
        assert_eq!(
            cleanup,
            json!({
                "intentional_shutdown": true,
                "forced_kill": false,
                "exit_code": null,
                "signal": 15,
            })
        );
        link.finish();
        assert!(link.eof);
        assert_eq!(
            link.ensure_running(&mut child),
            Err(Failure::new(
                "QEMU exited or closed output early (signal: 15 (SIGTERM))"
            ))
        );
        assert_eq!(
            std::fs::read(scratch.path("in.bin")).unwrap(),
            b"CASXI_READY\nhello\r\n"
        );
        assert_eq!(
            std::fs::read(scratch.path("out.log")).unwrap(),
            b"CASXI_READY\nhello\r\n"
        );
    }

    /// A fatal record before the ready line fails the wait with the record,
    /// whose quotes, backslash and control byte are escaped; the lines before
    /// it are passed over, and the ready line after it is not reached.
    #[test]
    fn a_fatal_record_before_ready_fails_with_its_line() {
        let scratch = Scratch::new("serial-fatal");
        let mut child = echo_guest();
        let output_log = File::create(scratch.path("out.log")).unwrap();
        let input_log = File::create(scratch.path("in.bin")).unwrap();
        let mut link = Link::new(&mut child, output_log, input_log, &TIMING).unwrap();
        link.enqueue(b"boot\nCASXI_PANIC at \"main.rs\" 'x'\x01\\\r\nCASXI_READY\n")
            .unwrap();
        assert_eq!(
            link.wait_ready(&mut child, TEST_WAIT),
            Err(Failure::new(
                "Guest failed before ready: CASXI_PANIC at \\\"main.rs\\\" \\'x\\'\\x01\\\\"
            ))
        );
        stop_process(&mut child, &TIMING);
        link.finish();
        assert!(link.eof);
    }

    /// Output that ends while the process runs fails the link, which names
    /// the process as still running. The shell sends its standard output and
    /// standard error to `/dev/null`, so that both pipes end, and becomes
    /// `cat`, which has an output to write to and waits for input that the
    /// link never sends. A `cat` whose standard output is closed would exit
    /// at once instead.
    #[test]
    fn output_that_ends_before_the_process_fails_the_link() {
        let scratch = Scratch::new("serial-closed");
        let mut child = Command::new("sh")
            .args(["-c", "exec >/dev/null 2>&1; exec cat"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .expect("start sh");
        let output_log = File::create(scratch.path("out.log")).unwrap();
        let input_log = File::create(scratch.path("in.bin")).unwrap();
        let mut link = Link::new(&mut child, output_log, input_log, &TIMING).unwrap();
        let deadline = Instant::now() + TEST_WAIT;
        while !link.eof && Instant::now() < deadline {
            link.poll(Duration::from_millis(50)).unwrap();
        }
        assert!(link.eof, "the output ends");
        assert_eq!(
            link.ensure_running(&mut child),
            Err(Failure::new(
                "QEMU exited or closed output early (still running)"
            ))
        );
        assert_eq!(stop_process(&mut child, &TIMING)["signal"], 15);
        link.finish();
        assert_eq!(link.received_bytes, 0);
    }
}
