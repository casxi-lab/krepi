//! The process helpers of the QEMU runner: a thread that drains an output
//! stream of a child process, and the stop of a child with a report of how
//! it ended. The serial link over the standard streams of a guest uses them.

use crate::report::Value;
use crate::timing::Timing;
use serde_json::json;
use std::io::Read;
use std::os::unix::process::ExitStatusExt;
use std::process::{Child, ExitStatus};
use std::sync::mpsc::Sender;
use std::time::{Duration, Instant};

/// The bytes one read of [`spawn_reader`] takes at most.
const READ_BUFFER: usize = 65536;

/// Drains `stream` into `sender` on a thread of its own until the end of the
/// stream, a failed read or the receiver's end; the sender's drop marks the
/// end.
pub(crate) fn spawn_reader<R: Read + Send + 'static>(mut stream: R, sender: Sender<Vec<u8>>) {
    std::thread::spawn(move || {
        let mut buffer = vec![0u8; READ_BUFFER];
        loop {
            match stream.read(&mut buffer) {
                Ok(0) | Err(_) => break,
                Ok(count) => {
                    if sender.send(buffer[..count].to_vec()).is_err() {
                        break;
                    }
                }
            }
        }
    });
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
mod tests {
    use super::*;
    use crate::TEST_WAIT;
    use std::io::{BufRead, BufReader};
    use std::process::{Command, Stdio};

    /// A child that has exited is reported with its exit code and no signal;
    /// one that SIGTERM ends with that signal; and one that ignores SIGTERM
    /// is killed and reported with SIGKILL. A grace that a slow host never
    /// exceeds keeps the first two from being killed; the third waits its
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
        let keys: Vec<&String> = report.as_object().unwrap().keys().collect();
        assert_eq!(
            keys,
            ["intentional_shutdown", "forced_kill", "exit_code", "signal"]
        );

        // The shell ignores SIGTERM, prints a line once it does, and hands
        // the ignored disposition on to `cat`, which waits for input.
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
}
