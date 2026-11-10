//! The commands of the proof gate, each in a process group of its own, with
//! its output in files. [`run`] sees the end of a command without collecting
//! it and kills its group before collecting it, so that the kill cannot reach
//! a group that took over a freed number.
//!
//! `cargo xtask check` shares the module: it watches and kills the process
//! groups of its commands in the same order, through [`leader_ended`],
//! [`kill_group`] and [`group_ended`], and reads the stop signal that
//! [`init`] lets in through [`stop_signal`] instead of ending by it.

use std::fs::{self, File, OpenOptions};
use std::io;
use std::os::fd::AsRawFd;
use std::os::unix::process::{CommandExt, ExitStatusExt};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

use serde::{Deserialize, Serialize};

use super::toolchain::environment::Environment;
use super::toolchain::sha256;

/// How long [`run`] waits for the processes of a killed group to end.
pub const GROUP_END: Duration = Duration::from_secs(60);

/// The pause between two looks at a command or a group.
pub(crate) const PAUSE: Duration = Duration::from_millis(10);

/// The stop signal that reached the gate or `cargo xtask check`, or 0.
static STOP: AtomicUsize = AtomicUsize::new(0);

/// What set the limit of a command: the cap of its call site, or the rest
/// of the budget of its phase or of the gate.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum LimitBy {
    Cap,
    Phase,
    Gate,
}

/// The time that a command may run, and what set it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limit {
    pub duration: Duration,
    pub by: LimitBy,
}

/// A command to run, with its output files `<NNNN>-<name>.stdout` and
/// `.stderr` in `logs`, where `NNNN` is `sequence`.
pub struct Spec<'a> {
    pub name: &'a str,
    pub program: &'a str,
    pub args: &'a [String],
    pub cwd: &'a Path,
    pub env: &'a Environment,
    pub stdin: Option<&'a Path>,
    pub logs: &'a Path,
    pub sequence: u32,
    pub limit: Limit,
}

/// How a command ended.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ended {
    Exited(i32),
    Signaled(i32),
    /// It ran until its limit and was killed.
    TimedOut,
    /// It could not start, or its output could not be kept or read back.
    Failed(String),
}

/// An output file of a command.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Log {
    pub path: PathBuf,
    pub bytes: u64,
    pub sha256: String,
}

/// A command that [`run`] ran, or tried to run.
#[derive(Debug, Clone, PartialEq)]
pub struct Ran {
    pub name: String,
    /// The command's process group, or `None` if it did not start.
    pub group: Option<i32>,
    pub ended: Ended,
    pub limit: Limit,
    /// The time from the start of the command until it was collected.
    pub seconds: Duration,
    pub stdout: Option<Log>,
    pub stderr: Option<Log>,
    /// The standard output and then, from a new line, the standard error,
    /// as lossy UTF-8.
    pub output: String,
    /// Whether processes of the group outlived the kill by [`GROUP_END`].
    pub survivors: bool,
}

impl Ran {
    /// The exit code, if the command exited.
    pub fn code(&self) -> Option<i32> {
        match self.ended {
            Ended::Exited(code) => Some(code),
            _ => None,
        }
    }
}

/// Restores the default disposition of `SIGCHLD`, which [`run`] needs, and
/// lets SIGINT and SIGTERM stop the gate, and SIGHUP unless it is ignored, as
/// under `nohup`. Called once, before the gate starts any command, and by
/// `cargo xtask check` before its first step: the signal then sets the flag
/// that [`stop_signal`] reads.
pub fn init() {
    // SAFETY: the default disposition installs no handler and touches no
    // memory of this process.
    unsafe { libc::signal(libc::SIGCHLD, libc::SIG_DFL) };
    // SAFETY: all bits zero is a valid `sigaction`, into which a null new
    // action only reads the disposition of SIGHUP.
    let ignored = unsafe {
        let mut hangup: libc::sigaction = std::mem::zeroed();
        libc::sigaction(libc::SIGHUP, std::ptr::null(), &mut hangup);
        hangup.sa_sigaction == libc::SIG_IGN
    };
    for signal in [libc::SIGINT, libc::SIGTERM, libc::SIGHUP] {
        if signal != libc::SIGHUP || !ignored {
            // The crate refuses only the signals that cannot be caught.
            signal_hook::flag::register_usize(signal, &STOP, signal as usize)
                .expect("SIGINT, SIGTERM and SIGHUP can be caught");
        }
    }
}

/// The stop signal that reached the process since [`init`], if one did.
pub(crate) fn stop_signal() -> Option<i32> {
    let signal = STOP.load(Ordering::SeqCst);
    // Signal numbers are small and positive.
    (signal != 0).then_some(signal as i32)
}

/// Ends the gate by the stop signal that reached it, if one did.
pub fn stop_if_asked() {
    let signal = STOP.load(Ordering::SeqCst);
    if signal != 0 {
        let _ = signal_hook::low_level::emulate_default_handler(signal as libc::c_int);
        std::process::abort();
    }
}

/// Runs the command of `spec` until it ends or reaches its limit, kills its
/// group and waits up to [`GROUP_END`] for the group to be empty. A failure
/// to start the command, to watch it or to keep its output is an
/// [`Ended::Failed`]; a command that did not start has no output files.
pub(super) fn run(spec: &Spec) -> Ran {
    stop_if_asked();
    let paths = [log_path(spec, "stdout"), log_path(spec, "stderr")];
    let begin = Instant::now();
    let (mut ended, group) = match start(spec, &paths) {
        Err(message) => (Ended::Failed(message), None),
        Ok(mut child) => {
            // Process numbers are positive and below 2^31.
            let group = child.id() as libc::pid_t;
            (
                supervise(&mut child, group, begin + spec.limit.duration),
                Some(group),
            )
        }
    };
    let seconds = begin.elapsed();
    let survivors = group.is_some_and(|group| !group_ended(group));
    let (mut logs, mut output) = ([None, None], String::new());
    for (log, path) in logs.iter_mut().zip(&paths).filter(|_| group.is_some()) {
        match fs::read(path) {
            Ok(bytes) => {
                if !output.is_empty() && !output.ends_with('\n') && !bytes.is_empty() {
                    output.push('\n');
                }
                output.push_str(&String::from_utf8_lossy(&bytes));
                *log = Some(Log {
                    path: path.clone(),
                    bytes: bytes.len() as u64,
                    sha256: sha256(&bytes),
                });
            }
            Err(error) if !matches!(ended, Ended::Failed(_)) => {
                ended = Ended::Failed(format!("cannot read {}: {error}", path.display()));
            }
            Err(_) => {}
        }
    }
    let [stdout, stderr] = logs;
    Ran {
        name: spec.name.to_string(),
        group,
        ended,
        limit: spec.limit,
        seconds,
        stdout,
        stderr,
        output,
        survivors,
    }
}

fn log_path(spec: &Spec, stream: &str) -> PathBuf {
    spec.logs
        .join(format!("{:04}-{}.{stream}", spec.sequence, spec.name))
}

/// Creates the two output files and starts the command in a new process
/// group.
fn start(spec: &Spec, paths: &[PathBuf; 2]) -> Result<Child, String> {
    let create = |path: &PathBuf| {
        OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .map_err(|error| format!("cannot create {}: {error}", path.display()))
    };
    let (stdout, stderr) = (create(&paths[0])?, create(&paths[1])?);
    let stdin = match spec.stdin {
        Some(path) => Stdio::from(
            File::open(path).map_err(|error| format!("cannot open {}: {error}", path.display()))?,
        ),
        None => Stdio::null(),
    };
    let mut command = Command::new(spec.program);
    command.args(spec.args).current_dir(spec.cwd);
    spec.env.apply(&mut command);
    command
        .stdin(stdin)
        .stdout(stdout)
        .stderr(stderr)
        .process_group(0)
        .spawn()
        .map_err(|error| format!("cannot start {}: {error}", spec.program))
}

/// Waits until the command `child`, the leader of `group`, has ended or
/// `deadline` has passed, kills the group and collects the command. A stop
/// signal kills the group, collects the command and ends the gate.
fn supervise(child: &mut Child, group: libc::pid_t, deadline: Instant) -> Ended {
    let timed_out = loop {
        match leader_ended(group) {
            Ok(true) => break false,
            Ok(false) => {}
            Err(error) => {
                // The number may name another process now: nothing is signalled.
                let _ = child.try_wait();
                return Ended::Failed(format!("cannot watch the command: {error}"));
            }
        }
        if STOP.load(Ordering::SeqCst) != 0 {
            kill_group(group);
            let _ = child.wait();
            group_ended(group);
            stop_if_asked();
        }
        let now = Instant::now();
        if now >= deadline {
            break true;
        }
        std::thread::sleep(PAUSE.min(deadline - now));
    };
    kill_group(group);
    match child.wait() {
        Err(error) => Ended::Failed(format!("cannot collect the command: {error}")),
        Ok(_) if timed_out => Ended::TimedOut,
        Ok(status) => status.code().map_or_else(
            || Ended::Signaled(status.signal().unwrap_or_default()),
            Ended::Exited,
        ),
    }
}

/// Whether the command `leader` has ended, looked at without collecting it.
pub(crate) fn leader_ended(leader: libc::pid_t) -> io::Result<bool> {
    // SAFETY: all bits zero is a valid `siginfo_t`.
    let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
    // SAFETY: `info` is valid and writable for the call. `leader` is an
    // uncollected child of this process, so it names that child alone;
    // `WNOWAIT` leaves it uncollected, and `WNOHANG` returns at once.
    let result = unsafe {
        libc::waitid(
            libc::P_PID,
            leader as libc::id_t,
            &mut info,
            libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
        )
    };
    if result == -1 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: after a successful `waitid`, `info` holds the zeroes written
    // above or the report of a child, whose process number is set.
    let reported = unsafe { info.si_pid() } != 0;
    // Some systems report a stopped child even though only ended children
    // were asked for.
    Ok(reported
        && matches!(
            info.si_code,
            libc::CLD_EXITED | libc::CLD_KILLED | libc::CLD_DUMPED
        ))
}

/// Kills every process of `group`, whose leader has not been collected.
pub(crate) fn kill_group(group: libc::pid_t) {
    // SAFETY: killpg touches no memory of this process. The uncollected
    // leader keeps the number of `group` from naming a later group. A
    // failure leaves processes behind, which `group_ended` reports.
    unsafe { libc::killpg(group, libc::SIGKILL) };
}

/// Whether `group`, whose leader has been collected, has no process left
/// within [`GROUP_END`].
pub(crate) fn group_ended(group: libc::pid_t) -> bool {
    let deadline = Instant::now() + GROUP_END;
    loop {
        // SAFETY: signal 0 sends nothing and touches no memory of this
        // process; a new group with the number would only be reported as
        // survivors.
        let result = unsafe { libc::kill(-group, 0) };
        if result == -1 && io::Error::last_os_error().raw_os_error() == Some(libc::ESRCH) {
            return true;
        }
        let now = Instant::now();
        if now >= deadline {
            return false;
        }
        std::thread::sleep(PAUSE.min(deadline - now));
    }
}

/// The effective user ID of the gate.
pub fn effective_uid() -> u32 {
    // SAFETY: geteuid touches no memory of this process and cannot fail.
    unsafe { libc::geteuid() }
}

/// The bytes available to unprivileged users on the file system of `path`.
pub fn disk_available(path: &Path) -> Option<u64> {
    // SAFETY: all bits zero is a valid `statvfs`.
    let mut stat: libc::statvfs = unsafe { std::mem::zeroed() };
    // SAFETY: the opened file outlives the call, and `stat` is writable.
    (unsafe { libc::fstatvfs(File::open(path).ok()?.as_raw_fd(), &mut stat) } == 0).then_some(())?;
    u64::try_from(u128::from(stat.f_bavail) * u128::from(stat.f_frsize)).ok()
}

/// The largest maximum resident set of a collected child of the gate, or of
/// a descendant that it collected, in bytes; Linux reports kibibytes.
pub fn largest_child_rss() -> Option<u64> {
    // SAFETY: all bits zero is a valid `rusage`.
    let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
    // SAFETY: `usage` is writable for the call.
    (unsafe { libc::getrusage(libc::RUSAGE_CHILDREN, &mut usage) } == 0).then_some(())?;
    let unit = if cfg!(target_os = "linux") { 1_024 } else { 1 };
    u64::try_from(usage.ru_maxrss).ok()?.checked_mul(unit)
}

/// The `memory.peak` of the gate's cgroup, under cgroup version 2.
pub fn cgroup_memory_peak() -> Option<u64> {
    let cgroup = fs::read_to_string("/proc/self/cgroup").ok()?;
    let path = cgroup.lines().find_map(|line| line.strip_prefix("0::/"))?;
    let peak = Path::new("/sys/fs/cgroup").join(path).join("memory.peak");
    fs::read_to_string(peak).ok()?.trim().parse().ok()
}

#[cfg(test)]
pub(crate) mod tests {
    use super::super::toolchain::environment::SYSTEM_PATH;
    use super::*;
    use crate::scratch::Scratch;

    /// The variable that makes the process of a test the one that reports
    /// how [`init`] leaves the stop signals.
    const INIT: &str = "KREPI_XTASK_INIT";

    /// A limit that no command of these tests reaches unless it hangs.
    const LONG: Limit = Limit {
        duration: Duration::from_secs(3_600),
        by: LimitBy::Cap,
    };

    /// The limit of the commands that these tests expect to hang. It only
    /// decides that the command is stopped; nothing bounds how long a step
    /// takes.
    const SHORT: Limit = Limit {
        duration: Duration::from_secs(1),
        by: LimitBy::Cap,
    };

    fn system() -> Environment {
        Environment::of(&[("PATH", SYSTEM_PATH)])
    }

    /// Runs `program` with `args` as command `sequence` named `fake`, with
    /// its output files in `logs` of `scratch`.
    fn run_in(
        scratch: &Scratch,
        program: &str,
        args: &[&str],
        env: &Environment,
        stdin: Option<&Path>,
        limit: Limit,
    ) -> Ran {
        let logs = scratch.0.join("logs");
        fs::create_dir_all(&logs).expect("create the log directory");
        let args: Vec<String> = args.iter().map(|arg| arg.to_string()).collect();
        run(&Spec {
            name: "fake",
            program,
            args: &args,
            cwd: &scratch.0,
            env,
            stdin,
            logs: &logs,
            sequence: 7,
            limit,
        })
    }

    /// Runs the shell script `script`.
    fn shell(scratch: &Scratch, script: &str, limit: Limit) -> Ran {
        run_in(scratch, "/bin/sh", &["-c", script], &system(), None, limit)
    }

    /// Makes `command` start with `disposition` for SIGHUP.
    pub(crate) fn with_hangup(command: &mut Command, disposition: libc::sighandler_t) {
        // SAFETY: between fork and exec the closure calls only `signal`,
        // which is async-signal-safe, and allocates nothing.
        unsafe {
            command.pre_exec(move || {
                libc::signal(libc::SIGHUP, disposition);
                Ok(())
            })
        };
    }

    /// The disposition of `signal` in this process: `SIG_DFL`, `SIG_IGN` or
    /// a handler.
    fn disposition(signal: libc::c_int) -> libc::sighandler_t {
        // SAFETY: all bits zero is a valid `sigaction`, into which a null new
        // action only reads the disposition of `signal`.
        unsafe {
            let mut action: libc::sigaction = std::mem::zeroed();
            libc::sigaction(signal, std::ptr::null(), &mut action);
            action.sa_sigaction
        }
    }

    /// The error number with which signal 0 to the group `group` fails, or
    /// `None` if a process of the group exists.
    pub(crate) fn probe(group: i32) -> Option<i32> {
        // SAFETY: signal 0 sends nothing and touches no memory of this
        // process.
        let result = unsafe { libc::kill(-group, 0) };
        (result == -1).then(|| {
            io::Error::last_os_error()
                .raw_os_error()
                .expect("kill sets an error number")
        })
    }

    #[test]
    fn no_process_of_the_group_survives_a_timeout() {
        let scratch = Scratch::new("group-timeout");
        let ran = shell(&scratch, "sleep 30 & sleep 30", SHORT);
        assert_eq!(ran.ended, Ended::TimedOut);
        assert!(!ran.survivors);
        let group = ran.group.expect("the command started");
        assert_eq!(probe(group), Some(libc::ESRCH));
    }

    #[test]
    fn the_group_is_killed_when_its_leader_exits() {
        let scratch = Scratch::new("group-exit");
        let ran = shell(&scratch, "sleep 30 & exit 0", LONG);
        assert_eq!(ran.ended, Ended::Exited(0));
        assert!(!ran.survivors);
        let group = ran.group.expect("the command started");
        assert_eq!(probe(group), Some(libc::ESRCH));
    }

    #[test]
    fn both_output_streams_are_written_to_files() {
        let scratch = Scratch::new("streams");
        let ran = shell(&scratch, "printf out; printf 'err\\n' >&2; exit 3", LONG);
        assert_eq!(ran.ended, Ended::Exited(3));
        assert_eq!(ran.code(), Some(3));
        assert_eq!(ran.name, "fake");
        assert_eq!(ran.limit, LONG);
        let logs = scratch.0.join("logs");
        let stdout = ran.stdout.as_ref().expect("the standard output is kept");
        assert_eq!(stdout.path, logs.join("0007-fake.stdout"));
        assert_eq!(stdout.bytes, 3);
        // The digest of the three bytes `out`, from `shasum -a 256`.
        assert_eq!(
            stdout.sha256,
            "762069bc07a6e1b5df123a5ae7bd91c10daa04694fbaa17fba0cd6a8dcce8f22"
        );
        let stderr = ran.stderr.as_ref().expect("the standard error is kept");
        assert_eq!(stderr.path, logs.join("0007-fake.stderr"));
        assert_eq!(stderr.bytes, 4);
        assert_eq!(fs::read(&stdout.path).unwrap(), b"out");
        assert_eq!(fs::read(&stderr.path).unwrap(), b"err\n");
        assert_eq!(ran.output, "out\nerr\n");
    }

    #[test]
    fn a_killed_command_keeps_what_it_wrote() {
        let scratch = Scratch::new("killed-output");
        let ran = shell(&scratch, "echo started; echo working >&2; kill -9 $$", LONG);
        assert_eq!(ran.ended, Ended::Signaled(9));
        assert_eq!(ran.code(), None);
        assert_eq!(ran.output, "started\nworking\n");
    }

    #[test]
    fn the_input_is_read_from_the_given_file() {
        let scratch = Scratch::new("input");
        scratch.write("input", "in\nput\n");
        let input = scratch.0.join("input");
        let ran = run_in(&scratch, "cat", &[], &system(), Some(&input), LONG);
        assert_eq!(ran.ended, Ended::Exited(0));
        assert_eq!(ran.output, "in\nput\n");
        // Without an input file, the command reads nothing and does not wait.
        let scratch = Scratch::new("no-input");
        let ran = run_in(&scratch, "cat", &[], &system(), None, LONG);
        assert_eq!(ran.ended, Ended::Exited(0));
        assert_eq!(ran.output, "");
        let stdout = ran.stdout.expect("the standard output is kept");
        assert_eq!(stdout.bytes, 0);
        assert_eq!(
            stdout.sha256,
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
    }

    #[test]
    fn the_command_sees_only_its_environment() {
        let scratch = Scratch::new("environment");
        let env = Environment::of(&[("PATH", SYSTEM_PATH), ("ONLY", "this")]);
        let ran = run_in(&scratch, "env", &[], &env, None, LONG);
        assert_eq!(ran.ended, Ended::Exited(0));
        let mut lines: Vec<&str> = ran.output.lines().collect();
        lines.sort_unstable();
        assert_eq!(lines, ["ONLY=this", &format!("PATH={SYSTEM_PATH}")]);
    }

    #[test]
    fn a_program_that_cannot_start_ends_with_an_io_error() {
        let scratch = Scratch::new("cannot-start");
        let missing = scratch.0.join("missing-tool");
        let ran = run_in(
            &scratch,
            missing.to_str().expect("a UTF-8 path"),
            &[],
            &system(),
            None,
            LONG,
        );
        let Ended::Failed(message) = &ran.ended else {
            panic!("{:?}", ran.ended);
        };
        assert!(
            message.starts_with(&format!("cannot start {}: ", missing.display())),
            "{message}"
        );
        assert_eq!(ran.group, None);
        // A command that did not start has no output.
        assert_eq!((ran.stdout, ran.stderr), (None, None));
        // So does an input file that cannot be opened.
        let other = Scratch::new("cannot-open");
        let ran = run_in(
            &other,
            "cat",
            &[],
            &system(),
            Some(&other.0.join("missing-input")),
            LONG,
        );
        let Ended::Failed(message) = &ran.ended else {
            panic!("{:?}", ran.ended);
        };
        assert!(message.starts_with("cannot open "), "{message}");
        assert_eq!(ran.group, None);
    }

    #[test]
    fn a_log_that_cannot_be_created_ends_with_an_io_error() {
        let scratch = Scratch::new("log");
        // The standard error file of the command exists already.
        scratch.write("logs/0007-fake.stderr", "earlier\n");
        let ran = shell(&scratch, "exit 0", LONG);
        let Ended::Failed(message) = &ran.ended else {
            panic!("{:?}", ran.ended);
        };
        let path = scratch.0.join("logs/0007-fake.stderr");
        assert!(
            message.starts_with(&format!("cannot create {}: ", path.display())),
            "{message}"
        );
        assert_eq!(ran.group, None);
        assert_eq!((ran.stdout, ran.stderr), (None, None));
        assert_eq!(fs::read(&path).unwrap(), b"earlier\n");
    }

    #[test]
    fn a_hangup_that_is_ignored_at_the_start_stays_ignored() {
        if let Some(ignored) = std::env::var_os(INIT) {
            // The test executable, started again with SIGHUP ignored or not.
            init();
            let handled = |signal| !matches!(disposition(signal), libc::SIG_DFL | libc::SIG_IGN);
            assert!(handled(libc::SIGINT) && handled(libc::SIGTERM));
            if ignored == "yes" {
                assert_eq!(disposition(libc::SIGHUP), libc::SIG_IGN);
            } else {
                assert!(handled(libc::SIGHUP));
            }
            return;
        }
        let (_, tests) = module_path!()
            .split_once("::")
            .expect("a module path below the crate");
        let name = format!("{tests}::a_hangup_that_is_ignored_at_the_start_stays_ignored");
        for (ignored, disposition) in [("no", libc::SIG_DFL), ("yes", libc::SIG_IGN)] {
            let mut command = Command::new(std::env::current_exe().expect("the test executable"));
            command
                .args([name.as_str(), "--exact", "--test-threads=1"])
                .env(INIT, ignored)
                .stdin(Stdio::null());
            with_hangup(&mut command, disposition);
            let output = command.output().expect("run the test executable");
            let said = String::from_utf8_lossy(&output.stdout);
            assert!(output.status.success(), "{ignored}: {said}");
            assert!(said.contains("test result: ok. 1 passed"), "{said}");
        }
    }

    #[test]
    fn the_effective_user_owns_what_the_gate_creates() {
        let scratch = Scratch::temporary("owner");
        scratch.write("file", "");
        let meta = fs::metadata(scratch.0.join("file")).expect("the file");
        assert_eq!(std::os::unix::fs::MetadataExt::uid(&meta), effective_uid());
    }

    #[test]
    fn the_disk_available_is_read_for_a_directory_and_not_for_a_missing_path() {
        let scratch = Scratch::temporary("disk");
        assert!(disk_available(&scratch.0).is_some_and(|bytes| bytes > 0));
        assert_eq!(disk_available(&scratch.0.join("missing")), None);
    }

    #[test]
    fn the_largest_collected_child_is_measured() {
        let scratch = Scratch::temporary("rss");
        let ran = shell(&scratch, "exit 0", LONG);
        assert_eq!(ran.ended, Ended::Exited(0));
        // The test process ran other children before, so only a lower
        // bound holds: a process takes at least a page.
        assert!(largest_child_rss().is_some_and(|bytes| bytes >= 4_096));
    }

    #[test]
    fn the_cgroup_memory_peak_is_read_only_under_cgroup_version_2() {
        let peak = cgroup_memory_peak();
        let cgroup = fs::read_to_string("/proc/self/cgroup").unwrap_or_default();
        if !cgroup.lines().any(|line| line.starts_with("0::/")) {
            assert_eq!(peak, None);
        }
        if let Some(bytes) = peak {
            assert!(bytes > 0);
        }
    }
}
