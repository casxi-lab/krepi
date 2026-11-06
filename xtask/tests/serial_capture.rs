//! What only the binary of `cargo xtask serial-capture` shows: the arguments
//! and streams as the process starts with them and its environment. The
//! command's rules are tested in the host tooling crate; these tests start
//! the binary of this build, the one that `cargo xtask` runs, whose
//! repository root is compiled in, so every run names its output directory
//! below the target's temporary directory. A shell closes a descriptor for
//! its `exec`, and a pipe from the standard library stands for one whose
//! reader has gone.

use std::ffi::OsStr;
use std::os::unix::ffi::OsStrExt;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::{Mutex, MutexGuard, PoisonError};

/// The binary of this build.
const XTASK: &str = env!("CARGO_BIN_EXE_xtask");
/// A port that no open finds.
const MISSING_PORT: &str = "/nonexistent/krepi-port";
/// The start of the usage line of clap, which names the command; the help
/// and a usage error hold it.
const USAGE: &[u8] = b"Usage: cargo xtask serial-capture ";
/// The report of a failed write on standard output whose reader has gone.
const BROKEN_PIPE: &str =
    "cargo xtask serial-capture: cannot write standard output: Broken pipe (os error 32)\n";
/// The exit status of a process that a Rust panic ends.
const PANICKED: i32 = 101;

/// Held by a test while it starts the binary. On Darwin a pipe's descriptors
/// become close-on-exec only after the pipe exists, so a process that another
/// test of this binary starts at that moment could keep the read end of a
/// pipe that a test needs without a reader.
static ONE_AT_A_TIME: Mutex<()> = Mutex::new(());

fn one_at_a_time() -> MutexGuard<'static, ()> {
    ONE_AT_A_TIME.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Whether `text` holds [`USAGE`].
fn holds_usage(text: &[u8]) -> bool {
    text.windows(USAGE.len()).any(|window| window == USAGE)
}

/// A directory below the target's temporary directory, removed at its end.
struct Scratch(PathBuf);

impl Scratch {
    #[track_caller]
    fn new(name: &str) -> Self {
        let path = Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("serial-capture-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&path);
        std::fs::create_dir_all(&path).unwrap();
        Scratch(path)
    }

    fn join(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// `xtask serial-capture`.
fn command() -> Command {
    let mut command = Command::new(XTASK);
    command.arg("serial-capture");
    command
}

/// The command with one standard stream closed when the process starts.
#[track_caller]
fn with_a_closed_stream(redirection: &str, args: &[&str]) -> Output {
    Command::new("/bin/sh")
        .arg("-c")
        .arg(format!("exec \"$0\" \"$@\" {redirection}"))
        .arg(XTASK)
        .arg("serial-capture")
        .args(args)
        .output()
        .unwrap()
}

/// A capture of a port that no open finds, which fails its receipt: the
/// arguments for a new output directory.
fn missing_port(output: &Path) -> [&OsStr; 6] {
    [
        OsStr::new("--port"),
        OsStr::new(MISSING_PORT),
        OsStr::new("--seconds"),
        OsStr::new("0.01"),
        OsStr::new("--output-dir"),
        output.as_os_str(),
    ]
}

/// An argument that is not UTF-8 ends the process before the command runs,
/// as it ends every `cargo xtask` command: `std::env::args` panics, and the
/// panic ends the process with status 101 and its message on standard
/// error, without a signal. The output directory is never created.
#[test]
fn an_argument_that_is_not_utf8_ends_the_process_before_the_command_runs() {
    let _alone = one_at_a_time();
    let scratch = Scratch::new("bytes");
    let output = scratch.join("capture");
    let mut not_utf8 = output.as_os_str().as_bytes().to_vec();
    not_utf8.push(0xff);
    let rows: [&[&OsStr]; 3] = [
        &[
            OsStr::new("serial-capture"),
            OsStr::new("--port"),
            OsStr::from_bytes(b"/nonexistent/krepi-\xff"),
            OsStr::new("--output-dir"),
            output.as_os_str(),
        ],
        &[
            OsStr::new("serial-capture"),
            OsStr::new("--port"),
            OsStr::new(MISSING_PORT),
            OsStr::new("--output-dir"),
            OsStr::from_bytes(&not_utf8),
        ],
        &[OsStr::from_bytes(b"docs\xff")],
    ];
    for args in rows {
        let ended = Command::new(XTASK).args(args).output().unwrap();
        assert_eq!(ended.status.code(), Some(PANICKED), "{args:?}: {ended:?}");
        assert_eq!(ended.status.signal(), None, "{args:?}");
        assert_eq!(ended.stdout, b"", "{args:?}");
        let stderr = String::from_utf8_lossy(&ended.stderr);
        assert!(stderr.contains("panicked at"), "{args:?}: {stderr}");
        assert_eq!(
            std::fs::read_dir(&scratch.0).unwrap().count(),
            0,
            "{args:?}"
        );
    }
}

/// With a standard stream closed when the process starts, the command
/// writes nothing on the other stream and keeps its exit status: the
/// standard library reopens the descriptor on `/dev/null` before `main`, so
/// that the writes succeed there and no failed write reaches the exit
/// status. A last run with standard error closed shows that the shell starts
/// the binary and closes only the stream it names.
#[test]
fn a_closed_stream_moves_no_text_to_the_other() {
    let _alone = one_at_a_time();
    let scratch = Scratch::new("closed");
    let existing = scratch.join("existing");
    std::fs::create_dir(&existing).unwrap();
    let existing = existing.to_str().unwrap();
    let output = scratch.join("capture");
    let output = output.to_str().unwrap();
    let failed = [
        "--port",
        MISSING_PORT,
        "--seconds",
        "0.01",
        "--output-dir",
        output,
    ];
    let refused = ["--port", MISSING_PORT, "--output-dir", existing];
    for (redirection, args, code) in [
        (">&-", &["--help"][..], 0),
        (">&-", &failed, 2),
        ("2>&-", &["--bogus"], 2),
        ("2>&-", &refused, 2),
    ] {
        let ended = with_a_closed_stream(redirection, args);
        assert_eq!(ended.status.code(), Some(code), "{redirection} {args:?}");
        assert!(
            ended.stdout.is_empty() && ended.stderr.is_empty(),
            "{redirection} {args:?}: {ended:?}"
        );
    }
    assert!(Path::new(output).join("summary.json").is_file());
    assert_eq!(std::fs::read_dir(existing).unwrap().count(), 0);
    let ended = with_a_closed_stream("2>&-", &["--help"]);
    assert_eq!(ended.status.code(), Some(0), "{ended:?}");
    assert!(holds_usage(&ended.stdout), "{ended:?}");
}

/// A write that fails on a real stream, a pipe whose reader has gone, makes
/// the exit status of the process 120 and is reported on standard error,
/// after a capture too, whose files are written by then; on standard error
/// it makes the status 120 with nothing to report it on.
#[test]
fn a_stream_whose_reader_has_gone_makes_the_exit_status_120() {
    let _alone = one_at_a_time();
    let scratch = Scratch::new("reader");
    let broken = || {
        let (reader, writer) = std::io::pipe().unwrap();
        drop(reader);
        Stdio::from(writer)
    };
    let ended = command().arg("--help").stdout(broken()).output().unwrap();
    assert_eq!(ended.status.code(), Some(120), "{ended:?}");
    assert_eq!(String::from_utf8_lossy(&ended.stderr), BROKEN_PIPE);
    let output = scratch.join("capture");
    let ended = command()
        .args(missing_port(&output))
        .stdout(broken())
        .output()
        .unwrap();
    assert_eq!(ended.status.code(), Some(120), "{ended:?}");
    assert_eq!(String::from_utf8_lossy(&ended.stderr), BROKEN_PIPE);
    assert!(output.join("summary.json").is_file());
    let ended = command().arg("--bogus").stderr(broken()).output().unwrap();
    assert_eq!(ended.status.code(), Some(120), "{ended:?}");
    assert_eq!(ended.stdout, b"");
}

/// On a pipe, too, the help and the usage do not follow the variables that
/// set a width or ask for colour: their text is the same with `COLUMNS=40`,
/// `FORCE_COLOR=1`, `PYTHON_COLORS=1` and `CLICOLOR_FORCE=1` as without
/// them, and has no escape byte.
#[test]
fn the_help_and_the_usage_keep_their_text_on_a_pipe() {
    let _alone = one_at_a_time();
    for arg in ["--help", "--bogus"] {
        let plain = command().arg(arg).env_clear().output().unwrap();
        let varied = command()
            .arg(arg)
            .env_clear()
            .env("COLUMNS", "40")
            .env("FORCE_COLOR", "1")
            .env("PYTHON_COLORS", "1")
            .env("CLICOLOR_FORCE", "1")
            .output()
            .unwrap();
        assert_eq!(varied, plain, "{arg}");
        let text = if arg == "--help" {
            &plain.stdout
        } else {
            &plain.stderr
        };
        assert!(holds_usage(text), "{arg}: {plain:?}");
        assert!(!text.contains(&0x1b), "{arg}: {plain:?}");
    }
}

/// The command lists, helps and captures with an empty environment, away
/// from the repository, and with variables of a language environment that
/// it ignores, such as a `VIRTUAL_ENV` and a `PATH` that leads nowhere.
#[test]
fn the_command_runs_with_an_empty_environment_outside_the_repository() {
    let _alone = one_at_a_time();
    let scratch = Scratch::new("environment");
    let ended = command()
        .arg("--list")
        .current_dir(&scratch.0)
        .env_clear()
        .output()
        .unwrap();
    assert_eq!(ended.status.code(), Some(0), "{ended:?}");
    assert_eq!(ended.stderr, b"", "{ended:?}");
    let ended = command()
        .arg("--help")
        .current_dir(&scratch.0)
        .env_clear()
        .env("VIRTUAL_ENV", "/nonexistent/environment")
        .env("PATH", "/nonexistent")
        .output()
        .unwrap();
    assert_eq!(ended.status.code(), Some(0), "{ended:?}");
    assert_eq!(ended.stderr, b"", "{ended:?}");
    assert!(holds_usage(&ended.stdout), "{ended:?}");
    let output = scratch.join("capture");
    let ended = command()
        .args(missing_port(&output))
        .current_dir(&scratch.0)
        .env_clear()
        .output()
        .unwrap();
    assert_eq!(ended.status.code(), Some(2), "{ended:?}");
    assert_eq!(ended.stderr, b"", "{ended:?}");
    let stdout = String::from_utf8_lossy(&ended.stdout);
    assert!(
        stdout.starts_with("FAIL: 0 bytes; board boot is not evaluated.\n"),
        "{stdout}"
    );
    assert!(output.join("summary.json").is_file());
}
