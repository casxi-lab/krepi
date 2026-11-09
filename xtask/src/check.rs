//! `cargo xtask check`: the required host checks, in two segments of lanes
//! that stop together.
//!
//! The first segment is the lint lane: the toolchain, manifest, format and
//! Clippy steps, one after another. Once it has passed, the second segment
//! starts its lanes at once, and each lane runs its steps one after another:
//! the debug lane holds the tests of every workspace and the documentation,
//! Lean source, provable-subset and workflow checks; the release lane holds
//! the tests of the kernel and user-space workspaces in the release profile;
//! the formal lane has no step yet. `--sequential` runs every step in one
//! lane instead, in the order of [`steps`], which is also the order of the
//! summary and of the receipt; each step keeps its lane there.
//!
//! Once a step fails, or SIGINT, SIGTERM or SIGHUP (unless it is ignored)
//! reaches the check, no further step or command starts. A running command
//! of a step that runs commands is killed with its process group, and its
//! step is recorded as cancelled. A check written in this crate runs inside
//! the check process, and the commands it starts run in the process group of
//! the check: one that is running is not stopped, finishes and keeps its own
//! result. The runner is in [`lanes`].
//!
//! The check ends with a summary table, one row per step with its segment,
//! lane, status, start and seconds, writes the receipt if one was asked for
//! ([`crate::receipt`]) and exits with 0 when every step passed, 1 when a
//! step failed or the receipt could not be written, and 128 plus the number
//! of the stop signal when one reached it before the summary, which takes
//! precedence; a stop signal that arrives later is ignored.
//!
//! `--slow` also runs the slow tests of every workspace: those marked
//! `#[ignore = "slow"]`, whose names start with [`SLOW`].

#[cfg(test)]
mod ci;
mod lanes;

use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Duration;

use clap::{Arg, ArgAction, value_parser};
use yaml_rust2::YamlLoader;

use crate::formal::{Layout, lean, process, toolchain as tools};
use crate::repo::{Entry, Tree};
use crate::{docs, manifests, receipt, subset, toolchain, workflows};

/// The Cargo workspaces that the format, Clippy and test steps cover, as
/// repository-relative directories.
pub const WORKSPACES: [&str; 4] = ["kernel", "user", "xtask", "tools"];

/// The workspaces that the release tests cover: the kernel and user-space
/// workspaces, from which the kernel and user-space images are to be built.
pub const RELEASE_WORKSPACES: [&str; 2] = ["kernel", "user"];

/// The bare-metal target of the kernel images, for which the Clippy step
/// also lints the kernel workspace.
pub const TARGET: &str = "aarch64-unknown-none-softfloat";

/// The start of the name of a slow test, which `--slow` passes to libtest as
/// the filter of the ignored tests.
pub const SLOW: &str = "slow_";

/// The directory below the repository root in which each run creates the
/// directory of its step logs.
pub const LOGS: &str = "artifacts/check";

/// A command run in the repository root.
#[derive(Debug, Clone)]
pub struct Cmd {
    pub program: OsString,
    pub args: Vec<String>,
}

/// Named values that a step observed, in the order it observed them, for the
/// receipt. A step adds them as it goes, so they are kept when it fails.
pub type Facts = Vec<(String, String)>;

/// A check written in this crate, run with the repository root. Lanes run on
/// threads of their own, so a check can be shared with them.
pub type Check = Box<dyn Fn(&Path, &mut Facts) -> Result<(), String> + Send + Sync>;

/// What a step does.
pub enum Action {
    /// Run commands in order; each must exit with status 0.
    Commands(Vec<Cmd>),
    /// Run a check written in this crate.
    Internal(Check),
}

/// A lane of the check: a sequence of steps that runs beside the other lanes
/// of its segment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Lane {
    Lint,
    Debug,
    Release,
    Formal,
}

impl Lane {
    /// Every lane, in the order of the summary and the receipt.
    pub const ALL: [Lane; 4] = [Lane::Lint, Lane::Debug, Lane::Release, Lane::Formal];

    /// The name of the lane in the output and the receipt.
    pub fn name(self) -> &'static str {
        match self {
            Lane::Lint => "lint",
            Lane::Debug => "debug",
            Lane::Release => "release",
            Lane::Formal => "formal",
        }
    }

    /// The segment of the lane: the lint lane runs first, alone, and the
    /// other lanes run after it, at once.
    pub fn segment(self) -> u32 {
        match self {
            Lane::Lint => 1,
            Lane::Debug | Lane::Release | Lane::Formal => 2,
        }
    }
}

/// How the check runs its steps.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// The lanes of a segment at once.
    Parallel,
    /// Every step in one lane, in order.
    Sequential,
}

impl Mode {
    /// The name of the mode in the output and the receipt.
    pub fn name(self) -> &'static str {
        match self {
            Mode::Parallel => "parallel",
            Mode::Sequential => "sequential",
        }
    }
}

/// A named step of the check, in its lane.
pub struct Step {
    pub name: &'static str,
    pub lane: Lane,
    pub action: Action,
}

/// How a step ended.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Status {
    /// The step passed.
    Passed,
    /// The step failed, and why.
    Failed(String),
    /// The check stopped while the step ran, and why: the step that failed
    /// or the stop signal. Its running command was killed with its group, or
    /// its next command did not start.
    Cancelled(String),
    /// The check stopped before the step started.
    NotRun,
}

impl Status {
    /// The name of the status in the output and the receipt.
    pub fn name(&self) -> &'static str {
        match self {
            Status::Passed => "passed",
            Status::Failed(_) => "failed",
            Status::Cancelled(_) => "cancelled",
            Status::NotRun => "not run",
        }
    }
}

/// The result of one step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Outcome {
    pub step: &'static str,
    pub lane: Lane,
    pub status: Status,
    /// The time from the start of the check to the start of the step, or
    /// `None` for a step that did not run.
    pub offset: Option<Duration>,
    pub duration: Duration,
    pub facts: Facts,
}

/// A lane with the names of its steps, in order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LaneSteps {
    pub lane: Lane,
    pub steps: Vec<&'static str>,
}

/// Every lane of [`Lane::ALL`] with the steps of `steps` in it; a lane
/// without steps, such as the formal lane today, is listed with none.
pub fn layout(steps: &[Step]) -> Vec<LaneSteps> {
    Lane::ALL
        .iter()
        .map(|&lane| LaneSteps {
            lane,
            steps: (steps.iter().filter(|step| step.lane == lane))
                .map(|step| step.name)
                .collect(),
        })
        .collect()
}

/// How a run ended.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    Passed,
    Failed,
    /// A stop signal reached the check, with its number.
    Interrupted(i32),
}

impl Verdict {
    /// The name of the verdict in the receipt.
    pub fn name(self) -> &'static str {
        match self {
            Verdict::Passed => "passed",
            Verdict::Failed => "failed",
            Verdict::Interrupted(_) => "interrupted",
        }
    }
}

/// A finished run, as the summary and the receipt record it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Report {
    pub mode: Mode,
    pub slow: bool,
    pub layout: Vec<LaneSteps>,
    /// One outcome per step, in the order of the steps.
    pub outcomes: Vec<Outcome>,
    /// The time from the start of the first step until the last one ended.
    pub elapsed: Duration,
    /// The stop signal that reached the check by the time the report was
    /// made, once its steps had ended and before the summary.
    pub signal: Option<i32>,
}

impl Report {
    /// `Interrupted` whenever a stop signal reached the check, whatever the
    /// steps did; otherwise `Passed` only if every step passed.
    pub fn verdict(&self) -> Verdict {
        match self.signal {
            Some(signal) => Verdict::Interrupted(signal),
            None if (self.outcomes.iter()).all(|outcome| outcome.status == Status::Passed) => {
                Verdict::Passed
            }
            None => Verdict::Failed,
        }
    }
}

/// The name of `signal`, such as `SIGTERM`.
pub fn signal_name(signal: i32) -> String {
    signal_hook::low_level::signal_name(signal)
        .map_or_else(|| format!("signal {signal}"), str::to_string)
}

/// The Cargo that the steps run: `CARGO`, which Cargo sets for the commands it
/// runs, or else `cargo` from the search path.
pub fn cargo() -> OsString {
    std::env::var_os("CARGO").unwrap_or_else(|| "cargo".into())
}

/// The same Cargo command for each of `workspaces`.
fn per_workspace(workspaces: &[&str], args: &[&str], trailing: &[&str]) -> Vec<Cmd> {
    workspaces
        .iter()
        .map(|workspace| {
            let mut all: Vec<String> = args.iter().map(|arg| arg.to_string()).collect();
            all.push("--manifest-path".into());
            all.push(format!("{workspace}/Cargo.toml"));
            all.extend(trailing.iter().map(|arg| arg.to_string()));
            Cmd {
                program: cargo(),
                args: all,
            }
        })
        .collect()
}

/// Clippy on every member of the kernel workspace for [`TARGET`], with
/// warnings as errors: the library, binary and example targets, which are
/// the targets that build for it, so that the modules compiled only for the
/// bare-metal target are linted as well. The tests need the standard library
/// and are linted by the host Clippy only.
fn target_clippy() -> Cmd {
    let args = [
        "clippy",
        "--manifest-path",
        "kernel/Cargo.toml",
        "--workspace",
        "--lib",
        "--bins",
        "--examples",
        "--locked",
        "--target",
        TARGET,
        "--",
        "-D",
        "warnings",
    ];
    Cmd {
        program: cargo(),
        args: args.map(str::to_string).to_vec(),
    }
}

/// The steps of `cargo xtask check`, in the order in which `--sequential`
/// runs them, each in its lane; with `slow`, the test step also runs the slow
/// tests of each workspace, after the other tests of every workspace.
pub fn steps(slow: bool) -> Vec<Step> {
    let internal = |name, lane, check: Check| Step {
        name,
        lane,
        action: Action::Internal(check),
    };
    let commands = |name, lane, commands| Step {
        name,
        lane,
        action: Action::Commands(commands),
    };
    let test = ["test", "--workspace", "--locked"];
    let mut tests = per_workspace(&WORKSPACES, &test, &[]);
    if slow {
        tests.extend(per_workspace(
            &WORKSPACES,
            &test,
            &["--", "--ignored", SLOW],
        ));
    }
    let release = ["test", "--release", "--workspace", "--locked"];
    let mut clippy = per_workspace(
        &WORKSPACES,
        &["clippy", "--workspace", "--all-targets", "--locked"],
        &["--", "-D", "warnings"],
    );
    clippy.push(target_clippy());
    vec![
        internal("toolchain", Lane::Lint, Box::new(toolchain::run)),
        internal(
            "manifests",
            Lane::Lint,
            Box::new(|root, _| manifests::run(root)),
        ),
        commands(
            "fmt",
            Lane::Lint,
            per_workspace(&WORKSPACES, &["fmt", "--all", "--check"], &[]),
        ),
        commands("clippy", Lane::Lint, clippy),
        commands("test", Lane::Debug, tests),
        commands(
            "test-release",
            Lane::Release,
            per_workspace(&RELEASE_WORKSPACES, &release, &[]),
        ),
        internal("docs", Lane::Debug, Box::new(|root, _| docs::run(root))),
        internal("lean", Lane::Debug, Box::new(|root, _| check_lean(root))),
        internal("subset", Lane::Debug, Box::new(subset::run)),
        internal("workflows", Lane::Debug, Box::new(check_workflows)),
    ]
}

/// The workflows step on the tracked files; the files it read become facts.
fn check_workflows(root: &Path, facts: &mut Facts) -> Result<(), String> {
    let tree = Tree::load(root)?;
    let tracked = || {
        tree.entries().map(|(path, entry)| match entry {
            Entry::File(bytes) => (path, Some(bytes.as_slice())),
            Entry::Symlink(_) | Entry::Submodule => (path, None),
        })
    };
    let files: Vec<&str> = tracked()
        .map(|(path, _)| path)
        .filter(|path| workflows::is_workflow(path))
        .collect();
    if files.is_empty() {
        println!("workflows: no workflow files");
    } else {
        println!("workflows: {}", files.join(", "));
    }
    facts.push(("files".to_string(), files.join(", ")));
    let mut problems = workflows::check(tracked());
    problems.extend(image_problems(&tree));
    problems.extend(cache_problems(&tree));
    if problems.is_empty() {
        Ok(())
    } else {
        Err(problems.join("\n"))
    }
}

/// The problems of the image references in the workflows of `tree` that run
/// on pull requests, against its image pin.
pub fn image_problems(tree: &Tree) -> Vec<String> {
    let pull = |file: &(&str, &str)| workflows::runs_on_pull_request(file.1);
    let files = tree
        .texts()
        .filter(|file| workflows::is_workflow(file.0) && pull(file));
    let pin = tree.text(Layout::PRODUCTION.image_pin).unwrap_or_default();
    tools::image_references(pin, &files.collect::<Vec<_>>())
}

/// The actions that save a cache: `actions/cache` saves one when its job
/// ends, and `actions/cache/save` saves one in its step.
pub const CACHE_SAVES: [&str; 2] = ["actions/cache", "actions/cache/save"];

/// The problems of the caches in the workflows of `tree` that run on pull
/// requests, or whose triggers cannot be read: no step uses an action of
/// [`CACHE_SAVES`], at any pin, so that such a job only restores a cache,
/// with `actions/cache/restore`. Both the `uses` of each step, as YAML
/// decodes it, and the text of the file, comments included, are read, in
/// any letter case, so that neither an escape nor a comment hides a use.
pub fn cache_problems(tree: &Tree) -> Vec<String> {
    // The actions of [`CACHE_SAVES`] that `text` names with a pin, and those
    // that it starts with.
    let named = |text: &str| {
        let text = text.to_ascii_lowercase();
        (CACHE_SAVES.into_iter()).filter(move |action| text.contains(&format!("{action}@")))
    };
    let used = |uses: &str| {
        let uses = uses.to_ascii_lowercase();
        (CACHE_SAVES.into_iter()).filter(move |action| uses.starts_with(&format!("{action}@")))
    };
    let saves = |action: &str| {
        format!("{action}, which saves a cache, in a workflow that runs on pull_request")
    };
    let mut problems = Vec::new();
    let files = (tree.texts()).filter(|(path, text)| {
        workflows::is_workflow(path) && workflows::runs_on_pull_request(text)
    });
    for (path, text) in files {
        for (at, line) in text.lines().enumerate() {
            for action in named(line) {
                problems.push(format!("{path}:{}: names {}", at + 1, saves(action)));
            }
        }
        let documents = YamlLoader::load_from_str(text).unwrap_or_default();
        let jobs = (documents.iter())
            .filter_map(|document| document["jobs"].as_hash())
            .flatten();
        for (key, job) in jobs {
            let key = key.as_str().unwrap_or_default();
            let uses = (job["steps"].as_vec().into_iter().flatten())
                .filter_map(|step| step["uses"].as_str());
            for action in uses.flat_map(used) {
                problems.push(format!(
                    "{path}: job `{key}` uses {}; such a job restores a cache with \
                     actions/cache/restore",
                    saves(action)
                ));
            }
        }
    }
    problems
}

/// The `lean` step on the tracked files: the source rules of the
/// hand-written Lean.
fn check_lean(root: &Path) -> Result<(), String> {
    let problems = lean_problems(&Tree::load(root)?, &Layout::PRODUCTION);
    if problems.is_empty() {
        Ok(())
    } else {
        Err(problems.join("\n"))
    }
}

/// The problems of the source rules in the tracked Lean files of the Lake
/// project in `tree`, each of which must be a UTF-8 regular file, with the
/// items of its `tcb.json`, which must be read.
pub fn lean_problems(tree: &Tree, layout: &Layout) -> Vec<String> {
    let unread = || "it is not a tracked UTF-8 regular file".to_string();
    let tcb = tree.text(layout.tcb).ok_or_else(unread);
    let (items, mut problems) = match tcb.and_then(lean::load_tcb) {
        Ok(items) => (items, Vec::new()),
        Err(error) => (Vec::new(), vec![format!("{}: {error}", layout.tcb)]),
    };
    let project = format!("{}/", layout.project);
    let file = |path: &&str| path.starts_with(&project) && path.ends_with(".lean");
    for (path, _) in tree.entries().filter(|(path, _)| file(path)) {
        match tree.text(path) {
            Some(text) => problems.extend(lean::source_problems(path, text, &items, layout)),
            None => problems.push(format!("{path}: {}", unread())),
        }
    }
    problems
}

/// The first failed step in the order of the steps and why it failed, if
/// one did.
pub fn failure(outcomes: &[Outcome]) -> Option<(&'static str, &str)> {
    outcomes.iter().find_map(|outcome| match &outcome.status {
        Status::Failed(detail) => Some((outcome.step, detail.as_str())),
        _ => None,
    })
}

/// The summary table of a run: a line with the mode, the elapsed seconds and
/// `logs`, which says where the step logs are, then one row per step in the
/// order of the steps, with its segment, lane, status, start and seconds
/// from the start of the check (`-` for a step that did not run), and a row
/// for each lane without steps.
pub fn summary(report: &Report, logs: &str) -> String {
    let longest = report.outcomes.iter().map(|outcome| outcome.step.len());
    let width = longest.max().unwrap_or(0).max("step".len()) + 2;
    let row = |cells: [&str; 6]| {
        let [segment, lane, step, status, start, seconds] = cells;
        let line = format!("{segment:<9}{lane:<9}{step:<width$}{status:<10}{start:>6}{seconds:>9}");
        format!("{}\n", line.trim_end())
    };
    let seconds = |duration: Duration| format!("{:.1}", duration.as_secs_f64());
    let mut text = format!(
        "summary: {}, {} s; {logs}\n",
        report.mode.name(),
        seconds(report.elapsed)
    );
    text.push_str(&row([
        "segment", "lane", "step", "status", "start", "seconds",
    ]));
    for outcome in &report.outcomes {
        let (start, took) = match outcome.offset {
            Some(offset) => (seconds(offset), seconds(outcome.duration)),
            None => ("-".to_string(), "-".to_string()),
        };
        let segment = outcome.lane.segment().to_string();
        let lane = outcome.lane.name();
        text.push_str(&row([
            &segment,
            lane,
            outcome.step,
            outcome.status.name(),
            &start,
            &took,
        ]));
    }
    for empty in report.layout.iter().filter(|lane| lane.steps.is_empty()) {
        let segment = empty.lane.segment().to_string();
        text.push_str(&row([
            &segment,
            empty.lane.name(),
            "(no steps)",
            "",
            "",
            "",
        ]));
    }
    text
}

/// The last line of a run, after the summary: on standard output (`Ok`)
/// when the check passed or was interrupted, on standard error (`Err`) with
/// the detail of the failed step before it when it failed.
pub fn ending(report: &Report) -> Result<String, String> {
    match report.verdict() {
        Verdict::Passed => Ok("check passed\n".to_string()),
        Verdict::Interrupted(signal) => {
            Ok(format!("check interrupted by {}\n", signal_name(signal)))
        }
        Verdict::Failed => Err(match failure(&report.outcomes) {
            Some((step, detail)) => format!("{detail}\ncheck failed at step {step}\n"),
            None => "check failed\n".to_string(),
        }),
    }
}

/// The exit status of a run: 128 plus the number of the stop signal of an
/// interrupted run, which takes precedence; otherwise 1 when a step failed
/// or the receipt that was asked for could not be written, and 0 when the
/// check passed.
pub fn exit_code(verdict: Verdict, receipt_written: bool) -> u8 {
    match verdict {
        Verdict::Interrupted(signal) => u8::try_from(128 + signal).unwrap_or(u8::MAX),
        Verdict::Failed => 1,
        Verdict::Passed if receipt_written => 0,
        Verdict::Passed => 1,
    }
}

/// The options of `cargo xtask check`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Options {
    pub sequential: bool,
    pub slow: bool,
    pub receipt: Option<PathBuf>,
}

/// The command line of `cargo xtask check`.
fn cli() -> clap::Command {
    let about = (crate::COMMANDS.iter())
        .find(|command| command.name == "check")
        .map_or("", |command| command.about);
    clap::Command::new("check")
        .bin_name("cargo xtask check")
        .about(about)
        .arg(
            Arg::new("sequential")
                .long("sequential")
                .help("Run every step in one lane, in order, and stop at the first failure")
                .action(ArgAction::SetTrue),
        )
        .arg(
            Arg::new("slow")
                .long("slow")
                .help("Also run the slow tests, those marked #[ignore = \"slow\"]")
                .action(ArgAction::SetTrue),
        )
        .arg(
            Arg::new("receipt")
                .long("receipt")
                .value_name("PATH")
                .help(
                    "Write a JSON receipt of the run to PATH, whether the check passes, fails or \
                     is interrupted",
                )
                .value_parser(value_parser!(PathBuf)),
        )
}

/// The arguments of the check when `args`, the arguments of `cargo xtask`,
/// name it: `check` with options of the check after it, before it or both,
/// in any order. The options before `check` come first, and the value of an
/// option that takes one is not read as the command, so that
/// `cargo xtask --receipt check check` writes the receipt `check`. `None`
/// when no `check` follows the options of the check that start `args`.
pub fn arguments<'a>(args: &[&'a str]) -> Option<Vec<&'a str>> {
    let cli = cli();
    let mut at = 0;
    loop {
        let arg = *args.get(at)?;
        if arg == "check" {
            return Some([&args[..at], &args[at + 1..]].concat());
        }
        let name = arg.strip_prefix("--")?;
        let (long, inline) = (name.split_once('=')).map_or((name, false), |(long, _)| (long, true));
        let option = (cli.get_arguments()).find(|option| option.get_long() == Some(long))?;
        at += if option.get_action().takes_values() && !inline {
            2
        } else {
            1
        };
    }
}

/// The options in `args`, the arguments of the check that [`arguments`]
/// gives.
fn options(args: &[&str]) -> Result<Options, clap::Error> {
    let matches =
        cli().try_get_matches_from(std::iter::once("check").chain(args.iter().copied()))?;
    Ok(Options {
        sequential: matches.get_flag("sequential"),
        slow: matches.get_flag("slow"),
        receipt: matches.get_one::<PathBuf>("receipt").cloned(),
    })
}

/// Entry point of `cargo xtask check`, with the arguments of the check that
/// [`arguments`] gives. `--help` prints the help and exits with 0, and a
/// usage error exits with 2.
pub fn command(root: PathBuf, args: &[&str]) -> ExitCode {
    match options(args) {
        Err(error) => {
            let _ = error.print();
            ExitCode::from(u8::try_from(error.exit_code()).unwrap_or(2))
        }
        Ok(options) => ExitCode::from(run(&root, &options, &steps(options.slow))),
    }
}

/// Creates the directory of the step logs of a new run below `root`.
fn create_logs(root: &Path) -> Result<PathBuf, String> {
    let name = format!(
        "{}-{}",
        krepi_tools::report::utc_stamp(),
        std::process::id()
    );
    let dir = root.join(LOGS).join(name);
    match fs::create_dir_all(&dir) {
        Ok(()) => Ok(dir),
        Err(error) => Err(format!("cannot create {}: {error}", dir.display())),
    }
}

/// Runs `steps` in `root` with `options`, prints the summary, writes the
/// receipt if one was asked for and returns the exit status. A stop signal
/// that arrives from before the first step until the report is made, once
/// the steps have ended and the Git state after them has been read, stops
/// the check instead of ending it; one that arrives later, while the summary
/// is printed or the receipt written, is ignored.
pub fn run(root: &Path, options: &Options, steps: &[Step]) -> u8 {
    process::init();
    let git = || {
        options
            .receipt
            .as_ref()
            .map(|_| receipt::GitState::read(root))
    };
    let before = git();
    let logs = create_logs(root);
    let mode = if options.sequential {
        Mode::Sequential
    } else {
        Mode::Parallel
    };
    let ran = lanes::run(root, steps, mode, logs.as_deref().map_err(String::as_str));
    let after = git();
    let report = Report {
        mode,
        slow: options.slow,
        layout: layout(steps),
        outcomes: ran.outcomes,
        elapsed: ran.elapsed,
        signal: process::stop_signal(),
    };
    let logs = match &logs {
        Ok(dir) => format!(
            "step logs in {}",
            dir.strip_prefix(root).unwrap_or(dir).display()
        ),
        Err(error) => format!("no step logs: {error}"),
    };
    print!("{}", summary(&report, &logs));
    match ending(&report) {
        Ok(line) => print!("{line}"),
        Err(lines) => eprint!("{lines}"),
    }
    let mut written = true;
    if let (Some(path), Some(before), Some(after)) = (&options.receipt, before, after) {
        let text = receipt::render(&before, &after, &report, &receipt::Environment::read());
        match receipt::write(path, &text) {
            Ok(()) => println!("receipt written to {}", path.display()),
            Err(error) => {
                eprintln!("cannot write the receipt {}: {error}", path.display());
                written = false;
            }
        }
    }
    exit_code(report.verdict(), written)
}

#[cfg(test)]
mod tests {
    use std::fs::File;
    use std::process::{Command, Stdio};
    use std::time::Instant;

    use serde_json::Value;
    use syn::visit::Visit;

    use super::*;
    use crate::formal::process::tests::{probe, with_hangup};
    use crate::scratch::Scratch;

    /// The steps in the order in which `--sequential` runs them.
    pub(super) const ORDER: [&str; 10] = [
        "toolchain",
        "manifests",
        "fmt",
        "clippy",
        "test",
        "test-release",
        "docs",
        "lean",
        "subset",
        "workflows",
    ];

    /// The variable that makes the process of a test the check that the
    /// test stops, in the directory that it names.
    const STOPPED: &str = "KREPI_XTASK_CHECK_STOP";

    #[test]
    fn the_committed_workflows_pull_the_pinned_image() {
        let mut tree = Tree::load(&crate::repo::root()).expect("the tracked files");
        assert_eq!(image_problems(&tree), Vec::<String>::new());
        let pin = Layout::PRODUCTION.image_pin;
        let text = tree.text(pin).expect("the pin is tracked").to_string();
        let (_, pinned) = tools::image_pin(&text).expect("the pin reads");
        // A workflow that runs on pull requests only, or on push only.
        let workflow =
            |on: &str, image: &str| format!("on: {on}\njobs:\n  j:\n    image: {image}\n");
        let (repository, digest) = pinned.split_once('@').expect("a digest");
        let tag = format!("{repository}:latest");
        tree.insert(
            ".github/workflows/push.yml",
            Entry::File(workflow("push", &tag).into()),
        );
        tree.insert("docs/image.md", Entry::File(tag.clone().into()));
        assert_eq!(image_problems(&tree), Vec::<String>::new());
        let path = ".github/workflows/z.yml";
        tree.insert(path, Entry::File(workflow("pull_request", &tag).into()));
        assert_eq!(image_problems(&tree), [format!("{path}:4: not {pinned}")]);
        // Another pin than the one the workflows name.
        let other = text.replace(&digest[7..], &"0".repeat(64));
        tree.insert(path, Entry::File(workflow("pull_request", &pinned).into()));
        tree.insert(pin, Entry::File(other.clone().into()));
        let problems = image_problems(&tree);
        let (_, reference) = tools::image_pin(&other).expect("the other pin reads");
        assert!(
            problems.contains(&format!("no workflow names {reference}")),
            "{problems:?}"
        );
        assert!(
            problems.contains(&format!("{path}:4: not {reference}")),
            "{problems:?}"
        );
        // No pull request workflow names the image.
        let mut tree = Tree::from_files(&[(pin, &text), (".github/workflows/a.yml", "on: push\n")]);
        assert_eq!(
            image_problems(&tree),
            [format!("no workflow names {pinned}")]
        );
        tree.insert(pin, Entry::Symlink("elsewhere".to_string()));
        assert_eq!(image_problems(&tree).len(), 1);
    }

    #[test]
    fn the_workflows_step_checks_the_image_references() {
        // A repository that tracks the committed pin and the committed
        // workflow of the gate, which names the pinned image or a tag of it.
        let root = crate::repo::root();
        let scratch = Scratch::temporary("workflows");
        let pin = Layout::PRODUCTION.image_pin;
        let text = std::fs::read_to_string(root.join(pin)).expect("the pin");
        let (repository, pinned) = tools::image_pin(&text).expect("the pin reads");
        let path = ".github/workflows/formal.yml";
        let workflow = std::fs::read_to_string(root.join(path)).expect("the workflow");
        assert!(workflow.contains(&pinned), "{path} names {pinned}");
        scratch.write(pin, &text);
        let git = |args: &[&str]| {
            let status = Command::new("git")
                .args(args)
                .current_dir(&scratch.0)
                .env("GIT_CONFIG_NOSYSTEM", "1")
                .env("GIT_CONFIG_GLOBAL", "/dev/null")
                .status()
                .expect("run git");
            assert!(status.success(), "git {args:?}");
        };
        git(&["init", "--quiet"]);
        let tag = format!("{repository}:latest");
        for image in [pinned.as_str(), tag.as_str()] {
            scratch.write(path, &workflow.replace(&pinned, image));
            git(&["add", "--all"]);
            let mut facts = Facts::new();
            let result = check_workflows(&scratch.0, &mut facts);
            assert_eq!(facts, [("files".to_string(), path.to_string())]);
            if image == pinned {
                assert_eq!(result, Ok(()));
            } else {
                let problems = result.expect_err("a tag fails the step");
                assert!(problems.contains(&format!("no workflow names {pinned}")));
                let line = workflow.lines().position(|line| line.contains(&pinned));
                let line = line.expect("the line of the reference") + 1;
                let named = format!("{path}:{line}: not {pinned}");
                assert!(
                    problems.lines().any(|problem| problem == named),
                    "{problems}"
                );
            }
        }
    }

    #[test]
    fn cache_problems_reject_a_save_in_a_pull_request_workflow() {
        let tree = Tree::load(&crate::repo::root()).expect("the tracked files");
        assert_eq!(cache_problems(&tree), Vec::<String>::new());
        let path = ".github/workflows/a.yml";
        let sha = "0123456789abcdef0123456789abcdef01234567";
        let workflow = |on: &str, uses: &str| {
            format!("on: {on}\njobs:\n  j:\n    steps:\n      - uses: {uses}\n")
        };
        let problems =
            |text: &str| cache_problems(&Tree::from_files(&[(path, text), ("README.md", text)]));
        let saves = "which saves a cache, in a workflow that runs on pull_request";
        let named = |line: usize, action: &str| format!("{path}:{line}: names {action}, {saves}");
        let used = |action: &str| {
            format!(
                "{path}: job `j` uses {action}, {saves}; such a job restores a cache with \
                 actions/cache/restore"
            )
        };
        for action in CACHE_SAVES {
            let uses = format!("{action}@{sha}");
            let both = [named(5, action), used(action)];
            assert_eq!(problems(&workflow("pull_request", &uses)), both);
            assert_eq!(problems(&workflow("[push, pull_request]", &uses)), both);
            assert_eq!(problems(&workflow("Pull_Request", &uses)), both);
            let upper = uses.to_ascii_uppercase();
            assert_eq!(problems(&workflow("pull_request", &upper)), both);
            // A workflow whose triggers cannot be read counts as one that
            // runs on pull requests.
            assert_eq!(problems(&workflow("", &uses)), both);
            // A workflow that does not run on pull requests may save.
            assert_eq!(problems(&workflow("push", &uses)), Vec::<String>::new());
            assert_eq!(
                problems(&workflow(
                    "{push: {branches: [main]}, schedule: [{cron: '1 2 * * *'}]}",
                    &uses
                )),
                Vec::<String>::new()
            );
        }
        // Restoring is what a pull request workflow does.
        let restore = format!("actions/cache/restore@{sha}");
        assert_eq!(
            problems(&workflow("pull_request", &restore)),
            Vec::<String>::new()
        );
        // A comment counts, and so does a use that an escape hides.
        let comment = format!(
            "on: pull_request\n# then actions/cache/save@{sha}\njobs:\n  j:\n    steps:\n      \
             - uses: {restore}\n"
        );
        assert_eq!(problems(&comment), [named(2, "actions/cache/save")]);
        let escaped = format!(
            "on: pull_request\njobs:\n  j:\n    steps:\n      - uses: \"actions/cache\\x2Fsave@{sha}\"\n"
        );
        assert_eq!(problems(&escaped), [used("actions/cache/save")]);
    }

    #[test]
    fn the_workflows_step_rejects_a_cache_save_in_a_pull_request_workflow() {
        // A repository with the committed pin and the committed workflow of
        // the gate, as in the test of the image references, and a workflow
        // that runs on pull requests and uses a cache.
        let root = crate::repo::root();
        let scratch = Scratch::temporary("workflows-cache");
        let pin = Layout::PRODUCTION.image_pin;
        let formal = ".github/workflows/formal.yml";
        for file in [pin, formal] {
            let text = std::fs::read_to_string(root.join(file)).expect("a committed file");
            scratch.write(file, &text);
        }
        let git = |args: &[&str]| {
            let status = Command::new("git")
                .args(args)
                .current_dir(&scratch.0)
                .env("GIT_CONFIG_NOSYSTEM", "1")
                .env("GIT_CONFIG_GLOBAL", "/dev/null")
                .status()
                .expect("run git");
            assert!(status.success(), "git {args:?}");
        };
        git(&["init", "--quiet"]);
        let path = ".github/workflows/cache.yml";
        let sha = "0123456789abcdef0123456789abcdef01234567";
        for (action, saves) in [
            ("actions/cache/save", true),
            ("actions/cache", true),
            ("actions/cache/restore", false),
        ] {
            let workflow = format!(
                "on: pull_request\njobs:\n  j:\n    permissions: {{}}\n    steps:\n      \
                 - uses: {action}@{sha}\n"
            );
            scratch.write(path, &workflow);
            git(&["add", "--all"]);
            let result = check_workflows(&scratch.0, &mut Facts::new());
            if saves {
                let problems = result.expect_err("a save fails the step");
                let expected = format!("{path}: job `j` uses {action}, which saves a cache");
                assert!(problems.contains(&expected), "{problems}");
            } else {
                assert_eq!(result, Ok(()));
            }
        }
    }

    #[test]
    fn every_step_is_in_one_segment_or_lane() {
        let expected = [
            (Lane::Lint, vec!["toolchain", "manifests", "fmt", "clippy"]),
            (
                Lane::Debug,
                vec!["test", "docs", "lean", "subset", "workflows"],
            ),
            (Lane::Release, vec!["test-release"]),
            (Lane::Formal, vec![]),
        ]
        .map(|(lane, steps)| LaneSteps { lane, steps });
        for slow in [false, true] {
            let steps = steps(slow);
            let names: Vec<&str> = steps.iter().map(|step| step.name).collect();
            assert_eq!(names, ORDER, "the order of --sequential");
            assert_eq!(layout(&steps), expected);
            // Each step is in exactly one lane, and so in one segment.
            let mut placed: Vec<&str> = layout(&steps)
                .into_iter()
                .flat_map(|lane| lane.steps)
                .collect();
            placed.sort_unstable();
            let mut sorted = ORDER;
            sorted.sort_unstable();
            assert_eq!(placed, sorted);
        }
        let segments: Vec<(&str, u32)> = (Lane::ALL.iter())
            .map(|lane| (lane.name(), lane.segment()))
            .collect();
        assert_eq!(
            segments,
            [("lint", 1), ("debug", 2), ("release", 2), ("formal", 2)]
        );
    }

    /// The manifest of each command of `step`, which must run commands.
    fn manifests_of(step: &Step) -> Vec<&str> {
        let Action::Commands(commands) = &step.action else {
            panic!("{} runs commands", step.name);
        };
        commands
            .iter()
            .map(|cmd| {
                let at = cmd.args.iter().position(|arg| arg == "--manifest-path");
                cmd.args[at.expect("each command names a manifest") + 1].as_str()
            })
            .collect()
    }

    #[test]
    fn command_steps_cover_their_workspaces() {
        let every = [
            "kernel/Cargo.toml",
            "user/Cargo.toml",
            "xtask/Cargo.toml",
            "tools/Cargo.toml",
        ];
        for slow in [false, true] {
            let steps = steps(slow);
            let step = |name: &str| {
                (steps.iter())
                    .find(|step| step.name == name)
                    .expect("the step exists")
            };
            assert_eq!(manifests_of(step("fmt")), every);
            // The host Clippy of each workspace, then the kernel workspace
            // for the bare-metal target.
            let mut clippy = every.to_vec();
            clippy.push("kernel/Cargo.toml");
            assert_eq!(manifests_of(step("clippy")), clippy);
            let Action::Commands(commands) = &step("clippy").action else {
                unreachable!("checked above");
            };
            let target = commands.last().expect("the target Clippy");
            assert_eq!(
                target.args,
                [
                    "clippy",
                    "--manifest-path",
                    "kernel/Cargo.toml",
                    "--workspace",
                    "--lib",
                    "--bins",
                    "--examples",
                    "--locked",
                    "--target",
                    TARGET,
                    "--",
                    "-D",
                    "warnings",
                ]
            );
            let tests = manifests_of(step("test"));
            let runs = if slow { 2 } else { 1 };
            assert_eq!(tests, every.repeat(runs), "slow: {slow}");
            assert_eq!(
                manifests_of(step("test-release")),
                ["kernel/Cargo.toml", "user/Cargo.toml"]
            );
            let Action::Commands(commands) = &step("test").action else {
                unreachable!("checked above");
            };
            for (at, cmd) in commands.iter().enumerate() {
                assert_eq!(cmd.args[..3], ["test", "--workspace", "--locked"]);
                let trailing = &cmd.args[5..];
                if at < every.len() {
                    assert!(trailing.is_empty(), "{:?}", cmd.args);
                } else {
                    assert_eq!(trailing, ["--", "--ignored", SLOW]);
                }
            }
            let Action::Commands(commands) = &step("test-release").action else {
                unreachable!("checked above");
            };
            for cmd in commands {
                assert_eq!(
                    cmd.args[..4],
                    ["test", "--release", "--workspace", "--locked"]
                );
                assert_eq!(cmd.args.len(), 6, "{:?}", cmd.args);
            }
        }
    }

    #[test]
    fn the_target_clippy_rejects_an_undocumented_unsafe_block() {
        // A kernel workspace of one crate that denies undocumented unsafe
        // blocks, as the crates of the kernel workspace do, with a module for
        // the bare-metal target only. Below the build directory, so that the
        // toolchain of the repository and its Cargo configuration apply as
        // they do to the step.
        let scratch = Scratch::new("target-clippy");
        scratch.write(
            "kernel/Cargo.toml",
            "[workspace]\nresolver = \"3\"\nmembers = [\"probe\"]\n",
        );
        scratch.write(
            "kernel/probe/Cargo.toml",
            "[package]\nname = \"probe\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\
             publish = false\n\n[lints.clippy]\nundocumented_unsafe_blocks = \"deny\"\n",
        );
        let source = |comment: &str| {
            format!(
                "//! A probe.\n#![cfg_attr(not(test), no_std)]\n\n\
                 #[cfg(all(target_arch = \"aarch64\", target_os = \"none\"))]\n\
                 pub mod target_only {{\n    /// Reads a word.\n    \
                 pub fn read(word: &u32) -> u32 {{\n        {comment}\
                 unsafe {{ core::ptr::read_volatile(word) }}\n    }}\n}}\n"
            )
        };
        scratch.write("kernel/probe/src/lib.rs", &source(""));
        scratch.lock();
        let steps = steps(false);
        let clippy = (steps.iter())
            .find(|step| step.name == "clippy")
            .expect("the clippy step");
        let Action::Commands(commands) = &clippy.action else {
            panic!("the clippy step runs commands");
        };
        let kernel: Vec<&Cmd> = (commands.iter())
            .filter(|cmd| cmd.args.iter().any(|arg| arg == "kernel/Cargo.toml"))
            .collect();
        let [host, target] = kernel[..] else {
            panic!("two commands of the step lint the kernel workspace: {kernel:?}");
        };
        let run = |cmd: &Cmd| {
            Command::new(&cmd.program)
                .args(&cmd.args)
                .current_dir(&scratch.0)
                .stdin(Stdio::null())
                .output()
                .expect("run Clippy")
        };
        // The host build does not compile the module, so it passes.
        let output = run(host);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{stderr}");
        let output = run(target);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert_eq!(output.status.code(), Some(101), "{stderr}");
        assert!(stderr.contains("undocumented_unsafe_blocks"), "{stderr}");
        // With its safety comment, the block passes on the target as well.
        let comment = "// SAFETY: a reference is valid for reads and aligned.\n        ";
        scratch.write("kernel/probe/src/lib.rs", &source(comment));
        let output = run(target);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "{stderr}");
    }

    /// The problems of the naming rule of slow tests in the Rust source
    /// `text` of the file `path`.
    fn slow_problems(path: &str, text: &str) -> Vec<String> {
        struct Visitor<'a> {
            path: &'a str,
            problems: Vec<String>,
        }
        impl Visitor<'_> {
            fn ignore(attrs: &[syn::Attribute]) -> Option<Option<String>> {
                let ignore = attrs.iter().find(|attr| attr.path().is_ident("ignore"))?;
                Some(match &ignore.meta {
                    syn::Meta::NameValue(syn::MetaNameValue {
                        value:
                            syn::Expr::Lit(syn::ExprLit {
                                lit: syn::Lit::Str(reason),
                                ..
                            }),
                        ..
                    }) => Some(reason.value()),
                    _ => None,
                })
            }
        }
        impl<'ast> Visit<'ast> for Visitor<'_> {
            fn visit_item_fn(&mut self, item: &'ast syn::ItemFn) {
                let name = item.sig.ident.to_string();
                let test = item.attrs.iter().any(|attr| attr.path().is_ident("test"));
                let path = self.path;
                match Visitor::ignore(&item.attrs) {
                    Some(Some(reason)) if reason == "slow" => {
                        if !test {
                            self.problems
                                .push(format!("{path}: {name} is marked slow but is no test"));
                        }
                        if !name.starts_with(SLOW) {
                            self.problems
                                .push(format!("{path}: the slow test {name} lacks {SLOW}"));
                        }
                    }
                    Some(_) if name.contains(SLOW) => self.problems.push(format!(
                        "{path}: the ignored test {name} is not slow but holds {SLOW}"
                    )),
                    _ => {}
                }
                syn::visit::visit_item_fn(self, item);
            }

            fn visit_item_mod(&mut self, item: &'ast syn::ItemMod) {
                let name = item.ident.to_string();
                if name.contains(SLOW) {
                    let path = self.path;
                    (self.problems).push(format!("{path}: the module {name} holds {SLOW}"));
                }
                syn::visit::visit_item_mod(self, item);
            }
        }
        let mut visitor = Visitor {
            path,
            problems: Vec::new(),
        };
        let stem = Path::new(path).file_stem().and_then(|stem| stem.to_str());
        if stem.is_some_and(|stem| stem.contains(SLOW)) {
            (visitor.problems).push(format!("{path}: the file name holds {SLOW}"));
        }
        match syn::parse_file(text) {
            Ok(file) => visitor.visit_file(&file),
            Err(error) => visitor.problems.push(format!("{path}: {error}")),
        }
        visitor.problems
    }

    #[test]
    fn slow_tests_follow_the_naming_rule() {
        // The tracked Rust sources of every workspace.
        let tree = Tree::load(&crate::repo::root()).expect("the tracked files");
        let mut problems = Vec::new();
        let mut files = 0;
        for (path, text) in tree.texts() {
            let inside = (WORKSPACES.iter()).any(|ws| crate::repo::is_within(path, ws));
            if inside && path.ends_with(".rs") {
                files += 1;
                problems.extend(slow_problems(path, text));
            }
        }
        assert!(files > 0);
        assert_eq!(problems, Vec::<String>::new());
        // One source per rule.
        let cases = [
            (
                "a.rs",
                "#[ignore = \"slow\"]\nfn slow_helper() {}\n",
                "a.rs: slow_helper is marked slow but is no test",
            ),
            (
                "a.rs",
                "#[test]\n#[ignore = \"slow\"]\nfn long_walk() {}\n",
                "a.rs: the slow test long_walk lacks slow_",
            ),
            (
                "a.rs",
                "#[test]\n#[ignore = \"needs a tool\"]\nfn not_slow_at_all() {}\n",
                "a.rs: the ignored test not_slow_at_all is not slow but holds slow_",
            ),
            (
                "a.rs",
                "mod tests {\n    mod slow_cases {}\n}\n",
                "a.rs: the module slow_cases holds slow_",
            ),
            (
                "src/very_slow_walk.rs",
                "",
                "src/very_slow_walk.rs: the file name holds slow_",
            ),
        ];
        for (path, text, problem) in cases {
            assert_eq!(slow_problems(path, text), [problem], "{text}");
        }
        let fine = "#[test]\n#[ignore = \"slow\"]\nfn slow_walk() {}\n\
                    #[test]\n#[ignore]\nfn plain() {}\n#[test]\nfn slow_but_not_ignored() {}\n";
        assert_eq!(slow_problems("a.rs", fine), Vec::<String>::new());
    }

    #[test]
    fn the_command_line_takes_the_options_in_any_order() {
        let all = ["--sequential", "--slow", "--receipt p"];
        let expected = Options {
            sequential: true,
            slow: true,
            receipt: Some(PathBuf::from("p")),
        };
        for order in [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ] {
            // `check` before all the options, between them and after them.
            for split in 0..=order.len() {
                let mut words = order.map(|at| all[at]).to_vec();
                words.insert(split, "check");
                let line = words.join(" ");
                let words: Vec<&str> = line.split(' ').collect();
                let args = arguments(&words).expect("the line names the check");
                assert_eq!(
                    options(&args).expect("the options parse"),
                    expected,
                    "{line}"
                );
            }
        }
        let none = Options {
            sequential: false,
            slow: false,
            receipt: None,
        };
        assert_eq!(options(&[]).expect("no option"), none);
        let slow = options(&["--slow"]).expect("one option");
        assert_eq!((slow.sequential, slow.slow), (false, true));
        for wrong in [
            &["--receipt"][..],
            &["--fast"],
            &["--slow", "--slow"],
            &["--receipt", "a", "--receipt", "b"],
            &["extra"],
        ] {
            let error = options(wrong).expect_err("a usage error");
            assert_eq!(error.exit_code(), 2, "{wrong:?}");
        }
        let help = options(&["--help"]).expect_err("help is printed");
        assert_eq!(help.exit_code(), 0);
        let text = help.to_string();
        for option in ["--sequential", "--slow", "--receipt <PATH>"] {
            assert!(text.contains(option), "{text}");
        }
    }

    #[test]
    fn only_options_of_the_check_come_before_it() {
        let cases: [(&[&str], &[&str]); 4] = [
            (&["check"], &[]),
            (
                &["--receipt=p", "check", "--slow"],
                &["--receipt=p", "--slow"],
            ),
            (&["--receipt", "check", "check"], &["--receipt", "check"]),
            (&["--slow", "check", "--slow"], &["--slow", "--slow"]),
        ];
        for (line, args) in cases {
            assert_eq!(arguments(line).as_deref(), Some(args), "{line:?}");
        }
        let receipt = options(&arguments(&["--receipt", "check", "check"]).expect("the check"));
        assert_eq!(
            receipt.expect("a receipt").receipt,
            Some(PathBuf::from("check"))
        );
        let twice = options(&arguments(&["--slow", "check", "--slow"]).expect("the check"));
        assert_eq!(twice.expect_err("a usage error").exit_code(), 2);
        for other in [
            &[][..],
            &["help"],
            &["--slow"],
            &["--receipt", "check"],
            &["--fast", "check"],
            &["extra", "check"],
            &["qemu", "--slow", "check"],
            &["formal", "run", "check"],
        ] {
            assert_eq!(arguments(other), None, "{other:?}");
        }
    }

    /// An outcome of a step that ran from `start` for `seconds`.
    fn ran(step: &'static str, lane: Lane, status: Status, start: f64, seconds: f64) -> Outcome {
        Outcome {
            step,
            lane,
            status,
            offset: Some(Duration::from_secs_f64(start)),
            duration: Duration::from_secs_f64(seconds),
            facts: Facts::new(),
        }
    }

    /// A report of four steps in three lanes and the empty formal lane.
    fn sample() -> Report {
        let not_run = Outcome {
            step: "docs",
            lane: Lane::Debug,
            status: Status::NotRun,
            offset: None,
            duration: Duration::ZERO,
            facts: Facts::new(),
        };
        let outcomes = vec![
            ran("toolchain", Lane::Lint, Status::Passed, 0.0, 0.43),
            ran(
                "test",
                Lane::Debug,
                Status::Cancelled("step test-release failed".to_string()),
                15.72,
                3.021,
            ),
            ran(
                "test-release",
                Lane::Release,
                Status::Failed("`cargo test` exited with exit status: 101".to_string()),
                15.72,
                3.0,
            ),
            not_run,
        ];
        let lane = |lane, steps| LaneSteps { lane, steps };
        Report {
            mode: Mode::Parallel,
            slow: false,
            layout: vec![
                lane(Lane::Lint, vec!["toolchain"]),
                lane(Lane::Debug, vec!["test", "docs"]),
                lane(Lane::Release, vec!["test-release"]),
                lane(Lane::Formal, vec![]),
            ],
            outcomes,
            elapsed: Duration::from_millis(18_760),
            signal: None,
        }
    }

    #[test]
    fn the_summary_has_a_row_with_seconds_for_every_step() {
        let report = sample();
        let expected = "\
summary: parallel, 18.8 s; step logs in artifacts/check/x
segment  lane     step          status     start  seconds
1        lint     toolchain     passed       0.0      0.4
2        debug    test          cancelled   15.7      3.0
2        release  test-release  failed      15.7      3.0
2        debug    docs          not run        -        -
2        formal   (no steps)
";
        assert_eq!(summary(&report, "step logs in artifacts/check/x"), expected);
        assert_eq!(
            ending(&report),
            Err("`cargo test` exited with exit status: 101\n\
                 check failed at step test-release\n"
                .to_string())
        );
        let mut passed = report.clone();
        passed.outcomes.truncate(1);
        assert_eq!(ending(&passed), Ok("check passed\n".to_string()));
        let mut stopped = report.clone();
        stopped.signal = Some(libc::SIGTERM);
        assert_eq!(
            ending(&stopped),
            Ok("check interrupted by SIGTERM\n".to_string())
        );
        // A sequential run of other steps: the column of the names widens.
        let mut other = passed;
        other.mode = Mode::Sequential;
        other.outcomes[0].step = "a-much-longer-step";
        other.layout.clear();
        let text = summary(&other, "no step logs: cannot create x");
        assert_eq!(
            text.lines().collect::<Vec<_>>(),
            [
                "summary: sequential, 18.8 s; no step logs: cannot create x",
                "segment  lane     step                status     start  seconds",
                "1        lint     a-much-longer-step  passed       0.0      0.4",
            ]
        );
    }

    #[test]
    fn an_interrupted_run_exits_with_128_plus_the_signal() {
        let report = sample();
        assert_eq!(report.verdict(), Verdict::Failed);
        assert_eq!(exit_code(report.verdict(), true), 1);
        let mut passed = report.clone();
        passed.outcomes.truncate(1);
        assert_eq!(passed.verdict(), Verdict::Passed);
        assert_eq!(exit_code(passed.verdict(), true), 0);
        assert_eq!(exit_code(passed.verdict(), false), 1);
        // The interruption takes precedence over a failed step, a passed
        // run and a receipt that could not be written.
        for (signal, code) in [
            (libc::SIGTERM, 143),
            (libc::SIGINT, 130),
            (libc::SIGHUP, 129),
        ] {
            for mut stopped in [report.clone(), passed.clone()] {
                stopped.signal = Some(signal);
                assert_eq!(stopped.verdict(), Verdict::Interrupted(signal));
                assert_eq!(exit_code(stopped.verdict(), true), code);
                assert_eq!(exit_code(stopped.verdict(), false), code);
            }
        }
        assert_eq!(signal_name(libc::SIGINT), "SIGINT");
        assert_eq!(signal_name(libc::SIGHUP), "SIGHUP");
    }

    #[test]
    fn a_term_signal_interrupts_the_check_with_143() {
        let sleepers = ["debug-sleeper", "release-sleeper"];
        if let Some(root) = std::env::var_os(STOPPED) {
            // The check that the test stops: one sleeper in each of two
            // lanes, which write the numbers of their groups and wait.
            let root = PathBuf::from(root);
            let steps = [
                lanes::tests::sleeper(sleepers[0], Lane::Debug),
                lanes::tests::sleeper(sleepers[1], Lane::Release),
            ];
            let options = Options {
                sequential: false,
                slow: false,
                receipt: Some(root.join("receipt.json")),
            };
            std::process::exit(i32::from(run(&root, &options, &steps)));
        }
        let (_, tests) = module_path!()
            .split_once("::")
            .expect("a module path below the crate");
        let name = format!("{tests}::a_term_signal_interrupts_the_check_with_143");
        // Outside the repository, so that the receipt reads no Git state.
        let scratch = Scratch::temporary("check-term");
        let (stdout, stderr) = (scratch.0.join("stdout"), scratch.0.join("stderr"));
        let mut command = Command::new(std::env::current_exe().expect("the test executable"));
        command
            .args([name.as_str(), "--exact", "--test-threads=1", "--nocapture"])
            .env(STOPPED, &scratch.0)
            .stdin(Stdio::null())
            .stdout(File::create(&stdout).expect("create the output file"))
            .stderr(File::create(&stderr).expect("create the error file"));
        // Under `nohup`, the check would inherit SIGHUP ignored.
        with_hangup(&mut command, libc::SIG_DFL);
        let mut child = command.spawn().expect("start the test executable");
        let said = || {
            let read = |path: &Path| fs::read_to_string(path).unwrap_or_default();
            format!("{}{}", read(&stdout), read(&stderr))
        };
        // A bound for a check that hangs before both lanes run, not a bound
        // on how long a step takes.
        let deadline = Instant::now() + Duration::from_secs(120);
        let groups: Vec<i32> = loop {
            let read = |name: &str| fs::read_to_string(scratch.0.join(format!("{name}.pgid")));
            if let [Ok(first), Ok(second)] = sleepers.map(read) {
                let number = |text: String| text.trim().parse().expect("a process number");
                break vec![number(first), number(second)];
            }
            let ended = child.try_wait().expect("look at the check").is_some();
            assert!(!ended && Instant::now() < deadline, "{}", said());
            std::thread::sleep(Duration::from_millis(10));
        };
        // SAFETY: kill touches no memory of this process; the check is a
        // child of it that has not been collected.
        unsafe { libc::kill(child.id() as libc::pid_t, libc::SIGTERM) };
        let status = child.wait().expect("collect the check");
        // The check exits; the signal does not end it.
        assert_eq!(status.code(), Some(143), "{}", said());
        let output = fs::read_to_string(&stdout).expect("the output");
        for sleeper in sleepers {
            let row = output.lines().find(|line| {
                line.split_whitespace().nth(2) == Some(sleeper) && line.starts_with('2')
            });
            let row = row.unwrap_or_else(|| panic!("a summary row for {sleeper}: {output}"));
            assert_eq!(row.split_whitespace().nth(3), Some("cancelled"), "{row}");
        }
        assert!(output.contains("\nsummary: parallel, "), "{output}");
        assert!(
            output.contains("\ncheck interrupted by SIGTERM\n"),
            "{output}"
        );
        let text = fs::read_to_string(scratch.0.join("receipt.json")).expect("the receipt");
        let receipt: Value = serde_json::from_str(&text).expect("the receipt is JSON");
        assert_eq!(receipt["result"], "interrupted");
        assert_eq!(receipt["signal"], 15);
        assert_eq!(receipt["mode"], "parallel");
        let steps = receipt["steps"].as_array().expect("the steps");
        assert_eq!(steps.len(), 2);
        for step in steps {
            assert_eq!(step["status"], "cancelled", "{step}");
            assert_eq!(step["detail"], "SIGTERM", "{step}");
        }
        for group in groups {
            assert_eq!(probe(group), Some(libc::ESRCH));
        }
    }
}
