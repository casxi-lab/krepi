//! The runner of `cargo xtask check`: its segments of lanes, the process
//! groups of its commands, the logs of its steps and how it stops.
//!
//! The segments run one after another, and the lanes of a segment at once,
//! each on a thread of its own that runs its steps in order. Before each
//! step, before each command and every [`process::PAUSE`] while a command
//! runs, the runner looks whether a step has failed or a stop signal has
//! arrived; from then on no step or command starts. A command of a step
//! runs in a process group of its own, with its standard input empty and
//! both output streams appended to the log of its step; when its leader has
//! ended, or when the check stops, the group is killed before the leader is
//! collected, in the order of the proof gate, so the kill cannot reach a
//! group that took over a freed number. A passing command therefore leaves
//! no process of its group behind either. A check written in this crate runs
//! on the thread of its lane until it returns, with the commands it starts
//! in the group of the check. When a step ends, its log and a line with its
//! status and seconds are printed in one write, so the output of two lanes
//! never interleaves.

use std::fs::{self, OpenOptions};
use std::io::{self, Write};
use std::os::unix::process::CommandExt;
use std::panic::{self, AssertUnwindSafe};
use std::path::Path;
use std::process::{Command, ExitStatus, Stdio};
use std::sync::OnceLock;
use std::thread;
use std::time::{Duration, Instant};

use super::{Action, Check, Cmd, Facts, Lane, Mode, Outcome, Status, Step, signal_name};
use crate::formal::process;

/// What a run of the steps gives.
pub struct Run {
    /// One outcome per step, in the order of the steps.
    pub outcomes: Vec<Outcome>,
    /// The time from the start of the first step until the last one ended.
    pub elapsed: Duration,
}

/// Why the check stops: the first step that failed, or the stop signal.
#[derive(Default)]
pub(super) struct Stop {
    failed: OnceLock<&'static str>,
}

impl Stop {
    /// Why the check stops, if it does: the stop signal, which takes
    /// precedence, or the first step that failed.
    pub(super) fn reason(&self) -> Option<String> {
        let failed = || (self.failed.get()).map(|step| format!("step {step} failed"));
        process::stop_signal().map(signal_name).or_else(failed)
    }
}

/// What every lane of a run shares.
struct Context<'a> {
    root: &'a Path,
    steps: &'a [Step],
    /// The directory of the step logs, or why it could not be created.
    logs: Result<&'a Path, &'a str>,
    begin: Instant,
    stop: &'a Stop,
}

/// Runs `steps` in `root` in `mode`, with the logs of their commands in
/// `logs`. Every step has an outcome; those that did not start are not run.
pub fn run(root: &Path, steps: &[Step], mode: Mode, logs: Result<&Path, &str>) -> Run {
    run_with(root, steps, mode, logs, &Stop::default())
}

/// [`run`], stopping also when `stop` holds a failed step.
pub(super) fn run_with(
    root: &Path,
    steps: &[Step],
    mode: Mode,
    logs: Result<&Path, &str>,
    stop: &Stop,
) -> Run {
    let context = Context {
        root,
        steps,
        logs,
        begin: Instant::now(),
        stop,
    };
    let context = &context;
    let mut outcomes: Vec<Option<Outcome>> = steps.iter().map(|_| None).collect();
    for segment in segments(steps, mode) {
        if context.stop.reason().is_some() {
            break;
        }
        thread::scope(|scope| {
            let lanes: Vec<_> = (segment.iter())
                .map(|lane| scope.spawn(move || run_lane(context, lane)))
                .collect();
            for lane in lanes {
                let ran = lane
                    .join()
                    .unwrap_or_else(|payload| panic::resume_unwind(payload));
                for (index, outcome) in ran {
                    outcomes[index] = Some(outcome);
                }
            }
        });
    }
    let outcomes = (outcomes.into_iter().zip(steps))
        .map(|(outcome, step)| outcome.unwrap_or_else(|| not_run(step)))
        .collect();
    Run {
        outcomes,
        elapsed: context.begin.elapsed(),
    }
}

/// The segments of a run, one after another, each of the lanes that run at
/// once, as the positions of their steps in order: in parallel mode the lint
/// lane, then the other lanes that have steps; in sequential mode one lane
/// of every step.
fn segments(steps: &[Step], mode: Mode) -> Vec<Vec<Vec<usize>>> {
    let every = || 0..steps.len();
    if mode == Mode::Sequential {
        return vec![vec![every().collect()]];
    }
    let lane =
        |lane: Lane| -> Vec<usize> { every().filter(|&at| steps[at].lane == lane).collect() };
    let segment = |segment: u32| -> Vec<Vec<usize>> {
        (Lane::ALL.iter())
            .filter(|lane| lane.segment() == segment)
            .map(|&each| lane(each))
            .filter(|steps| !steps.is_empty())
            .collect()
    };
    vec![segment(1), segment(2)]
}

/// The outcome of a step that did not start.
fn not_run(step: &Step) -> Outcome {
    Outcome {
        step: step.name,
        lane: step.lane,
        status: Status::NotRun,
        offset: None,
        duration: Duration::ZERO,
        facts: Facts::new(),
    }
}

/// Runs the steps at the positions `lane` in order.
fn run_lane(context: &Context, lane: &[usize]) -> Vec<(usize, Outcome)> {
    (lane.iter())
        .map(|&at| (at, run_step(context, at)))
        .collect()
}

/// Runs the step at position `at`, unless the check stops, and prints its
/// block when it ends. A failure makes the check stop.
fn run_step(context: &Context, at: usize) -> Outcome {
    let step = &context.steps[at];
    if context.stop.reason().is_some() {
        return not_run(step);
    }
    println!("==> {} ({})", step.name, step.lane.name());
    let offset = context.begin.elapsed();
    let started = Instant::now();
    let mut facts = Facts::new();
    let mut log = None;
    let status = match &step.action {
        Action::Commands(commands) => match context.logs {
            Ok(dir) => {
                let path = dir.join(format!("{:02}-{}.log", at + 1, step.name));
                let status = run_commands(context, commands, &path);
                log = Some(path);
                status
            }
            Err(error) => Status::Failed(error.to_string()),
        },
        Action::Internal(check) => match run_internal(check, context.root, &mut facts) {
            Ok(()) => Status::Passed,
            Err(detail) => Status::Failed(detail),
        },
    };
    if matches!(status, Status::Failed(_)) {
        let _ = context.stop.failed.set(step.name);
    }
    let duration = started.elapsed();
    print!("{}", block(step, &status, duration, log.as_deref()));
    Outcome {
        step: step.name,
        lane: step.lane,
        status,
        offset: Some(offset),
        duration,
        facts,
    }
}

/// The output of a step once it has ended: the log of its commands, then a
/// line with its status and seconds.
fn block(step: &Step, status: &Status, duration: Duration, log: Option<&Path>) -> String {
    let mut text = String::new();
    if let Some(path) = log {
        match fs::read(path) {
            Ok(bytes) => {
                text.push_str(&String::from_utf8_lossy(&bytes));
                if !text.is_empty() && !text.ends_with('\n') {
                    text.push('\n');
                }
            }
            // A step that stopped before its first command has no log.
            Err(error) if error.kind() == io::ErrorKind::NotFound => {}
            Err(error) => text.push_str(&format!("cannot read {}: {error}\n", path.display())),
        }
    }
    text.push_str(&format!(
        "<== {} ({}): {}, {:.1} s\n",
        step.name,
        step.lane.name(),
        status.name(),
        duration.as_secs_f64()
    ));
    text
}

/// Runs `commands` in order with their output appended to `log`, until one
/// fails or the check stops.
fn run_commands(context: &Context, commands: &[Cmd], log: &Path) -> Status {
    for cmd in commands {
        if let Some(reason) = context.stop.reason() {
            return Status::Cancelled(reason);
        }
        match run_command(context.root, cmd, log, context.stop) {
            Ended::Exited(status) if status.success() => {}
            Ended::Exited(status) => {
                return Status::Failed(format!("`{}` exited with {status}", shown(cmd)));
            }
            Ended::Cancelled(reason) => return Status::Cancelled(reason),
            Ended::Failed(detail) => return Status::Failed(detail),
        }
    }
    Status::Passed
}

/// How a command ended.
#[derive(Debug)]
enum Ended {
    Exited(ExitStatus),
    /// The check stopped, and why; the command's group was killed.
    Cancelled(String),
    /// It could not start, be watched or be collected, or processes of its
    /// group outlived the kill.
    Failed(String),
}

/// The command line of `cmd` as the log and the messages show it.
fn shown(cmd: &Cmd) -> String {
    format!("{} {}", cmd.program.to_string_lossy(), cmd.args.join(" "))
}

/// Runs `cmd` in `root` in a process group of its own, with its output
/// appended to `log`, until its leader has ended or the check stops, then
/// kills the group and waits up to [`process::GROUP_END`] for it to be
/// empty.
fn run_command(root: &Path, cmd: &Cmd, log: &Path, stop: &Stop) -> Ended {
    let shown = shown(cmd);
    let open = || {
        let mut file = OpenOptions::new().create(true).append(true).open(log)?;
        writeln!(file, "$ {shown}")?;
        let error = file.try_clone()?;
        Ok::<_, io::Error>((file, error))
    };
    let (output, error) = match open() {
        Ok(files) => files,
        Err(error) => return Ended::Failed(format!("cannot write {}: {error}", log.display())),
    };
    let started = Command::new(&cmd.program)
        .args(&cmd.args)
        .current_dir(root)
        .stdin(Stdio::null())
        .stdout(output)
        .stderr(error)
        .process_group(0)
        .spawn();
    let mut child = match started {
        Ok(child) => child,
        Err(error) => return Ended::Failed(format!("cannot run `{shown}`: {error}")),
    };
    // Process numbers are positive and below 2^31.
    let group = child.id() as libc::pid_t;
    let cancelled = loop {
        match process::leader_ended(group) {
            Ok(true) => break None,
            Ok(false) => {}
            Err(error) => {
                // The number may name another process now: nothing is signalled.
                let _ = child.try_wait();
                return Ended::Failed(format!("cannot watch `{shown}`: {error}"));
            }
        }
        if let Some(reason) = stop.reason() {
            break Some(reason);
        }
        thread::sleep(process::PAUSE);
    };
    process::kill_group(group);
    let collected = child.wait();
    let ended = process::group_ended(group);
    match (collected, cancelled) {
        (Err(error), _) => Ended::Failed(format!("cannot collect `{shown}`: {error}")),
        _ if !ended => Ended::Failed(format!(
            "processes of the group of `{shown}` outlived the kill"
        )),
        (Ok(_), Some(reason)) => Ended::Cancelled(reason),
        (Ok(status), None) => Ended::Exited(status),
    }
}

/// Runs a check written in this crate. A panic in it fails the step like an
/// error, so that the receipt is still written.
fn run_internal(check: &Check, root: &Path, facts: &mut Facts) -> Result<(), String> {
    panic::catch_unwind(AssertUnwindSafe(|| check(root, facts))).unwrap_or_else(|payload| {
        let message = payload
            .downcast_ref::<&str>()
            .map(|text| text.to_string())
            .or_else(|| payload.downcast_ref::<String>().cloned())
            .unwrap_or_default();
        Err(format!("panicked: {message}"))
    })
}

#[cfg(test)]
pub(super) mod tests {
    use std::sync::{Arc, Mutex};

    use super::super::tests::ORDER;
    use super::super::{failure, steps};
    use super::*;
    use crate::formal::process::tests::probe;
    use crate::scratch::Scratch;

    /// The names of the internal steps that ran, in the order they ran.
    type Ran = Arc<Mutex<Vec<&'static str>>>;

    /// A wait of at most 60 s for each of `files` in the working directory,
    /// as a shell loop; only a failing test reaches the bound.
    fn wait_for(files: &[String]) -> String {
        let missing: Vec<String> = (files.iter())
            .map(|file| format!("[ ! -f {file} ]"))
            .collect();
        format!(
            "i=0; while {{ {}; }} && [ $i -lt 6000 ]; do sleep 0.01; i=$((i+1)); done",
            missing.join(" || ")
        )
    }

    /// A step `name` that runs the shell script `script`.
    fn shell(name: &'static str, lane: Lane, script: String) -> Step {
        let cmd = Cmd {
            program: "/bin/sh".into(),
            args: vec!["-c".into(), script],
        };
        Step {
            name,
            lane,
            action: Action::Commands(vec![cmd]),
        }
    }

    /// A step `name` that starts a sleep of 240 s as a grandchild, writes the
    /// number of its process group to `<name>.pgid` in the working
    /// directory and waits; only a kill ends it before the sleep.
    pub(in crate::check) fn sleeper(name: &'static str, lane: Lane) -> Step {
        let script = format!("sleep 240 & echo $$ > {name}.new && mv {name}.new {name}.pgid; wait");
        shell(name, lane, script)
    }

    /// A step `name` that waits until each of `running` has written its
    /// group and then exits with status 3.
    fn failer(name: &'static str, lane: Lane, running: &[&str]) -> Step {
        let files: Vec<String> = running.iter().map(|step| format!("{step}.pgid")).collect();
        shell(name, lane, format!("{}; exit 3", wait_for(&files)))
    }

    /// An internal step `name` that records that it ran and adds a fact.
    fn recorder(name: &'static str, lane: Lane, ran: &Ran) -> Step {
        let ran = Arc::clone(ran);
        let check: Check = Box::new(move |_, facts| {
            ran.lock().expect("the record").push(name);
            facts.push(("ran".to_string(), name.to_string()));
            Ok(())
        });
        Step {
            name,
            lane,
            action: Action::Internal(check),
        }
    }

    /// The process group that the sleeper `name` wrote in `scratch`.
    fn group(scratch: &Scratch, name: &str) -> i32 {
        let text = fs::read_to_string(scratch.0.join(format!("{name}.pgid")));
        let text = text.expect("the sleeper wrote its group");
        text.trim().parse().expect("a process number")
    }

    /// Runs `steps` in `scratch`, with their logs in it.
    fn run_in(scratch: &Scratch, steps: &[Step], mode: Mode) -> Run {
        let logs = scratch.0.join("logs");
        fs::create_dir_all(&logs).expect("create the log directory");
        run(&scratch.0, steps, mode, Ok(&logs))
    }

    /// The outcome of the step `name`.
    fn outcome<'a>(run: &'a Run, name: &str) -> &'a Outcome {
        (run.outcomes.iter())
            .find(|outcome| outcome.step == name)
            .unwrap_or_else(|| panic!("an outcome for {name}"))
    }

    /// Checks the outcomes after the step `failer` failed while the
    /// sleepers `cancelled` ran: those are cancelled, their groups are gone,
    /// `next` did not run and the check ended within 10 s after `failer`.
    fn assert_cancelled(run: &Run, scratch: &Scratch, failer: &str, cancelled: &[&str]) {
        let failed = outcome(run, failer);
        assert!(
            matches!(&failed.status, Status::Failed(detail) if detail.ends_with("exit status: 3")),
            "{failed:?}"
        );
        for name in cancelled {
            let reason = format!("step {failer} failed");
            assert_eq!(outcome(run, name).status, Status::Cancelled(reason));
            assert_eq!(probe(group(scratch, name)), Some(libc::ESRCH), "{name}");
        }
        let after = run.elapsed - (failed.offset.expect("the step ran") + failed.duration);
        // Only a check that waited for a sleeper of 240 s takes longer.
        assert!(after < Duration::from_secs(10), "{after:?}");
        // The log of the failed step holds its command line.
        let log = fs::read_to_string(scratch.0.join("logs").join(format!(
            "{:02}-{failer}.log",
            1 + run.outcomes.iter().position(|o| o.step == failer).unwrap()
        )));
        assert!(log.expect("the log").starts_with("$ /bin/sh -c "));
    }

    #[test]
    fn a_release_failure_cancels_the_debug_and_formal_lanes() {
        let scratch = Scratch::new("release-failure");
        let ran = Ran::default();
        let steps = [
            recorder("lint", Lane::Lint, &ran),
            sleeper("debug-sleeper", Lane::Debug),
            recorder("debug-next", Lane::Debug, &ran),
            failer(
                "release-failer",
                Lane::Release,
                &["debug-sleeper", "formal-sleeper"],
            ),
            recorder("release-next", Lane::Release, &ran),
            sleeper("formal-sleeper", Lane::Formal),
        ];
        let run = run_in(&scratch, &steps, Mode::Parallel);
        assert_cancelled(
            &run,
            &scratch,
            "release-failer",
            &["debug-sleeper", "formal-sleeper"],
        );
        // No step started after the failure.
        assert_eq!(*ran.lock().unwrap(), ["lint"]);
        for name in ["debug-next", "release-next"] {
            assert_eq!(outcome(&run, name).status, Status::NotRun);
            assert_eq!(outcome(&run, name).offset, None);
        }
        assert_eq!(outcome(&run, "lint").status, Status::Passed);
    }

    #[test]
    fn a_debug_failure_cancels_the_release_lane() {
        let scratch = Scratch::new("debug-failure");
        let ran = Ran::default();
        let steps = [
            failer("debug-failer", Lane::Debug, &["release-sleeper"]),
            recorder("debug-next", Lane::Debug, &ran),
            sleeper("release-sleeper", Lane::Release),
            recorder("release-next", Lane::Release, &ran),
        ];
        let run = run_in(&scratch, &steps, Mode::Parallel);
        assert_cancelled(&run, &scratch, "debug-failer", &["release-sleeper"]);
        assert!(ran.lock().unwrap().is_empty());
        for name in ["debug-next", "release-next"] {
            assert_eq!(outcome(&run, name).status, Status::NotRun);
        }
    }

    #[test]
    fn a_parallel_check_that_passes_records_every_step() {
        let scratch = Scratch::new("passes");
        let ran = Ran::default();
        // Each of the two meets waits for the other to have started, so
        // they pass only when they run at once.
        let meet = |name: &'static str, lane, other: &str| {
            let wait = wait_for(&[format!("{other}.started")]);
            shell(
                name,
                lane,
                format!("touch {name}.started; {wait}; [ -f {other}.started ]"),
            )
        };
        let steps = [
            recorder("lint", Lane::Lint, &ran),
            meet("debug-meet", Lane::Debug, "release-meet"),
            recorder("debug-next", Lane::Debug, &ran),
            meet("release-meet", Lane::Release, "debug-meet"),
        ];
        let run = run_in(&scratch, &steps, Mode::Parallel);
        let names: Vec<&str> = run.outcomes.iter().map(|outcome| outcome.step).collect();
        assert_eq!(names, ["lint", "debug-meet", "debug-next", "release-meet"]);
        for outcome in &run.outcomes {
            assert_eq!(outcome.status, Status::Passed, "{outcome:?}");
            assert!(outcome.offset.is_some(), "{outcome:?}");
        }
        let lanes: Vec<Lane> = run.outcomes.iter().map(|outcome| outcome.lane).collect();
        assert_eq!(lanes, [Lane::Lint, Lane::Debug, Lane::Debug, Lane::Release]);
        let span = |name| {
            let outcome = outcome(&run, name);
            let start = outcome.offset.unwrap();
            (start, start + outcome.duration)
        };
        let (debug, release) = (span("debug-meet"), span("release-meet"));
        assert!(
            debug.0 < release.1 && release.0 < debug.1,
            "{debug:?} {release:?}"
        );
        // The lint lane ended before the other segment started.
        let (_, lint_end) = span("lint");
        assert!(lint_end <= debug.0 && lint_end <= release.0);
        assert_eq!(*ran.lock().unwrap(), ["lint", "debug-next"]);
        assert!(run.elapsed >= debug.1.max(release.1));
    }

    #[test]
    fn a_running_internal_check_finishes_and_keeps_its_result() {
        let scratch = Scratch::new("internal");
        let ran = Ran::default();
        let stop = Arc::new(Stop::default());
        let seen = Arc::clone(&stop);
        // A check that waits until the release step has failed and then
        // passes: the check does not interrupt it.
        let waits: Check = Box::new(move |_, facts| {
            let deadline = Instant::now() + Duration::from_secs(60);
            while seen.reason().is_none() && Instant::now() < deadline {
                thread::sleep(Duration::from_millis(10));
            }
            facts.push(("saw".to_string(), seen.reason().unwrap_or_default()));
            Ok(())
        });
        let steps = [
            Step {
                name: "debug-internal",
                lane: Lane::Debug,
                action: Action::Internal(waits),
            },
            recorder("debug-next", Lane::Debug, &ran),
            shell("release-failer", Lane::Release, "exit 4".to_string()),
        ];
        let logs = scratch.0.join("logs");
        fs::create_dir_all(&logs).expect("create the log directory");
        let run = run_with(&scratch.0, &steps, Mode::Parallel, Ok(&logs), &stop);
        let internal = outcome(&run, "debug-internal");
        assert_eq!(internal.status, Status::Passed);
        let saw = ("saw".to_string(), "step release-failer failed".to_string());
        assert_eq!(internal.facts, [saw]);
        assert_eq!(outcome(&run, "debug-next").status, Status::NotRun);
        assert!(ran.lock().unwrap().is_empty());
        assert!(matches!(
            outcome(&run, "release-failer").status,
            Status::Failed(_)
        ));
    }

    #[test]
    fn a_lint_failure_starts_no_lane() {
        let scratch = Scratch::new("lint-failure");
        let ran = Ran::default();
        let run = run_in(&scratch, &with_failure("clippy", &ran), Mode::Parallel);
        assert_eq!(failure(&run.outcomes).map(|(step, _)| step), Some("clippy"));
        assert_eq!(*ran.lock().unwrap(), ["toolchain", "manifests", "fmt"]);
        for outcome in run.outcomes.iter().filter(|o| o.lane != Lane::Lint) {
            assert_eq!(outcome.status, Status::NotRun, "{outcome:?}");
        }
    }

    /// The real step list with `failing` replaced by a failing action and
    /// every other step replaced by one that records that it ran and adds a
    /// fact; each keeps its lane.
    fn with_failure(failing: &str, ran: &Ran) -> Vec<Step> {
        steps(false)
            .into_iter()
            .map(|step| {
                let (name, lane) = (step.name, step.lane);
                if name != failing {
                    return recorder(name, lane, ran);
                }
                let action = match step.action {
                    // A real process that exits with a non-zero status.
                    Action::Commands(_) => Action::Commands(vec![Cmd {
                        program: "/bin/sh".into(),
                        args: vec!["-c".into(), "exit 3".into()],
                    }]),
                    Action::Internal(_) => Action::Internal(Box::new(|_, facts| {
                        facts.push(("seen".to_string(), "before failing".to_string()));
                        Err("forced failure".to_string())
                    })),
                };
                Step { name, lane, action }
            })
            .collect()
    }

    fn assert_fails_at(failing: &'static str) {
        let scratch = Scratch::new("sequential");
        let ran = Ran::default();
        let steps = with_failure(failing, &ran);
        let run = run_in(&scratch, &steps, Mode::Sequential);
        let (step, _) = failure(&run.outcomes).expect("the check fails");
        assert_eq!(step, failing);
        let failed_at = ORDER.iter().position(|name| *name == failing).unwrap();
        assert_eq!(
            *ran.lock().unwrap(),
            ORDER[..failed_at],
            "steps after the failure must not run"
        );
        let names: Vec<&str> = run.outcomes.iter().map(|outcome| outcome.step).collect();
        assert_eq!(names, ORDER, "every step has an outcome");
        let mut previous = Duration::ZERO;
        for (index, outcome) in run.outcomes.iter().enumerate() {
            match index.cmp(&failed_at) {
                std::cmp::Ordering::Less => {
                    assert_eq!(outcome.status, Status::Passed);
                    assert_eq!(
                        outcome.facts,
                        [("ran".to_string(), outcome.step.to_string())]
                    );
                    // One step after another.
                    let start = outcome.offset.expect("the step ran");
                    assert!(start >= previous);
                    previous = start + outcome.duration;
                }
                std::cmp::Ordering::Equal => {
                    assert!(matches!(outcome.status, Status::Failed(_)), "{outcome:?}");
                    assert!(outcome.offset.expect("the step ran") >= previous);
                }
                std::cmp::Ordering::Greater => {
                    assert_eq!(outcome.status, Status::NotRun);
                    assert_eq!(outcome.offset, None);
                    assert_eq!(outcome.duration, Duration::ZERO);
                    assert!(outcome.facts.is_empty());
                }
            }
        }
    }

    #[test]
    fn sequential_mode_runs_the_frozen_order_and_stops_at_the_first_failure() {
        for failing in ORDER {
            assert_fails_at(failing);
        }
    }

    #[test]
    fn a_format_failure_stops_the_check() {
        assert_fails_at("fmt");
    }

    #[test]
    fn a_clippy_failure_stops_the_check() {
        assert_fails_at("clippy");
    }

    #[test]
    fn a_test_failure_stops_the_check() {
        assert_fails_at("test");
    }

    #[test]
    fn a_release_test_failure_stops_the_check() {
        assert_fails_at("test-release");
    }

    #[test]
    fn a_docs_failure_stops_the_check() {
        assert_fails_at("docs");
    }

    #[test]
    fn a_lean_failure_stops_the_check() {
        assert_fails_at("lean");
    }

    #[test]
    fn a_subset_failure_stops_the_check() {
        assert_fails_at("subset");
    }

    #[test]
    fn a_workflows_failure_fails_the_check_after_every_other_step() {
        assert_fails_at("workflows");
    }

    #[test]
    fn a_panicking_step_fails_like_an_error_and_keeps_its_facts() {
        let scratch = Scratch::new("panic");
        let ran = Ran::default();
        let mut steps = with_failure("docs", &ran);
        let docs = ORDER.iter().position(|name| *name == "docs").unwrap();
        steps[docs].action = Action::Internal(Box::new(|_, facts| {
            facts.push(("seen".to_string(), "before panicking".to_string()));
            panic!("forced {}", "panic");
        }));
        for mode in [Mode::Sequential, Mode::Parallel] {
            let run = run_in(&scratch, &steps, mode);
            assert_eq!(
                run.outcomes[docs].status,
                Status::Failed("panicked: forced panic".to_string())
            );
            assert_eq!(
                run.outcomes[docs].facts,
                [("seen".to_string(), "before panicking".to_string())]
            );
            assert_eq!(run.outcomes[docs + 1].status, Status::NotRun);
        }
    }

    #[test]
    fn a_failing_step_keeps_the_facts_it_added() {
        let scratch = Scratch::new("facts");
        let ran = Ran::default();
        let run = run_in(&scratch, &with_failure("toolchain", &ran), Mode::Parallel);
        assert_eq!(
            run.outcomes[0].facts,
            [("seen".to_string(), "before failing".to_string())]
        );
        assert_eq!(
            run.outcomes[0].status,
            Status::Failed("forced failure".to_string())
        );
        assert!(ran.lock().unwrap().is_empty());
    }

    #[test]
    fn a_command_that_cannot_start_fails_its_step() {
        let scratch = Scratch::new("cannot-start");
        let ran = Ran::default();
        let missing = scratch.0.join("missing-tool");
        let steps = [
            Step {
                name: "missing",
                lane: Lane::Lint,
                action: Action::Commands(vec![Cmd {
                    program: missing.clone().into(),
                    args: vec!["--version".to_string()],
                }]),
            },
            recorder("next", Lane::Debug, &ran),
        ];
        let run = run_in(&scratch, &steps, Mode::Parallel);
        let Status::Failed(detail) = &run.outcomes[0].status else {
            panic!("{:?}", run.outcomes[0]);
        };
        let shown = format!("cannot run `{} --version`: ", missing.display());
        assert!(detail.starts_with(&shown), "{detail}");
        assert_eq!(run.outcomes[1].status, Status::NotRun);
        assert!(ran.lock().unwrap().is_empty());
    }

    #[test]
    fn a_log_that_cannot_be_created_fails_its_step() {
        let scratch = Scratch::new("log");
        let ran = Ran::default();
        let steps = || {
            [
                shell("first", Lane::Lint, "exit 0".to_string()),
                recorder("next", Lane::Lint, &ran),
            ]
        };
        // The log directory could not be created.
        let without = run(
            &scratch.0,
            &steps(),
            Mode::Sequential,
            Err("cannot create x"),
        );
        assert_eq!(
            without.outcomes[0].status,
            Status::Failed("cannot create x".to_string())
        );
        assert_eq!(without.outcomes[1].status, Status::NotRun);
        // The log of the step is a directory.
        let logs = scratch.0.join("logs");
        fs::create_dir_all(logs.join("01-first.log")).expect("create the directory");
        let run = run(&scratch.0, &steps(), Mode::Sequential, Ok(&logs));
        let Status::Failed(detail) = &run.outcomes[0].status else {
            panic!("{:?}", run.outcomes[0]);
        };
        let path = logs.join("01-first.log");
        assert!(
            detail.starts_with(&format!("cannot write {}: ", path.display())),
            "{detail}"
        );
        assert_eq!(run.outcomes[1].status, Status::NotRun);
        assert!(ran.lock().unwrap().is_empty());
    }

    #[test]
    fn the_block_of_a_step_is_its_log_and_a_status_line() {
        let scratch = Scratch::new("block");
        let steps = [shell(
            "speaks",
            Lane::Release,
            "printf out; printf 'err\\n' >&2".to_string(),
        )];
        let logs = scratch.0.join("logs");
        let run = run_in(&scratch, &steps, Mode::Parallel);
        assert_eq!(run.outcomes[0].status, Status::Passed);
        let log = fs::read_to_string(logs.join("01-speaks.log")).expect("the log");
        assert_eq!(
            log,
            "$ /bin/sh -c printf out; printf 'err\\n' >&2\nouterr\n"
        );
        let text = block(
            &steps[0],
            &run.outcomes[0].status,
            Duration::from_millis(1_260),
            Some(&logs.join("01-speaks.log")),
        );
        assert_eq!(text, format!("{log}<== speaks (release): passed, 1.3 s\n"));
        // A log without a final newline gets one, and a missing log is left
        // out.
        fs::write(logs.join("partial"), "no newline").expect("write the log");
        let status = Status::Cancelled("SIGTERM".to_string());
        let duration = Duration::ZERO;
        assert_eq!(
            block(&steps[0], &status, duration, Some(&logs.join("partial"))),
            "no newline\n<== speaks (release): cancelled, 0.0 s\n"
        );
        assert_eq!(
            block(&steps[0], &status, duration, Some(&logs.join("missing"))),
            "<== speaks (release): cancelled, 0.0 s\n"
        );
    }
}
