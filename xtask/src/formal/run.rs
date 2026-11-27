//! `cargo xtask formal run`: a run of the proof gate, from the snapshot of
//! the gate inputs to its receipt, as "Gate run" in
//! `docs/formal-verification.md` describes. Every command runs through
//! [`Gate::command`], which limits, classifies, records and prints it.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::env::consts::{ARCH, OS};
use std::fs;
use std::io::{self, Write};
use std::panic::{self, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::atomic::{AtomicU32, Ordering};
use std::sync::{Mutex, MutexGuard, PoisonError, mpsc};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use super::Layout;
use super::comparator;
use super::inventory::{self, Inventory};
use super::lean;
use super::outcome::{self, Class, Conclusion, Site, Status, Verdict, word};
use super::paths::{self, Files, Git, Snapshot};
use super::process::{self, Ended, Limit, LimitBy, Ran, Spec};
use super::receipt::{self, Budgets, Failure, Mode, Receipt, Trigger};
use super::registry::{self, State, Target};
use super::toolchain::environment::{self, Installation, RunDirs, Tool};
use super::toolchain::{self, Manifest};
use super::{base, classify, externals, extract, guard, merge, mutants, qualify, storage, waiver};
use crate::manifests;
use crate::repo::{self, Entry, Tree};

/// The two phases of 3,600 s that the gate runs, from the start of a run.
pub const GATE_BUDGET: Duration = Duration::from_secs(7_200);

/// The time after [`GATE_BUDGET`] that the closing steps have.
pub const RECEIPT_MARGIN: Duration = Duration::from_secs(300);

/// The directory of the run directories, relative to the repository root.
pub const RUNS: &str = "artifacts/formal/runs";

/// A run directory, named by the Unix time, the process and a count.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RunDir {
    pub id: String,
    pub path: PathBuf,
}

impl RunDir {
    pub fn create(root: &Path) -> io::Result<RunDir> {
        static COUNT: AtomicU32 = AtomicU32::new(0);
        let count = COUNT.fetch_add(1, Ordering::Relaxed);
        let id = format!("{}-{}-{count}", unix_seconds(), std::process::id());
        fs::create_dir_all(root.join(RUNS))?;
        let path = root.join(RUNS).join(&id);
        fs::create_dir(&path)?;
        for directory in ["logs", "work/home", "work/tmp"] {
            fs::create_dir_all(path.join(directory))?;
        }
        Ok(RunDir { id, path })
    }

    /// The export of the gate inputs.
    pub fn source(&self) -> PathBuf {
        self.path.join("work/source")
    }

    pub fn receipt(&self) -> PathBuf {
        self.path.join("receipt.json")
    }
}

/// The body of a phase: it runs the commands of its units and concludes
/// them. An error or a panic in it stops the run.
pub type Body<'a> = Box<dyn FnOnce(&mut Gate) -> Result<(), String> + 'a>;

/// A phase of a run, with its budget and the units that it concludes.
pub struct Phase<'a> {
    pub name: String,
    pub budget: Duration,
    pub units: Vec<String>,
    pub body: Body<'a>,
}

/// The limit of a command: the smallest of the cap of its site, the rest of
/// its phase's budget and the rest of the gate's. On a tie the cap wins
/// over a budget, and the gate's budget over the phase's.
pub fn limit(cap: Option<Duration>, phase_left: Duration, gate_left: Duration) -> Limit {
    // `min_by_key` keeps the first of equal limits.
    let (duration, by) = cap
        .map(|cap| (cap, LimitBy::Cap))
        .into_iter()
        .chain([(gate_left, LimitBy::Gate), (phase_left, LimitBy::Phase)])
        .min_by_key(|(duration, _)| *duration)
        .unwrap_or((gate_left, LimitBy::Gate));
    Limit { duration, by }
}

/// The host of the tool manifest's column that this process runs on.
pub fn host() -> Option<&'static str> {
    match (OS, ARCH) {
        ("linux", "aarch64") => Some("linux-aarch64"),
        ("macos", "aarch64") => Some("darwin-arm64"),
        _ => None,
    }
}

fn unix_seconds() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_or(0, |since| since.as_secs())
}

fn relative(base: &Path, path: &Path) -> String {
    match path.strip_prefix(base) {
        Ok(rest) if rest.as_os_str().is_empty() => ".".to_string(),
        Ok(rest) => rest.to_string_lossy().into_owned(),
        Err(_) => path.to_string_lossy().into_owned(),
    }
}

/// What a run takes from its caller: `host` as [`host`] finds it, `uid`,
/// the effective user, and `var` for the variables of the process environment.
pub(crate) struct Context<'a> {
    pub root: &'a Path,
    pub layout: &'a Layout,
    pub host: Option<&'a str>,
    pub uid: u32,
    pub var: &'a dyn Fn(&str) -> Option<String>,
    /// The budget of the run in place of [`GATE_BUDGET`].
    pub budget: Option<Duration>,
    /// Whether the run keeps its work directory, which it otherwise removes
    /// at its end.
    pub keep: bool,
    /// Reads the bytes available on the file system of a path:
    /// [`process::disk_available`], or a reading that a test gives.
    pub free: fn(&Path) -> Option<u64>,
    /// The part of the run, if any: `qualification`, `lane/<name>` or `target/<name>/1`.
    pub shard: Option<&'a str>,
    /// Whether the run of a lane is that of its comparator, which reads the
    /// base record of its base run.
    pub comparator: bool,
}

/// A command, with the environment of `tool` and its input from `stdin`.
pub struct Request<'a> {
    pub site: Site,
    pub tool: Tool<'a>,
    pub program: &'a str,
    pub args: &'a [String],
    pub cwd: &'a Path,
    pub stdin: Option<&'a Path>,
}

/// What the commands of a run write while they run, which threads that
/// run commands side by side share: the commands recorded, in the order in
/// which they ended, the conclusions, the number of commands started and,
/// by its sequence, the unit, the start and, once it has ended, the end of
/// each command that is not recorded yet.
#[derive(Default)]
pub(super) struct Records {
    pub(super) commands: Vec<receipt::Command>,
    conclusions: Vec<(String, Conclusion)>,
    started: u32,
    running: BTreeMap<u32, (Option<String>, f64, Option<f64>)>,
}

impl Records {
    /// The seconds, up to `now`, during which a command of a unit whose
    /// budget is that of `owner` ran: the length of the union of their
    /// intervals, from the run's start.
    fn spent(&self, owner: &str, now: f64) -> f64 {
        let mine = |unit: &Option<String>| unit.as_deref().map(mutants::owner) == Some(owner);
        let ended = (self.commands.iter()).filter(|c| mine(&c.unit));
        let running = (self.running.values()).filter(|(unit, ..)| mine(unit));
        let ended = ended.map(|c| (c.started, c.started + c.seconds));
        covered(ended.chain(running.map(|(_, start, end)| (*start, end.unwrap_or(now)))))
    }
}

/// The length of the union of `intervals`, each its start and its end.
pub fn covered(intervals: impl IntoIterator<Item = (f64, f64)>) -> f64 {
    let mut intervals = Vec::from_iter(intervals);
    intervals.sort_by(|a, b| a.0.total_cmp(&b.0));
    let (mut length, mut reached) = (0.0, f64::NEG_INFINITY);
    for (start, end) in intervals {
        length += (end - start.max(reached)).max(0.0);
        reached = reached.max(end);
    }
    length
}

/// The state of a run, through which the body of a phase runs its commands.
pub struct Gate {
    root: PathBuf,
    layout: Layout,
    run: RunDir,
    /// The tool manifest that the run read from the checkout, and its text.
    manifest: Option<(Manifest, String)>,
    /// The start of the run, from which the receipt gives the start of each command.
    start: Instant,
    deadline: Instant,
    /// Whether it is a run of `formal mutants`, whose targets do not grow its budget.
    fixed: bool,
    /// The phase that runs, and its deadline.
    phase: Option<(String, Instant)>,
    records: Mutex<Records>,
    /// Phases fill only their own records and read the rest; commands, units
    /// and failures are written by the gate.
    pub(super) receipt: Receipt,
    /// The modules whose errors and warnings make a failed base build a
    /// proof failure, which the base round sets.
    pub(super) own: Vec<String>,
    /// The budget of the unit of each target that the run selects.
    budgets: BTreeMap<String, Duration>,
    /// The inventory of the export, when the run selects targets.
    inventory: Option<(Inventory, BTreeSet<String>)>,
    /// The hand-written module files of the Lake project, which the base
    /// round finds and the stages of the targets hold too.
    pub(super) handwritten: Vec<String>,
    /// What the waivers that hold leave out of the base round, which the
    /// qualification job finds when it extracts.
    pub(super) waived: waiver::LeftOut,
    /// Whether the run keeps its work directory and what it extracted.
    pub(super) keep: bool,
    progress: Mutex<Box<dyn Write + Send>>,
    /// The site, limit and program that a test gives the commands there.
    #[cfg(test)]
    pub(crate) overrides: Option<(Site, Limit, String)>,
}

impl Gate {
    fn fail(&mut self, status: Status, message: String) {
        self.receipt.failures.push(Failure { status, message });
    }

    /// The records of the commands, as a thread that panicked with them left them.
    pub(super) fn records(&self) -> MutexGuard<'_, Records> {
        self.records.lock().unwrap_or_else(PoisonError::into_inner)
    }

    /// Runs `request` unless its limit is used up or `skip` says why it does
    /// not start, reads with `read` what it wrote, which returns why a file
    /// could not be read, then classifies, records and prints it; a line
    /// that cannot be printed is left out. Threads may run commands side by
    /// side.
    fn command(
        &self,
        unit: Option<&str>,
        request: &Request,
        skip: Option<&str>,
        read: &mut dyn FnMut(&Ran) -> Option<String>,
    ) -> (Option<Ran>, Verdict) {
        #[cfg(test)]
        let overridden = (self.overrides.clone()).filter(|(site, ..)| *site == request.site);
        #[cfg(test)]
        let request = &Request {
            program: (overridden.as_ref()).map_or(request.program, |(_, _, program)| program),
            ..*request
        };
        let mut records = self.records();
        records.started += 1;
        let (sequence, now) = (records.started, Instant::now());
        let at = now.saturating_duration_since(self.start);
        let left = |end: Instant| end.saturating_duration_since(now);
        let phase_end = self.phase.as_ref().map_or(self.deadline, |(_, end)| *end);
        let mut limit = limit(request.site.cap(), left(phase_end), left(self.deadline));
        // The commands of a target's unit, and of its mutants, share its
        // budget, which counts the time during which any of them runs.
        let owner = unit.map(mutants::owner);
        if let Some((owner, budget)) = owner.and_then(|o| Some((o, self.budgets.get(o)?))) {
            let spent = Duration::from_secs_f64(records.spent(owner, at.as_secs_f64()));
            let rest = budget.saturating_sub(spent);
            if rest < limit.duration {
                (limit.duration, limit.by) = (rest, LimitBy::Target);
            }
        }
        #[cfg(test)]
        let limit = overridden.as_ref().map_or(limit, |(_, set, _)| *set);
        let name = word(&request.site);
        // The receipt writes a limit below half a millisecond as 0.
        let starts = receipt::seconds(limit.duration) > 0.0 && skip.is_none();
        if starts {
            let running = (unit.map(str::to_string), receipt::seconds(at), None);
            records.running.insert(sequence, running);
        }
        drop(records);
        let ran = if receipt::seconds(limit.duration) <= 0.0 {
            let used_up = format!("the {} budget was used up", word(&limit.by));
            Err((Class::NotRun, used_up))
        } else if let Some(reason) = skip {
            Err((Class::NotRun, format!("not started: {reason}")))
        } else {
            let (manifest, _) = (self.manifest.as_ref()).expect("commands run after the start");
            let host = self.receipt.host.as_deref().unwrap_or_default();
            let work = WORK.with_borrow(Clone::clone).unwrap_or(self.work());
            let [home, tmp] = ["home", "tmp"].map(|dir| work.join(dir));
            let dirs = RunDirs { home, tmp };
            environment::environment(request.tool, manifest, host, &self.root, &dirs)
                .map(|env| {
                    process::run(&Spec {
                        name: &name,
                        program: request.program,
                        args: request.args,
                        cwd: request.cwd,
                        env: &env,
                        stdin: request.stdin,
                        logs: &self.run.path.join("logs"),
                        sequence,
                        limit,
                        begin: now,
                    })
                })
                .map_err(|error| {
                    let reason = format!("{name}: cannot set up its environment: {error}");
                    (Class::ToolFailure, reason)
                })
        };
        // A command that ended counts by its interval until it is recorded.
        let seconds = receipt::seconds(ran.as_ref().map_or(Duration::ZERO, |ran| ran.seconds));
        if let Some((.., end)) = self.records().running.get_mut(&sequence) {
            *end = Some(receipt::seconds(at) + seconds);
        }
        let own = |ran: &Ran| lean::proof_messages(&ran.output, &self.own).len();
        let verdict = match &ran {
            Ok(ran) => outcome::classify(request.site, ran, own(ran), read(ran).as_deref()),
            Err((class, reason)) => Verdict {
                class: *class,
                reason: Some(reason.clone()),
            },
        };
        let ran = ran.ok();
        let done = ran.as_ref();
        let mut argv = vec![request.program.to_string()];
        argv.extend_from_slice(request.args);
        let (shown, class) = (argv.join(" "), word(&verdict.class));
        let reason = verdict.reason.as_ref().map(|reason| format!(": {reason}"));
        let reason = reason.unwrap_or_default();
        let mut progress = self.progress.lock().unwrap_or_else(PoisonError::into_inner);
        let _ = writeln!(progress, "[{sequence:04}] {shown}: {class}{reason}");
        drop(progress);
        let log = |log: &Option<process::Log>| {
            log.as_ref().map(|log| receipt::Log {
                path: relative(&self.run.path, &log.path),
                bytes: log.bytes,
                sha256: log.sha256.clone(),
            })
        };
        let mut records = self.records();
        records.running.remove(&sequence);
        records.commands.push(receipt::Command {
            sequence,
            started: receipt::seconds(at),
            phase: self.phase.as_ref().map(|(phase, _)| phase.clone()),
            unit: unit.map(str::to_string),
            site: request.site,
            argv,
            cwd: relative(&self.root, request.cwd),
            class: verdict.class,
            reason: verdict.reason.clone(),
            exit_code: done.and_then(Ran::code),
            signal: done.and_then(|ran| match ran.ended {
                Ended::Signaled(signal) => Some(signal),
                _ => None,
            }),
            timed_out: done.is_some_and(|ran| ran.ended == Ended::TimedOut),
            limit_seconds: receipt::seconds(limit.duration),
            limit: limit.by,
            seconds,
            group_survived: done.is_some_and(|ran| ran.survivors),
            stdout: done.and_then(|ran| log(&ran.stdout)),
            stderr: done.and_then(|ran| log(&ran.stderr)),
        });
        (ran, verdict)
    }

    /// Runs a command of the gate itself and returns its standard output, or
    /// why it did not pass.
    fn output(&self, request: &Request) -> Result<Vec<u8>, String> {
        let (ran, verdict) = self.command(None, request, None, &mut |_| None);
        match ran.and_then(|ran| ran.stdout) {
            Some(log) if verdict.class == Class::Passed => fs::read(&log.path)
                .map_err(|error| format!("cannot read {}: {error}", log.path.display())),
            _ => Err(verdict.reason.unwrap_or_default()),
        }
    }

    /// Runs `request` as a command of `unit`, with `read` reading the files
    /// that it wrote before it is classified, so that a file that `read`
    /// cannot read makes it a tool failure; returns what it gave, if it ran,
    /// its class, and what `read` read.
    pub fn run<T>(
        &self,
        unit: &str,
        request: &Request,
        mut read: impl FnMut(&Ran) -> Result<T, String>,
    ) -> (Option<Ran>, Verdict, Option<T>) {
        let mut value = None;
        let mut reader = |ran: &Ran| read(ran).map(|read| value = Some(read)).err();
        let (ran, verdict) = self.command(Some(unit), request, None, &mut reader);
        (ran, verdict, value)
    }

    /// Records `request` as a command of `unit` that does not start because
    /// of `reason`, such as a missing input: `NOT_RUN`, with the limit that
    /// it would have had.
    pub fn skip(&self, unit: &str, request: &Request, reason: &str) {
        self.command(Some(unit), request, Some(reason), &mut |_| None);
    }

    /// Concludes `unit` with `conclusion`, unless a command of the unit
    /// forces another one ([`outcome::forced`]), and returns its status.
    pub fn conclude(&self, unit: &str, conclusion: Conclusion) -> Status {
        self.conclude_from(unit, unit, conclusion)
    }

    /// Concludes `unit` as [`Gate::conclude`] does, from the commands of the
    /// unit `of`, such as a theorem from those of its case.
    pub fn conclude_from(&self, unit: &str, of: &str, conclusion: Conclusion) -> Status {
        // A command skipped with its limit left forces nothing: the command
        // that should have written its input decides.
        let skipped = |command: &receipt::Command| {
            command.class == Class::NotRun && command.limit_seconds > 0.0
        };
        let mut records = self.records();
        let own: Vec<Verdict> = (records.commands.iter())
            .filter(|command| command.unit.as_deref() == Some(of) && !skipped(command))
            .map(|command| Verdict {
                class: command.class,
                reason: command.reason.clone(),
            })
            .collect();
        let conclusion = outcome::forced(&own).unwrap_or(conclusion);
        records
            .conclusions
            .push((unit.to_string(), conclusion.clone()));
        conclusion.0
    }

    pub fn source(&self) -> PathBuf {
        self.run.source()
    }

    /// The work directory of the run, which holds the export.
    pub fn work(&self) -> PathBuf {
        self.run.path.join("work")
    }

    pub fn layout(&self) -> &Layout {
        &self.layout
    }

    /// Takes the deadline of the run from that of a run that started at the
    /// Unix time `started` with the budget `seconds`.
    pub(super) fn continue_from(&mut self, started: u64, seconds: u64) {
        let end = Duration::from_secs(started.saturating_add(seconds));
        let elapsed = Duration::from_secs(self.receipt.started);
        self.deadline = self.start + end.saturating_sub(elapsed);
    }

    /// The tool installation that the run uses.
    pub fn installation(&self) -> Result<Installation, String> {
        let (manifest, _) = (self.manifest.as_ref()).expect("phases run after the start");
        let host = self.receipt.host.as_deref().unwrap_or_default();
        environment::installation(manifest, host, &self.root)
    }
}

/// Git in the repository root, with literal pathspecs and without the
/// optional locks that would write to the repository.
impl Git for Gate {
    fn git(&mut self, args: &[&str], stdin: Option<&Path>) -> Result<Vec<u8>, String> {
        let options = ["--literal-pathspecs", "--no-optional-locks"];
        let args: Vec<String> = (options.iter().chain(args))
            .map(|arg| arg.to_string())
            .collect();
        let root = self.root.clone();
        self.output(&Request {
            site: Site::Git,
            tool: Tool::Git,
            program: "git",
            args: &args,
            cwd: &root,
            stdin,
        })
    }
}

/// The receipt of a run that has not done anything yet, of the mode that
/// [`receipt::mode`] gives unless it is scoped, and failed by its error.
fn blank(context: &Context, targets: &BTreeSet<String>, run: &str, directory: &str) -> Receipt {
    let (mode, status) = (receipt::mode(context.var), Status::ToolFailure);
    Receipt {
        schema: receipt::SCHEMA,
        command: receipt::COMMAND.to_string(),
        trigger: Trigger {
            mode: if targets.is_empty() || context.shard.is_some() {
                mode.clone().unwrap_or_default()
            } else {
                Mode::Scoped
            },
            event: (context.var)("GITHUB_EVENT_NAME"),
            reference: (context.var)("GITHUB_REF"),
            run_id: (context.var)("GITHUB_RUN_ID"),
            attempt: (context.var)("GITHUB_RUN_ATTEMPT"),
        },
        targets: targets.iter().cloned().collect(),
        shard: context.shard.map(str::to_string),
        host: context.host.map(str::to_string),
        image: (context.host == Some(toolchain::HOSTS[0])).then(|| receipt::Image {
            reference: (context.var)("KREPI_FORMAL_IMAGE"),
            uid: context.uid,
            os_release: fs::read_to_string("/etc/os-release").ok(),
            ..Default::default()
        }),
        run: run.to_string(),
        directory: directory.to_string(),
        started: unix_seconds(),
        budgets: Budgets {
            gate_seconds: context.budget.unwrap_or(GATE_BUDGET).as_secs(),
            receipt_margin_seconds: RECEIPT_MARGIN.as_secs(),
        },
        failures: Vec::from_iter(mode.err().map(|message| Failure { status, message })),
        ..Receipt::default()
    }
}

thread_local! {
    /// The work directory of the mutant whose commands this thread runs,
    /// whose `home` and `tmp` they take in place of those of the run.
    static WORK: RefCell<Option<PathBuf>> = const { RefCell::new(None) };
}

/// Runs `f` with the commands that it runs on this thread in the home and
/// temporary directories `home` and `tmp` of `work`, which it creates.
pub(super) fn in_work<T>(work: &Path, f: impl FnOnce() -> Result<T, String>) -> Result<T, String> {
    for dir in ["home", "tmp"].map(|dir| work.join(dir)) {
        fs::create_dir_all(&dir).map_err(|error| format!("{}: {error}", dir.display()))?;
    }
    struct Restore(Option<PathBuf>);
    impl Drop for Restore {
        fn drop(&mut self) {
            WORK.set(self.0.take());
        }
    }
    let _restore = Restore(WORK.replace(Some(work.to_path_buf())));
    f()
}

/// Runs `f`, and makes a panic in it an error with the panic's text.
pub(super) fn caught<T>(f: impl FnOnce() -> T) -> Result<T, String> {
    panic::catch_unwind(AssertUnwindSafe(f)).map_err(|payload| {
        let text = payload
            .downcast_ref::<&str>()
            .map(|text| text.to_string())
            .or_else(|| payload.downcast_ref::<String>().cloned())
            .unwrap_or_default();
        format!("panicked: {text}")
    })
}

/// Runs the gate on `context.root` into `run` for `targets`, or the whole
/// gate when there are none, and returns its receipt, which holds every
/// failure, and the draft of the list of survivors of a run of `formal
/// mutants`, read before the work directory is removed. A panic in a step
/// of the gate ends the run as a tool failure.
pub(crate) fn execute(
    context: &Context,
    run: &RunDir,
    targets: &BTreeSet<String>,
    phases: Vec<Phase<'_>>,
    progress: Box<dyn Write + Send>,
) -> (Receipt, Option<String>) {
    let start = Instant::now();
    let directory = relative(context.root, &run.path);
    let mut gate = Gate {
        root: context.root.to_path_buf(),
        layout: *context.layout,
        run: run.clone(),
        manifest: None,
        start,
        deadline: start + context.budget.unwrap_or(GATE_BUDGET),
        fixed: context.budget == Some(mutants::RUN_BUDGET),
        phase: None,
        records: Mutex::default(),
        receipt: blank(context, targets, &run.id, &directory),
        own: Vec::new(),
        budgets: BTreeMap::new(),
        inventory: None,
        handwritten: Vec::new(),
        waived: waiver::LeftOut::new(),
        keep: context.keep,
        progress: Mutex::new(progress),
        #[cfg(test)]
        overrides: None,
    };
    let resources = &mut gate.receipt.resources;
    resources.disk_available_at_start = (context.free)(&run.path);
    resources.disk_least_available = resources.disk_available_at_start;
    // A thread reads the free space until the second snapshot is taken.
    let (stop, stopped) = mpsc::channel::<()>();
    let sampler = storage::sample(run.path.clone(), context.free, storage::SAMPLE, stopped);
    if let Err(error) = &sampler {
        let error = format!("cannot start the reading of the free space: {error}");
        gate.fail(Status::ToolFailure, error);
    }
    let inputs = paths::gate_inputs(context.layout);
    let mut phases = Some(phases);
    let steps = caught(|| {
        let started = take_start(&mut gate, &inputs);
        // An error of the start, or of the export and its checks, fails the run.
        let checked = (started.clone())
            .and_then(|(commit, before)| export_and_check(&mut gate, &inputs, &commit, &before));
        if let Err(error) = checked {
            gate.fail(Status::ToolFailure, error);
        }
        if gate.receipt.failures.is_empty()
            && let Err(error) = disk_guard(&mut gate)
        {
            gate.fail(Status::ToolFailure, error);
        }
        // No command may write the library or Lean, from the first phase to the last.
        let listing = (gate.receipt.failures.is_empty()).then(|| backend_listing(&gate, None));
        if let Some(Err(error)) = &listing {
            let error = format!("cannot list the installation before the first phase: {error}");
            gate.fail(Status::ToolFailure, error);
        }
        run_phases(&mut gate, phases.take().unwrap_or_default());
        if let Some(Ok(before)) = &listing
            && let Err(error) = backend_listing(&gate, Some(before))
        {
            let changed = "the tool installation changed during the ";
            let error = match error.strip_prefix(&format!("{changed}phase")) {
                Some(rest) => format!("{changed}run{rest}"),
                None => format!("cannot list the installation after the last phase: {error}"),
            };
            gate.fail(Status::ToolFailure, error);
        }
        // The closing steps have the margin beyond the gate's budget.
        gate.deadline += RECEIPT_MARGIN;
        if let Ok((_, before)) = started
            && let Err(error) = take_end(&mut gate, &inputs, &before)
        {
            gate.fail(Status::ToolFailure, error);
        }
    });
    if let Err(error) = steps {
        gate.fail(Status::ToolFailure, format!("the run {error}"));
        // Phases that a panic left before them run none and account for their units.
        if let Some(phases) = phases {
            run_phases(&mut gate, phases);
        }
    }
    drop(stop);
    let joined = sampler.map(|thread| thread.join());
    if let Ok(Err(_)) = &joined {
        let panicked = "the reading of the free space panicked";
        gate.fail(Status::ToolFailure, panicked.to_string());
    }
    let least = joined.ok().and_then(Result::ok).flatten();
    let resources = &mut gate.receipt.resources;
    resources.disk_least_available = least
        .into_iter()
        .chain(resources.disk_least_available)
        .min();
    let draft = fs::read_to_string(gate.work().join(mutants::DRAFT)).ok();
    // A stop signal before the removal ends the run with its work directory.
    process::stop_if_asked();
    if !context.keep {
        if let Err(error) = storage::remove(&[gate.work()]) {
            gate.fail(Status::ToolFailure, error);
        } else if Instant::now() > gate.deadline {
            let late =
                "the removal of the work directory ended after the deadline of the closing steps";
            gate.fail(Status::ToolFailure, late.to_string());
        }
    }
    let mut commands = std::mem::take(&mut gate.records().commands);
    commands.sort_by_key(|command| command.sequence);
    let mut receipt = gate.receipt;
    receipt.commands = commands;
    mutants::seconds(&mut receipt);
    receipt.resources.largest_process_max_rss = process::largest_child_rss();
    receipt.resources.cgroup_memory_peak = process::cgroup_memory_peak();
    conclude(&mut receipt, !targets.is_empty() && context.shard.is_none());
    receipt.seconds = receipt::seconds(start.elapsed());
    (receipt, draft)
}

/// Concludes `receipt`, which is `scoped` or not, from its failures and units.
pub(super) fn conclude(receipt: &mut Receipt, scoped: bool) {
    let failures = receipt.failures.iter().map(|failure| failure.status);
    let units = receipt.units.values().map(|unit| unit.status);
    // Every failure but STALE stops the run or makes it a tool failure.
    let complete = !scoped
        && failures.clone().all(|status| status == Status::Stale)
        && (units.clone()).all(|status| !matches!(status, Status::NotRun | Status::Budget));
    // A run that the disk guard refused is NOT_RUN, whatever else it found.
    let status = match failures.clone().any(|status| status == Status::NotRun) {
        true => Status::NotRun,
        false => outcome::run_status(&failures.chain(units).collect::<Vec<_>>(), scoped),
    };
    (receipt.complete, receipt.status) = (complete, status);
}

/// Checks the host, reads the tool manifest and takes the snapshot of the
/// start, whose gate inputs must be clean.
fn take_start(gate: &mut Gate, inputs: &[&str]) -> Result<(String, Snapshot), String> {
    if gate.receipt.host.is_none() {
        let hosts = toolchain::HOSTS.join(" and ");
        return Err(format!(
            "the host is {OS}-{ARCH}, and the tools are pinned for {hosts} only"
        ));
    }
    let path = gate.layout.toolchain;
    let manifest = fs::read_to_string(gate.root.join(path))
        .map_err(|error| error.to_string())
        .and_then(|text| Ok((toolchain::parse(&text)?, text)));
    gate.manifest = Some(manifest.map_err(|error| format!("cannot read {path}: {error}"))?);
    let (commit, tree, before) = paths::snapshot(gate, inputs)
        .map_err(|error| format!("cannot take the snapshot of the gate inputs: {error}"))?;
    (gate.receipt.commit, gate.receipt.tree) = (Some(commit.clone()), Some(tree));
    gate.receipt.inputs.before = Some(before.clone());
    let changes = paths::changes(gate, inputs)
        .map_err(|error| format!("cannot find whether the gate inputs are clean: {error}"))?;
    if !changes.is_empty() {
        let changes = changes.join(", ");
        return Err(format!(
            "the gate inputs are not clean at the start of the run: {changes}"
        ));
    }
    Ok((commit, before))
}

/// Exports the snapshot and checks the tool manifest, the targets and the
/// rules of the gate inputs; a rule that rejects the run adds its failure.
fn export_and_check(
    gate: &mut Gate,
    inputs: &[&str],
    commit: &str,
    before: &Snapshot,
) -> Result<(), String> {
    // `git archive` fails on a path that the commit does not have.
    let present: Vec<&str> = (inputs.iter().copied())
        .filter(|input| before.get(*input).is_some_and(Option::is_some))
        .collect();
    let (work, source) = (gate.run.path.join("work"), gate.run.source());
    let files = paths::export(gate, commit, &present, &work, &source)
        .map_err(|error| format!("cannot export the snapshot: {error}"))?;
    let (toolchain, registry) = (gate.layout.toolchain, gate.layout.registry);
    let read = fs::read_to_string(source.join(toolchain)).ok();
    if read.as_ref() != gate.manifest.as_ref().map(|(_, text)| text) {
        return Err(format!(
            "{toolchain} of the snapshot is not the file that the run read at its start"
        ));
    }
    let prefix = gate.installation()?.prefix;
    let pin = source.join(gate.layout.image_pin);
    if let Some((image, (_, text))) = gate.receipt.image.as_mut().zip(gate.manifest.as_ref()) {
        let problems = toolchain::image(image, &prefix, text, &pin);
        if !problems.is_empty() {
            return Err(format!("image: {}", problems.join("; ")));
        }
    }
    let (states, registered) = fs::read_to_string(source.join(registry))
        .map_err(|error| error.to_string())
        .and_then(|text| Ok((registry::states(&text)?, registry::parse(&text)?.targets)))
        .map_err(|error| format!("cannot read {registry}: {error}"))?;
    let (targets, shard) = (&gate.receipt.targets, gate.receipt.shard.is_some());
    // The target of a shard is a formal one.
    let planned = |name: &String| shard && states[name].0 == State::Planned;
    let unknown: Vec<&str> = (targets.iter())
        .filter(|target| !states.contains_key(*target) || planned(target))
        .map(String::as_str)
        .collect();
    if !unknown.is_empty() {
        let (unknown, formal) = (unknown.join(", "), ["", "formal "][usize::from(shard)]);
        let error = format!("{registry} registers no {formal}target named {unknown}");
        return Err(error);
    }
    let chosen = selected(&states, targets, shard);
    // A run with a base round extracts every formal target for it, and the
    // planned ones that hand-written modules import.
    let part = gate.receipt.shard.as_deref();
    let round = !alone(part, !targets.is_empty(), gate.fixed);
    let imported = round && !base::planned_imports(&source, &gate.layout, &registered)?.is_empty();
    let formal = states.values().any(|(state, _)| *state == State::Formal);
    let extracts = !chosen.is_empty() || formal || imported;
    // The gate's budget grows by the budget of each target that it selects.
    let budget = |name: &str| Duration::from_secs(states[name].1);
    let all: Duration =
        chosen.iter().map(|name| budget(name)).sum::<Duration>() * u32::from(!gate.fixed);
    gate.deadline += all;
    gate.receipt.budgets.gate_seconds += all.as_secs();
    gate.budgets = BTreeMap::from_iter(chosen.iter().map(|name| (target_unit(name), budget(name))));
    // The deadline of a lane grows by its registered budget.
    if let Some(name) = part.and_then(merge::lane) {
        let lanes = base::lanes(&source, &gate.layout)?;
        let lane = lanes.iter().find(|lane| lane.name == name);
        let lane = lane.ok_or(format!(
            "{} registers no lane named {name}",
            gate.layout.lanes
        ))?;
        gate.deadline += Duration::from_secs(lane.budget);
        gate.receipt.budgets.gate_seconds += lane.budget;
    }
    for problem in paths::rejected(&files, &gate.layout) {
        gate.fail(Status::Rejected, problem);
    }
    check_kernel(gate, &source, &files, extracts)
}

/// Refuses the run, with a failure `NOT_RUN`, when the file system of its
/// directory had less free at its start than 1.5 times the disk peak that
/// the shard plan of the export gives its parts: the part of a run of one,
/// and otherwise the qualification and the part of each target that it
/// selects.
fn disk_guard(gate: &mut Gate) -> Result<(), String> {
    let path = gate.layout.shards;
    let plan = fs::read_to_string(gate.source().join(path))
        .map_err(|error| error.to_string())
        .and_then(|text| storage::parse(&text))
        .map_err(|error| format!("cannot read {path}: {error}"))?;
    let free = (gate.receipt.resources.disk_available_at_start)
        .ok_or("the bytes available on the file system of the run directory cannot be read")?;
    let selected = (gate.budgets.keys()).filter_map(|unit| merge::target(unit).map(merge::part));
    let parts = match gate.receipt.shard.clone() {
        Some(shard) => vec![shard],
        None => Vec::from_iter([qualify::PHASE.to_string()].into_iter().chain(selected)),
    };
    if let Some(refusal) = storage::refusal(&plan, &parts, free) {
        gate.fail(Status::NotRun, refusal);
    }
    Ok(())
}

/// The listing of the Aeneas Lean library of the installation, with its
/// packages, and of Lean, which no command may write; with `before`, it
/// fails when they differ.
fn backend_listing(gate: &Gate, before: Option<&lean::Listing>) -> Result<lean::Listing, String> {
    let installation = gate.installation()?;
    lean::listing(
        &[installation.backend(), installation.lean_bin().join("..")],
        before,
    )
}

/// The targets that a run of `named` targets selects: those, or every
/// formal target of the registry when it names none and is no `shard`, for
/// a planned target runs only when it is named.
fn selected<'a>(
    states: &'a BTreeMap<String, (State, u64)>,
    named: &'a [String],
    shard: bool,
) -> Vec<&'a str> {
    let formal = |(name, (state, _)): (&'a String, &(State, u64))| {
        (*state == State::Formal).then_some(name.as_str())
    };
    match named {
        [] if !shard => states.iter().filter_map(formal).collect(),
        named => named.iter().map(String::as_str).collect(),
    }
}

/// Checks the exported kernel workspace: that Cargo reads no Cargo
/// configuration but the snapshot's, which is a file, in the export and in
/// the checkout root when it has the same bytes there; that its path
/// dependencies stay inside it; with Cargo resolving it offline, that its
/// packages are its members inside it and its root manifest has its shape;
/// and, when the run `extracts` kernel targets, that the workspace has the
/// root package that they are extracted from.
fn check_kernel(
    gate: &mut Gate,
    source: &Path,
    files: &Files,
    extracts: bool,
) -> Result<(), String> {
    let resolved = |path: &Path| {
        fs::canonicalize(path)
            .map_err(|error| format!("cannot resolve {}: {error}", path.display()))
    };
    let (root, export) = (resolved(&gate.root)?, resolved(source)?);
    let own = (files.get(paths::CARGO_CONFIG))
        .filter(|entry| matches!(entry.mode.as_str(), "100644" | "100755"))
        .and_then(|_| fs::read(export.join(paths::CARGO_CONFIG)).ok());
    let mut found = Vec::new();
    for directory in export.ancestors() {
        for path in [paths::CARGO_CONFIG, ".cargo/config"].map(|name| directory.join(name)) {
            let snapshot = (directory == export || directory == root)
                && path.ends_with(paths::CARGO_CONFIG)
                && own.is_some()
                && fs::read(&path).ok() == own;
            if fs::symlink_metadata(&path).is_ok() && !snapshot {
                let path = path.display();
                found.push(format!(
                    "Cargo would read {path} in the export, which is not in the snapshot"
                ));
            }
        }
    }
    let rejected = manifests::kernel_dependency_problems(source, files.keys())?;
    if !found.is_empty() || !rejected.is_empty() {
        for problem in found {
            gate.fail(Status::ToolFailure, problem);
        }
        for problem in rejected {
            gate.fail(Status::Rejected, problem);
        }
        return Ok(());
    }
    let metadata = gate
        .output(&Request {
            site: Site::CargoMetadata,
            tool: Tool::CargoMetadata,
            program: "cargo",
            args: &manifests::kernel_metadata_args(gate.layout.kernel),
            cwd: source,
            stdin: None,
        })
        .and_then(|bytes| {
            serde_json::from_slice(&bytes)
                .map_err(|error| format!("its output is not JSON: {error}"))
        })
        .map_err(|error| format!("cannot resolve the kernel workspace: {error}"))?;
    let (dir, kernel) = (gate.layout.kernel, source.join(gate.layout.kernel));
    for problem in manifests::check_kernel_metadata(&metadata, &kernel, [dir, gate.layout.package])
    {
        gate.fail(Status::Rejected, problem);
    }
    // The inventory of the export, which the registration checks read.
    if extracts {
        let mut tree = Tree::default();
        let rust = |path: &&String| path.ends_with(".rs") && repo::is_within(path, dir);
        for path in files.keys().filter(rust) {
            let text = fs::read(source.join(path)).map_err(|error| format!("{path}: {error}"))?;
            tree.insert(path, Entry::File(text));
        }
        let roots = inventory::roots(&metadata, dir)?;
        gate.inventory = Some(inventory::inventory(&tree, &roots, dir));
    }
    let path = format!("{}/Cargo.toml", gate.layout.kernel);
    let root = fs::read_to_string(source.join(&path))
        .map_err(|error| format!("cannot read {path}: {error}"))?;
    let package = manifests::root_package(&root).map_err(|error| format!("{path}: {error}"))?;
    if extracts && package.as_deref() != Some(gate.layout.package) {
        gate.fail(
            Status::Rejected,
            format!(
                "the run extracts kernel targets, and {path} has no [package] named {}, the root package that they are extracted from",
                gate.layout.package
            ),
        );
    }
    Ok(())
}

/// The unit of the target `name`.
pub fn target_unit(name: &str) -> String {
    format!("target/{name}")
}

/// The directory of the Lake project in the stage of the target `name`.
pub fn target_project(gate: &Gate, name: &str) -> PathBuf {
    let project = (Path::new(gate.layout.project).file_name()).unwrap_or_default();
    let stage = gate.work().join("targets").join(name).join("stage");
    stage.join(project)
}

/// The phases of the targets of the registry of the checkout `root`:
/// `extraction`, before the base round, which extracts the selected targets,
/// the formal ones and the planned ones whose generated modules a
/// hand-written module imports, which the base round builds, and concludes
/// the selected planned ones; and `targets`, after it, which concludes the
/// selected formal ones and their mutants, the source mutants of `generate`
/// in a run that generates them. The first stops on another registry, or
/// other imports of planned targets, in the export; a run of targets
/// [`alone`] extracts them alone, and a lane those of its modules
/// ([`lane_targets`]) but those of a waiver that holds.
pub(super) fn target_phases<'a>(
    root: &Path,
    layout: &Layout,
    named: &BTreeSet<String>,
    generate: Option<Vec<String>>,
    shard: Option<&str>,
) -> [Phase<'a>; 2] {
    let path = layout.registry;
    let read = fs::read_to_string(root.join(path)).map_err(|error| error.to_string());
    let read = read.and_then(|text| Ok((registry::parse(&text)?.targets, text)));
    let read = read.map_err(|error| format!("cannot read {path}: {error}"));
    let mut all = Vec::from_iter(read.iter().flat_map(|(targets, _)| targets.clone()));
    let states = BTreeMap::from_iter(all.iter().map(|t| (t.name.clone(), (t.state, t.budget))));
    let named = Vec::from_iter(named.iter().cloned());
    let chosen = selected(&states, &named, shard.is_some()).into_iter();
    let chosen = BTreeSet::from_iter(chosen.map(String::from));
    let alone = alone(shard, !named.is_empty(), generate.is_some());
    let lane = shard.and_then(merge::lane).map(str::to_string);
    // The base round builds the planned targets that hand-written modules
    // import, and that of a lane the targets of its modules.
    let imports = move |dir: &Path, layout: &Layout, targets: &[Target]| match (alone, &lane) {
        (true, _) => Ok(receipt::Lane::default()),
        (false, Some(lane)) => lane_targets(dir, layout, lane, targets),
        (false, None) => base::planned_imports(dir, layout, targets).map(|imported| {
            let targets = imported
                .into_iter()
                .map(|name| (name, receipt::Role::Planned));
            receipt::Lane {
                targets: targets.collect(),
                ..receipt::Lane::default()
            }
        }),
    };
    let start = (read.clone()).and_then(|(targets, _)| imports(root, layout, &targets));
    let imported = start.clone().unwrap_or_default().targets;
    let margin = shard.and_then(merge::lane).is_some();
    let extracted = |t: &Target| chosen.contains(&t.name) || imported.contains_key(&t.name);
    all.retain(|t| (t.state == State::Formal && !alone && !margin) || extracted(t));
    let pick = |t: &&Target, state| t.state == state && chosen.contains(&t.name);
    let formal = Vec::from_iter(all.iter().filter(|t| pick(t, State::Formal)).cloned());
    let planned = Vec::from_iter(all.iter().filter(|t| pick(t, State::Planned)).cloned());
    let units = |targets: &[Target]| Vec::from_iter(targets.iter().map(|t| target_unit(&t.name)));
    let sum = |targets: &[Target]| (targets.iter().map(|t| t.budget)).fold(0, u64::saturating_add);
    let budget = |targets: &[Target]| Duration::from_secs(sum(targets));
    let mut finish = units(&formal);
    finish.extend(
        formal
            .iter()
            .flat_map(|t| mutants::units(t, generate.is_some())),
    );
    let finished = generate
        .as_ref()
        .map_or(budget(&formal), |_| mutants::RUN_BUDGET);
    let extracting = [budget(&all), merge::EXTRACTION_MARGIN][usize::from(margin)];
    let phases = [
        ("extraction", extracting, units(&planned)),
        ("targets", finished, finish),
    ];
    let bodies: [Body<'a>; 2] = [
        Box::new(move |gate| {
            let (registered, text) = read?;
            if base::read(&gate.source().join(path))? != text {
                return Err(format!("{path} differs from the one read at the start"));
            }
            let start = start?;
            if imports(&gate.source(), &gate.layout, &registered)? != start {
                let other = "import other planned targets than at the start";
                return Err(format!("the hand-written modules of the export {other}"));
            }
            if margin {
                let waived;
                (waived, gate.waived) = waive(gate, &registered)?;
                all.retain(|t| t.state != State::Formal || !waived.contains(&t.name));
                gate.receipt.lane = Some(start);
            }
            (all.iter()).try_for_each(|t| extract_target(gate, t, chosen.contains(&t.name)))
        }),
        Box::new(move |gate| {
            // Without a base round, the run lists the hand-written modules.
            if alone && !formal.is_empty() {
                gate.handwritten = merge::handwritten(gate)?.0;
            }
            let generate = generate.as_deref();
            (formal.iter()).try_for_each(|t| finish_target(gate, t, generate))
        }),
    ];
    let mut phases = (phases.into_iter().zip(bodies)).map(|((name, budget, units), body)| {
        let name = name.to_string();
        Phase {
            name,
            budget,
            units,
            body,
        }
    });
    [(); 2].map(|()| phases.next().expect("two phases"))
}

/// The lane `name` of `layout` in `dir`, a checkout or an export, with what it
/// extracts of the registered `targets`: each formal one of its components, a
/// planned one of them that its own modules import, and any other that these
/// or the hand-written modules that they reach import. Links are not followed.
fn lane_targets(
    dir: &Path,
    layout: &Layout,
    name: &str,
    targets: &[Target],
) -> Result<receipt::Lane, String> {
    let lanes = base::lanes(dir, layout)?;
    let lane = lanes.iter().find(|lane| lane.name == name);
    let lane = lane.ok_or(format!("{} registers no lane named {name}", layout.lanes))?;
    let (project, mut imports) = (dir.join(layout.project), BTreeMap::new());
    let below = project.join(layout.namespace);
    let walk = walkdir::WalkDir::new(&below).into_iter();
    for entry in walk.filter(|_| below.is_dir()) {
        let entry = entry.map_err(|error| format!("cannot list {}: {error}", below.display()))?;
        if entry.file_type().is_file() && entry.path().extension().is_some_and(|e| e == "lean") {
            let file = entry.path().strip_prefix(&project).unwrap_or(entry.path());
            let module = file.with_extension("").to_string_lossy().replace('/', ".");
            imports.insert(module, base::header(entry.path())?);
        }
    }
    let homes = base::homes(layout, imports.keys().cloned());
    let part = format!("lane/{name}");
    let held =
        |m: &&String| base::part_of(&lanes, m, homes.get(*m)).as_deref() == Some(part.as_str());
    let own = BTreeSet::from_iter(imports.keys().filter(held).cloned());
    // The modules that the own ones import, directly or through others.
    let mut cone = own.clone();
    loop {
        let more = (cone.iter()).flat_map(|module| &imports[module]);
        let more = Vec::from_iter(more.filter(|m| imports.contains_key(*m) && !cone.contains(*m)));
        if more.is_empty() {
            break;
        }
        cone.extend(more.into_iter().cloned());
    }
    let of = |modules: &BTreeSet<String>| {
        let named = Vec::from_iter(modules.iter().flat_map(|module| imports[module].clone()));
        base::generating(layout, &named, targets)
    };
    let (direct, needed, mut found) = (of(&own), of(&cone), BTreeMap::new());
    for target in targets {
        let ours = target.module.iter().any(|m| lane.components.contains(m));
        let role = match (target.state, ours) {
            (registry::State::Formal, true) => receipt::Role::Formal,
            (registry::State::Planned, true) if direct.contains(&target.name) => {
                receipt::Role::Planned
            }
            _ if needed.contains(&target.name) => receipt::Role::Cone,
            _ => continue,
        };
        found.insert(target.name.clone(), role);
    }
    let mut held = receipt::Lane::default();
    (held.name, held.components, held.targets) = (name.to_string(), lane.components.clone(), found);
    Ok(held)
}

/// The targets of the waivers of the export of `gate` that hold today, with
/// the registered `targets`, and what they leave out of the base round.
pub(super) fn waive(
    gate: &Gate,
    targets: &[Target],
) -> Result<(BTreeSet<String>, waiver::LeftOut), String> {
    let waivers = waiver::read(&gate.source(), &gate.layout, targets)?;
    let waived = waiver::holding(&waivers, &waiver::today(SystemTime::now())?);
    let left = waiver::left_out(&gate.layout, targets, &waived);
    Ok((waived, left))
}

/// Extracts `target`, installs what the tools generated in its stage and
/// type-checks the generated definitions with warnings as errors, as
/// commands of its unit when the run selects it, `chosen`, and of `base`
/// otherwise; checks the registration of a selected formal target,
/// concludes a selected planned one and records it. A target with more
/// mutants than a target may register is not run and is `BUDGET`.
fn extract_target(gate: &mut Gate, target: &Target, chosen: bool) -> Result<(), String> {
    let (layout, name) = (gate.layout, &target.name);
    let unit = if chosen {
        target_unit(name)
    } else {
        base::unit_of(gate.receipt.shard.as_deref())
    };
    let mut record = receipt::Target {
        unit: chosen.then(|| unit.clone()),
        state: target.state,
        budget_seconds: target.budget,
        proof_modules: target.proof_modules.clone(),
        ..receipt::Target::default()
    };
    let many = target.mutants.len() > registry::MUTANTS;
    let module = (target.module.as_deref()).filter(|module| qualify::is_module(module) && !many);
    let work = gate.work().join("targets").join(name);
    if let Some(module) = module {
        let (package, extracted) = (gate.source().join(layout.kernel), work.join("extract"));
        let opaque = Vec::from_iter(target.opaque.iter().map(|opaque| opaque.pattern.clone()));
        let request = extract::Request {
            unit: &unit,
            module,
            package: &package,
            start_from: &target.start_from,
            opaque: &opaque,
            work: &extracted,
            triple: Some(layout.triple),
        };
        let extraction = extract::extract(gate, &request)?;
        record.observed = qualify::observed(std::slice::from_ref(&extraction));
        record.generated.clone_from(&extraction.files);
        let args = lean::build_args(&[format!("{}.{module}.Funs", layout.generated)], true);
        let project = target_project(gate, name);
        let check = qualify::lake(Site::TargetBuild, &args, &project);
        let installed = match extraction.complete {
            true => externals::stage(gate, target, &extraction, &work.join("stage"))?,
            false => Err("the extraction is not complete".to_string()),
        };
        match installed {
            Ok(kept) => {
                let (ran, verdict, _) = gate.run(&unit, &check, |_| Ok(()));
                (record.declarations, record.typed) = (kept, verdict.class == Class::Passed);
                let failed = ran.filter(|_| verdict.class == Class::ProofFailure);
                let errors = failed.map(|ran| lean::errors(&ran.output).join(" | "));
                let errors =
                    errors.map(|e| format!("its generated definitions do not type-check: {e}"));
                record.problems.extend(errors);
            }
            Err(why) => {
                gate.skip(&unit, &check, &why);
                record.problems.push(why);
            }
        }
        if chosen && target.state == State::Formal {
            let none = (Inventory::default(), BTreeSet::new());
            let (inventory, unread) = gate.inventory.as_ref().unwrap_or(&none);
            let found = classify::classify(target, &extraction, layout.kernel, inventory).0;
            (record.problems).extend(unread.iter().cloned().chain(found));
        }
    } else if many {
        let (count, most) = (target.mutants.len(), registry::MUTANTS);
        let problem = format!("it registers {count} mutants, more than the {most} it may");
        record.problems.push(problem);
    } else {
        (record.problems).push("its module is not a Lean module path".to_string());
    }
    if chosen && (many || target.state == State::Planned) {
        let (status, reason) = qualify::conclusion(&record.problems);
        let scoped = [status, Status::Scoped][usize::from(status == Status::Verified)];
        gate.conclude(&unit, ([scoped, Status::Budget][usize::from(many)], reason));
    }
    gate.receipt.proof_targets.insert(name.clone(), record);
    Ok(())
}

/// Builds the proof modules of the selected formal target `target` in its
/// stage, with the hand-written Lean of the export and warnings as errors,
/// audits the theorems of its obligations with the allowlist of a target,
/// its trusted axioms and the declarations that its templates keep, runs
/// its mutants, or the source mutants of `generate`, once it is verified,
/// and concludes its unit, unless its extraction concluded it.
fn finish_target(
    gate: &mut Gate,
    target: &Target,
    generate: Option<&[String]>,
) -> Result<(), String> {
    let (layout, source, unit) = (gate.layout, gate.source(), target_unit(&target.name));
    if (gate.records().conclusions.iter()).any(|(concluded, _)| *concluded == unit) {
        return mutants::after(gate, target, None, generate).map(|_| ());
    }
    let mut record = gate.receipt.proof_targets[&target.name].clone();
    let (project, modules) = (target_project(gate, &target.name), &target.proof_modules);
    let build_args = lean::build_args(&[format!("+{}", layout.namespace)], true);
    let audit_args = lean::check_args(lean::AUDIT);
    let build = qualify::lake(Site::TargetBuild, &build_args, &project);
    let audit = qualify::lake(Site::AxiomAudit, &audit_args, &project);
    let theorems = Vec::from_iter(target.obligations.iter().flat_map(|o| o.theorems.iter()));
    let mut problems = record.problems.clone();
    if theorems.is_empty() {
        problems.push("its obligations name no theorem".to_string());
    }
    let (mut audited, mut built, mut tool) = (None, false, None);
    if record.typed {
        let (ran, verdict) = mutants::prove(gate, &unit, &project, modules)?;
        built = verdict.class == Class::Passed;
        match ran
            .filter(|_| !built)
            .map(|ran| mutants::build_failure(modules, &ran))
        {
            Some(Ok(problem)) => problems.push(problem),
            failure => tool = failure.and_then(Result::err),
        }
    } else {
        gate.skip(&unit, &build, "its generated definitions do not type-check");
    }
    if built {
        let text = lean::audit_source(layout.namespace, &[], modules);
        let written = fs::write(project.join(lean::AUDIT), text);
        written.map_err(|error| format!("{}: {error}", lean::AUDIT))?;
        let (ran, verdict, _) = gate.run(&unit, &audit, |_| Ok(()));
        let passed = ran.filter(|_| verdict.class == Class::Passed);
        audited = passed.map(|ran| lean::audit_output(&ran.output));
    } else {
        gate.skip(&unit, &audit, "the proofs did not build");
    }
    if let Some(audit) = &audited {
        let input = |path: &str| base::read(&source.join(path));
        let mut sources = lean::Sources {
            registry: lean::load_axioms(&input(layout.axioms)?)?,
            tcb: lean::load_tcb(&input(layout.tcb)?)?,
            declared: BTreeSet::from_iter(record.declarations.iter().cloned()),
            native: audit.native.clone(),
            ..lean::Sources::default()
        };
        let trusted = target.trusted_axioms.iter().map(|axiom| &axiom.name);
        (sources.registry).extend(record.declarations.iter().chain(trusted).cloned());
        problems.extend(lean::target_problems(audit, &theorems, modules, &sources));
    } else if built {
        problems.push("the audit did not pass".to_string());
    }
    let verified = (audited.is_some() && problems.is_empty() && tool.is_none()).then_some(&project);
    tool = tool.or(mutants::after(
        gate,
        target,
        verified.map(PathBuf::as_path),
        generate,
    )?);
    problems.extend(tool.clone());
    let (status, reason) = qualify::conclusion(&problems);
    gate.conclude(
        &unit,
        (
            [status, Status::ToolFailure][usize::from(tool.is_some())],
            reason,
        ),
    );
    record.problems = problems;
    (gate.receipt.proof_targets).insert(target.name.clone(), record);
    Ok(())
}

/// Runs the phases until one stops the run, and accounts for the
/// conclusions of their units.
fn run_phases(gate: &mut Gate, phases: Vec<Phase<'_>>) {
    let mut registered = Vec::new();
    let mut stopped = (!gate.receipt.failures.is_empty())
        .then(|| "a failure before the phases stopped the run".to_string());
    for phase in phases {
        let name = phase.name;
        registered.extend(phase.units.into_iter().map(|unit| (unit, name.clone())));
        let (ran, begin) = (stopped.is_none(), Instant::now());
        if ran {
            gate.phase = Some((name.clone(), begin + phase.budget));
            let result = caught(|| (phase.body)(&mut *gate)).and_then(|result| result);
            gate.phase = None;
            if let Err(error) = result {
                let message = format!("the phase {name} stopped: {error}");
                gate.fail(Status::ToolFailure, message.clone());
                stopped = Some(message);
            }
        }
        let phase = receipt::Phase {
            budget_seconds: phase.budget.as_secs(),
            seconds: receipt::seconds(if ran { begin.elapsed() } else { Duration::ZERO }),
            ran,
        };
        gate.receipt.phases.insert(name, phase);
    }
    let conclusions = std::mem::take(&mut gate.records().conclusions);
    let (units, problems) = outcome::account(&registered, conclusions, stopped.as_deref());
    for problem in problems {
        gate.fail(Status::ToolFailure, problem);
    }
    gate.receipt.units = units;
}

/// Takes the snapshot of the end, which must match the start and be clean.
fn take_end(gate: &mut Gate, inputs: &[&str], before: &Snapshot) -> Result<(), String> {
    let (_, _, after) = paths::snapshot(gate, inputs).map_err(|error| {
        format!("cannot take the snapshot of the gate inputs at the end: {error}")
    })?;
    let mut changed: Vec<String> = (before.iter())
        .filter(|(path, entry)| after.get(*path) != Some(entry))
        .map(|(path, _)| path.clone())
        .collect();
    gate.receipt.inputs.after = Some(after);
    let changes = paths::changes(gate, inputs).map_err(|error| {
        format!("cannot find whether the gate inputs are clean at the end: {error}")
    })?;
    gate.receipt.inputs.clean_after = Some(changes.is_empty());
    changed.extend(changes);
    if !changed.is_empty() {
        let changed = changed.join(", ");
        let message = format!("gate inputs changed during the run: {changed}");
        gate.fail(Status::Stale, message);
    }
    Ok(())
}

/// Makes the receipt of the base run of a lane its base record, and that of
/// its comparator run the receipt of the lane with that record.
fn close(context: &Context, receipt: &mut Receipt) {
    let runs = (context.var)(comparator::RUNS).map_or(context.root.join(RUNS), PathBuf::from);
    match (context.shard.and_then(merge::lane), context.comparator) {
        (Some(_), true) => comparator::combine(&runs, receipt),
        (Some(_), false) => receipt.schema = receipt::BASE_SCHEMA,
        _ => {}
    }
}

/// Writes `receipt` into `run`, or to `stderr` without a run directory or
/// when it cannot be written, with the exit codes under "Results" in
/// `docs/formal-verification.md`.
pub(crate) fn finish(
    receipt: &Receipt,
    run: Option<&RunDir>,
    stdout: &mut dyn Write,
    stderr: &mut dyn Write,
) -> ExitCode {
    for failure in &receipt.failures {
        let _ = writeln!(stderr, "{}: {}", word(&failure.status), failure.message);
    }
    let text = receipt::render(receipt);
    let based = receipt.schema == receipt::BASE_SCHEMA;
    let path = |run: &RunDir| match based {
        true => run.path.join(receipt::BASE_RECORD),
        false => run.receipt(),
    };
    let written = run.map(|run| (path(run), fs::write(path(run), &text)));
    if let Some((path, Ok(()))) = &written {
        let (status, path) = (word(&receipt.status), path.display());
        let complete = if receipt.complete { "" } else { "not " };
        let _ = writeln!(
            stdout,
            "formal run: {status}, {complete}complete; receipt {path}"
        );
        return match receipt.status {
            Status::Verified | Status::Scoped => ExitCode::SUCCESS,
            _ => ExitCode::FAILURE,
        };
    }
    if let Some((path, Err(error))) = written {
        let _ = writeln!(stderr, "cannot write {}: {error}", path.display());
    }
    let _ = stderr.write_all(text.as_bytes());
    ExitCode::from(120)
}

/// Whether a run runs the part of its targets alone: the shard of a target,
/// and a run that names targets without a shard or source mutants.
fn alone(shard: Option<&str>, named: bool, generate: bool) -> bool {
    shard.and_then(merge::target).is_some() || (shard.is_none() && named && !generate)
}

/// The phases of a run of `targets` with `context`, the guard on a pull
/// request first: the comparator of a lane has only its phase, the base run
/// of a lane its extraction and base round, a run of targets [`alone`] only
/// their extraction and phase, and the qualification job the guard, the
/// qualification and the base round.
fn phases<'a>(
    context: &Context<'a>,
    targets: &BTreeSet<String>,
    generate: Option<Vec<String>>,
) -> Vec<Phase<'a>> {
    let (root, layout, shard) = (context.root, context.layout, context.shard);
    let lane = shard.and_then(merge::lane);
    if let Some(lane) = lane.filter(|_| context.comparator) {
        let runs = (context.var)(comparator::RUNS);
        return vec![comparator::phase(root, layout, lane, runs)];
    }
    let (alone, job) = (
        alone(shard, !targets.is_empty(), generate.is_some()),
        shard == Some(qualify::PHASE),
    );
    let qualifies = !alone && lane.is_none();
    let mut phases = Vec::from_iter(guard::phase(context.var).filter(|_| qualifies));
    let [extraction, finish] = target_phases(root, layout, targets, generate, shard);
    phases.extend(qualifies.then(|| qualify::phase(root, layout)));
    phases.extend((!job).then_some(extraction));
    phases.extend((!alone).then(|| base::phase(root, layout, shard)));
    phases.extend((shard.is_none() || alone).then_some(finish));
    phases
}

/// Entry point of `cargo xtask formal run`, and of `cargo xtask formal
/// mutants` for the source mutants of `generate`; `keep` keeps the work
/// directory of the run, `shard` names the part that it runs, and in a lane
/// `comparator` runs its comparator on what its base run kept.
pub fn command(
    root: &Path,
    layout: &Layout,
    targets: BTreeSet<String>,
    generate: Option<Vec<String>>,
    (keep, comparator): (bool, bool),
    shard: Option<&str>,
) -> ExitCode {
    process::init();
    let lane = shard.and_then(merge::lane);
    if comparator && lane.is_none() {
        eprintln!("--comparator runs the comparator of a lane, --shard lane/<name>");
        return ExitCode::from(2);
    }
    let var = |name: &str| std::env::var(name).ok().filter(|value| !value.is_empty());
    let context = Context {
        root,
        layout,
        host: host(),
        uid: process::effective_uid(),
        var: &var,
        budget: (generate.as_ref().map(|_| mutants::RUN_BUDGET))
            .or(shard.map(merge::budget))
            .or((!targets.is_empty()).then_some(merge::SHARD_MARGIN)),
        keep,
        free: process::disk_available,
        shard,
        comparator,
    };
    let lists = generate.as_ref().and_then(|_| targets.first().cloned());
    let run = RunDir::create(root);
    let (receipt, draft) = match &run {
        Ok(run) => {
            let phases = phases(&context, &targets, generate);
            execute(&context, run, &targets, phases, Box::new(io::stdout()))
        }
        Err(error) => {
            let mut receipt = blank(&context, &targets, "", RUNS);
            let message = format!("cannot create a run directory below {RUNS}: {error}");
            let status = Status::ToolFailure;
            receipt.failures.push(Failure { status, message });
            (receipt, None)
        }
    };
    let mut receipt = receipt;
    close(&context, &mut receipt);
    // A stop signal after the last command ends the run without a receipt.
    process::stop_if_asked();
    let (stdout, stderr) = (&mut io::stdout(), &mut io::stderr());
    let code = finish(&receipt, run.as_ref().ok(), stdout, stderr);
    match (lists, run) {
        (Some(target), Ok(run)) => mutants::write_list(
            root,
            layout,
            &target,
            draft.as_deref(),
            &run,
            &receipt,
            code,
        ),
        _ => code,
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use std::os::unix::fs::PermissionsExt;
    use std::os::unix::process::ExitStatusExt;
    use std::process::{Command, Stdio};
    use std::sync::atomic::AtomicU64;

    use super::*;
    use crate::formal::fixture::{self, Fixture};

    /// The budget of a test phase whose commands end by themselves.
    pub(crate) const LONG: Duration = Duration::from_secs(3_600);

    /// The variable that makes the process of a test the gate that the test
    /// stops, with the fixture that it names.
    const STOPPED: &str = "KREPI_XTASK_STOPPED_GATE";

    /// Progress that panics on the line `after` + 1, a panic in a step of the
    /// gate.
    struct Panicking {
        after: usize,
    }

    impl Write for Panicking {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            if bytes.contains(&b'\n') {
                if self.after == 0 {
                    panic!("asked to by the test");
                }
                self.after -= 1;
            }
            Ok(bytes.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    /// What a test run gives.
    pub(crate) struct Done {
        pub(crate) receipt: Receipt,
        pub(crate) code: ExitCode,
        pub(crate) run: RunDir,
        /// The draft of the list of survivors that the run read before it
        /// removed its work directory.
        pub(crate) draft: Option<String>,
        stdout: String,
        stderr: String,
    }

    impl Done {
        /// The receipt as the run wrote it.
        pub(crate) fn written(&self) -> Receipt {
            let paths = [self.run.receipt(), self.run.path.join(receipt::BASE_RECORD)];
            let path = paths
                .into_iter()
                .find(|path| path.exists())
                .unwrap_or_default();
            let text = fs::read_to_string(path).expect("the receipt is written");
            serde_json::from_str(&text).expect("the receipt reads back")
        }

        pub(crate) fn failures(&self) -> Vec<&str> {
            self.receipt
                .failures
                .iter()
                .map(|failure| failure.message.as_str())
                .collect()
        }

        fn has_failure(&self, status: Status, start: &str) -> bool {
            self.receipt
                .failures
                .iter()
                .any(|failure| failure.status == status && failure.message.starts_with(start))
        }

        fn sites(&self) -> Vec<Site> {
            self.receipt
                .commands
                .iter()
                .map(|command| command.site)
                .collect()
        }
    }

    /// Runs the gate on `fixture` into a new run directory, for `targets`,
    /// keeping its work directory, which the tests read, with [`plenty`]
    /// free.
    pub(crate) fn gate(fixture: &Fixture, targets: &[&str], phases: Vec<Phase<'_>>) -> Done {
        gate_as(fixture, targets, phases, true, plenty)
    }

    /// The host of the run: this one, or one of the manifest elsewhere.
    pub(crate) fn test_host() -> Option<&'static str> {
        host().or(Some("linux-aarch64"))
    }

    /// Runs the gate on `fixture` into a new run directory, for `targets`,
    /// with the free-space reading `free`, keeping its work directory only
    /// when `keep`, as the command does with and without `--keep`.
    pub(crate) fn gate_as(
        fixture: &Fixture,
        targets: &[&str],
        phases: Vec<Phase<'_>>,
        keep: bool,
        free: fn(&Path) -> Option<u64>,
    ) -> Done {
        let run = RunDir::create(fixture.root()).expect("create the run directory");
        let targets = targets.iter().map(|name| name.to_string()).collect();
        let context = Context {
            root: fixture.root(),
            layout: &Layout::PRODUCTION,
            host: test_host(),
            uid: other_uid(),
            var: &|_| None,
            budget: None,
            keep,
            free,
            shard: None,
            comparator: false,
        };
        gate_with(&context, run, &targets, phases, Box::new(io::sink()))
    }

    /// A reading of the free space that the disk guard of no test refuses.
    pub(crate) fn plenty(_: &Path) -> Option<u64> {
        Some(1 << 50)
    }

    /// Runs the gate on the fixture at `root` into `run` on `host`, without
    /// printing its commands, and writes its receipt, keeping its work
    /// directory, which the tests read, and with [`plenty`] free.
    pub(crate) fn gate_in(
        root: &Path,
        run: RunDir,
        targets: &BTreeSet<String>,
        phases: Vec<Phase<'_>>,
        host: Option<&str>,
        progress: Box<dyn Write + Send>,
    ) -> Done {
        let context = Context {
            root,
            layout: &Layout::PRODUCTION,
            host,
            uid: other_uid(),
            var: &|_| None,
            budget: None,
            keep: true,
            free: plenty,
            shard: None,
            comparator: false,
        };
        gate_with(&context, run, targets, phases, progress)
    }

    /// A user other than root and the one that runs the tests, which owns
    /// the fixtures.
    pub(crate) fn other_uid() -> u32 {
        process::effective_uid() + 1
    }

    /// Runs the gate with `context` into `run`, and writes its receipt.
    fn gate_with(
        context: &Context,
        run: RunDir,
        targets: &BTreeSet<String>,
        phases: Vec<Phase<'_>>,
        progress: Box<dyn Write + Send>,
    ) -> Done {
        let (mut receipt, draft) = execute(context, &run, targets, phases, progress);
        close(context, &mut receipt);
        let (mut stdout, mut stderr) = (Vec::new(), Vec::new());
        let code = finish(&receipt, Some(&run), &mut stdout, &mut stderr);
        Done {
            receipt,
            code,
            run,
            draft,
            stdout: String::from_utf8(stdout).expect("UTF-8"),
            stderr: String::from_utf8(stderr).expect("UTF-8"),
        }
    }

    pub(crate) fn phase<'a>(
        name: &str,
        budget: Duration,
        units: &[&str],
        body: impl FnOnce(&mut Gate) -> Result<(), String> + 'a,
    ) -> Phase<'a> {
        Phase {
            name: name.to_string(),
            budget,
            units: units.iter().map(|unit| unit.to_string()).collect(),
            body: Box::new(body),
        }
    }

    /// Runs the shell script `script` as a command of `unit` at the base
    /// build.
    fn shell(run: &Gate, unit: &str, script: &str) -> Verdict {
        shell_reading(run, unit, script, |_| Ok(()))
    }

    /// [`shell`], with `read` reading what the command wrote.
    fn shell_reading(
        run: &Gate,
        unit: &str,
        script: &str,
        read: impl FnMut(&Ran) -> Result<(), String>,
    ) -> Verdict {
        let source = run.source();
        let args = vec!["-c".to_string(), script.to_string()];
        let request = Request {
            site: Site::BaseBuild,
            tool: Tool::LakeBuild,
            program: "/bin/sh",
            args: &args,
            cwd: &source,
            stdin: None,
        };
        run.run(unit, &request, read).1
    }

    #[test]
    fn a_hanging_command_is_stopped_at_its_phase_budget_and_the_receipt_is_written() {
        let fixture = Fixture::new("hang");
        let phases = vec![phase("base", Duration::from_secs(1), &["base"], |run| {
            shell(run, "base", "exec sleep 30");
            run.conclude("base", (Status::Verified, None));
            Ok(())
        })];
        let done = gate(&fixture, &[], phases);
        assert_eq!(done.code, ExitCode::FAILURE);
        let receipt = done.written();
        assert_eq!(receipt, done.receipt);
        assert_eq!(receipt.status, Status::Budget);
        assert!(!receipt.complete);
        let hung = receipt
            .commands
            .iter()
            .find(|command| command.site == Site::BaseBuild)
            .expect("the command is recorded");
        assert_eq!(hung.limit, LimitBy::Phase);
        assert!(hung.limit_seconds <= 1.0, "{}", hung.limit_seconds);
        // A thread that waited longer than the budget before the command
        // finds it used up, which is the other outcome at the budget.
        if hung.class != Class::NotRun {
            assert_eq!(hung.class, Class::Budget);
            assert!(hung.timed_out);
            assert!(!hung.group_survived);
        }
        assert_eq!(receipt.units["base"].status, Status::Budget);
        assert_eq!(
            receipt.units["base"].reason.as_deref(),
            hung.reason.as_deref()
        );
    }

    #[test]
    fn a_failed_copy_of_the_snapshot_gives_an_incomplete_tool_failure_receipt() {
        let fixture = Fixture::new("copy");
        let run = RunDir::create(fixture.root()).expect("create the run directory");
        // A file stands where the export goes.
        fs::write(run.source(), "in the way\n").expect("write a file");
        let done = gate_in(
            fixture.root(),
            run,
            &BTreeSet::new(),
            Vec::new(),
            test_host(),
            Box::new(io::sink()),
        );
        assert_eq!(done.code, ExitCode::FAILURE);
        let receipt = done.written();
        assert_eq!(receipt.status, Status::ToolFailure);
        assert!(!receipt.complete);
        assert!(
            done.has_failure(
                Status::ToolFailure,
                "cannot export the snapshot: cannot create "
            ),
            "{:?}",
            done.failures()
        );
        // The end snapshot is taken all the same.
        assert_eq!(receipt.inputs.after, receipt.inputs.before);
        assert!(receipt.inputs.after.is_some());
        assert_eq!(receipt.inputs.clean_after, Some(true));
        assert!(
            done.stderr.contains("cannot export the snapshot"),
            "{}",
            done.stderr
        );
    }

    #[test]
    fn a_unit_without_a_conclusion_fails_the_run() {
        let fixture = Fixture::new("missing");
        let phases = vec![phase("checks", LONG, &["u1", "u2"], |run| {
            run.conclude("u1", (Status::Verified, None));
            Ok(())
        })];
        let done = gate(&fixture, &[], phases);
        assert_eq!(done.code, ExitCode::FAILURE);
        assert_eq!(done.written().status, Status::ToolFailure);
        assert!(!done.receipt.complete);
        assert_eq!(done.failures(), ["the unit u2 has no conclusion"]);
        assert_eq!(done.receipt.units["u1"].status, Status::Verified);
        assert_eq!(done.receipt.units["u2"].status, Status::ToolFailure);
        assert!(done.receipt.phases["checks"].ran);
    }

    #[test]
    fn a_unit_with_two_conclusions_fails_the_run() {
        let fixture = Fixture::new("duplicate");
        let phases = vec![phase("checks", LONG, &["u1", "u2"], |run| {
            run.conclude("u1", (Status::Verified, None));
            run.conclude("u2", (Status::Verified, None));
            run.conclude("u1", (Status::Rejected, Some("again".to_string())));
            Ok(())
        })];
        let done = gate(&fixture, &[], phases);
        assert_eq!(done.code, ExitCode::FAILURE);
        assert_eq!(done.written().status, Status::ToolFailure);
        assert!(!done.receipt.complete);
        assert_eq!(done.failures(), ["the unit u1 has 2 conclusions"]);
        assert_eq!(
            done.receipt.units["u1"].reason.as_deref(),
            Some("the unit has 2 conclusions")
        );
    }

    #[test]
    fn an_unknown_target_fails_the_run() {
        let fixture = Fixture::new("unknown-target");
        let done = gate(&fixture, &["missing"], Vec::new());
        assert_eq!(done.code, ExitCode::FAILURE);
        let receipt = done.written();
        assert_eq!(receipt.status, Status::ToolFailure);
        assert!(!receipt.complete);
        assert_eq!(receipt.targets, ["missing"]);
        assert_eq!(
            done.failures(),
            ["verification/targets.json registers no target named missing"]
        );
    }

    /// The failure of a run that extracts kernel targets from a kernel
    /// workspace without its root package.
    const NO_ROOT_PACKAGE: &str = "the run extracts kernel targets, and kernel/Cargo.toml has no [package] named krepi-kernel, the root package that they are extracted from";

    /// Gives the kernel workspace of `fixture` the root package `name`, whose
    /// manifest ends with `extra`, and commits it.
    pub(crate) fn root_package(fixture: &Fixture, name: &str, extra: &str) {
        fixture.write(
            "kernel/Cargo.toml",
            &format!(
                "[package]\nname = \"{name}\"\nversion = \"0.0.0\"\nedition = \"2024\"\npublish = false\n\n\
                 [workspace]\nresolver = \"3\"\nmembers = [\"abi\"]\n\n\
                 [lints.rust]\nunsafe_code = \"forbid\"\n{extra}"
            ),
        );
        fixture.write("kernel/src/lib.rs", "#![no_std]\n");
        fixture.lock();
        fixture.commit_all();
    }

    /// Registers the targets `targets`, a JSON list, in `fixture` and
    /// commits them.
    pub(crate) fn register(fixture: &Fixture, targets: &str) {
        fixture.write(
            "verification/targets.json",
            &format!("{{\"schema\": 2, \"specifications\": [], \"targets\": {targets}}}\n"),
        );
        fixture.commit_all();
    }

    /// A phase that concludes its unit `base` as verified.
    fn verified() -> Vec<Phase<'static>> {
        vec![phase("base", LONG, &["base"], |run| {
            run.conclude("base", (Status::Verified, None));
            Ok(())
        })]
    }

    #[test]
    fn a_run_that_extracts_kernel_targets_needs_the_root_package() {
        // A whole run selects every formal target, and the kernel workspace
        // of the fixture is virtual.
        let fixture = Fixture::new("no-root");
        register(&fixture, r#"[{"name": "demo"}]"#);
        let done = gate(&fixture, &[], verified());
        assert_eq!(done.code, ExitCode::FAILURE);
        assert_eq!(done.written().status, Status::Rejected);
        assert!(!done.receipt.complete);
        assert_eq!(done.failures(), [NO_ROOT_PACKAGE]);
        assert!(!done.receipt.phases["base"].ran);
        assert_eq!(done.receipt.units["base"].status, Status::NotRun);
        // A root package of another name is no root package either.
        root_package(&fixture, "kernel", "");
        let done = gate(&fixture, &[], Vec::new());
        assert_eq!(done.receipt.status, Status::Rejected);
        assert_eq!(
            done.failures(),
            [
                "kernel/Cargo.toml: the root package is named `kernel`, not `krepi-kernel`",
                NO_ROOT_PACKAGE
            ]
        );
    }

    #[test]
    fn a_run_that_extracts_no_kernel_target_needs_no_root_package() {
        // The registry is empty: the run only has the phases of the tools
        // and of krepi's own Lean.
        let fixture = Fixture::new("no-kernel-target");
        let done = gate(&fixture, &[], verified());
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        assert_eq!(done.written().status, Status::Verified);
        assert!(done.receipt.complete);
        assert_eq!(done.receipt.units["base"].status, Status::Verified);
    }

    #[test]
    fn a_whole_run_does_not_select_a_planned_target() {
        // The kernel workspace is virtual and the fixture has no proof tools:
        // a whole run extracts nothing and has the budget of the gate alone.
        let fixture = Fixture::new("planned");
        let planned = serde_json::json!([
            {"name": "demo", "state": "planned", "module": "Demo", "start_from": ["crate::f"]}
        ]);
        register(&fixture, &planned.to_string());
        let done = gate(&fixture, &[], target_run(&fixture, &[]));
        assert_eq!(
            done.receipt.status,
            Status::Verified,
            "{:?}",
            done.failures()
        );
        assert!(done.receipt.complete);
        assert_eq!(done.receipt.targets, Vec::<String>::new());
        assert!(done.receipt.proof_targets.is_empty());
        assert!(!done.sites().contains(&Site::Charon));
        assert_eq!(done.receipt.budgets.gate_seconds, 7_200);
        let extraction = &done.receipt.phases["extraction"];
        assert_eq!((extraction.ran, extraction.budget_seconds), (true, 0));
        // A run that names it extracts it.
        let done = gate(&fixture, &["demo"], target_run(&fixture, &["demo"]));
        assert_eq!(done.receipt.status, Status::Rejected);
        assert_eq!(done.failures(), [NO_ROOT_PACKAGE]);
    }

    #[test]
    fn a_root_manifest_out_of_shape_rejects_the_run_as_it_fails_the_manifests_step() {
        let fixture = Fixture::new("shape");
        root_package(&fixture, "krepi-kernel", "\n[profile.dev]\nopt-level = 1\n");
        let problem = "kernel/Cargo.toml: the root manifest may not have profile.dev";
        let done = gate(&fixture, &[], Vec::new());
        assert_eq!(done.written().status, Status::Rejected);
        assert_eq!(done.failures(), [problem]);
        assert_eq!(manifests::check_kernel_workspace(fixture.root()), [problem]);
    }

    /// A fixture with the Lake project and the stand-ins of the
    /// qualification, a kernel workspace with its root package, the empty
    /// registries of the base round and of models, the proof module of the
    /// target `t`, whose build in the stage of a mutant fails in its theorem,
    /// and the target registry `targets`, committed.
    pub(crate) fn with_targets(label: &str, targets: &str) -> Fixture {
        let fixture = fixture::qualification(label, &serde_json::json!([]));
        for (file, list) in [("models", "models"), ("axioms", "axioms"), ("tcb", "items")] {
            let text = format!("{{\"schema\": 1, \"{list}\": []}}\n");
            fixture.write(&format!("verification/{file}.json"), &text);
        }
        let proof = "module\n\npublic theorem f_spec : True := trivial\n";
        fixture.write("verification/Krepi/Proofs/T.lean", proof);
        let failed = "error: Krepi/Proofs/T.lean:3:0: unsolved goals";
        let failing = fixture::failing("Krepi.Proofs.T", &[failed], 1);
        let mutant = format!("case $PWD in */mutants/*) {failing};; esac\n");
        fixture::lake_script(&fixture, "+Krepi", &mutant);
        root_package(&fixture, "krepi-kernel", "");
        register(&fixture, targets);
        fixture
    }

    /// The registry of the formal target `t`, with `budget` and `mutants`,
    /// and of the planned target `p`.
    pub(crate) fn two_targets(budget: u64, mutants: usize) -> String {
        let theorem = "Krepi.Proofs.T.f_spec";
        let mutant = |index| {
            let name = format!("m{index}");
            serde_json::json!({"name": name, "file": "src/lib.rs", "find": "no_std", "replace": "no_std", "fails": [theorem]})
        };
        let mutants = Vec::from_iter((0..mutants).map(mutant));
        serde_json::json!([
            {"name": "t", "module": "T", "budget": budget, "start_from": ["crate::f"],
             "proof_modules": ["Krepi.Proofs.T"], "obligations": [{"id": "f", "theorems": [theorem]}],
             "mutants": mutants},
            {"name": "p", "state": "planned", "module": "P", "start_from": ["crate::f"]}
        ])
        .to_string()
    }

    /// The phases of the targets of `fixture` for `named`, around a base
    /// round that finds the proof module of `t` and is verified.
    pub(crate) fn target_run<'a>(fixture: &Fixture, named: &[&str]) -> Vec<Phase<'a>> {
        generating_run(fixture, named, None)
    }

    /// The phases of [`target_run`], which generate the source mutants of
    /// `generate` when given.
    pub(crate) fn generating_run<'a>(
        fixture: &Fixture,
        named: &[&str],
        generate: Option<Vec<String>>,
    ) -> Vec<Phase<'a>> {
        let named = BTreeSet::from_iter(named.iter().map(|name| name.to_string()));
        let [extraction, finish] =
            target_phases(fixture.root(), &Layout::PRODUCTION, &named, generate, None);
        let base = phase("base", LONG, &["base"], |run| {
            run.handwritten = vec!["Krepi/Proofs/T.lean".to_string()];
            run.conclude("base", (Status::Verified, None));
            Ok(())
        });
        vec![extraction, base, finish]
    }

    /// The phases of a whole run of the fixture at `root` in the production
    /// layout, as [`command`] puts them together but the guard, with the
    /// extraction of a run of `named` targets.
    pub(crate) fn every_phase<'a>(root: &Path, named: &[&str]) -> Vec<Phase<'a>> {
        let named = BTreeSet::from_iter(named.iter().map(|name| name.to_string()));
        let layout = &Layout::PRODUCTION;
        let [extraction, finish] = target_phases(root, layout, &named, None, None);
        let (qualification, base) = (
            qualify::phase(root, layout),
            base::phase(root, layout, None),
        );
        vec![qualification, extraction, base, finish]
    }

    /// The variables of a run outside a pull request: none.
    fn no_variable(_: &str) -> Option<String> {
        None
    }

    /// What a run of `shard` in the checkout `root` takes from its caller as
    /// `cargo xtask formal run --shard` gives it, with the variables `var`
    /// and the free-space reading `free`, keeping its work directory.
    fn shard_context<'a>(
        root: &'a Path,
        shard: Option<&'a str>,
        var: &'a dyn Fn(&str) -> Option<String>,
        free: fn(&Path) -> Option<u64>,
    ) -> Context<'a> {
        Context {
            root,
            layout: &Layout::PRODUCTION,
            host: test_host(),
            uid: other_uid(),
            var,
            budget: shard.map(merge::budget),
            keep: true,
            free,
            shard,
            comparator: false,
        }
    }

    /// The targets of a run of `shard`: that of the shard of a target.
    fn shard_targets(shard: &str) -> BTreeSet<String> {
        BTreeSet::from_iter(merge::target(shard).map(String::from))
    }

    /// Runs the shard `shard` of `fixture` with `phases` and the free-space
    /// reading `free` into a new run directory, and writes its receipt.
    pub(crate) fn gate_shard(
        fixture: &Fixture,
        shard: &str,
        phases: Vec<Phase<'_>>,
        free: fn(&Path) -> Option<u64>,
    ) -> Done {
        let run = RunDir::create(fixture.root()).expect("create the run directory");
        let context = shard_context(fixture.root(), Some(shard), &no_variable, free);
        let targets = shard_targets(shard);
        gate_with(&context, run, &targets, phases, Box::new(io::sink()))
    }

    /// Runs the targets `named` of `fixture` as `cargo xtask formal run
    /// --target` does, with the phases and the budget that [`command`] gives
    /// it outside a pull request, into a new run directory, and writes its
    /// receipt.
    fn named_run(fixture: &Fixture, named: &[&str]) -> Done {
        let root = fixture.root();
        let context = Context {
            budget: Some(merge::SHARD_MARGIN),
            ..shard_context(root, None, &no_variable, plenty)
        };
        let targets = BTreeSet::from_iter(named.iter().map(|name| name.to_string()));
        let run = RunDir::create(root).expect("create the run directory");
        let phases = phases(&context, &targets, None);
        gate_with(&context, run, &targets, phases, Box::new(io::sink()))
    }

    /// Runs the comparator of the lane `lane` of `fixture` in `layout` as
    /// `cargo xtask formal run --shard lane/<lane> --comparator` does, with
    /// `runs` in the variable of its runs directory, if given, into a new run
    /// directory, and writes the receipt of the lane.
    pub(crate) fn comparator_run(
        fixture: &Fixture,
        layout: &Layout,
        lane: &str,
        runs: Option<&Path>,
    ) -> Done {
        let runs = runs.map(|runs| runs.display().to_string());
        let var = |name: &str| runs.clone().filter(|_| name == comparator::RUNS);
        let shard = format!("lane/{lane}");
        let context = Context {
            layout,
            comparator: true,
            ..shard_context(fixture.root(), Some(&shard), &var, plenty)
        };
        let run = RunDir::create(fixture.root()).expect("create the run directory");
        let phases = phases(&context, &BTreeSet::new(), None);
        gate_with(
            &context,
            run,
            &BTreeSet::new(),
            phases,
            Box::new(io::sink()),
        )
    }

    /// The phases of the shard `shard` of the checkout `root`, as [`command`]
    /// puts them together outside a pull request.
    pub(crate) fn shard_phases<'a>(root: &'a Path, shard: &'a str) -> Vec<Phase<'a>> {
        let context = shard_context(root, Some(shard), &no_variable, plenty);
        phases(&context, &shard_targets(shard), None)
    }

    /// Runs the shard `shard` of `fixture` in `layout` with the phases that
    /// [`command`] gives it outside a pull request, into a new run directory,
    /// and writes its receipt.
    pub(crate) fn layout_shard(fixture: &Fixture, layout: &Layout, shard: &str) -> Done {
        let context = Context {
            layout,
            ..shard_context(fixture.root(), Some(shard), &no_variable, plenty)
        };
        let run = RunDir::create(fixture.root()).expect("create the run directory");
        let (targets, sink) = (shard_targets(shard), Box::new(io::sink()));
        let phases = phases(&context, &targets, None);
        gate_with(&context, run, &targets, phases, sink)
    }

    /// The phases of the qualification job of `fixture` but its
    /// qualification, with a base round that is verified.
    fn lane_job<'a>(fixture: &Fixture) -> Vec<Phase<'a>> {
        let (root, layout, none) = (fixture.root(), &Layout::PRODUCTION, &BTreeSet::new());
        let [extraction, _] = target_phases(root, layout, none, None, Some("lane/a"));
        let mut phases = vec![extraction];
        phases.extend(verified());
        phases
    }

    /// Writes the lane `a` of `fixture` with `components` and the shared
    /// modules `modules`, committed.
    fn lane_a(fixture: &Fixture, components: &[&str], modules: &[&str]) {
        let lane = serde_json::json!({"name": "a", "components": components, "modules": modules});
        let lanes = serde_json::json!({"schema": 1, "lanes": [lane]});
        fixture.write(Layout::PRODUCTION.lanes, &format!("{lanes}\n"));
        fixture.commit_all();
    }

    #[test]
    fn the_phases_of_a_shard_are_those_of_its_part_with_the_guard_of_a_pull_request() {
        fn names(root: &Path, shard: Option<&str>, pull_request: bool) -> Vec<String> {
            let event = |name: &str| match name {
                "GITHUB_EVENT_NAME" => Some("pull_request".to_string()),
                "GITHUB_EVENT_PATH" => Some("event.json".to_string()),
                _ => None,
            };
            let var: &dyn Fn(&str) -> Option<String> = match pull_request {
                true => &event,
                false => &no_variable,
            };
            let context = shard_context(root, shard, var, plenty);
            let targets = shard.map_or_else(BTreeSet::new, shard_targets);
            Vec::from_iter(
                phases(&context, &targets, None)
                    .into_iter()
                    .map(|phase| phase.name),
            )
        }
        let fixture = with_targets("shard-phases", &two_targets(1_800, 1));
        let root = fixture.root();
        let whole = ["guard", "qualification", "extraction", "base", "targets"];
        assert_eq!(names(root, None, true), whole);
        assert_eq!(names(root, None, false), whole[1..]);
        // The qualification job has the guard of a pull request and no
        // extraction, and a lane and the part of a target have no guard.
        let job = Some("qualification");
        assert_eq!(names(root, job, true), ["guard", "qualification", "base"]);
        assert_eq!(names(root, job, false), ["qualification", "base"]);
        for pull_request in [true, false] {
            let shard = names(root, Some("target/t/1"), pull_request);
            assert_eq!(shard, ["extraction", "targets"]);
            assert_eq!(
                names(root, Some("lane/a"), pull_request),
                ["extraction", "base"]
            );
        }
    }

    #[test]
    fn the_qualification_job_extracts_no_target_and_a_lane_the_formal_ones_of_its_components() {
        let fixture = with_targets("qualification-job", &two_targets(1_800, 1));
        let done = gate_shard(&fixture, "qualification", verified(), plenty);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        let receipt = done.written();
        assert_eq!(receipt.shard.as_deref(), Some("qualification"));
        assert_eq!(
            (receipt.trigger.mode, receipt.budgets.gate_seconds),
            (Mode::Manual, 7_200)
        );
        assert!(receipt.proof_targets.is_empty() && !done.sites().contains(&Site::Charon));
        // A lane extracts the formal target of its components as commands of
        // the unit of its base round, and not a planned one that no module
        // of it imports. Its budget is the shard margin, its registered
        // budget and the extraction margin, that of its extraction.
        lane_a(&fixture, &["T", "P"], &["Krepi.Proofs.T"]);
        let done = gate_shard(&fixture, "lane/a", lane_job(&fixture), plenty);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        let receipt = done.written();
        assert_eq!((receipt.status, receipt.complete), (Status::Verified, true));
        assert_eq!(
            (receipt.shard.as_deref(), receipt.targets.len()),
            (Some("lane/a"), 0)
        );
        assert_eq!(receipt.budgets.gate_seconds, 300 + 2_400 + 600);
        assert_eq!(receipt.phases["extraction"].budget_seconds, 600);
        assert!(!receipt.phases.contains_key("targets"));
        assert_eq!(Vec::from_iter(receipt.proof_targets.keys()), ["t"]);
        assert_eq!(receipt.proof_targets["t"].unit, None);
        assert!(receipt.proof_targets["t"].typed);
        let base = fixture::commands(&done, "base/lane/a")
            .into_iter()
            .map(|c| c.site);
        assert_eq!(
            Vec::from_iter(base),
            [Site::Charon, Site::Aeneas, Site::TargetBuild]
        );
        let lane = receipt.lane.expect("the lane");
        assert_eq!(
            (lane.name.as_str(), lane.components),
            ("a", vec!["T".to_string(), "P".to_string()])
        );
        assert_eq!(
            lane.targets,
            BTreeMap::from([("t".to_string(), receipt::Role::Formal)])
        );
        // A lane without its component extracts it neither.
        lane_a(&fixture, &["P"], &["Krepi.Proofs.T"]);
        let done = gate_shard(&fixture, "lane/a", lane_job(&fixture), plenty);
        assert!(
            done.written().proof_targets.is_empty(),
            "{:?}",
            done.failures()
        );
    }

    #[test]
    fn a_lane_leaves_out_the_targets_of_a_waiver_that_holds_when_it_extracts() {
        let fixture = with_targets("waived-job", &two_targets(1_800, 1));
        lane_a(
            &fixture,
            &["T", "P"],
            &["Krepi.Proofs.T", "Krepi.Statements.P"],
        );
        let job = |fixture: &Fixture| {
            let done = gate_shard(fixture, "lane/a", lane_job(fixture), plenty);
            let charon = (done.receipt.commands.iter()).any(|c| c.site == Site::Charon);
            (done.written(), charon)
        };
        // An expired waiver leaves nothing out.
        waiver::tests::waive(&fixture, "t", "2000-01-01");
        let (receipt, charon) = job(&fixture);
        assert_eq!((receipt.status, receipt.complete), (Status::Verified, true));
        assert_eq!(Vec::from_iter(receipt.proof_targets.keys()), ["t"]);
        assert!(charon);
        // A waiver that holds leaves its target out of the extraction.
        waiver::tests::waive(&fixture, "t", "9999-12-31");
        let (receipt, charon) = job(&fixture);
        assert_eq!((receipt.status, receipt.complete), (Status::Verified, true));
        assert!(receipt.proof_targets.is_empty() && !charon);
        assert!(receipt.phases["extraction"].ran);
        // No waiver leaves out a planned target that a hand-written module
        // imports.
        let both = serde_json::json!({"schema": 1, "waivers": [waiver::tests::waiver(&["t", "p"], "9999-12-31")]});
        fixture.write(Layout::PRODUCTION.waivers, &format!("{both}\n"));
        let statement = "module\n\npublic import KrepiGen.P.Funs\n";
        fixture.write("verification/Krepi/Statements/P.lean", statement);
        fixture.commit_all();
        let (receipt, _) = job(&fixture);
        assert_eq!((receipt.status, receipt.complete), (Status::Verified, true));
        assert_eq!(Vec::from_iter(receipt.proof_targets.keys()), ["p"]);
        // A record that breaks its rules stops the extraction.
        fixture.write(
            Layout::PRODUCTION.waivers,
            "{\"schema\": 2, \"waivers\": []}\n",
        );
        fixture.commit_all();
        let done = gate_shard(&fixture, "lane/a", lane_job(&fixture), plenty);
        let receipt = done.written();
        assert_eq!(
            (receipt.status, receipt.complete),
            (Status::ToolFailure, false)
        );
        let stopped =
            "the phase extraction stopped: verification/waivers.json: schema 2 where 1 is expected";
        assert_eq!(done.failures(), [stopped]);
        assert!(receipt.proof_targets.is_empty() && !receipt.phases["base"].ran);
    }

    #[test]
    fn a_whole_run_and_the_shard_of_a_waived_target_extract_it() {
        let fixture = with_targets("waived-run", &two_targets(1_800, 1));
        waiver::tests::waive(&fixture, "t", "9999-12-31");
        let done = gate(&fixture, &[], target_run(&fixture, &[]));
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        assert_eq!(Vec::from_iter(done.receipt.proof_targets.keys()), ["t"]);
        assert_eq!(fixture::status(&done, "target/t"), (Status::Verified, None));
        let phases = shard_phases(fixture.root(), "target/t/1");
        let done = gate_shard(&fixture, "target/t/1", phases, plenty);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        assert_eq!(Vec::from_iter(done.receipt.proof_targets.keys()), ["t"]);
    }

    #[test]
    fn the_shard_of_a_target_runs_its_extraction_and_its_phase_alone() {
        let fixture = with_targets("target-shard", &two_targets(1_800, 1));
        let phases = shard_phases(fixture.root(), "target/t/1");
        let done = gate_shard(&fixture, "target/t/1", phases, plenty);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        let receipt = done.written();
        assert_eq!((receipt.status, receipt.complete), (Status::Verified, true));
        assert_eq!(receipt.shard.as_deref(), Some("target/t/1"));
        assert_eq!(receipt.trigger.mode, Mode::Manual);
        assert_eq!(receipt.targets, ["t"]);
        // Its budget is the shard margin and the budget of its target, which
        // its extraction shares with the phase of the target.
        assert_eq!(receipt.budgets.gate_seconds, 300 + 1_800);
        assert_eq!(
            Vec::from_iter(receipt.phases.keys()),
            ["extraction", "targets"]
        );
        assert_eq!(receipt.phases["extraction"].budget_seconds, 1_800);
        let units = ["target/t", "target/t/mutant/m0"];
        assert_eq!(Vec::from_iter(receipt.units.keys()), units);
        for unit in units {
            assert_eq!(fixture::status(&done, unit), (Status::Verified, None));
        }
        let sites = |unit| Vec::from_iter(fixture::commands(&done, unit).iter().map(|c| c.site));
        let extracted = [Site::Charon, Site::Aeneas, Site::TargetBuild];
        let after = [Site::TargetBuild, Site::AxiomAudit, Site::DeclarationRanges];
        assert_eq!(sites("target/t"), [&extracted[..], &after].concat());
        assert!(sites("base").is_empty());
        assert_eq!(Vec::from_iter(receipt.proof_targets.keys()), ["t"]);
        // Without a base round, the phase of the target lists the
        // hand-written module files at the snapshot commit with one command
        // of Git, and its stage holds them.
        let commit = receipt.commit.clone().expect("the snapshot commit");
        let listing = format!("ls-tree -r -z {commit} -- verification");
        let listings = (receipt.commands.iter())
            .filter(|c| c.site == Site::Git && c.argv.join(" ").ends_with(&listing));
        let phases = Vec::from_iter(listings.map(|c| c.phase.as_deref()));
        assert_eq!(phases, [Some("targets")]);
        let stage = done.run.path.join("work/targets/t/stage/verification");
        assert!(stage.join("Krepi/Proofs/T.lean").is_file());
    }

    #[test]
    fn a_run_of_named_targets_runs_only_their_part_within_the_shard_margin() {
        let fixture = with_targets("named-run", &two_targets(1_800, 1));
        // On a pull request as elsewhere, it has neither the guard nor the
        // qualification or the base round.
        let event = |name: &str| match name {
            "GITHUB_EVENT_NAME" => Some("pull_request".to_string()),
            "GITHUB_EVENT_PATH" => Some("event.json".to_string()),
            _ => None,
        };
        let context = shard_context(fixture.root(), None, &event, plenty);
        let named = BTreeSet::from(["t".to_string()]);
        let phases = phases(&context, &named, None).into_iter();
        let names = Vec::from_iter(phases.map(|phase| phase.name));
        assert_eq!(names, ["extraction", "targets"]);
        let done = named_run(&fixture, &["t"]);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        let receipt = done.written();
        assert_eq!((receipt.status, receipt.complete), (Status::Scoped, false));
        assert_eq!(receipt.trigger.mode, Mode::Scoped);
        assert_eq!(receipt.shard, None);
        assert_eq!(receipt.targets, ["t"]);
        // Its budget is the shard margin and the budget of its target, which
        // its extraction shares with the phase of the target.
        assert_eq!(receipt.budgets.gate_seconds, 300 + 1_800);
        assert_eq!(
            Vec::from_iter(receipt.phases.keys()),
            ["extraction", "targets"]
        );
        assert_eq!(receipt.phases["extraction"].budget_seconds, 1_800);
        let units = ["target/t", "target/t/mutant/m0"];
        assert_eq!(Vec::from_iter(receipt.units.keys()), units);
        for unit in units {
            assert_eq!(fixture::status(&done, unit), (Status::Verified, None));
        }
        assert!(fixture::commands(&done, "base").is_empty());
        assert_eq!(Vec::from_iter(receipt.proof_targets.keys()), ["t"]);
        // Without a base round, the phase of the target lists the
        // hand-written module files, and its stage holds them.
        let stage = done.run.path.join("work/targets/t/stage/verification");
        assert!(stage.join("Krepi/Proofs/T.lean").is_file());
    }

    #[test]
    fn a_run_of_formal_mutants_keeps_its_own_budget() {
        // It runs every phase of the gate, with the budget of `formal mutants`
        // in place of the gate's, which the budget of its target does not grow.
        let fixture = with_targets("mutants-budget", &two_targets(1_800, 1));
        let context = Context {
            budget: Some(mutants::RUN_BUDGET),
            ..shard_context(fixture.root(), None, &no_variable, plenty)
        };
        let named = BTreeSet::from(["t".to_string()]);
        let operators = vec!["literal".to_string()];
        let phases = phases(&context, &named, Some(operators.clone())).into_iter();
        let names = Vec::from_iter(phases.map(|phase| phase.name));
        assert_eq!(names, ["qualification", "extraction", "base", "targets"]);
        let run = RunDir::create(fixture.root()).expect("create the run directory");
        let phases = generating_run(&fixture, &["t"], Some(operators));
        let done = gate_with(&context, run, &named, phases, Box::new(io::sink()));
        assert_eq!(done.receipt.status, Status::Scoped, "{:?}", done.failures());
        assert_eq!(done.receipt.budgets.gate_seconds, 14_400);
        let verified = (Status::Verified, None);
        assert_eq!(fixture::status(&done, "mutants/t"), verified);
    }

    #[test]
    fn only_a_run_with_a_base_round_extracts_a_planned_target_that_a_module_imports() {
        // A statement module imports the generated modules of the planned
        // target `p`.
        let fixture = with_targets("imported-planned", &two_targets(1_800, 1));
        let statement = "module\n\npublic import KrepiGen.P.Funs\n";
        fixture.write("verification/Krepi/Statements/P.lean", statement);
        fixture.commit_all();
        let extracted = |done: &Done| Vec::from_iter(done.receipt.proof_targets.keys().cloned());
        // A run of named targets and the shard of a target extract theirs
        // alone.
        let done = named_run(&fixture, &["t"]);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        assert_eq!(extracted(&done), ["t"]);
        let phases = shard_phases(fixture.root(), "target/t/1");
        let done = gate_shard(&fixture, "target/t/1", phases, plenty);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        assert_eq!(extracted(&done), ["t"]);
        // A whole run extracts it for the base round, without a unit, and
        // its extraction has the budgets of both targets.
        let done = gate(&fixture, &[], target_run(&fixture, &[]));
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        assert_eq!(extracted(&done), ["p", "t"]);
        assert_eq!(done.receipt.proof_targets["p"].unit, None);
        assert!(!done.receipt.units.contains_key("target/p"));
        assert_eq!(done.receipt.phases["extraction"].budget_seconds, 3_600);
        // So does a run of `formal mutants`.
        let context = Context {
            budget: Some(mutants::RUN_BUDGET),
            ..shard_context(fixture.root(), None, &no_variable, plenty)
        };
        let named = BTreeSet::from(["t".to_string()]);
        let run = RunDir::create(fixture.root()).expect("create the run directory");
        let phases = generating_run(&fixture, &["t"], Some(vec!["literal".to_string()]));
        let done = gate_with(&context, run, &named, phases, Box::new(io::sink()));
        assert_eq!(done.receipt.status, Status::Scoped, "{:?}", done.failures());
        assert_eq!(extracted(&done), ["p", "t"]);
        assert!(!done.receipt.units.contains_key("target/p"));
    }

    #[test]
    fn no_other_budget_of_a_run_equals_that_of_formal_mutants() {
        // A run is one of `formal mutants`, whose budget its targets do not
        // grow, by its budget alone.
        let budgets = [
            merge::SHARD_MARGIN,
            merge::budget(qualify::PHASE),
            merge::budget("target/t/1"),
            merge::budget("lane/l"),
            comparator::BUDGET,
        ];
        for budget in budgets {
            assert_ne!(budget, mutants::RUN_BUDGET);
        }
        assert_eq!(merge::budget(qualify::PHASE), GATE_BUDGET);
        let lane = merge::SHARD_MARGIN + merge::EXTRACTION_MARGIN;
        assert_eq!(merge::budget("lane/l"), lane);
    }

    #[test]
    fn a_lane_runs_its_base_round_and_then_its_comparator_by_the_deadline_of_its_base_run() {
        let mut fixture = base::tests::base("lane-runs");
        root_package(&fixture, "krepi-kernel", "");
        base::tests::hashed(&mut fixture);
        // On a pull request as elsewhere, the base run has the extraction and
        // the base round, and the comparator run its phase alone.
        let event = |name: &str| match name {
            "GITHUB_EVENT_NAME" => Some("pull_request".to_string()),
            "GITHUB_EVENT_PATH" => Some("event.json".to_string()),
            _ => None,
        };
        let root = fixture.root();
        let context = shard_context(root, Some("lane/a"), &event, plenty);
        let names = |context: &Context| {
            let phases = phases(context, &BTreeSet::new(), None).into_iter();
            Vec::from_iter(phases.map(|phase| phase.name))
        };
        assert_eq!(names(&context), ["extraction", "base"]);
        assert_eq!(
            names(&Context {
                comparator: true,
                ..context
            }),
            ["comparator"]
        );
        // The base run writes its base record, of the deadline of the lane:
        // the shard margin, the registered budget of the lane and the
        // extraction margin from its start.
        let job = base::tests::job(&fixture);
        assert_eq!(job.code, ExitCode::SUCCESS, "{:?}", job.failures());
        assert!(!job.run.receipt().exists());
        let record = job.written();
        assert_eq!(record.schema, receipt::BASE_SCHEMA);
        assert_eq!(record.budgets.gate_seconds, 300 + 2_400 + 600);
        assert_eq!(Vec::from_iter(record.phases.keys()), ["base", "extraction"]);
        // Its commands run by that deadline: the build of the base round,
        // whose phase has 3,600 s, has what was left of the 3,300 s when it
        // started.
        let build = (record.commands.iter()).find(|c| c.site == Site::BaseBuild);
        let build = build.expect("the base build");
        assert_eq!(build.limit, LimitBy::Gate, "{build:?}");
        let left = (300 + 2_400 + 600) as f64 - build.started;
        assert!(
            (left - 1.0..=left + 1.0).contains(&build.limit_seconds),
            "{build:?}"
        );
        // The comparator run writes the receipt of the lane with that record:
        // its start, budget, phases, units and commands, and the seconds of
        // both runs.
        let done = comparator_run(&fixture, &Layout::PRODUCTION, "a", None);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        let receipt = done.written();
        assert_eq!(
            (receipt.schema, receipt.shard.as_deref()),
            (receipt::SCHEMA, Some("lane/a"))
        );
        assert_eq!((receipt.status, receipt.complete), (Status::Verified, true));
        assert_eq!(
            (receipt.started, &receipt.budgets),
            (record.started, &record.budgets)
        );
        let read = receipt.base_record.clone().expect("the base record");
        let bytes = fs::read(job.run.path.join(receipt::BASE_RECORD)).expect("the record");
        assert_eq!(
            (read.sha256, read.run),
            (toolchain::sha256(&bytes), job.run.id.clone())
        );
        assert_eq!(
            (read.started, read.seconds),
            (record.started, record.seconds)
        );
        let both = receipt::seconds(Duration::from_secs_f64(
            record.seconds + read.comparator_seconds,
        ));
        assert_eq!(receipt.seconds, both);
        let phases = Vec::from_iter(receipt.phases.keys());
        assert_eq!(phases, ["base", "comparator", "extraction"]);
        let units = Vec::from_iter(receipt.units.keys());
        assert_eq!(
            units,
            [
                "base/Krepi.Proofs.Counter.t",
                "base/lane/a",
                "comparator/lane/a"
            ]
        );
        let sequences = Vec::from_iter(receipt.commands.iter().map(|c| c.sequence));
        assert!(
            sequences.windows(2).all(|pair| pair[0] < pair[1]),
            "{sequences:?}"
        );
        let lane = receipt.lane.clone().expect("the lane");
        assert_eq!(lane.name, "a");
        assert!(
            lane.modules.contains(&"Krepi.Proofs.Counter".to_string()),
            "{lane:?}"
        );
        // Its deadline is that of the base run: with 100 s of it left, its
        // command has at most these, whatever the budget of its phase.
        let mut earlier = record.clone();
        earlier.started = unix_seconds() + 100 - earlier.budgets.gate_seconds;
        fs::write(
            job.run.path.join(receipt::BASE_RECORD),
            receipt::render(&earlier),
        )
        .expect("write");
        let done = comparator_run(&fixture, &Layout::PRODUCTION, "a", None);
        let compared = (done.receipt.commands.iter()).find(|c| c.site == Site::Comparator);
        let compared = compared.expect("the comparator");
        assert_eq!(compared.limit, LimitBy::Gate);
        assert!(
            (90.0..=100.0).contains(&compared.limit_seconds),
            "{compared:?}"
        );
        assert_eq!(done.receipt.phases["comparator"].budget_seconds, 1_800);
        // `--comparator` runs only in a lane.
        let code = command(
            root,
            &Layout::PRODUCTION,
            BTreeSet::new(),
            None,
            (false, true),
            Some("qualification"),
        );
        assert_eq!(code, ExitCode::from(2));
    }

    #[test]
    fn the_budgets_of_the_target_phases_saturate_instead_of_overflowing() {
        let fixture = with_targets("saturated-budgets", &two_targets(u64::MAX, 0));
        // The extraction adds the budget of the planned target to the largest.
        let named = BTreeSet::from(["t", "p"].map(String::from));
        let [extraction, finish] =
            target_phases(fixture.root(), &Layout::PRODUCTION, &named, None, None);
        let most = Duration::from_secs(u64::MAX);
        assert_eq!((extraction.budget, finish.budget), (most, most));
    }

    #[test]
    fn a_shard_of_a_planned_or_unknown_target_is_a_tool_failure_before_the_phases() {
        let fixture = with_targets("planned-shard", &two_targets(1_800, 1));
        for (name, units) in [("p", &["target/p"][..]), ("x", &[])] {
            let shard = target_unit(name);
            let done = gate_shard(
                &fixture,
                &shard,
                shard_phases(fixture.root(), &shard),
                plenty,
            );
            assert_eq!(done.code, ExitCode::FAILURE);
            let receipt = done.written();
            assert_eq!(
                (receipt.status, receipt.complete),
                (Status::ToolFailure, false)
            );
            let failure =
                format!("verification/targets.json registers no formal target named {name}");
            assert_eq!(done.failures(), [failure]);
            assert!(receipt.phases.values().all(|phase| !phase.ran));
            assert_eq!(Vec::from_iter(receipt.units.keys()), units);
            assert!(receipt.units.values().all(|u| u.status == Status::NotRun));
        }
        // A run of named targets may name the planned one, and names an
        // unknown one as before.
        let done = gate(&fixture, &["p", "x"], Vec::new());
        assert_eq!(
            done.failures(),
            ["verification/targets.json registers no target named x"]
        );
    }

    #[test]
    fn a_formal_target_is_verified_in_its_stage_and_a_planned_one_is_scoped() {
        let fixture = with_targets("targets", &two_targets(1_800, 1));
        let done = gate(&fixture, &[], target_run(&fixture, &[]));
        assert_eq!(done.receipt.status, Status::Verified, "{:?}", done.receipt);
        assert_eq!(fixture::status(&done, "target/t"), (Status::Verified, None));
        let sites = |unit| Vec::from_iter(fixture::commands(&done, unit).iter().map(|c| c.site));
        let expected = [Site::Charon, Site::Aeneas, Site::TargetBuild];
        let after = [Site::TargetBuild, Site::AxiomAudit, Site::DeclarationRanges];
        assert_eq!(sites("target/t"), [&expected[..], &after].concat());
        // Its mutant is extracted and built in a stage of its own, where the
        // build fails in the theorem that it names, and is verified.
        assert_eq!(sites("target/t/mutant/m0"), expected);
        let mutant = (Status::Verified, None);
        assert_eq!(fixture::status(&done, "target/t/mutant/m0"), mutant);
        // The target is extracted for the extraction triple, and the planned
        // one not at all.
        let charon = &fixture::commands(&done, "target/t")[0];
        assert!(
            charon
                .argv
                .ends_with(&["--target", "aarch64-unknown-none"].map(String::from))
        );
        let formal = &done.receipt.proof_targets["t"];
        assert_eq!(Vec::from_iter(done.receipt.proof_targets.keys()), ["t"]);
        assert_eq!(formal.unit.as_deref(), Some("target/t"));
        assert!(formal.typed && formal.problems.is_empty());
        assert_eq!(done.receipt.budgets.gate_seconds, 7_200 + 1_800);
        assert_eq!(done.receipt.phases["extraction"].budget_seconds, 1_800);
        // The Cargo target directory of the extraction is removed after it.
        assert!(done.run.path.join("work/targets/t/extract").is_dir());
        assert!(!done.run.path.join("work/targets/t/extract/target").exists());
        // A run of the planned target, which runs its part alone, extracts
        // and concludes it as scoped, and extracts no other target.
        let done = named_run(&fixture, &["p"]);
        assert_eq!(done.receipt.status, Status::Scoped, "{:?}", done.receipt);
        assert_eq!(fixture::status(&done, "target/p"), (Status::Scoped, None));
        assert_eq!(Vec::from_iter(done.receipt.units.keys()), ["target/p"]);
        assert_eq!(Vec::from_iter(done.receipt.proof_targets.keys()), ["p"]);
        let planned = &done.receipt.proof_targets["p"];
        assert_eq!(planned.unit.as_deref(), Some("target/p"));
        assert!(planned.typed);
        let planned = fixture::commands(&done, "target/p").into_iter();
        let sites = Vec::from_iter(planned.map(|command| command.site));
        assert_eq!(sites, [Site::Charon, Site::Aeneas, Site::TargetBuild]);
        assert!(fixture::commands(&done, "base").is_empty());
        assert_eq!(done.receipt.budgets.gate_seconds, 300 + 1_800);
        assert_eq!(done.receipt.phases["extraction"].budget_seconds, 1_800);
    }

    #[test]
    fn a_mutant_stage_holds_nothing_that_its_target_stage_wrote_and_the_backend_is_unchanged() {
        let fixture = with_targets("isolation", &two_targets(1_800, 1));
        // The build of the proofs writes a file into the stage of the
        // target, and records it when it finds one in the stage of a mutant,
        // where it then fails in the theorem that the mutant names.
        let failed = "error: Krepi/Proofs/T.lean:3:0: unsolved goals";
        let failing = fixture::failing("Krepi.Proofs.T", &[failed], 1);
        let script = format!(
            "case $PWD in\n  */mutants/*) if [ -e leaked ]; then : > \"$lake/leaked\"; fi\n\
             {failing};;\n  *) echo target > leaked ;;\nesac\n"
        );
        fixture::lake_script(&fixture, "+Krepi", &script);
        let tools = fixture.root().join("artifacts/formal/tools");
        let roots = [tools.join("backend"), tools.join("lean")];
        let before = lean::listing(&roots, None).expect("a listing");
        let done = gate(&fixture, &[], target_run(&fixture, &[]));
        assert_eq!(
            done.receipt.status,
            Status::Verified,
            "{:?}",
            done.failures()
        );
        assert_eq!(fixture::status(&done, "target/t"), (Status::Verified, None));
        let mutant = (Status::Verified, None);
        assert_eq!(fixture::status(&done, "target/t/mutant/m0"), mutant);
        // The proofs of the target are built before its mutant.
        let target = fixture::commands(&done, "target/t").into_iter();
        let target = target
            .filter(|c| c.site == Site::TargetBuild)
            .map(|c| c.sequence);
        let mutant = fixture::commands(&done, "target/t/mutant/m0").into_iter();
        let (target, mutant) = (target.max(), mutant.map(|c| c.sequence).min());
        assert!(target.is_some() && target < mutant, "{target:?} {mutant:?}");
        // The file is in the stage of the target and was not in that of
        // the mutant.
        let work = done.run.path.join("work/targets/t");
        assert!(work.join("stage/verification/leaked").is_file());
        assert!(work.join("mutants/m0/stage/verification").is_dir());
        assert!(!fixture.root().join("artifacts/lake/leaked").exists());
        // The listing of the backend and Lean is unchanged, after each
        // phase and over the run.
        assert_eq!(done.receipt.failures, []);
        assert_eq!(lean::listing(&roots, Some(&before)), Ok(before.clone()));
    }

    #[test]
    fn a_mutant_starts_from_the_build_of_its_target_which_must_not_change() {
        let fixture = with_targets("seeded", &two_targets(1_800, 2));
        // Aeneas writes other definitions for a mutant than for its target.
        let bin = fixture.root().join("artifacts/formal/tools/bin");
        fs::rename(bin.join("aeneas"), bin.join("aeneas-stand-in")).expect("rename");
        let wrapper = "\"$(dirname \"$0\")/aeneas-stand-in\" \"$@\" || exit\n\
            while [ $# -gt 0 ]; do\n  \
              case \"$1\" in -subdir) subdir=$2 ;; -dest) dest=$2 ;; esac\n  shift\n\
            done\n\
            case $PWD in */mutants/*) echo '-- mutant' >> \"$dest/$subdir/Funs.lean\" ;; esac";
        fixture.tool("aeneas", wrapper);
        // The build of the target writes its output below the build
        // directory of its stage; that of a mutant records the output that it
        // finds there and the generated definitions of its stage, which Lake
        // reads to decide what to build again, and fails in the theorem that
        // the mutant names.
        let olean = ".lake/build/lib/lean/KrepiGen/T/Funs.olean";
        let failed = "error: Krepi/Proofs/T.lean:3:0: unsolved goals";
        let failing = fixture::failing("Krepi.Proofs.T", &[failed], 1);
        let mutant = |extra: &str| {
            format!(
                "case $PWD in\n  */mutants/*) cat {olean} KrepiGen/T/Funs.lean > \"$lake/seen-$$\"\n\
                 {extra}{failing};;\n  \
                 *) mkdir -p \"$(dirname {olean})\" && echo 'target build' > {olean} ;;\nesac\n"
            )
        };
        fixture::lake_script(&fixture, "+Krepi", &mutant(""));
        let done = gate(&fixture, &[], target_run(&fixture, &[]));
        assert_eq!(
            done.receipt.status,
            Status::Verified,
            "{:?}",
            done.failures()
        );
        let seen = fs::read_dir(fixture.root().join("artifacts/lake")).expect("the calls");
        let seen = seen.map(|entry| entry.expect("a file").path());
        let seen = seen.filter(|path| path.to_string_lossy().contains("/seen-"));
        let seen = Vec::from_iter(seen.map(|path| fs::read_to_string(path).expect("seen")));
        assert_eq!(seen, ["target build\n-- mutant\n"; 2]);
        let target = done.run.path.join("work/targets/t/stage/verification");
        let built = fs::read_to_string(target.join(olean)).expect("the build of the target");
        assert_eq!(built, "target build\n");
        // A mutant whose build writes the build of the target leaves the
        // mutants judged and fails the target.
        let fixture = with_targets("seed-changed", &two_targets(1_800, 1));
        let write = format!("echo changed >> ../../../../stage/verification/{olean}\n");
        fixture::lake_script(&fixture, "+Krepi", &mutant(&write));
        let done = gate(&fixture, &[], target_run(&fixture, &[]));
        assert_eq!(done.receipt.status, Status::ToolFailure);
        let mutant = (Status::Verified, None);
        assert_eq!(fixture::status(&done, "target/t/mutant/m0"), mutant);
        let (status, reason) = fixture::status(&done, "target/t");
        let changed = "the build that seeded the mutants changed during the phase; \
                       changed paths (1)";
        assert_eq!(status, Status::ToolFailure);
        assert!(
            reason.is_some_and(|reason| reason.starts_with(changed)),
            "{reason:?}"
        );
    }

    /// Makes the stand-in `tool` of `fixture` run `script` after it passes.
    fn after_tool(fixture: &Fixture, tool: &str, script: &str) {
        let bin = fixture.root().join("artifacts/formal/tools/bin");
        let stand_in = format!("{tool}-stand-in");
        fs::rename(bin.join(tool), bin.join(&stand_in)).expect("rename");
        fixture.tool(
            tool,
            &format!("\"$(dirname \"$0\")/{stand_in}\" \"$@\" || exit\n{script}\n"),
        );
    }

    /// A shell loop that waits for `path` to exist, looking 6,000 times, 10 ms
    /// apart: a minute or more.
    fn waits_for(path: &Path) -> String {
        let path = path.display();
        format!("i=0; while [ ! -e {path} ] && [ $i -lt 6000 ]; do sleep 0.01; i=$((i+1)); done\n")
    }

    #[test]
    fn the_commands_of_a_target_and_its_mutants_share_its_budget_by_the_time_that_any_runs() {
        assert_eq!(covered([]), 0.0);
        assert_eq!(covered([(2.0, 3.0), (0.0, 1.0), (4.0, 4.0)]), 2.0);
        assert_eq!(
            covered([(0.0, 2.0), (1.5, 2.5), (1.0, 3.0), (3.0, 4.0)]),
            4.0
        );
        assert_eq!(covered([(0.0, 4.0), (1.0, 2.0), (3.0, 5.0)]), 5.0);
        // The command of the target waits for that of its mutant, which
        // starts while it runs.
        let fixture = Fixture::new("overlap");
        let [first, second] =
            ["first", "second"].map(|file| fixture.root().join("artifacts").join(file));
        let (target, mutant) = ("target/t", "target/t/mutant/m0");
        let phases = vec![phase("targets", LONG, &[target, mutant], |run| {
            run.budgets
                .insert(target.to_string(), Duration::from_secs(1_800));
            let record = receipt::Target {
                unit: Some(target.to_string()),
                ..receipt::Target::default()
            };
            run.receipt.proof_targets.insert("t".to_string(), record);
            let waits = format!("touch {}; {}", first.display(), waits_for(&second));
            let started = format!("sleep 0.1; touch {}", second.display());
            let gate = &*run;
            std::thread::scope(|scope| {
                scope.spawn(|| shell(gate, target, &waits));
                fixture::wait_until(|| first.exists(), "the first command did not start");
                scope.spawn(|| shell(gate, mutant, &started));
            });
            // A command of the mutant once the budget is used up.
            let spent = run
                .records()
                .spent(target, run.start.elapsed().as_secs_f64());
            run.budgets
                .insert(target.to_string(), Duration::from_secs_f64(spent));
            assert_eq!(shell(run, mutant, "exit 0").class, Class::NotRun);
            for unit in [target, mutant] {
                run.conclude(unit, (Status::Verified, None));
            }
            Ok(())
        })];
        let done = gate(&fixture, &[], phases);
        let [a, b] = [target, mutant].map(|unit| fixture::commands(&done, unit)[0].clone());
        let late = fixture::commands(&done, mutant)[1].clone();
        // Both reach the limit of the target together.
        assert_eq!((a.limit, b.limit), (LimitBy::Target, LimitBy::Target));
        let end = |c: &receipt::Command| c.started + c.limit_seconds;
        assert!((end(&a) - end(&b)).abs() < 0.0025, "{a:?} {b:?}");
        assert!(b.started > a.started && b.limit_seconds < a.limit_seconds);
        // The time during which both ran counts once.
        let t = &done.receipt.proof_targets["t"];
        let intervals = [&a, &b, &late].map(|c| (c.started, c.started + c.seconds));
        assert_eq!(
            t.seconds,
            receipt::seconds(Duration::from_secs_f64(covered(intervals)))
        );
        assert!(t.seconds < a.seconds + b.seconds, "{t:?} {a:?} {b:?}");
        assert_eq!(t.mutants, BTreeMap::from([("m0".to_string(), b.seconds)]));
        let used_up = Some("the target budget was used up");
        assert_eq!(
            (late.class, late.reason.as_deref()),
            (Class::NotRun, used_up)
        );
        assert_eq!(fixture::status(&done, mutant), (Status::Budget, used_up));
        assert_eq!(done.receipt.status, Status::Budget);
        // Two commands that hang side by side meet the limit together, and
        // each concludes its unit BUDGET.
        let fixture = Fixture::new("overlap-budget");
        let started = fixture.root().join("artifacts/started");
        let phases = vec![phase("targets", LONG, &[target, mutant], |run| {
            run.budgets
                .insert(target.to_string(), Duration::from_secs(1));
            let hangs = format!("touch {}; exec sleep 30", started.display());
            let gate = &*run;
            std::thread::scope(|scope| {
                scope.spawn(|| shell(gate, target, &hangs));
                fixture::wait_until(|| started.exists(), "the first command did not start");
                scope.spawn(|| shell(gate, mutant, "exec sleep 30"));
            });
            for unit in [target, mutant] {
                run.conclude(unit, (Status::Verified, None));
            }
            Ok(())
        })];
        let done = gate(&fixture, &[], phases);
        let [a, b] = [target, mutant].map(|unit| fixture::commands(&done, unit)[0].clone());
        let stopped = |c: &receipt::Command| {
            c.timed_out && (c.limit, c.class) == (LimitBy::Target, Class::Budget)
        };
        assert!(stopped(&a), "{a:?}");
        // A thread that started its command after the limit finds it used
        // up, which is the other outcome at the limit.
        if b.class != Class::NotRun {
            assert!(
                stopped(&b) && (end(&a) - end(&b)).abs() < 0.0025,
                "{a:?} {b:?}"
            );
        }
        for unit in [target, mutant] {
            assert_eq!(fixture::status(&done, unit).0, Status::Budget);
        }
        // A command of another unit runs before the target's, which counts
        // while it is read and recorded: a command of the mutant that starts
        // then has only what the target's left, and is recorded first.
        let fixture = Fixture::new("overlap-window");
        let (other, ended) = ("target/u", fixture.root().join("artifacts/ended"));
        let phases = vec![phase("targets", LONG, &[other, target, mutant], |run| {
            run.budgets
                .insert(target.to_string(), Duration::from_secs(1));
            let record = receipt::Target {
                unit: Some(target.to_string()),
                ..receipt::Target::default()
            };
            run.receipt.proof_targets.insert("t".to_string(), record);
            let gate = &*run;
            shell(gate, other, "sleep 0.3");
            let read = |_: &Ran| {
                let recorded = gate.records().commands.len();
                fs::write(&ended, "").expect("the mark");
                fixture::wait_until(|| gate.records().commands.len() > recorded, "no mutant");
                Ok(())
            };
            std::thread::scope(|scope| {
                scope.spawn(|| shell_reading(gate, target, "sleep 0.7", read));
                fixture::wait_until(|| ended.exists(), "the target's command did not end");
                shell(gate, mutant, "sleep 0.6");
            });
            for unit in [other, target, mutant] {
                run.conclude(unit, (Status::Verified, None));
            }
            Ok(())
        })];
        let done = gate(&fixture, &[], phases);
        let [a, b] = [target, mutant].map(|unit| fixture::commands(&done, unit)[0].clone());
        assert_eq!((a.limit, a.limit_seconds), (LimitBy::Target, 1.0), "{a:?}");
        assert!(
            b.limit_seconds <= (1.0 - a.seconds).max(0.0) + 0.0025,
            "{a:?} {b:?}"
        );
        let intervals = [&a, &b].map(|c| (c.started, c.started + c.seconds));
        assert_eq!(
            done.receipt.proof_targets["t"].seconds,
            receipt::seconds(Duration::from_secs_f64(covered(intervals)))
        );
        let status = (fixture::status(&done, mutant).0, done.receipt.status);
        assert_eq!(status, (Status::Budget, Status::Budget));
        // The receipt lists the commands in the order in which they started.
        let commands = &done.receipt.commands;
        assert!(
            (commands.windows(2))
                .all(|w| w[0].sequence < w[1].sequence && w[0].started <= w[1].started),
            "{commands:?}"
        );
    }

    #[test]
    fn a_mutant_is_extracted_while_the_one_before_it_builds() {
        // The mutant after m0 on its worker, `next`, is extracted while m0 builds.
        let fixture = with_targets("pipeline", &two_targets(1_800, merge::WORKERS + 1));
        let next = format!("m{}", merge::WORKERS);
        let extracted = fixture.root().join("artifacts/extracted");
        let mark = format!(
            "case $PWD in */mutants/{next}/*) touch {} ;; esac",
            extracted.display()
        );
        after_tool(&fixture, "aeneas", &mark);
        let failed = "error: Krepi/Proofs/T.lean:3:0: unsolved goals";
        let failing = fixture::failing("Krepi.Proofs.T", &[failed], 1);
        let wait = waits_for(&extracted);
        let script = format!("case $PWD in */mutants/m0/*) {wait};; esac\n{failing}");
        fixture::lake_script(
            &fixture,
            "+Krepi",
            &format!("case $PWD in */mutants/*) {script};; esac\n"),
        );
        let done = gate(&fixture, &[], target_run(&fixture, &[]));
        assert_eq!(
            done.receipt.status,
            Status::Verified,
            "{:?}",
            done.failures()
        );
        let site = |unit: &str, site| {
            fixture::commands(&done, unit)
                .into_iter()
                .find(|c| c.site == site)
        };
        let built = site("target/t/mutant/m0", Site::TargetBuild).expect("the build of m0");
        let aeneas = site(&format!("target/t/mutant/{next}"), Site::Aeneas).expect("Aeneas");
        assert!(
            aeneas.started < built.started + built.seconds,
            "{aeneas:?} {built:?}"
        );
    }

    #[test]
    fn a_mutant_whose_extraction_fails_is_not_built_and_the_run_is_not_verified() {
        let fixture = with_targets("pipeline-failed", &two_targets(1_800, 3));
        after_tool(
            &fixture,
            "aeneas",
            "case $PWD in */mutants/m1/*) exit 1 ;; esac",
        );
        let done = gate(&fixture, &[], target_run(&fixture, &[]));
        assert_eq!(
            done.receipt.status,
            Status::Rejected,
            "{:?}",
            done.failures()
        );
        let (status, reason) = fixture::status(&done, "target/t/mutant/m1");
        let inconclusive = "inconclusive, its extraction failed";
        assert!(status == Status::Rejected && reason.is_some_and(|r| r.starts_with(inconclusive)));
        let sites = fixture::commands(&done, "target/t/mutant/m1")
            .into_iter()
            .map(|c| c.site);
        assert_eq!(Vec::from_iter(sites), [Site::Charon, Site::Aeneas]);
        for unit in ["target/t", "target/t/mutant/m0", "target/t/mutant/m2"] {
            assert_eq!(fixture::status(&done, unit), (Status::Verified, None));
        }
    }

    #[test]
    fn a_worker_that_stops_at_an_error_fails_the_run_and_keeps_what_ran() {
        // The second mutant of the first worker edits a file that the
        // package does not have.
        let mut targets: serde_json::Value =
            serde_json::from_str(&two_targets(1_800, merge::WORKERS + 1)).expect("JSON");
        targets[0]["mutants"][merge::WORKERS]["file"] = "src/missing.rs".into();
        let fixture = with_targets("worker-failed", &targets.to_string());
        let done = gate(&fixture, &[], target_run(&fixture, &[]));
        assert_eq!(
            (done.receipt.status, done.receipt.complete),
            (Status::ToolFailure, false)
        );
        let stopped = done
            .failures()
            .into_iter()
            .find(|f| f.starts_with("the phase targets stopped"));
        let stopped = stopped.expect("the phase stopped");
        assert!(stopped.contains("No such file or directory"), "{stopped}");
        // The mutant before it is concluded; the failed one ran nothing.
        assert_eq!(
            fixture::status(&done, "target/t/mutant/m0"),
            (Status::Verified, None)
        );
        let failed = format!("target/t/mutant/m{}", merge::WORKERS);
        assert_eq!(
            fixture::status(&done, &failed),
            (Status::NotRun, Some(stopped))
        );
        assert!(fixture::commands(&done, &failed).is_empty());
        for unit in (1..merge::WORKERS).map(|index| format!("target/t/mutant/m{index}")) {
            let (status, _) = fixture::status(&done, &unit);
            assert!(
                matches!(status, Status::Verified | Status::NotRun),
                "{status:?}"
            );
        }
        assert_eq!(
            fixture::status(&done, "target/t"),
            (Status::NotRun, Some(stopped))
        );
    }

    #[test]
    fn the_workers_of_a_target_share_no_stage_cargo_directory_or_work_directory() {
        let count = 2 * merge::WORKERS;
        let fixture = with_targets("workers", &two_targets(1_800, count));
        // Charon records its Cargo target directory and both its home and
        // temporary directories, as the build of each mutant does; that build
        // also records a file that it finds in its stage and leaves one.
        let lake = fixture.root().join("artifacts/lake");
        let cargo = format!(
            "echo \"$CARGO_TARGET_DIR $HOME $TMPDIR\" >> {}",
            lake.join("cargo").display()
        );
        after_tool(
            &fixture,
            "charon",
            &format!("case $PWD in */mutants/*) {cargo} ;; esac"),
        );
        let failed = "error: Krepi/Proofs/T.lean:3:0: unsolved goals";
        let failing = fixture::failing("Krepi.Proofs.T", &[failed], 1);
        let script = format!(
            "case $PWD in */mutants/*) if [ -e leaked ]; then : > \"$lake/leaked\"; fi\n\
             echo \"$PWD\" > leaked; echo \"$HOME $TMPDIR\" >> \"$lake/homes\"\n{failing};; esac\n"
        );
        fixture::lake_script(&fixture, "+Krepi", &script);
        let done = gate(&fixture, &[], target_run(&fixture, &[]));
        assert_eq!(
            done.receipt.status,
            Status::Verified,
            "{:?}",
            done.failures()
        );
        assert!(!lake.join("leaked").exists());
        // Each mutant runs its commands in its own work directory, where
        // Charon builds and its commands have their home and temporary
        // directories.
        let run = relative(fixture.root(), &done.run.path);
        let read = |file| fs::read_to_string(lake.join(file)).expect(file);
        let lines = |file| BTreeSet::from_iter(read(file).lines().map(str::to_string));
        let (cargo, homes) = (lines("cargo"), lines("homes"));
        assert_eq!((cargo.len(), homes.len()), (count, count), "{cargo:?}");
        for name in (0..count).map(|index| format!("m{index}")) {
            let own = format!("{run}/work/targets/t/mutants/{name}/");
            let commands = fixture::commands(&done, &format!("target/t/mutant/{name}"));
            assert!(
                commands.iter().all(|c| c.cwd.starts_with(&own)),
                "{commands:?}"
            );
            let path = |dir| fixture.root().join(&own).join(dir).display().to_string();
            let dirs = format!("{} {}", path("home"), path("tmp"));
            assert!(homes.contains(&dirs), "{homes:?}");
            let target = format!("{} {dirs}", path("extract/target"));
            assert!(cargo.contains(&target), "{cargo:?}");
        }
    }

    #[test]
    fn a_target_is_rejected_for_each_problem_of_its_unit() {
        // Each case gives the target `t` its `registry` entries, makes Lake
        // run a `script` for a key and names the reason of `target/t`.
        let theorem = "Krepi.Proofs.T.f_spec";
        let types = "error: KrepiGen/T/Funs.lean:3:8: type mismatch";
        let proofs = "error: Krepi/Proofs/T.lean:3:0: unsolved goals";
        let other = "Krepi.Proofs.T.g_spec";
        let trusted = serde_json::json!([{"name": "Krepi.Extra.ax", "reason": "Reviewed."}]);
        let cases = [
            (
                serde_json::json!({}),
                Some((
                    "KrepiGen.T.Funs",
                    fixture::failing("KrepiGen.T.Funs", &[types], 1),
                )),
                format!(
                    "its generated definitions do not type-check: {types} | error: build failed"
                ),
            ),
            (
                serde_json::json!({}),
                Some(("+Krepi", fixture::failing("Krepi.Proofs.T", &[proofs], 1))),
                format!(
                    "the proofs failed at Krepi/Proofs/T.lean:3:0: {proofs} | error: build failed"
                ),
            ),
            (
                serde_json::json!({}),
                Some(("audit", "exit 1\n".to_string())),
                "the audit did not pass".to_string(),
            ),
            (
                serde_json::json!({"obligations": [{"id": "f", "theorems": [other]}]}),
                None,
                format!("the audit did not report {other} in a proof module"),
            ),
            (
                serde_json::json!({"obligations": [{"id": "f", "theorems": []}]}),
                None,
                "its obligations name no theorem".to_string(),
            ),
            (
                serde_json::json!({"unconstrained": ["core::x"]}),
                None,
                "t: registered external item core::x is not reached".to_string(),
            ),
            (
                serde_json::json!({}),
                None,
                format!("{theorem} depends on Krepi.Extra.ax"),
            ),
        ];
        for (index, (entries, script, reason)) in cases.into_iter().enumerate() {
            let mut registry: serde_json::Value =
                serde_json::from_str(&two_targets(1_800, 1)).expect("JSON");
            let target = registry[0].as_object_mut().expect("the target t");
            target.extend(entries.as_object().expect("entries").clone());
            let fixture = with_targets(&format!("rejected-{index}"), &registry.to_string());
            if let Some((key, script)) = script {
                fixture::lake_script(&fixture, key, &script);
            }
            // The audit reports an axiom that no source admits.
            if index == 6 {
                fixture.write(
                    &format!("artifacts/lake/axioms/{theorem}"),
                    "Krepi.Extra.ax",
                );
            }
            let done = gate(&fixture, &[], target_run(&fixture, &[]));
            assert_eq!(done.receipt.status, Status::Rejected, "{:?}", done.receipt);
            let rejected = (Status::Rejected, Some(reason.as_str()));
            assert_eq!(fixture::status(&done, "target/t"), rejected, "case {index}");
            assert_eq!(done.receipt.proof_targets["t"].problems, [reason]);
            // The axiom is the only problem until the target trusts it.
            if index == 6 {
                registry[0]["trusted_axioms"] = trusted.clone();
                register(&fixture, &registry.to_string());
                let done = gate(&fixture, &[], target_run(&fixture, &[]));
                assert_eq!(fixture::status(&done, "target/t"), (Status::Verified, None));
            }
        }
    }

    #[test]
    fn a_target_that_outruns_its_budget_is_budget_and_its_receipt_is_written() {
        // The build of the proofs hangs after the extraction, whose seconds
        // the budget of the target has already spent.
        let fixture = with_targets("target-budget", &two_targets(3, 1));
        fixture::lake_script(&fixture, "+Krepi", "exec sleep 30\n");
        let done = gate(&fixture, &[], target_run(&fixture, &[]));
        assert_eq!(done.code, ExitCode::FAILURE);
        let receipt = done.written();
        assert_eq!(receipt, done.receipt);
        assert_eq!(receipt.status, Status::Budget);
        assert_eq!(receipt.units["target/t"].status, Status::Budget);
        let own = fixture::commands(&done, "target/t");
        let hung = own
            .iter()
            .position(|c| c.site == Site::TargetBuild && c.argv.ends_with(&["+Krepi".to_string()]));
        let (before, hung) = (
            &own[..hung.expect("the build of the proofs")],
            own[hung.unwrap_or(0)],
        );
        let spent: f64 = before.iter().map(|command| command.seconds).sum();
        assert_eq!(
            (hung.limit, hung.class),
            (LimitBy::Target, Class::Budget),
            "{hung:?}"
        );
        assert!(hung.timed_out && spent > 0.0 && (hung.limit_seconds + spent - 3.0).abs() < 0.01);
        let target = &receipt.proof_targets["t"];
        assert_eq!(target.budget_seconds, 3);
        assert!(
            target.seconds >= hung.limit_seconds + spent - 0.01,
            "{target:?}"
        );
    }

    #[test]
    fn a_target_with_more_mutants_than_it_may_register_is_budget_without_running() {
        let fixture = with_targets("target-mutants", &two_targets(1_800, registry::MUTANTS + 1));
        let done = gate(&fixture, &[], target_run(&fixture, &[]));
        assert_eq!(done.receipt.status, Status::Budget, "{:?}", done.failures());
        let reason = "it registers 31 mutants, more than the 30 it may";
        assert_eq!(
            fixture::status(&done, "target/t"),
            (Status::Budget, Some(reason))
        );
        assert!(fixture::commands(&done, "target/t").is_empty());
        assert!(!done.receipt.proof_targets["t"].typed);
    }

    #[test]
    fn the_calibration_targets_are_outside_the_target_set_of_production() {
        let read = |layout: &Layout| fs::read_to_string(repo::root().join(layout.registry));
        let names =
            |layout| registry::states(&read(layout).expect("a registry")).expect("a registry");
        let (production, calibration) = (names(&Layout::PRODUCTION), names(&Layout::CALIBRATION));
        assert!(!calibration.is_empty());
        assert!(
            calibration
                .keys()
                .all(|name| !production.contains_key(name))
        );
        // A run in the production layout selects none of them, cannot name
        // them and records none.
        let fixture = Fixture::new("calibration-set");
        let text = read(&Layout::CALIBRATION).expect("the calibration registry");
        fixture.write(Layout::CALIBRATION.registry, &text);
        fixture.commit_all();
        let named = gate(&fixture, &["calibration"], Vec::new());
        let unknown = "verification/targets.json registers no target named calibration";
        assert!(
            named.has_failure(Status::ToolFailure, unknown),
            "{:?}",
            named.failures()
        );
        let whole = gate(&fixture, &[], target_run(&fixture, &[]));
        assert_eq!(
            whole.receipt.status,
            Status::Verified,
            "{:?}",
            whole.failures()
        );
        assert!(whole.receipt.phases["extraction"].ran && whole.receipt.phases["targets"].ran);
        assert!(whole.receipt.targets.is_empty() && whole.receipt.proof_targets.is_empty());
        // `formal check` in the production layout reads its own registry
        // alone: a calibration registry that it would refuse changes nothing.
        let mut tree = Tree::load(&repo::root()).expect("the repository");
        let roots = manifests::kernel_metadata(&repo::root(), manifests::KERNEL)
            .expect("the kernel workspace");
        let roots = inventory::roots(&roots, manifests::KERNEL).expect("the roots");
        let before = inventory::check(&tree, &roots, &Layout::PRODUCTION);
        tree.insert(
            Layout::CALIBRATION.registry,
            Entry::File(b"not a registry".to_vec()),
        );
        assert_eq!(inventory::check(&tree, &roots, &Layout::PRODUCTION), before);
    }

    #[test]
    fn a_run_of_named_targets_is_scoped_and_not_complete() {
        let fixture = Fixture::new("scoped");
        register(&fixture, r#"[{"name": "demo"}]"#);
        root_package(&fixture, "krepi-kernel", "");
        let done = gate(&fixture, &["demo"], Vec::new());
        assert_eq!(done.code, ExitCode::SUCCESS);
        let receipt = done.written();
        assert_eq!(receipt.status, Status::Scoped);
        assert_eq!(receipt.trigger.mode, Mode::Scoped);
        assert!(!receipt.complete);
        assert_eq!(receipt.targets, ["demo"]);
        assert_eq!(done.failures(), Vec::<&str>::new());
    }

    #[test]
    fn a_gate_input_changed_during_the_run_makes_it_stale() {
        let fixture = Fixture::new("stale");
        let registry = fixture.root().join("verification/targets.json");
        let phases = vec![phase("edit", LONG, &["u1"], |run| {
            let mut text = fs::read_to_string(&registry).map_err(|error| error.to_string())?;
            text.push('\n');
            fs::write(&registry, text).map_err(|error| error.to_string())?;
            run.conclude("u1", (Status::Verified, None));
            Ok(())
        })];
        let done = gate(&fixture, &[], phases);
        assert_eq!(done.code, ExitCode::FAILURE);
        let receipt = done.written();
        assert_eq!(receipt.status, Status::Stale);
        assert_eq!(receipt.inputs.clean_after, Some(false));
        assert_eq!(receipt.inputs.after, receipt.inputs.before);
        assert_eq!(
            done.failures(),
            ["gate inputs changed during the run:  M verification/targets.json"]
        );
        // A change that is committed during the run leaves the checkout
        // clean, and its snapshot differs.
        fixture.commit_all();
        let phases = vec![phase("commit", LONG, &["u1"], |run| {
            fixture.write("xtask/README", "Changed.\n");
            fixture.commit_all();
            run.conclude("u1", (Status::Verified, None));
            Ok(())
        })];
        let done = gate(&fixture, &[], phases);
        assert_eq!(done.receipt.status, Status::Stale);
        assert_eq!(done.receipt.inputs.clean_after, Some(true));
        let (before, after) = (&done.receipt.inputs.before, &done.receipt.inputs.after);
        let changed = |path: &str| {
            before.as_ref().map(|snapshot| &snapshot[path])
                != after.as_ref().map(|snapshot| &snapshot[path])
        };
        assert!(changed("xtask"));
        assert!(!changed("kernel"));
        assert_eq!(
            done.failures(),
            ["gate inputs changed during the run: xtask"]
        );
        // The receipt of the next run is not stale.
        assert_eq!(
            gate(&fixture, &[], Vec::new()).receipt.status,
            Status::Verified
        );
    }

    #[test]
    fn a_kernel_dependency_outside_the_kernel_workspace_rejects_the_run() {
        let fixture = Fixture::new("outside");
        fixture.write(
            "kernel/abi/Cargo.toml",
            "[package]\nname = \"abi\"\nedition = \"2024\"\n\n[dependencies]\n\
             outside = { path = \"../../verification/outside\" }\n",
        );
        fixture.write(
            "verification/outside/Cargo.toml",
            "[package]\nname = \"outside\"\nedition = \"2024\"\n\n[workspace]\n",
        );
        fixture.write("verification/outside/src/lib.rs", "");
        fixture.lock();
        fixture.commit_all();
        let done = gate(&fixture, &[], Vec::new());
        assert_eq!(done.code, ExitCode::FAILURE);
        let receipt = done.written();
        assert_eq!(receipt.status, Status::Rejected);
        assert!(!receipt.complete);
        assert_eq!(done.failures().len(), 1, "{:?}", done.failures());
        assert!(
            done.has_failure(
                Status::Rejected,
                "kernel/abi/Cargo.toml: [dependencies] outside"
            ),
            "{:?}",
            done.failures()
        );
        assert!(!done.sites().contains(&Site::CargoMetadata));
        // A dependency outside the gate inputs, which the export does not
        // hold, is rejected as well.
        let fixture = Fixture::new("not-exported");
        fixture.write(
            "kernel/abi/Cargo.toml",
            "[package]\nname = \"abi\"\nedition = \"2024\"\n\n[dependencies]\n\
             x = { path = \"../../user/x\" }\n",
        );
        fixture.write(
            "user/x/Cargo.toml",
            "[package]\nname = \"x\"\nedition = \"2024\"\n\n[workspace]\n",
        );
        fixture.write("user/x/src/lib.rs", "");
        fixture.lock();
        fixture.commit_all();
        let done = gate(&fixture, &[], Vec::new());
        assert_eq!(done.code, ExitCode::FAILURE);
        assert_eq!(done.receipt.status, Status::Rejected);
        assert!(!done.receipt.complete);
        assert_eq!(
            done.failures(),
            [
                "kernel/abi/Cargo.toml: [dependencies] x has path `../../user/x`; kernel-workspace \
                 crates may only depend on paths inside kernel/"
            ]
        );
        assert!(!done.sites().contains(&Site::CargoMetadata));
    }

    #[test]
    fn a_kernel_source_that_a_link_takes_out_of_the_workspace_rejects_the_run() {
        let fixture = Fixture::new("linked-source");
        fs::remove_dir_all(fixture.root().join("kernel/abi/src")).expect("remove the sources");
        fixture.symlink("kernel/abi/src", "../../verification/outside");
        fixture.write("verification/outside/lib.rs", "");
        fixture.commit_all();
        let done = gate(&fixture, &[], Vec::new());
        assert_eq!(done.code, ExitCode::FAILURE);
        let receipt = done.written();
        assert_eq!(receipt.status, Status::Rejected);
        assert!(!receipt.complete);
        assert_eq!(done.failures().len(), 1, "{:?}", done.failures());
        assert!(
            done.has_failure(
                Status::Rejected,
                "kernel workspace: target \"abi\" of package \"abi\" has a source that does not \
                 resolve inside kernel/"
            ),
            "{:?}",
            done.failures()
        );
        let metadata = receipt
            .commands
            .iter()
            .find(|command| command.site == Site::CargoMetadata)
            .expect("cargo metadata ran");
        assert_eq!(metadata.class, Class::Passed);
        assert!(metadata.cwd.ends_with("/work/source"), "{}", metadata.cwd);
    }

    #[test]
    fn cargo_configuration_outside_the_snapshot_fails_the_run() {
        let fixture = Fixture::new("cargo-config");
        let root = fs::canonicalize(fixture.root()).expect("resolve the fixture");
        let expect_found = |path: &str| {
            let done = gate(&fixture, &[], Vec::new());
            assert_eq!(done.code, ExitCode::FAILURE);
            assert_eq!(done.written().status, Status::ToolFailure);
            assert!(!done.receipt.complete);
            assert_eq!(
                done.failures(),
                [format!(
                    "Cargo would read {} in the export, which is not in the snapshot",
                    root.join(path).display()
                )]
            );
            assert!(!done.sites().contains(&Site::CargoMetadata));
        };
        // Files that Git ignores, or that are not gate inputs, leave the
        // checkout clean.
        for path in ["artifacts/.cargo/config.toml", ".cargo/config"] {
            fixture.write(path, "[build]\n");
            expect_found(path);
            fs::remove_file(fixture.root().join(path)).expect("remove the file");
        }
        // Git takes the file for unchanged, so the checkout is clean while
        // the root's configuration differs from the snapshot's.
        fixture.git(&["update-index", "--skip-worktree", ".cargo/config.toml"]);
        fixture.write(".cargo/config.toml", "[build]\n");
        expect_found(".cargo/config.toml");
        // A committed symbolic link takes Cargo to a file that the snapshot
        // does not hold, from the export and from the checkout root.
        let fixture = Fixture::new("cargo-config-link");
        let root = fs::canonicalize(fixture.root()).expect("resolve the fixture");
        fixture.write("artifacts/config.toml", "[build]\n");
        fs::remove_file(root.join(".cargo/config.toml")).expect("remove the file");
        let target = root.join("artifacts/config.toml");
        fixture.symlink(".cargo/config.toml", target.to_str().expect("UTF-8"));
        fixture.commit_all();
        let done = gate(&fixture, &[], Vec::new());
        assert_eq!(done.receipt.status, Status::ToolFailure);
        let source = fs::canonicalize(done.run.source()).expect("resolve the export");
        let found = |directory: &Path| {
            format!(
                "Cargo would read {} in the export, which is not in the snapshot",
                directory.join(".cargo/config.toml").display()
            )
        };
        assert_eq!(done.failures(), [found(&source), found(&root)]);
        assert!(!done.sites().contains(&Site::CargoMetadata));
    }

    #[test]
    fn a_stop_signal_kills_the_running_command_and_ends_the_run_without_a_receipt() {
        if let Some(root) = std::env::var_os(STOPPED) {
            // The gate that the test stops: its two commands, which run
            // side by side, write the numbers of their groups and wait.
            process::init();
            let root = PathBuf::from(root);
            let script = |group: &str| {
                let group = root.join("artifacts").join(group);
                format!(
                    "sleep 240 & echo $$ > {0}.new && mv {0}.new {0}; wait",
                    group.display()
                )
            };
            let phases = vec![phase("base", LONG, &["u1"], |run| {
                std::thread::scope(|scope| {
                    for script in [script("group"), script("other")] {
                        let run = &*run;
                        scope.spawn(move || shell(run, "u1", &script));
                    }
                });
                Ok(())
            })];
            let run = RunDir::create(&root).expect("create the run directory");
            let sink = Box::new(io::sink());
            gate_in(&root, run, &BTreeSet::new(), phases, test_host(), sink);
            panic!("the run ended by itself");
        }
        let (_, tests) = module_path!()
            .split_once("::")
            .expect("a module path below the crate");
        let name = format!(
            "{tests}::a_stop_signal_kills_the_running_command_and_ends_the_run_without_a_receipt"
        );
        for signal in [libc::SIGINT, libc::SIGTERM, libc::SIGHUP] {
            let fixture = Fixture::new("stopped");
            let log = fixture.root().join("artifacts/stderr");
            let mut command = Command::new(std::env::current_exe().expect("the test executable"));
            command
                .args([name.as_str(), "--exact", "--test-threads=1", "--nocapture"])
                .env(STOPPED, fixture.root())
                .stdin(Stdio::null())
                .stdout(Stdio::null())
                .stderr(fs::File::create(&log).expect("create the log"));
            // Under `nohup`, the gate would inherit SIGHUP ignored.
            process::tests::with_hangup(&mut command, libc::SIG_DFL);
            let mut child = command.spawn().expect("start the test executable");
            let said = || fs::read_to_string(&log).unwrap_or_default();
            // A bound for a gate that hangs before its command, not a
            // bound on how long a step takes.
            let deadline = Instant::now() + Duration::from_secs(120);
            let read = |group| fs::read_to_string(fixture.root().join("artifacts").join(group));
            let groups: Vec<i32> = loop {
                if let (Ok(group), Ok(other)) = (read("group"), read("other")) {
                    break Vec::from_iter(
                        [group, other].map(|g| g.trim().parse().expect("a group")),
                    );
                }
                let ended = child.try_wait().expect("look at the gate").is_some();
                assert!(!ended && Instant::now() < deadline, "{}", said());
                std::thread::sleep(Duration::from_millis(10));
            };
            // SAFETY: kill touches no memory of this process; the gate is a
            // child of it that has not been collected.
            unsafe { libc::kill(child.id() as libc::pid_t, signal) };
            let status = child.wait().expect("collect the gate");
            assert_eq!(status.signal(), Some(signal), "{}", said());
            // The leader of a group that the gate did not collect may take a
            // moment to be collected by another process.
            let gone = |group| process::tests::probe(group) == Some(libc::ESRCH);
            for group in groups {
                let failed = format!("the group {group} of a command was left behind");
                fixture::wait_until(|| gone(group), &failed);
            }
            let runs: Vec<PathBuf> = fs::read_dir(fixture.root().join(RUNS))
                .expect("the runs are listed")
                .map(|entry| entry.expect("a run").path())
                .collect();
            assert_eq!(runs.len(), 1, "{runs:?}");
            assert!(!runs[0].join("receipt.json").exists());
        }
    }

    #[test]
    fn a_panic_in_a_step_of_the_gate_is_an_internal_error_with_a_receipt() {
        let fixture = Fixture::new("step-panic");
        // The first command takes the snapshot of the start, the fifth exports
        // it and the ninth takes the snapshot of the end.
        for after in [0, 4, 8] {
            let run = RunDir::create(fixture.root()).expect("create the run directory");
            let progress = Box::new(Panicking { after });
            // The phase runs no command, so it writes no progress line.
            let phases = vec![phase("checks", LONG, &["u1"], |run| {
                run.conclude("u1", (Status::Verified, None));
                Ok(())
            })];
            let targets = BTreeSet::new();
            let done = gate_in(fixture.root(), run, &targets, phases, test_host(), progress);
            assert_eq!(done.code, ExitCode::FAILURE, "{after}");
            let receipt = done.written();
            assert_eq!(receipt.status, Status::ToolFailure, "{after}");
            assert!(!receipt.complete, "{after}");
            assert_eq!(
                done.failures(),
                ["the run panicked: asked to by the test"],
                "{after}"
            );
            // The run ends there, but a panic before the phases leaves them
            // to account for their units.
            assert_eq!(receipt.inputs.after, None, "{after}");
            let (ran, status) = match after {
                8 => (true, Status::Verified),
                _ => (false, Status::NotRun),
            };
            assert_eq!(receipt.phases["checks"].ran, ran, "{after}");
            assert_eq!(receipt.units["u1"].status, status, "{after}");
        }
    }

    #[test]
    fn a_tool_manifest_that_is_not_the_snapshot_s_fails_the_run() {
        let fixture = Fixture::new("manifest");
        // Git takes the file for unchanged, so the checkout is clean while
        // the run reads another manifest than the snapshot's.
        fixture.git(&[
            "update-index",
            "--skip-worktree",
            "verification/toolchain.json",
        ]);
        let path = fixture.root().join("verification/toolchain.json");
        let mut text = fs::read_to_string(&path).expect("read the manifest");
        text.push('\n');
        fs::write(&path, text).expect("write the manifest");
        let done = gate(&fixture, &[], Vec::new());
        assert_eq!(done.code, ExitCode::FAILURE);
        let receipt = done.written();
        assert_eq!(receipt.status, Status::ToolFailure);
        assert!(!receipt.complete);
        assert_eq!(receipt.inputs.clean_after, Some(true));
        assert_eq!(
            done.failures(),
            [
                "verification/toolchain.json of the snapshot is not the file that the run read at its start"
            ]
        );
    }

    #[test]
    fn a_lean_file_of_the_generated_namespace_in_the_checkout_rejects_the_run() {
        let fixture = Fixture::new("generated");
        fixture.write("verification/KrepiGen/Qual/X/Funs.lean", "module\n");
        // Other files there, and Lean files elsewhere, do not count.
        fixture.write("verification/KrepiGen/README", "Generated.\n");
        fixture.write("verification/Krepi/KrepiGen/Funs.lean", "module\n");
        fixture.commit_all();
        let phases = vec![phase("checks", LONG, &["u1"], |run| {
            run.conclude("u1", (Status::Verified, None));
            Ok(())
        })];
        let done = gate(&fixture, &[], phases);
        assert_eq!(done.code, ExitCode::FAILURE);
        let receipt = done.written();
        assert_eq!(receipt.status, Status::Rejected);
        assert!(!receipt.complete);
        assert_eq!(
            done.failures(),
            [
                "the gate inputs hold Lean files of the generated namespace: \
                 verification/KrepiGen/Qual/X/Funs.lean"
            ]
        );
        assert!(!receipt.phases["checks"].ran);
        assert_eq!(receipt.units["u1"].status, Status::NotRun);
    }

    #[test]
    fn a_cargo_configuration_below_the_root_in_the_gate_inputs_rejects_the_run() {
        let fixture = Fixture::new("nested-cargo");
        // Cargo reads both when it runs in the qualification crate.
        let flags = "[build]\nrustflags = [\"--cfg\", \"board=\\\"pi5\\\"\"]\n";
        fixture.write("verification/qualification/.cargo/config.toml", flags);
        fixture.write("verification/.cargo/config", flags);
        // A file of another name is not one.
        fixture.write("kernel/.cargo/config.toml.orig", flags);
        fixture.commit_all();
        let phases = vec![phase("checks", LONG, &["u1"], |run| {
            run.conclude("u1", (Status::Verified, None));
            Ok(())
        })];
        let done = gate(&fixture, &[], phases);
        assert_eq!(done.code, ExitCode::FAILURE);
        assert_eq!(done.receipt.status, Status::Rejected);
        assert_eq!(
            done.failures(),
            ["the gate inputs hold Cargo configuration below the root: \
                 verification/.cargo/config, verification/qualification/.cargo/config.toml"]
        );
        assert_eq!(done.receipt.units["u1"].status, Status::NotRun);
    }

    #[test]
    fn a_python_file_in_the_gate_inputs_rejects_the_run() {
        let fixture = Fixture::new("python");
        fixture.write("xtask/helper.py", "print()\n");
        // Outside the gate inputs, a Python file does not count.
        fixture.write("docs/notes.py", "print()\n");
        fixture.commit_all();
        let phases = vec![phase("checks", LONG, &["u1"], |run| {
            run.conclude("u1", (Status::Verified, None));
            Ok(())
        })];
        let done = gate(&fixture, &[], phases);
        assert_eq!(done.code, ExitCode::FAILURE);
        let receipt = done.written();
        assert_eq!(receipt.status, Status::Rejected);
        assert!(!receipt.complete);
        assert_eq!(
            done.failures(),
            ["the gate inputs hold Python sources: xtask/helper.py"]
        );
        // No phase runs after a failure before them.
        assert!(!receipt.phases["checks"].ran);
        assert_eq!(receipt.units["u1"].status, Status::NotRun);
        assert_eq!(
            receipt.units["u1"].reason.as_deref(),
            Some("a failure before the phases stopped the run")
        );
    }

    #[test]
    fn the_limit_is_the_smallest_of_the_cap_the_phase_and_the_gate() {
        let s = Duration::from_secs;
        let at = |duration, by| Limit { duration, by };
        assert_eq!(limit(Some(s(5)), s(10), s(20)), at(s(5), LimitBy::Cap));
        assert_eq!(limit(Some(s(50)), s(10), s(20)), at(s(10), LimitBy::Phase));
        assert_eq!(limit(Some(s(50)), s(30), s(20)), at(s(20), LimitBy::Gate));
        assert_eq!(limit(None, s(10), s(20)), at(s(10), LimitBy::Phase));
        assert_eq!(limit(None, s(20), s(20)), at(s(20), LimitBy::Gate));
        assert_eq!(limit(Some(s(10)), s(10), s(10)), at(s(10), LimitBy::Cap));
        assert_eq!(limit(Some(s(5)), s(0), s(20)), at(s(0), LimitBy::Phase));
    }

    #[test]
    fn a_command_after_the_budget_is_used_up_does_not_run() {
        let fixture = Fixture::new("used-up");
        let phases = vec![phase("late", Duration::ZERO, &["u1"], |run| {
            let verdict = shell(run, "u1", "exit 0");
            assert_eq!(verdict.class, Class::NotRun);
            run.conclude("u1", (Status::Verified, None));
            Ok(())
        })];
        let done = gate(&fixture, &[], phases);
        assert_eq!(done.receipt.status, Status::Budget);
        assert!(!done.receipt.complete);
        let late = done
            .receipt
            .commands
            .iter()
            .find(|command| command.site == Site::BaseBuild)
            .expect("the command is recorded");
        assert_eq!(late.class, Class::NotRun);
        assert_eq!(late.reason.as_deref(), Some("the phase budget was used up"));
        assert_eq!(late.argv, ["/bin/sh", "-c", "exit 0"]);
        assert_eq!((late.stdout.clone(), late.stderr.clone()), (None, None));
        assert_eq!(late.phase.as_deref(), Some("late"));
        assert_eq!(late.unit.as_deref(), Some("u1"));
        assert_eq!(done.receipt.units["u1"].status, Status::Budget);
    }

    #[test]
    fn a_command_whose_limit_the_receipt_writes_as_zero_does_not_run() {
        let fixture = Fixture::new("written-as-zero");
        let phases = vec![phase("short", LONG, &["u1"], |run| {
            // Above zero, but below half a millisecond: 0 in the receipt.
            let duration = Duration::from_micros(400);
            let limit = Limit {
                duration,
                by: LimitBy::Phase,
            };
            run.overrides = Some((Site::BaseBuild, limit, "/bin/sh".to_string()));
            assert_eq!(shell(run, "u1", "exit 0").class, Class::NotRun);
            run.conclude("u1", (Status::Verified, None));
            Ok(())
        })];
        let done = gate(&fixture, &[], phases);
        let short: Vec<&receipt::Command> = (done.receipt.commands.iter())
            .filter(|command| command.site == Site::BaseBuild)
            .collect();
        let [short] = short.as_slice() else {
            panic!("{short:?}");
        };
        assert_eq!(short.class, Class::NotRun);
        assert_eq!(
            short.reason.as_deref(),
            Some("the phase budget was used up")
        );
        assert_eq!((short.limit_seconds, short.limit), (0.0, LimitBy::Phase));
        assert_eq!((short.exit_code, short.seconds), (None, 0.0));
        assert_eq!((short.stdout.clone(), short.stderr.clone()), (None, None));
        assert_eq!(done.receipt.units["u1"].status, Status::Budget);
        assert_eq!(done.receipt.status, Status::Budget);
    }

    #[test]
    fn a_command_skipped_for_a_missing_input_does_not_force_its_unit() {
        let fixture = Fixture::new("skipped");
        // The script `script` at the qualification build, run or skipped.
        let build = |run: &mut Gate, unit: &str, script: &str, skip: bool| {
            let (source, args) = (run.source(), ["-c".to_string(), script.to_string()]);
            let request = Request {
                site: Site::QualificationBuild,
                tool: Tool::LakeBuild,
                program: "/bin/sh",
                args: &args,
                cwd: &source,
                stdin: None,
            };
            if skip {
                run.skip(unit, &request, "the command before it wrote nothing");
            } else {
                let verdict = run.run(unit, &request, |_| Ok(())).1;
                assert_eq!(verdict.class, Class::ProofFailure);
            }
        };
        let skip = |run: &mut Gate, unit: &str| build(run, unit, "exit 0", true);
        let phases = vec![
            phase("first", LONG, &["u1"], |run| {
                build(run, "u1", "exit 1", false);
                skip(run, "u1");
                run.conclude(
                    "u1",
                    (Status::Rejected, Some("nothing to build".to_string())),
                );
                Ok(())
            }),
            // Without a limit left, a command that would be skipped does
            // not start for the budget.
            phase("late", Duration::ZERO, &["u2"], |run| {
                skip(run, "u2");
                run.conclude("u2", (Status::Verified, None));
                Ok(())
            }),
        ];
        let done = gate(&fixture, &[], phases);
        let units = &done.receipt.units;
        assert_eq!(units["u1"].status, Status::Rejected);
        assert_eq!(units["u1"].reason.as_deref(), Some("nothing to build"));
        assert_eq!(units["u2"].status, Status::Budget);
        let skipped: Vec<&receipt::Command> = (done.receipt.commands.iter())
            .filter(|command| command.class == Class::NotRun)
            .collect();
        let [first, late] = skipped.as_slice() else {
            panic!("{skipped:?}");
        };
        assert_eq!(
            first.reason.as_deref(),
            Some("not started: the command before it wrote nothing")
        );
        assert_eq!(first.argv, ["/bin/sh", "-c", "exit 0"]);
        assert_eq!(
            (first.phase.as_deref(), first.unit.as_deref()),
            (Some("first"), Some("u1"))
        );
        assert!(first.limit_seconds > 0.0, "{}", first.limit_seconds);
        assert_eq!(first.limit, LimitBy::Phase);
        assert_eq!((first.exit_code, first.seconds), (None, 0.0));
        assert_eq!((first.stdout.clone(), first.stderr.clone()), (None, None));
        assert_eq!(late.reason.as_deref(), Some("the phase budget was used up"));
        assert_eq!(late.limit_seconds, 0.0);
        assert_eq!(done.receipt.status, Status::Budget);
        assert!(!done.receipt.complete);
    }

    #[test]
    fn a_unit_with_a_killed_command_cannot_conclude_verified() {
        let fixture = Fixture::new("killed");
        let phases = vec![phase("base", LONG, &["base", "other"], |run| {
            shell(run, "base", "kill -9 $$");
            shell(run, "other", "exit 0");
            run.conclude("base", (Status::Verified, None));
            run.conclude(
                "other",
                (Status::Rejected, Some("a proof fails".to_string())),
            );
            Ok(())
        })];
        let done = gate(&fixture, &[], phases);
        assert_eq!(done.receipt.status, Status::ToolFailure);
        assert_eq!(
            done.receipt.units["base"],
            receipt::Unit {
                phase: "base".to_string(),
                status: Status::ToolFailure,
                reason: Some("base-build was ended by signal 9".to_string()),
            }
        );
        // A unit whose commands passed takes the conclusion of the phase.
        assert_eq!(
            done.receipt.units["other"].reason.as_deref(),
            Some("a proof fails")
        );
        assert_eq!(done.receipt.units["other"].status, Status::Rejected);
        assert_eq!(done.receipt.failures, []);
    }

    #[test]
    fn a_failure_or_a_panic_in_a_phase_is_an_internal_error() {
        let fixture = Fixture::new("internal");
        let phases = vec![
            phase("first", LONG, &["a", "b"], |run| {
                run.conclude("a", (Status::Verified, None));
                Err("broken".to_string())
            }),
            phase("second", LONG, &["c"], |run| {
                run.conclude("c", (Status::Verified, None));
                Ok(())
            }),
        ];
        let done = gate(&fixture, &[], phases);
        assert_eq!(done.code, ExitCode::FAILURE);
        assert_eq!(done.written().status, Status::ToolFailure);
        assert!(!done.receipt.complete);
        assert_eq!(done.failures(), ["the phase first stopped: broken"]);
        let units = &done.receipt.units;
        assert_eq!(units["a"].status, Status::Verified);
        for unit in ["b", "c"] {
            assert_eq!(units[unit].status, Status::NotRun, "{unit}");
            assert_eq!(
                units[unit].reason.as_deref(),
                Some("the phase first stopped: broken"),
                "{unit}"
            );
        }
        assert!(done.receipt.phases["first"].ran);
        assert!(!done.receipt.phases["second"].ran);
        let phases = vec![phase("first", LONG, &["a"], |_| panic!("boom"))];
        let done = gate(&fixture, &[], phases);
        assert_eq!(done.receipt.status, Status::ToolFailure);
        assert!(!done.receipt.complete);
        assert_eq!(done.failures(), ["the phase first stopped: panicked: boom"]);
        assert_eq!(done.receipt.units["a"].status, Status::NotRun);
    }

    #[test]
    fn a_receipt_that_cannot_be_written_goes_to_standard_error() {
        let fixture = Fixture::new("unwritable");
        let run = RunDir::create(fixture.root()).expect("create the run directory");
        // A directory stands where the receipt goes.
        fs::create_dir(run.receipt()).expect("create a directory");
        let done = gate_in(
            fixture.root(),
            run,
            &BTreeSet::new(),
            Vec::new(),
            test_host(),
            Box::new(io::sink()),
        );
        assert_eq!(done.code, ExitCode::from(120));
        assert!(done.stderr.contains("cannot write "), "{}", done.stderr);
        let text = receipt::render(&done.receipt);
        assert!(done.stderr.ends_with(&text), "{}", done.stderr);
        assert_eq!(done.stdout, "");
        // So is the receipt of a run without a run directory.
        let mut stderr = Vec::new();
        assert_eq!(
            finish(&done.receipt, None, &mut io::sink(), &mut stderr),
            ExitCode::from(120)
        );
        assert!(stderr.ends_with(text.as_bytes()));
    }

    #[test]
    fn an_empty_pipeline_on_a_clean_snapshot_is_verified() {
        let fixture = Fixture::new("verified");
        let done = gate(&fixture, &[], Vec::new());
        assert_eq!(done.code, ExitCode::SUCCESS, "{}", done.stderr);
        let receipt = done.written();
        assert_eq!(receipt, done.receipt);
        assert_eq!(receipt.status, Status::Verified);
        assert!(receipt.complete);
        assert_eq!(
            done.stdout,
            format!(
                "formal run: VERIFIED, complete; receipt {}\n",
                done.run.receipt().display()
            )
        );
        assert_eq!(receipt.trigger.mode, Mode::Manual);
        assert_eq!(receipt.trigger.event, None);
        assert_eq!(receipt.run, done.run.id);
        assert_eq!(receipt.directory, format!("{RUNS}/{}", done.run.id));
        assert_eq!(receipt.host.as_deref(), test_host());
        // Only a run on the CI host records an image.
        assert_eq!(
            receipt.image.is_some(),
            test_host() == Some("linux-aarch64")
        );
        let resources = &receipt.resources;
        let start = resources
            .disk_available_at_start
            .expect("the disk at the start");
        let least = resources.disk_least_available.expect("the least disk");
        assert!(0 < least && least <= start, "{resources:?}");
        assert!(resources.largest_process_max_rss.is_some_and(|rss| rss > 0));
        if cfg!(target_os = "macos") {
            assert_eq!(resources.cgroup_memory_peak, None);
        }
        let commit = fixture.git(&["rev-parse", "HEAD"]);
        assert_eq!(receipt.commit.as_deref(), Some(commit.trim()));
        let tree = fixture.git(&["rev-parse", "HEAD^{tree}"]);
        assert_eq!(receipt.tree.as_deref(), Some(tree.trim()));
        assert_eq!(receipt.inputs.after, receipt.inputs.before);
        assert_eq!(receipt.inputs.clean_after, Some(true));
        let before = receipt
            .inputs
            .before
            .clone()
            .expect("the snapshot is taken");
        assert_eq!(before.len(), 8);
        assert_eq!(before["verification/qualification"], None);
        assert_eq!(
            (
                receipt.budgets.gate_seconds,
                receipt.budgets.receipt_margin_seconds
            ),
            (7_200, 300)
        );
        assert!(receipt.phases.is_empty() && receipt.units.is_empty());
        assert_eq!(receipt.failures, []);
        let sites = done.sites();
        assert!(sites.contains(&Site::CargoMetadata));
        assert!(
            sites
                .iter()
                .all(|site| matches!(site, Site::Git | Site::CargoMetadata))
        );
        for (index, command) in receipt.commands.iter().enumerate() {
            assert_eq!(command.sequence as usize, index + 1);
            assert_eq!(command.class, Class::Passed, "{command:?}");
            assert_eq!(command.exit_code, Some(0));
            assert_eq!(command.limit, LimitBy::Gate);
            // The closing steps have the margin beyond the gate's budget.
            let longest = (GATE_BUDGET + RECEIPT_MARGIN).as_secs_f64();
            assert!(
                command.limit_seconds > 0.0 && command.limit_seconds <= longest,
                "{}",
                command.limit_seconds
            );
            for log in [&command.stdout, &command.stderr] {
                let log = log.as_ref().expect("the output is kept");
                let bytes = fs::read(done.run.path.join(&log.path)).expect("the log is kept");
                assert_eq!(toolchain::sha256(&bytes), log.sha256);
                assert_eq!(bytes.len() as u64, log.bytes);
            }
        }
        let archive = receipt
            .commands
            .iter()
            .find(|command| command.argv.get(3).is_some_and(|arg| arg == "archive"))
            .expect("git archive ran");
        assert_eq!(archive.cwd, ".");
        // The export holds the gate inputs of the snapshot.
        assert!(
            done.run
                .source()
                .join("verification/targets.json")
                .is_file()
        );
        assert!(!done.run.source().join("README.md").exists());
    }

    /// The refusal of the disk guard of a run that had `free` bytes and
    /// needed 1.5 times `peak`.
    fn refusal(free: u64, peak: u64) -> String {
        format!(
            "the file system of the run directory had {free} bytes available at the start, less than 1.5 times the disk peak of the parts of the run, {peak} bytes"
        )
    }

    /// An entry of a shard plan for `part`, with `peak`.
    fn shard_entry(part: &str, peak: u64) -> serde_json::Value {
        serde_json::json!({"part": part, "disk_peak": peak, "seconds": 1.0,
            "cgroup_memory_peak": 1, "run_id": "1", "commit": "c"})
    }

    #[test]
    fn free_space_below_one_and_a_half_times_the_disk_peak_runs_no_phase_and_is_not_run() {
        let fixture = Fixture::new("disk-guard");
        let plan =
            |parts: serde_json::Value| serde_json::json!({"schema": 1, "parts": parts}).to_string();
        let entry = shard_entry("qualification", 1_000);
        fixture.write(
            "verification/shards.json",
            &plan(serde_json::json!([entry])),
        );
        fixture.commit_all();
        let phases = || {
            let concludes = |name: &str, unit: &'static str| {
                phase(name, LONG, &[unit], move |run| {
                    run.conclude(unit, (Status::Verified, None));
                    Ok(())
                })
            };
            vec![concludes("first", "u1"), concludes("second", "u2")]
        };
        let done = gate_as(&fixture, &[], phases(), true, |_| Some(1_499));
        assert_eq!(done.code, ExitCode::FAILURE);
        let receipt = done.written();
        assert_eq!(receipt, done.receipt);
        assert_eq!(receipt.status, Status::NotRun);
        assert!(!receipt.complete);
        assert_eq!(done.failures(), [refusal(1_499, 1_000)]);
        assert_eq!(receipt.failures[0].status, Status::NotRun);
        assert!(
            done.stderr.starts_with("NOT_RUN: the file system"),
            "{}",
            done.stderr
        );
        // No phase runs, and every unit is NOT_RUN.
        assert_eq!(Vec::from_iter(receipt.phases.keys()), ["first", "second"]);
        assert!(receipt.phases.values().all(|phase| !phase.ran));
        assert_eq!(Vec::from_iter(receipt.units.keys()), ["u1", "u2"]);
        assert!(receipt.units.values().all(|u| u.status == Status::NotRun));
        let sites = done.sites();
        assert!(
            sites
                .iter()
                .all(|s| matches!(s, Site::Git | Site::CargoMetadata))
        );
        // With 1.5 times the peak free, the run starts.
        let done = gate_as(&fixture, &[], phases(), true, |_| Some(1_500));
        assert_eq!(
            done.written().status,
            Status::Verified,
            "{:?}",
            done.failures()
        );
        assert!(done.receipt.complete);
        // A part without an entry counts 8 GiB, which needs 12 GiB free.
        fixture.write("verification/shards.json", &plan(serde_json::json!([])));
        fixture.commit_all();
        let done = gate_as(&fixture, &[], phases(), true, |_| Some((12 << 30) - 1));
        assert_eq!(done.written().status, Status::NotRun);
        assert_eq!(done.failures(), [refusal((12 << 30) - 1, 8 << 30)]);
        let done = gate_as(&fixture, &[], phases(), true, |_| Some(12 << 30));
        assert_eq!(
            done.written().status,
            Status::Verified,
            "{:?}",
            done.failures()
        );
    }

    #[test]
    fn the_disk_guard_counts_the_qualification_and_each_target_that_the_run_selects() {
        let fixture = with_targets("disk-guard-targets", &two_targets(1_800, 1));
        let parts = [
            shard_entry("qualification", 1_000),
            shard_entry("target/t/1", 2_000),
            shard_entry("target/p/1", 1 << 40),
        ];
        let plan = serde_json::json!({"schema": 1, "parts": parts}).to_string();
        fixture.write("verification/shards.json", &plan);
        fixture.commit_all();
        // A whole run selects the formal target, not the planned one.
        let whole = target_run(&fixture, &[]);
        let done = gate_as(&fixture, &[], whole, true, |_| Some(4_499));
        assert_eq!(done.written().status, Status::NotRun);
        assert_eq!(done.failures(), [refusal(4_499, 3_000)]);
        assert!(done.receipt.phases.values().all(|phase| !phase.ran));
        let units = done.receipt.units.iter();
        assert!(units.clone().any(|(unit, _)| unit == "target/t"));
        assert!(units.clone().all(|(_, unit)| unit.status == Status::NotRun));
        // A run of the planned target counts it.
        let named = target_run(&fixture, &["p"]);
        let done = gate_as(&fixture, &["p"], named, true, |_| Some(4_499));
        assert_eq!(done.written().status, Status::NotRun);
        assert_eq!(done.failures(), [refusal(4_499, 1_000 + (1 << 40))]);
        assert!(done.receipt.phases.values().all(|phase| !phase.ran));
    }

    #[test]
    fn the_disk_guard_of_a_part_counts_that_part_alone() {
        let fixture = with_targets("disk-guard-parts", &two_targets(1_800, 1));
        lane_a(&fixture, &["T"], &[]);
        let parts = [
            shard_entry("qualification", 1_000),
            shard_entry("lane/a", 3_000),
            shard_entry("target/t/1", 2_000),
            shard_entry("target/p/1", 1 << 40),
        ];
        let plan = serde_json::json!({"schema": 1, "parts": parts}).to_string();
        fixture.write("verification/shards.json", &plan);
        fixture.commit_all();
        // The qualification job counts the qualification, and no target.
        let done = gate_shard(&fixture, "qualification", verified(), |_| Some(1_499));
        assert_eq!(done.written().status, Status::NotRun);
        assert_eq!(done.failures(), [refusal(1_499, 1_000)]);
        assert!(done.receipt.phases.values().all(|phase| !phase.ran));
        let done = gate_shard(&fixture, "qualification", verified(), |_| Some(1_500));
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        // A lane counts its lane, and neither the qualification nor a target.
        let done = gate_shard(&fixture, "lane/a", lane_job(&fixture), |_| Some(4_499));
        assert_eq!(done.failures(), [refusal(4_499, 3_000)]);
        let done = gate_shard(&fixture, "lane/a", lane_job(&fixture), |_| Some(4_500));
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        // The shard of a target counts its target, and not the qualification.
        let phases = shard_phases(fixture.root(), "target/t/1");
        let done = gate_shard(&fixture, "target/t/1", phases, |_| Some(2_999));
        assert_eq!(done.written().status, Status::NotRun);
        assert_eq!(done.failures(), [refusal(2_999, 2_000)]);
        assert!(done.receipt.phases.values().all(|phase| !phase.ran));
    }

    #[test]
    fn the_receipt_keeps_the_least_reading_of_the_free_space_during_the_run() {
        // The reading of the start is the first; the thread reads less.
        fn falling(_: &Path) -> Option<u64> {
            static READS: AtomicU64 = AtomicU64::new(0);
            match READS.fetch_add(1, Ordering::SeqCst) {
                0 => Some(1 << 50),
                _ => Some(1 << 49),
            }
        }
        fn panicking(_: &Path) -> Option<u64> {
            static READS: AtomicU64 = AtomicU64::new(0);
            match READS.fetch_add(1, Ordering::SeqCst) {
                0 => Some(1 << 50),
                _ => panic!("a reading of the free space that panics"),
            }
        }
        let fixture = Fixture::new("sampled");
        let done = gate_as(&fixture, &[], verified(), true, falling);
        assert_eq!(
            done.written().status,
            Status::Verified,
            "{:?}",
            done.failures()
        );
        let resources = &done.receipt.resources;
        assert_eq!(resources.disk_available_at_start, Some(1 << 50));
        assert_eq!(resources.disk_least_available, Some(1 << 49));
        // A thread whose reading panics fails the run, which keeps the
        // reading of the start.
        let done = gate_as(&fixture, &[], verified(), true, panicking);
        assert_eq!(done.written().status, Status::ToolFailure);
        assert_eq!(done.failures(), ["the reading of the free space panicked"]);
        assert_eq!(done.receipt.resources.disk_least_available, Some(1 << 50));
        assert_eq!(fixture::status(&done, "base"), (Status::Verified, None));
    }

    #[test]
    fn an_unreadable_free_space_or_shard_plan_is_a_tool_failure_before_the_phases() {
        let fixture = Fixture::new("unreadable");
        let done = gate_as(&fixture, &[], verified(), true, |_| None);
        assert_eq!(done.written().status, Status::ToolFailure);
        assert_eq!(
            done.failures(),
            ["the bytes available on the file system of the run directory cannot be read"]
        );
        assert!(!done.receipt.phases["base"].ran);
        assert_eq!(done.receipt.resources.disk_least_available, None);
        fixture.write("verification/shards.json", "{");
        fixture.commit_all();
        let done = gate_as(&fixture, &[], verified(), true, plenty);
        assert_eq!(done.written().status, Status::ToolFailure);
        assert_eq!(done.failures().len(), 1);
        let start = "cannot read verification/shards.json: not a shard plan: ";
        assert!(
            done.has_failure(Status::ToolFailure, start),
            "{:?}",
            done.failures()
        );
        assert!(!done.receipt.phases["base"].ran);
    }

    #[test]
    fn the_work_directory_is_removed_at_the_end_unless_the_run_keeps_it() {
        let fixture = Fixture::new("removed");
        let backend = fixture.root().join("artifacts/formal/tools/backend");
        let at = |error: io::Error| error.to_string();
        for keep in [false, true] {
            // The phase writes a file and links to the backend in `work/`.
            let link = backend.clone();
            let phases = vec![phase("base", LONG, &["base"], move |run| {
                fs::write(run.work().join("made"), "made").map_err(at)?;
                std::os::unix::fs::symlink(&link, run.work().join("backend")).map_err(at)?;
                run.conclude("base", (Status::Verified, None));
                Ok(())
            })];
            let done = gate_as(&fixture, &[], phases, keep, plenty);
            assert_eq!(
                done.written().status,
                Status::Verified,
                "{:?}",
                done.failures()
            );
            assert!(done.receipt.complete);
            assert!(done.run.path.join("logs").is_dir());
            assert_eq!(done.run.path.join("work/made").is_file(), keep, "{keep}");
            assert_eq!(done.run.path.join("work").exists(), keep, "{keep}");
            // The link was removed, not followed.
            assert!(backend.join(".lake/packages/README").is_file());
        }
        // A work directory that cannot be removed fails the run.
        let phases = vec![phase("base", LONG, &["base"], |run| {
            let locked = run.work().join("locked");
            fs::create_dir(&locked).map_err(at)?;
            fs::write(locked.join("file"), "file").map_err(at)?;
            fs::set_permissions(&locked, fs::Permissions::from_mode(0o500)).map_err(at)?;
            run.conclude("base", (Status::Verified, None));
            Ok(())
        })];
        let done = gate_as(&fixture, &[], phases, false, plenty);
        let work = done.run.path.join("work");
        fs::set_permissions(work.join("locked"), fs::Permissions::from_mode(0o755))
            .expect("let the fixture be removed");
        let receipt = done.written();
        assert_eq!(receipt.status, Status::ToolFailure);
        assert!(!receipt.complete);
        assert_eq!(done.failures().len(), 1, "{:?}", done.failures());
        let start = format!("cannot remove {}: ", work.display());
        assert!(
            done.has_failure(Status::ToolFailure, &start),
            "{:?}",
            done.failures()
        );
        // So does a removal that ends after the deadline of the closing
        // steps, which the second snapshot, with no time left, misses too.
        let phases = vec![phase("base", LONG, &["base"], |run| {
            let now = Instant::now();
            run.deadline = now
                .checked_sub(RECEIPT_MARGIN)
                .expect("a time before the margin");
            run.conclude("base", (Status::Verified, None));
            Ok(())
        })];
        let done = gate_as(&fixture, &[], phases, false, plenty);
        assert_eq!(done.written().status, Status::ToolFailure);
        let late =
            "the removal of the work directory ended after the deadline of the closing steps";
        let failures = done.failures();
        assert_eq!(failures.len(), 2, "{failures:?}");
        let snapshot = "cannot take the snapshot of the gate inputs at the end: ";
        assert!(failures[0].starts_with(snapshot), "{failures:?}");
        assert_eq!(failures[1], late);
        assert!(!done.run.path.join("work").exists());
    }

    #[test]
    fn a_tool_that_writes_the_installation_in_the_phases_of_the_targets_fails_the_run() {
        let fixture = with_targets("backend-run", &two_targets(1_800, 1));
        // The type check of the generated definitions of the target writes
        // through the link of its stage.
        let write = "echo written >> ../artifacts/formal/lake/aeneas/.lake/packages/README";
        fixture::lake_script(&fixture, "KrepiGen.T.Funs", write);
        let done = gate(&fixture, &[], target_run(&fixture, &[]));
        assert_eq!(done.written().status, Status::ToolFailure);
        assert!(!done.receipt.complete);
        let packages = fixture
            .root()
            .join("artifacts/formal/tools/backend/.lake/packages");
        let changed = [fs::canonicalize(packages)
            .expect("the packages")
            .join("README")];
        assert_eq!(
            done.failures(),
            [format!(
                "the tool installation changed during the run; changed paths (1): {changed:?}"
            )]
        );
        // The phases of the targets have no listing of their own.
        assert_eq!(fixture::status(&done, "target/t"), (Status::Verified, None));
        // A listing that cannot be taken after the last phase fails the run.
        let fixture = Fixture::new("backend-gone");
        let backend = fixture.root().join("artifacts/formal/tools/backend");
        let phases = vec![phase("base", LONG, &["base"], move |run| {
            fs::remove_dir_all(&backend).map_err(|error| error.to_string())?;
            run.conclude("base", (Status::Verified, None));
            Ok(())
        })];
        let done = gate(&fixture, &[], phases);
        assert_eq!(done.written().status, Status::ToolFailure);
        assert_eq!(done.failures().len(), 1, "{:?}", done.failures());
        let start = "cannot list the installation after the last phase: ";
        assert!(
            done.has_failure(Status::ToolFailure, start),
            "{:?}",
            done.failures()
        );
    }

    #[test]
    fn a_dirty_checkout_stops_the_run_with_a_receipt() {
        let fixture = Fixture::new("dirty");
        fixture.write("xtask/README", "Changed.\n");
        fixture.write("kernel/new.rs", "\n");
        let done = gate(&fixture, &[], Vec::new());
        assert_eq!(done.code, ExitCode::FAILURE);
        let receipt = done.written();
        assert_eq!(receipt.status, Status::ToolFailure);
        assert!(!receipt.complete);
        // Nothing changed during the run, which is not stale.
        assert_eq!(
            done.failures(),
            [
                "the gate inputs are not clean at the start of the run:  M xtask/README, ?? kernel/new.rs"
            ]
        );
        assert!(receipt.inputs.before.is_some());
        assert_eq!(receipt.inputs.clean_after, None);
        assert!(
            !receipt
                .commands
                .iter()
                .any(|command| command.argv.iter().any(|arg| arg == "archive"))
        );
    }

    #[test]
    fn an_unsupported_host_is_an_internal_error() {
        let fixture = Fixture::new("host");
        let run = RunDir::create(fixture.root()).expect("create the run directory");
        let sink = Box::new(io::sink());
        let done = gate_in(
            fixture.root(),
            run,
            &BTreeSet::new(),
            Vec::new(),
            None,
            sink,
        );
        assert_eq!(done.code, ExitCode::FAILURE);
        assert_eq!(done.receipt.status, Status::ToolFailure);
        assert!(!done.receipt.complete);
        assert_eq!(done.receipt.host, None);
        assert_eq!(done.receipt.commit, None);
        assert_eq!(done.receipt.commands, []);
        assert!(
            done.has_failure(Status::ToolFailure, "the host is "),
            "{:?}",
            done.failures()
        );
    }

    /// Runs the gate on `fixture` on the CI host as the user `uid`, with
    /// the variables `vars`, and a phase whose unit `u1` is verified.
    fn on_the_ci_host(fixture: &Fixture, uid: u32, vars: &[(&str, &str)]) -> Done {
        let var = |name: &str| {
            let found = vars.iter().find(|(key, _)| *key == name);
            found.map(|(_, value)| value.to_string())
        };
        let context = Context {
            root: fixture.root(),
            layout: &Layout::PRODUCTION,
            host: Some("linux-aarch64"),
            uid,
            var: &var,
            budget: None,
            keep: true,
            free: plenty,
            shard: None,
            comparator: false,
        };
        let run = RunDir::create(fixture.root()).expect("create the run directory");
        let phases = vec![phase("checks", LONG, &["u1"], |run| {
            run.conclude("u1", (Status::Verified, None));
            Ok(())
        })];
        gate_with(
            &context,
            run,
            &BTreeSet::new(),
            phases,
            Box::new(io::sink()),
        )
    }

    /// Asserts that `done` stopped before its phases with the one failure
    /// `failure`, without running any tool of the installation.
    fn stopped_by_the_image(done: &Done, failure: &str) {
        assert_eq!(done.code, ExitCode::FAILURE);
        let receipt = done.written();
        assert_eq!(receipt, done.receipt);
        assert_eq!(receipt.status, Status::ToolFailure);
        assert!(!receipt.complete);
        assert_eq!(done.failures(), [failure]);
        assert_eq!(receipt.units["u1"].status, Status::NotRun);
        assert!(!receipt.phases["checks"].ran);
        assert!(!done.sites().contains(&Site::CargoMetadata));
    }

    #[test]
    fn an_image_whose_version_manifest_differs_from_the_tool_manifest_fails_the_run() {
        let fixture = Fixture::new("versions");
        let commit = "eb6cafb7290e8bd5f2937522d8d804f58f02bafc";
        let other = "0000000000000000000000000000000000000001";
        let versions = fixture::VERSIONS.replace(commit, other);
        assert_ne!(versions, fixture::VERSIONS);
        fixture.write("artifacts/formal/tools/versions.json", &versions);
        let done = on_the_ci_host(&fixture, other_uid(), &[]);
        let failure = format!("image: /lean/commit is \"{other}\", not \"{commit}\"");
        stopped_by_the_image(&done, &failure);
        let image = done.receipt.image.as_ref().expect("the image is recorded");
        assert_eq!(image.versions.as_deref(), Some(versions.as_str()));
        let digest = toolchain::sha256(versions.as_bytes());
        assert_eq!(image.versions_sha256, Some(digest));
        // The published version manifest passes.
        fixture.write("artifacts/formal/tools/versions.json", fixture::VERSIONS);
        let done = on_the_ci_host(&fixture, other_uid(), &[]);
        assert_eq!(
            done.receipt.status,
            Status::Verified,
            "{:?}",
            done.failures()
        );
        let image = done.receipt.image.as_ref().expect("the image is recorded");
        let digest = "8b5e39cb407d4d8f5cf7fd29d0485e43a439276ea6e3808a60e24f4c196a24e6";
        assert_eq!(image.versions_sha256.as_deref(), Some(digest));
    }

    #[test]
    fn an_image_without_a_version_manifest_fails_the_run() {
        let fixture = Fixture::new("no-versions");
        fs::remove_file(fixture.root().join("artifacts/formal/tools/versions.json"))
            .expect("remove the version manifest");
        let done = on_the_ci_host(&fixture, other_uid(), &[]);
        assert_eq!(done.failures().len(), 1, "{:?}", done.failures());
        let failure = done.failures()[0];
        assert!(
            failure.starts_with("image: cannot read versions.json: "),
            "{failure}"
        );
        stopped_by_the_image(&done, failure);
        let image = done.receipt.image.as_ref().expect("the image is recorded");
        assert_eq!((&image.versions, &image.versions_sha256), (&None, &None));
    }

    #[test]
    fn a_run_as_root_or_as_the_owner_of_the_installation_fails_the_run() {
        let fixture = Fixture::new("owner");
        let prefix = fixture.root().join("artifacts/formal/tools");
        for uid in [0, process::effective_uid()] {
            let done = on_the_ci_host(&fixture, uid, &[]);
            let failure = format!("image: user {uid} can write {}", prefix.display());
            stopped_by_the_image(&done, &failure);
            let image = done.receipt.image.as_ref().expect("the image is recorded");
            assert_eq!((image.uid, image.writable), (uid, Some(true)));
        }
        // Another user passes, unless the group or others may write the
        // prefix, whatever groups the user is in.
        let done = on_the_ci_host(&fixture, other_uid(), &[]);
        assert_eq!(
            done.receipt.status,
            Status::Verified,
            "{:?}",
            done.failures()
        );
        let image = done.receipt.image.as_ref().expect("the image is recorded");
        assert_eq!((image.uid, image.writable), (other_uid(), Some(false)));
        for mode in [0o775, 0o757] {
            fixture.chmod("artifacts/formal/tools", mode);
            let done = on_the_ci_host(&fixture, other_uid(), &[]);
            let failure = format!("image: user {} can write {}", other_uid(), prefix.display());
            stopped_by_the_image(&done, &failure);
        }
    }

    #[test]
    fn a_run_that_stops_before_its_export_has_not_checked_the_image() {
        let fixture = Fixture::new("image-unchecked");
        fixture.write("xtask/README", "Changed.\n");
        let done = on_the_ci_host(&fixture, other_uid(), &[("KREPI_FORMAL_IMAGE", "i")]);
        assert_eq!(done.receipt.status, Status::ToolFailure);
        let image = done.written().image.expect("the image is recorded");
        assert_eq!(
            (image.reference.as_deref(), image.uid),
            (Some("i"), other_uid())
        );
        assert_eq!((image.writable, image.versions), (None, None));
    }

    #[test]
    fn an_image_reference_other_than_the_pin_fails_the_run() {
        let fixture = Fixture::new("reference");
        let pin = include_str!("../../../verification/image-pin.json");
        fixture.write("verification/image-pin.json", pin);
        fixture.commit_all();
        let (_, pinned) = toolchain::image_pin(pin).expect("the committed pin reads");
        let trigger = [
            ("GITHUB_EVENT_NAME", "push"),
            ("GITHUB_REF", "refs/heads/main"),
            ("GITHUB_RUN_ID", "42"),
            ("GITHUB_RUN_ATTEMPT", "2"),
        ];
        let done = on_the_ci_host(&fixture, other_uid(), &trigger);
        assert_eq!(
            done.receipt.status,
            Status::Verified,
            "{:?}",
            done.failures()
        );
        assert_eq!(
            done.receipt.image.as_ref().expect("an image").reference,
            None
        );
        let given = [("KREPI_FORMAL_IMAGE", pinned.as_str())];
        let done = on_the_ci_host(&fixture, other_uid(), &[&given[..], &trigger].concat());
        assert_eq!(
            done.receipt.status,
            Status::Verified,
            "{:?}",
            done.failures()
        );
        let receipt = done.written();
        let image = receipt.image.as_ref().expect("the image is recorded");
        assert_eq!(image.reference.as_deref(), Some(pinned.as_str()));
        assert_eq!(image.uid, other_uid());
        assert_eq!(image.os_release, fs::read_to_string("/etc/os-release").ok());
        let trigger = &receipt.trigger;
        let found = [
            &trigger.event,
            &trigger.reference,
            &trigger.run_id,
            &trigger.attempt,
        ];
        let found = found.map(|value| value.as_deref());
        assert_eq!(
            found,
            [Some("push"), Some("refs/heads/main"), Some("42"), Some("2")]
        );
        // Another digest, a tag, the bare repository or no pin stop the run.
        let (repository, _) = pinned.split_once('@').expect("a digest");
        let other = format!("{repository}@sha256:{}", "0".repeat(64));
        let tag = format!("{repository}:latest");
        for given in [other.as_str(), tag.as_str(), repository] {
            let done = on_the_ci_host(&fixture, other_uid(), &[("KREPI_FORMAL_IMAGE", given)]);
            stopped_by_the_image(
                &done,
                "image: the snapshot pins no image or another than the job's",
            );
            let image = done.receipt.image.as_ref().expect("the image is recorded");
            assert_eq!(image.reference.as_deref(), Some(given));
        }
        fixture.git(&["rm", "--quiet", "verification/image-pin.json"]);
        fixture.commit_all();
        let done = on_the_ci_host(&fixture, other_uid(), &given);
        stopped_by_the_image(
            &done,
            "image: the snapshot pins no image or another than the job's",
        );
    }

    #[test]
    fn the_trigger_variable_gives_the_mode_of_whole_runs_and_shards_but_not_of_named_targets() {
        let weekly = |name: &str| (name == receipt::TRIGGER).then(|| "WEEKLY".to_string());
        let blank_of = |shard: Option<&str>, targets: &[&str]| {
            let context = shard_context(Path::new("."), shard, &weekly, plenty);
            let targets = BTreeSet::from_iter(targets.iter().map(|name| name.to_string()));
            blank(&context, &targets, "run", "directory")
        };
        let runs = [
            (None, &[][..]),
            (Some("qualification"), &[]),
            (Some("target/t"), &["t"]),
        ];
        for (shard, targets) in runs {
            let receipt = blank_of(shard, targets);
            assert_eq!(receipt.trigger.mode, Mode::Weekly);
            assert_eq!(receipt.failures, []);
        }
        assert_eq!(blank_of(None, &["t"]).trigger.mode, Mode::Scoped);
    }

    #[test]
    fn an_unknown_trigger_is_a_tool_failure_before_the_phases() {
        let fixture = Fixture::new("trigger");
        let done = on_the_ci_host(&fixture, other_uid(), &[(receipt::TRIGGER, "REQUIRED")]);
        assert_eq!(done.code, ExitCode::SUCCESS, "{:?}", done.failures());
        assert_eq!(done.written().trigger.mode, Mode::Required);
        // The mode of a run of named targets is no value of the variable.
        let done = on_the_ci_host(&fixture, other_uid(), &[(receipt::TRIGGER, "SCOPED")]);
        assert_eq!(done.code, ExitCode::FAILURE);
        let receipt = done.written();
        let found = (receipt.status, receipt.complete, receipt.trigger.mode);
        assert_eq!(found, (Status::ToolFailure, false, Mode::Manual));
        let not = "KREPI_FORMAL_TRIGGER is \"SCOPED\", not REQUIRED, FORCED_FULL or WEEKLY";
        assert_eq!(done.failures(), [not]);
        let stopped = Some("a failure before the phases stopped the run");
        assert_eq!(fixture::status(&done, "u1"), (Status::NotRun, stopped));
        assert!(!receipt.phases["checks"].ran);
    }

    #[test]
    fn the_hosts_are_those_of_the_tool_manifest() {
        if let Some(host) = host() {
            assert!(toolchain::HOSTS.contains(&host), "{host}");
        }
    }
}
