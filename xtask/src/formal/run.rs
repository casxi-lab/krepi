//! `cargo xtask formal run`: a run of the proof gate, from the snapshot of
//! the gate inputs to its receipt, as "Gate run" in
//! `docs/formal-verification.md` describes. Every command runs through
//! [`Gate::command`], which limits, classifies, records and prints it.

use std::collections::{BTreeMap, BTreeSet};
use std::env::consts::{ARCH, OS};
use std::fs;
use std::io::{self, Write};
use std::panic::{self, AssertUnwindSafe};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::atomic::{AtomicU32, Ordering};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use super::Layout;
use super::inventory::{self, Inventory};
use super::lean;
use super::outcome::{self, Class, Conclusion, Site, Status, Verdict, word};
use super::paths::{self, Files, Git, Snapshot};
use super::process::{self, Ended, Limit, LimitBy, Ran, Spec};
use super::receipt::{self, Budgets, Failure, Mode, Receipt, Trigger};
use super::registry::{self, State, Target};
use super::toolchain::environment::{self, Installation, RunDirs, Tool};
use super::toolchain::{self, Manifest};
use super::{base, classify, externals, extract, guard, qualify};
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

/// The state of a run, through which the body of a phase runs its commands.
pub struct Gate {
    root: PathBuf,
    layout: Layout,
    run: RunDir,
    /// The tool manifest that the run read from the checkout, and its text.
    manifest: Option<(Manifest, String)>,
    deadline: Instant,
    /// The phase that runs, and its deadline.
    phase: Option<(String, Instant)>,
    conclusions: Vec<(String, Conclusion)>,
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
    progress: Box<dyn Write>,
    /// The site, limit and program that a test gives the commands there.
    #[cfg(test)]
    pub(crate) overrides: Option<(Site, Limit, String)>,
}

impl Gate {
    fn fail(&mut self, status: Status, message: String) {
        self.receipt.failures.push(Failure { status, message });
    }

    /// Runs `request` unless its limit is used up or `skip` says why it does
    /// not start, reads with `read` what it wrote, which returns why a file
    /// could not be read, then classifies, records and prints it; a line
    /// that cannot be printed is left out.
    fn command(
        &mut self,
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
        let sequence = self.receipt.commands.len() as u32 + 1;
        let now = Instant::now();
        let left = |end: Instant| end.saturating_duration_since(now);
        let phase_end = self.phase.as_ref().map_or(self.deadline, |(_, end)| *end);
        let mut limit = limit(request.site.cap(), left(phase_end), left(self.deadline));
        // The commands of a target's unit share its budget.
        let mine = |command: &&receipt::Command| unit.is_some() && command.unit.as_deref() == unit;
        let spent = (self.receipt.commands.iter().filter(mine)).map(|command| command.seconds);
        let spent = Duration::from_secs_f64(spent.sum());
        let rest = (unit.and_then(|unit| self.budgets.get(unit))).map(|b| b.saturating_sub(spent));
        if let Some(rest) = rest.filter(|rest| *rest < limit.duration) {
            (limit.duration, limit.by) = (rest, LimitBy::Target);
        }
        #[cfg(test)]
        let limit = overridden.as_ref().map_or(limit, |(_, set, _)| *set);
        let name = word(&request.site);
        // The receipt writes a limit below half a millisecond as 0.
        let ran = if receipt::seconds(limit.duration) <= 0.0 {
            let used_up = format!("the {} budget was used up", word(&limit.by));
            Err((Class::NotRun, used_up))
        } else if let Some(reason) = skip {
            Err((Class::NotRun, format!("not started: {reason}")))
        } else {
            let (manifest, _) = (self.manifest.as_ref()).expect("commands run after the start");
            let host = self.receipt.host.as_deref().unwrap_or_default();
            let [home, tmp] = ["home", "tmp"].map(|dir| self.run.path.join("work").join(dir));
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
                    })
                })
                .map_err(|error| {
                    let reason = format!("{name}: cannot set up its environment: {error}");
                    (Class::ToolFailure, reason)
                })
        };
        let own = |ran: &Ran| lean::proof_messages(&ran.output, &self.own).len();
        let verdict = match &ran {
            Ok(ran) => outcome::classify(request.site, ran, own(ran), read(ran).as_deref()),
            Err((class, reason)) => Verdict {
                class: *class,
                reason: Some(reason.clone()),
            },
        };
        let disk = process::disk_available(&self.run.path);
        let least = &mut self.receipt.resources.disk_least_available;
        *least = disk.into_iter().chain(*least).min();
        let ran = ran.ok();
        let done = ran.as_ref();
        let mut argv = vec![request.program.to_string()];
        argv.extend_from_slice(request.args);
        let (shown, class) = (argv.join(" "), word(&verdict.class));
        let reason = verdict.reason.as_ref().map(|reason| format!(": {reason}"));
        let reason = reason.unwrap_or_default();
        let _ = writeln!(self.progress, "[{sequence:04}] {shown}: {class}{reason}");
        let log = |log: &Option<process::Log>| {
            log.as_ref().map(|log| receipt::Log {
                path: relative(&self.run.path, &log.path),
                bytes: log.bytes,
                sha256: log.sha256.clone(),
            })
        };
        self.receipt.commands.push(receipt::Command {
            sequence,
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
            seconds: done.map_or(0.0, |ran| receipt::seconds(ran.seconds)),
            group_survived: done.is_some_and(|ran| ran.survivors),
            stdout: done.and_then(|ran| log(&ran.stdout)),
            stderr: done.and_then(|ran| log(&ran.stderr)),
        });
        (ran, verdict)
    }

    /// Runs a command of the gate itself and returns its standard output, or
    /// why it did not pass.
    fn output(&mut self, request: &Request) -> Result<Vec<u8>, String> {
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
        &mut self,
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
    pub fn skip(&mut self, unit: &str, request: &Request, reason: &str) {
        self.command(Some(unit), request, Some(reason), &mut |_| None);
    }

    /// Concludes `unit` with `conclusion`, unless a command of the unit
    /// forces another one ([`outcome::forced`]), and returns its status.
    pub fn conclude(&mut self, unit: &str, conclusion: Conclusion) -> Status {
        self.conclude_from(unit, unit, conclusion)
    }

    /// Concludes `unit` as [`Gate::conclude`] does, from the commands of the
    /// unit `of`, such as a theorem from those of its case.
    pub fn conclude_from(&mut self, unit: &str, of: &str, conclusion: Conclusion) -> Status {
        // A command skipped with its limit left forces nothing: the command
        // that should have written its input decides.
        let skipped = |command: &receipt::Command| {
            command.class == Class::NotRun && command.limit_seconds > 0.0
        };
        let own: Vec<Verdict> = (self.receipt.commands.iter())
            .filter(|command| command.unit.as_deref() == Some(of) && !skipped(command))
            .map(|command| Verdict {
                class: command.class,
                reason: command.reason.clone(),
            })
            .collect();
        let conclusion = outcome::forced(&own).unwrap_or(conclusion);
        self.conclusions
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

/// The receipt of a run that has not done anything yet.
fn blank(context: &Context, targets: &BTreeSet<String>, run: &str, directory: &str) -> Receipt {
    Receipt {
        schema: receipt::SCHEMA,
        command: receipt::COMMAND.to_string(),
        trigger: Trigger {
            mode: if targets.is_empty() {
                Mode::Manual
            } else {
                Mode::Scoped
            },
            event: (context.var)("GITHUB_EVENT_NAME"),
            reference: (context.var)("GITHUB_REF"),
            run_id: (context.var)("GITHUB_RUN_ID"),
            attempt: (context.var)("GITHUB_RUN_ATTEMPT"),
        },
        targets: targets.iter().cloned().collect(),
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
            gate_seconds: GATE_BUDGET.as_secs(),
            receipt_margin_seconds: RECEIPT_MARGIN.as_secs(),
        },
        ..Receipt::default()
    }
}

/// Runs `f`, and makes a panic in it an error with the panic's text.
fn caught<T>(f: impl FnOnce() -> T) -> Result<T, String> {
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
/// failure. A panic in a step of the gate ends the run as a tool failure.
pub(crate) fn execute(
    context: &Context,
    run: &RunDir,
    targets: &BTreeSet<String>,
    phases: Vec<Phase<'_>>,
    progress: Box<dyn Write>,
) -> Receipt {
    let start = Instant::now();
    let directory = relative(context.root, &run.path);
    let mut gate = Gate {
        root: context.root.to_path_buf(),
        layout: *context.layout,
        run: run.clone(),
        manifest: None,
        deadline: start + GATE_BUDGET,
        phase: None,
        conclusions: Vec::new(),
        receipt: blank(context, targets, &run.id, &directory),
        own: Vec::new(),
        budgets: BTreeMap::new(),
        inventory: None,
        handwritten: Vec::new(),
        progress,
        #[cfg(test)]
        overrides: None,
    };
    let resources = &mut gate.receipt.resources;
    resources.disk_available_at_start = process::disk_available(&run.path);
    resources.disk_least_available = resources.disk_available_at_start;
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
        run_phases(&mut gate, phases.take().unwrap_or_default());
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
    let mut receipt = gate.receipt;
    // The seconds of the commands of the unit of each selected target.
    for target in receipt.proof_targets.values_mut() {
        let own = (receipt.commands.iter()).filter(|c| c.unit.is_some() && c.unit == target.unit);
        target.seconds = receipt::seconds(Duration::from_secs_f64(own.map(|c| c.seconds).sum()));
    }
    receipt.resources.largest_process_max_rss = process::largest_child_rss();
    receipt.resources.cgroup_memory_peak = process::cgroup_memory_peak();
    let scoped = !targets.is_empty();
    let failures = receipt.failures.iter().map(|failure| failure.status);
    let units = receipt.units.values().map(|unit| unit.status);
    // Every failure but STALE stops the run or makes it a tool failure.
    let complete = !scoped
        && failures.clone().all(|status| status == Status::Stale)
        && (units.clone()).all(|status| !matches!(status, Status::NotRun | Status::Budget));
    let status = outcome::run_status(&failures.chain(units).collect::<Vec<_>>(), scoped);
    (receipt.complete, receipt.status) = (complete, status);
    receipt.seconds = receipt::seconds(start.elapsed());
    receipt
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
    let states = fs::read_to_string(source.join(registry))
        .map_err(|error| error.to_string())
        .and_then(|text| registry::states(&text))
        .map_err(|error| format!("cannot read {registry}: {error}"))?;
    let targets = &gate.receipt.targets;
    let unknown: Vec<&str> = (targets.iter())
        .filter(|target| !states.contains_key(*target))
        .map(String::as_str)
        .collect();
    if !unknown.is_empty() {
        let unknown = unknown.join(", ");
        return Err(format!("{registry} registers no target named {unknown}"));
    }
    let chosen = selected(&states, targets);
    let extracts = !chosen.is_empty();
    // The gate's budget grows by the budget of each target that it extracts.
    let all = Duration::from_secs(states.values().map(|(_, budget)| budget).sum());
    (gate.deadline, gate.receipt.budgets.gate_seconds) =
        (gate.deadline + all, (GATE_BUDGET + all).as_secs());
    let budget = |name: &str| Duration::from_secs(states[name].1);
    gate.budgets = BTreeMap::from_iter(chosen.iter().map(|name| (target_unit(name), budget(name))));
    for problem in paths::rejected(&files, &gate.layout) {
        gate.fail(Status::Rejected, problem);
    }
    check_kernel(gate, &source, &files, extracts)
}

/// The targets that a run of `named` targets selects: those, or every
/// formal target of the registry when it names none, for a planned target
/// runs only when it is named.
fn selected<'a>(states: &'a BTreeMap<String, (State, u64)>, named: &'a [String]) -> Vec<&'a str> {
    let formal = |(name, (state, _)): (&'a String, &(State, u64))| {
        (*state == State::Formal).then_some(name.as_str())
    };
    match named {
        [] => states.iter().filter_map(formal).collect(),
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
/// `extraction`, before the base round, which extracts every target, whose
/// proofs the base round builds, and concludes the selected planned ones;
/// and `targets`, after it, which concludes the selected formal ones. The
/// first stops when the export's registry is not the one read here.
fn target_phases<'a>(root: &Path, layout: &Layout, named: &BTreeSet<String>) -> [Phase<'a>; 2] {
    let path = layout.registry;
    let read = fs::read_to_string(root.join(path)).map_err(|error| error.to_string());
    let read = read.and_then(|text| Ok((registry::parse(&text)?.targets, text)));
    let read = read.map_err(|error| format!("cannot read {path}: {error}"));
    let all = Vec::from_iter(read.iter().flat_map(|(targets, _)| targets.clone()));
    let states = BTreeMap::from_iter(all.iter().map(|t| (t.name.clone(), (t.state, t.budget))));
    let named = Vec::from_iter(named.iter().cloned());
    let chosen = BTreeSet::from_iter(selected(&states, &named).into_iter().map(String::from));
    let pick = |t: &&Target, state| t.state == state && chosen.contains(&t.name);
    let formal = Vec::from_iter(all.iter().filter(|t| pick(t, State::Formal)).cloned());
    let planned = Vec::from_iter(all.iter().filter(|t| pick(t, State::Planned)).cloned());
    let units = |targets: &[Target]| Vec::from_iter(targets.iter().map(|t| target_unit(&t.name)));
    let budget = |targets: &[Target]| Duration::from_secs(targets.iter().map(|t| t.budget).sum());
    let phases = [
        ("extraction", budget(&all), units(&planned)),
        ("targets", budget(&formal), units(&formal)),
    ];
    let bodies: [Body<'a>; 2] = [
        Box::new(move |gate| {
            let (targets, text) = read?;
            if base::read(&gate.source().join(path))? != text {
                return Err(format!("{path} differs from the one read at the start"));
            }
            (targets.iter()).try_for_each(|t| extract_target(gate, t, chosen.contains(&t.name)))
        }),
        Box::new(move |gate| (formal.iter()).try_for_each(|t| finish_target(gate, t))),
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
        base::PHASE.to_string()
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
/// its trusted axioms and the declarations that its templates keep, and
/// concludes its unit, unless its extraction concluded it.
fn finish_target(gate: &mut Gate, target: &Target) -> Result<(), String> {
    let (layout, source, unit) = (gate.layout, gate.source(), target_unit(&target.name));
    if (gate.conclusions.iter()).any(|(concluded, _)| *concluded == unit) {
        return Ok(());
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
    let write = |file: &str, text: String| {
        fs::write(project.join(file), text).map_err(|error| format!("{file}: {error}"))
    };
    let (mut audited, mut built) = (None, false);
    if record.typed {
        for file in gate.handwritten.clone() {
            lean::copy_into(&source.join(layout.project), &project, &file)?;
        }
        let root = lean::root_source(&BTreeSet::from_iter(modules.iter().cloned()));
        write(&lean::module_file(layout.namespace), root)?;
        let (ran, verdict, _) = gate.run(&unit, &build, |_| Ok(()));
        built = verdict.class == Class::Passed;
        let errors = (ran.filter(|_| !built)).map(|ran| lean::errors(&ran.output).join(" | "));
        problems.extend(errors.map(|errors| format!("the proofs do not build: {errors}")));
    } else {
        gate.skip(&unit, &build, "its generated definitions do not type-check");
    }
    if built {
        let text = lean::audit_source(layout.namespace, &[], modules);
        write(lean::AUDIT, text)?;
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
    gate.conclude(&unit, qualify::conclusion(&problems));
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
    let conclusions = std::mem::take(&mut gate.conclusions);
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
    let written = run.map(|run| (run.receipt(), fs::write(run.receipt(), &text)));
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

/// Entry point of `cargo xtask formal run`.
pub fn command(root: &Path, layout: &Layout, targets: BTreeSet<String>) -> ExitCode {
    process::init();
    let var = |name: &str| std::env::var(name).ok().filter(|value| !value.is_empty());
    let context = Context {
        root,
        layout,
        host: host(),
        uid: process::effective_uid(),
        var: &var,
    };
    let run = RunDir::create(root);
    let receipt = match &run {
        Ok(run) => {
            let mut phases = Vec::from_iter(guard::phase(&var));
            let [extraction, finish] = target_phases(root, layout, &targets);
            phases.extend([qualify::phase(root, layout), extraction]);
            phases.extend([base::phase(root, layout), finish]);
            execute(&context, run, &targets, phases, Box::new(io::stdout()))
        }
        Err(error) => {
            let mut receipt = blank(&context, &targets, "", RUNS);
            let message = format!("cannot create a run directory below {RUNS}: {error}");
            let status = Status::ToolFailure;
            receipt.failures.push(Failure { status, message });
            receipt
        }
    };
    // A stop signal after the last command ends the run without a receipt.
    process::stop_if_asked();
    let (stdout, stderr) = (&mut io::stdout(), &mut io::stderr());
    finish(&receipt, run.as_ref().ok(), stdout, stderr)
}

#[cfg(test)]
pub(crate) mod tests {
    use std::os::unix::process::ExitStatusExt;
    use std::process::{Command, Stdio};

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
        stdout: String,
        stderr: String,
    }

    impl Done {
        /// The receipt as the run wrote it.
        pub(crate) fn written(&self) -> Receipt {
            let text = fs::read_to_string(self.run.receipt()).expect("the receipt is written");
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

    /// Runs the gate on `fixture` into a new run directory, for `targets`.
    pub(crate) fn gate(fixture: &Fixture, targets: &[&str], phases: Vec<Phase<'_>>) -> Done {
        let run = RunDir::create(fixture.root()).expect("create the run directory");
        let targets = targets.iter().map(|name| name.to_string()).collect();
        gate_in(
            fixture.root(),
            run,
            &targets,
            phases,
            test_host(),
            Box::new(io::sink()),
        )
    }

    /// The host of the run: this one, or one of the manifest elsewhere.
    pub(crate) fn test_host() -> Option<&'static str> {
        host().or(Some("linux-aarch64"))
    }

    /// Runs the gate on the fixture at `root` into `run` on `host`, without
    /// printing its commands, and writes its receipt.
    pub(crate) fn gate_in(
        root: &Path,
        run: RunDir,
        targets: &BTreeSet<String>,
        phases: Vec<Phase<'_>>,
        host: Option<&str>,
        progress: Box<dyn Write>,
    ) -> Done {
        let context = Context {
            root,
            layout: &Layout::PRODUCTION,
            host,
            uid: other_uid(),
            var: &|_| None,
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
        progress: Box<dyn Write>,
    ) -> Done {
        let receipt = execute(context, &run, targets, phases, progress);
        let (mut stdout, mut stderr) = (Vec::new(), Vec::new());
        let code = finish(&receipt, Some(&run), &mut stdout, &mut stderr);
        Done {
            receipt,
            code,
            run,
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
    fn shell(run: &mut Gate, unit: &str, script: &str) -> Verdict {
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
        run.run(unit, &request, |_| Ok(())).1
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
    fn root_package(fixture: &Fixture, name: &str, extra: &str) {
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
    fn register(fixture: &Fixture, targets: &str) {
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
        let fixture = Fixture::new("planned");
        register(&fixture, r#"[{"name": "demo", "state": "planned"}]"#);
        let done = gate(&fixture, &[], Vec::new());
        assert_eq!(
            done.receipt.status,
            Status::Verified,
            "{:?}",
            done.failures()
        );
        assert_eq!(done.receipt.targets, Vec::<String>::new());
        // A run that names it extracts it.
        let done = gate(&fixture, &["demo"], Vec::new());
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
    /// target `t`, and the target registry `targets`, committed.
    fn with_targets(label: &str, targets: &str) -> Fixture {
        let fixture = fixture::qualification(label, &serde_json::json!([]));
        for (file, list) in [("models", "models"), ("axioms", "axioms"), ("tcb", "items")] {
            let text = format!("{{\"schema\": 1, \"{list}\": []}}\n");
            fixture.write(&format!("verification/{file}.json"), &text);
        }
        let proof = "module\n\npublic theorem f_spec : True := trivial\n";
        fixture.write("verification/Krepi/Proofs/T.lean", proof);
        root_package(&fixture, "krepi-kernel", "");
        register(&fixture, targets);
        fixture
    }

    /// The registry of the formal target `t`, with `budget` and `mutants`,
    /// and of the planned target `p`.
    fn two_targets(budget: u64, mutants: usize) -> String {
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
    fn target_run<'a>(fixture: &Fixture, named: &[&str]) -> Vec<Phase<'a>> {
        let named = BTreeSet::from_iter(named.iter().map(|name| name.to_string()));
        let [extraction, finish] = target_phases(fixture.root(), &Layout::PRODUCTION, &named);
        let base = phase("base", LONG, &["base"], |run| {
            run.handwritten = vec!["Krepi/Proofs/T.lean".to_string()];
            run.conclude("base", (Status::Verified, None));
            Ok(())
        });
        vec![extraction, base, finish]
    }

    #[test]
    fn a_formal_target_is_verified_in_its_stage_and_a_planned_one_is_scoped() {
        let fixture = with_targets("targets", &two_targets(1_800, 1));
        let done = gate(&fixture, &[], target_run(&fixture, &[]));
        assert_eq!(done.receipt.status, Status::Verified, "{:?}", done.receipt);
        assert_eq!(fixture::status(&done, "target/t"), (Status::Verified, None));
        let sites = Vec::from_iter(fixture::commands(&done, "target/t").iter().map(|c| c.site));
        let expected = [Site::Charon, Site::Aeneas, Site::TargetBuild];
        assert_eq!(
            sites,
            [&expected[..], &[Site::TargetBuild, Site::AxiomAudit]].concat()
        );
        // The target is extracted for the extraction triple; the planned one
        // only for the base round.
        let charon = &fixture::commands(&done, "target/t")[0];
        assert!(
            charon
                .argv
                .ends_with(&["--target", "aarch64-unknown-none"].map(String::from))
        );
        let (formal, planned) = (
            &done.receipt.proof_targets["t"],
            &done.receipt.proof_targets["p"],
        );
        assert_eq!(
            (formal.unit.as_deref(), planned.unit.as_deref()),
            (Some("target/t"), None)
        );
        assert!(formal.typed && planned.typed && formal.problems.is_empty());
        assert_eq!(done.receipt.budgets.gate_seconds, 7_200 + 2 * 1_800);
        // A run of the planned target concludes it as scoped.
        let done = gate(&fixture, &["p"], target_run(&fixture, &["p"]));
        assert_eq!(done.receipt.status, Status::Scoped, "{:?}", done.receipt);
        assert_eq!(fixture::status(&done, "target/p"), (Status::Scoped, None));
        assert!(!done.receipt.units.contains_key("target/t"));
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
        let whole = gate(&fixture, &[], verified());
        assert_eq!(
            whole.receipt.status,
            Status::Verified,
            "{:?}",
            whole.failures()
        );
        assert!(whole.receipt.targets.is_empty() && whole.receipt.proof_targets.is_empty());
        // `formal check` in the production layout reads its own registry
        // alone: a calibration registry that it would refuse changes nothing.
        let mut tree = Tree::load(&repo::root()).expect("the repository");
        let roots = manifests::kernel_metadata(&repo::root()).expect("the kernel workspace");
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
            // The gate that the test stops: its command writes the number
            // of its group and waits.
            process::init();
            let root = PathBuf::from(root);
            let group = root.join("artifacts/group");
            let script = format!(
                "sleep 240 & echo $$ > {0}.new && mv {0}.new {0}; wait",
                group.display()
            );
            let phases = vec![phase("base", LONG, &["u1"], |run| {
                shell(run, "u1", &script);
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
            let group: i32 = loop {
                if let Ok(text) = fs::read_to_string(fixture.root().join("artifacts/group")) {
                    break text.trim().parse().expect("a process number");
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
            assert_eq!(process::tests::probe(group), Some(libc::ESRCH));
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
    fn the_hosts_are_those_of_the_tool_manifest() {
        if let Some(host) = host() {
            assert!(toolchain::HOSTS.contains(&host), "{host}");
        }
    }
}
