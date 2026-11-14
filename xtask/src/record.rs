//! `cargo xtask run-record`: the record of one run of a workflow, from the
//! data of the GitHub API that the workflow `run record` collects.
//!
//! ```sh
//! cargo xtask run-record --input RUN.json [--workflow FILE] \
//!     [--own OWN.json --now SECONDS] --output DIR
//! cargo xtask run-record --id TEXT
//! ```
//!
//! # Input
//!
//! `--input` names a JSON object that `jq` writes from the API: `run`, with
//! the `id`, `attempt`, `workflow` (the name of the workflow), `path`,
//! `event`, `head_branch`, `head_sha` and `conclusion` of the run, and
//! `jobs`, each with its `id`, `name`, `conclusion`, `labels`,
//! `runner_group_name`, `runner_name`, its `annotations` (`level`, `title`
//! and `message` of each) and its `started_at` and `completed_at`. Every time
//! is a count of seconds since 1970, which `jq` computes with
//! `fromdateiso8601`, or null; no other field may be present. `--workflow`
//! names the text of the workflow file at the head of the run, from which
//! the limit of each job is read: its `timeout-minutes`, or 360 without one,
//! and none when it is an expression. A job takes the limit of the job of
//! the text whose name is its name, also followed by the values of a matrix
//! in parentheses; failing that, of the jobs whose names hold expressions
//! `${{ }}` and fit its name, with or without the values of a matrix in
//! parentheses, when each expression stands for some text and all of them
//! give the same limit ([`job_limit`]). A job with no limit there, or with
//! an expression, takes the minutes that it noted ([`noted`]), if any.
//! `--own` names the same object for the run of the record workflow itself,
//! with `--now` the current time.
//!
//! # Record
//!
//! The command creates `DIR`, which must not exist, and writes
//! [`RECORD_FILE`] and [`SUMMARY_FILE`] into it. The record holds the run
//! with its line ([`line`]); each job with its runner class ([`runner`]),
//! seconds, minutes (the seconds rounded up to whole minutes, 0 for a job
//! that ran on no runner), limit, conclusion and result, which is `TIMEOUT`
//! when the job did not succeed and either ran at least as long as its limit
//! or has the failure annotation of a command that `timeout` stopped at its
//! deadline ([`timeout`]), and otherwise the conclusion, with the reason of a
//! `TIMEOUT`, `limit` or `deadline`, in `timeout`; its annotations; the wall
//! clock of the run, from the first start to the last end of the jobs that
//! ran on a runner; the sum of the minutes; the limit of the line and
//! whether the run or one of its jobs took more than 80% of it ([`over`]);
//! the days that the record is kept ([`retention`]); and, with `--own`, the
//! record workflow's run until `--now`: its wall clock and minutes, and each
//! of its jobs with its runner class, seconds and minutes, a job still
//! running counting until `--now`.
//! The summary is the same in Markdown, with the text of the run escaped;
//! it states in neutral words a run that exceeds 80% of its limit, and names
//! each job that was stopped at the deadline of its main command.
//!
//! `--id TEXT` checks the run ID that a manual run of the record workflow
//! takes as its input and prints it: digits only, without a leading zero,
//! at most `u64::MAX`.
//!
//! The command prints only the paths that it writes and exits with 0, or with
//! 2 after a usage error or a failure, which it reports on standard error.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Arg, value_parser};
use serde::Deserialize;
use serde_json::{Value, json};
use yaml_rust2::{Yaml, YamlLoader};

use crate::image;

/// The version of the record format.
pub const FORMAT: u32 = 2;
/// The record in the output directory.
pub const RECORD_FILE: &str = "record.json";
/// The summary in the output directory.
pub const SUMMARY_FILE: &str = "summary.md";
/// The limit of a job without `timeout-minutes`, in minutes.
pub const DEFAULT_TIMEOUT: u64 = 360;
/// The limit of the jobs of the pull request line, in seconds.
pub const PULL_REQUEST_LIMIT: u64 = 20 * 60;
/// The limit of the jobs of the full line, in seconds.
pub const FULL_LIMIT: u64 = 3600;
/// The words of the summary for a run over 80% of its limit.
pub const OVER: &str = "exceeds 80% of its limit";
/// The annotation of a step whose command `timeout` stopped at its deadline:
/// `timeout` then exits with 124, and the runner reports that status.
pub const DEADLINE_EXIT: &str = "Process completed with exit code 124.";
/// The title of the notice in which a job whose limit is an expression
/// writes its minutes: `::notice title=timeout-minutes::<minutes>`.
pub const LIMIT_NOTICE: &str = "timeout-minutes";

/// The data of a run, as `jq` writes it.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Input {
    pub run: RunData,
    pub jobs: Vec<JobData>,
}

/// The fields of a run.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RunData {
    pub id: u64,
    pub attempt: u64,
    pub workflow: String,
    pub path: String,
    pub event: String,
    pub head_branch: Option<String>,
    pub head_sha: String,
    pub conclusion: Option<String>,
}

/// The fields of a job.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct JobData {
    pub id: u64,
    pub name: String,
    pub conclusion: Option<String>,
    pub labels: Vec<String>,
    pub runner_group_name: Option<String>,
    pub runner_name: Option<String>,
    pub started_at: Option<u64>,
    pub completed_at: Option<u64>,
    pub annotations: Vec<Annotation>,
}

/// An annotation of a job.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Annotation {
    pub level: String,
    pub title: Option<String>,
    pub message: String,
}

/// The line of a run of the workflow `workflow` triggered by `event`: the
/// pull request line, the full line, the main line, the nightly line, the
/// weekly line, or `none` for the other workflows.
pub fn line(workflow: &str, event: &str) -> &'static str {
    match (workflow, event) {
        ("check", "pull_request") => "pull request",
        ("check", "push") => "main",
        ("full", "pull_request") => "full",
        ("nightly", _) => "nightly",
        ("weekly", _) => "weekly",
        _ => "none",
    }
}

/// The limit of the jobs of `line` in seconds, if the line has one.
pub fn limit(line: &str) -> Option<u64> {
    match line {
        "pull request" => Some(PULL_REQUEST_LIMIT),
        "full" => Some(FULL_LIMIT),
        _ => None,
    }
}

/// The class of the runner of `job`: `none` for a job that ran on no
/// runner, `self-hosted` when its labels say so, `larger hosted` for a
/// runner group other than the one of the standard runners, `GitHub
/// Actions`, and otherwise `standard hosted`.
pub fn runner(job: &JobData) -> &'static str {
    runner_class(
        job.runner_name.as_deref(),
        &job.labels,
        job.runner_group_name.as_deref(),
    )
}

/// The class of the runner of a job with the runner name `name`, the labels
/// `labels` and the runner group `group`, as [`runner`] gives it. A job ran
/// on no runner when it has no runner name ([`ran_on_a_runner`]).
pub fn runner_class(name: Option<&str>, labels: &[String], group: Option<&str>) -> &'static str {
    if !ran_on_a_runner(name) {
        "none"
    } else if labels.iter().any(|label| label == "self-hosted") {
        "self-hosted"
    } else if group != Some("GitHub Actions") {
        "larger hosted"
    } else {
        "standard hosted"
    }
}

/// Whether a job with the runner name `name` ran on a runner. The API gives
/// a job that no runner took no name, as `null` or, for a job cancelled
/// before a runner took it, as an empty name.
pub fn ran_on_a_runner(name: Option<&str>) -> bool {
    name.is_some_and(|name| !name.is_empty())
}

/// The days that the record of a run of `event` on the branch `branch` is
/// kept: 90 for a run on `main` that a pull request did not trigger, 30 for
/// the others.
pub fn retention(event: &str, branch: Option<&str>) -> u64 {
    if event != "pull_request" && branch == Some("main") {
        90
    } else {
        30
    }
}

/// The seconds of `job`, if it ran on a runner and both its times are
/// known; a job still running counts until `now`.
fn seconds(job: &JobData, now: Option<u64>) -> Option<u64> {
    if !ran_on_a_runner(job.runner_name.as_deref()) {
        return None;
    }
    let end = job.completed_at.or(now)?;
    Some(end.saturating_sub(job.started_at?))
}

/// The whole minutes of `seconds`, rounded up.
pub fn minutes(seconds: u64) -> u64 {
    seconds.div_ceil(60)
}

/// The wall clock of `jobs`: from the first start to the last end of the
/// jobs that ran on a runner, a job still running ending at `now`.
fn wall(jobs: &[JobData], now: Option<u64>) -> Option<u64> {
    let ran = || jobs.iter().filter(|job| seconds(job, now).is_some());
    let start = ran().filter_map(|job| job.started_at).min()?;
    let end = ran().filter_map(|job| job.completed_at.or(now)).max()?;
    Some(end.saturating_sub(start))
}

/// The limits of the jobs of the workflow `text`: each job's display name,
/// its `name` or else its key, with its `timeout-minutes`, or
/// [`DEFAULT_TIMEOUT`] without one, or `None` when it is not a number.
pub fn limits(text: &str) -> Result<Vec<(String, Option<u64>)>, String> {
    let documents = YamlLoader::load_from_str(text).map_err(|error| error.to_string())?;
    let jobs = match documents.first().map(|document| &document["jobs"]) {
        Some(Yaml::Hash(jobs)) => jobs,
        _ => return Err("the workflow has no jobs".to_string()),
    };
    Ok((jobs.iter())
        .filter_map(|(key, job)| {
            let name = job["name"].as_str().or(key.as_str())?;
            let timeout = match &job["timeout-minutes"] {
                Yaml::BadValue => Some(DEFAULT_TIMEOUT),
                Yaml::Integer(minutes) => u64::try_from(*minutes).ok(),
                _ => None,
            };
            Some((name.to_string(), timeout))
        })
        .collect())
}

/// The literal pieces of the display name `display` around its expressions
/// `${{ … }}`, if it has one. A `${{` without a following `}}` is text.
fn pieces(display: &str) -> Option<Vec<&str>> {
    let mut pieces = Vec::new();
    let mut rest = display;
    while let Some(start) = rest.find("${{") {
        let Some(length) = rest[start + 3..].find("}}") else {
            break;
        };
        pieces.push(&rest[..start]);
        rest = &rest[start + 3 + length + 2..];
    }
    pieces.push(rest);
    (pieces.len() > 1).then_some(pieces)
}

/// Whether `name` is the display name of `pieces`, at least two, with each
/// expression between them evaluated to some text, possibly empty.
fn fits(pieces: &[&str], name: &str) -> bool {
    let (first, last) = (pieces[0], pieces[pieces.len() - 1]);
    if name.len() < first.len() + last.len() || !name.starts_with(first) || !name.ends_with(last) {
        return false;
    }
    let mut middle = &name[first.len()..name.len() - last.len()];
    for piece in &pieces[1..pieces.len() - 1] {
        match middle.find(piece) {
            Some(at) => middle = &middle[at + piece.len()..],
            None => return false,
        }
    }
    true
}

/// The limit in minutes of the job `name` in `limits`. A job whose display
/// name is `name`, or `name` followed by ` (` with the values of a matrix,
/// gives its limit. Otherwise the display names that hold expressions and
/// fit `name`, or `name` without the values of a matrix in parentheses,
/// give the limit when they all give the same one.
fn job_limit(limits: &[(String, Option<u64>)], name: &str) -> Option<u64> {
    let matches = |display: &str| {
        name == display || (name.strip_prefix(display)).is_some_and(|rest| rest.starts_with(" ("))
    };
    if let Some((_, timeout)) = limits.iter().find(|(display, _)| matches(display)) {
        return *timeout;
    }
    let mut names = vec![name];
    if name.ends_with(')') {
        names.extend(name.match_indices(" (").map(|(at, _)| &name[..at]));
    }
    let fit = |display: &str| {
        pieces(display).is_some_and(|pieces| names.iter().any(|name| fits(&pieces, name)))
    };
    let mut found = (limits.iter())
        .filter(|(display, _)| fit(display))
        .map(|(_, timeout)| *timeout);
    let first = found.next()?;
    found.all(|timeout| timeout == first).then_some(first)?
}

/// The minutes that `job` noted as its limit: the first message of its
/// notices titled [`LIMIT_NOTICE`] that is a whole number.
fn noted(job: &JobData) -> Option<u64> {
    let limit = |n: &&Annotation| n.level == "notice" && n.title.as_deref() == Some(LIMIT_NOTICE);
    (job.annotations.iter().filter(limit)).find_map(|note| note.message.parse().ok())
}

/// Why the job `job`, which ran for `seconds` against a limit of `limit`
/// minutes, is a `TIMEOUT`, if it is one: a job that did not succeed is one
/// when it ran at least as long as its limit (`limit`), or when one of its
/// annotations is the failure [`DEADLINE_EXIT`] of a command that `timeout`
/// stopped at its deadline (`deadline`). The first condition alone is the
/// rule of format 1, so every job that it judged a `TIMEOUT` is still one.
pub fn timeout(job: &JobData, seconds: Option<u64>, limit: Option<u64>) -> Option<&'static str> {
    if job.conclusion.as_deref() == Some("success") {
        return None;
    }
    if seconds
        .zip(limit)
        .is_some_and(|(seconds, minutes)| seconds >= minutes.saturating_mul(60))
    {
        return Some("limit");
    }
    let deadline = |note: &Annotation| note.level == "failure" && note.message == DEADLINE_EXIT;
    job.annotations.iter().any(deadline).then_some("deadline")
}

/// What took more than 80% of `limit` seconds: `run` for the wall clock of
/// the run, and `job <name>` for each job.
pub fn over(limit: u64, wall: Option<u64>, jobs: &[(String, Option<u64>)]) -> Vec<String> {
    let above = |seconds: u64| seconds * 10 > limit * 8;
    let mut over = Vec::new();
    if wall.is_some_and(above) {
        over.push("run".to_string());
    }
    for (name, seconds) in jobs {
        if seconds.is_some_and(above) {
            over.push(format!("job {name}"));
        }
    }
    over
}

/// The record of `input`, with the job limits of `limits` and, with `own`,
/// the run of the record workflow until `now`.
pub fn record(
    input: &Input,
    limits: Option<&[(String, Option<u64>)]>,
    own: Option<(&Input, u64)>,
) -> Value {
    let run = &input.run;
    let line = line(&run.workflow, &run.event);
    let mut jobs = Vec::new();
    let mut durations = Vec::new();
    let mut total = 0;
    for job in &input.jobs {
        let seconds = seconds(job, None);
        let used = seconds.map_or(0, minutes);
        total += used;
        let limit = limits.and_then(|limits| job_limit(limits, &job.name).or_else(|| noted(job)));
        let stopped = timeout(job, seconds, limit);
        let result = match stopped {
            Some(_) => Some("TIMEOUT"),
            None => job.conclusion.as_deref(),
        };
        durations.push((job.name.clone(), seconds));
        jobs.push(json!({
            "id": job.id,
            "name": job.name,
            "runner": runner(job),
            "labels": job.labels,
            "runner_group": job.runner_group_name,
            "started_at": job.started_at,
            "completed_at": job.completed_at,
            "seconds": seconds,
            "minutes": used,
            "timeout_minutes": limit,
            "conclusion": job.conclusion,
            "result": result,
            "timeout": stopped,
            "annotations": (job.annotations.iter())
                .map(|note| json!({"level": note.level, "title": note.title, "message": note.message}))
                .collect::<Vec<_>>(),
        }));
    }
    let clock = wall(&input.jobs, None);
    let limit = limit(line);
    let over = limit.map(|limit| over(limit, clock, &durations));
    let own = own.map(|(own, now)| {
        let mut used = 0;
        let mut jobs = Vec::new();
        for job in &own.jobs {
            let seconds = seconds(job, Some(now));
            used += seconds.map_or(0, minutes);
            jobs.push(json!({
                "id": job.id,
                "name": job.name,
                "runner": runner(job),
                "labels": job.labels,
                "runner_group": job.runner_group_name,
                "started_at": job.started_at,
                "completed_at": job.completed_at,
                "seconds": seconds,
                "minutes": seconds.map_or(0, minutes),
            }));
        }
        json!({
            "id": own.run.id,
            "attempt": own.run.attempt,
            "wall_seconds": wall(&own.jobs, Some(now)),
            "minutes": used,
            "jobs": jobs,
        })
    });
    json!({
        "format": FORMAT,
        "run": {
            "id": run.id,
            "attempt": run.attempt,
            "workflow": run.workflow,
            "path": run.path,
            "event": run.event,
            "head_branch": run.head_branch,
            "head_sha": run.head_sha,
            "conclusion": run.conclusion,
            "line": line,
        },
        "workflow_read": limits.is_some(),
        "wall_seconds": clock,
        "minutes": total,
        "limit_seconds": limit,
        "over_80_percent": over.as_ref().map(|over| !over.is_empty()),
        "over": over,
        "retention_days": retention(&run.event, run.head_branch.as_deref()),
        "jobs": jobs,
        "record_run": own,
    })
}

/// `text` for a cell of a Markdown table: control characters escaped and
/// `|` and backquotes taken out of the table's syntax.
pub fn cell(text: &str) -> String {
    crate::suite::printable(text)
        .replace('\\', "\\\\")
        .replace('|', "\\|")
        .replace('`', "'")
}

/// The Markdown summary of `record`.
pub fn summary(record: &Value) -> String {
    let text = |value: &Value| match value {
        Value::String(text) => cell(text),
        Value::Null => "-".to_string(),
        other => cell(&other.to_string()),
    };
    let run = &record["run"];
    let mut summary = format!(
        "## Run record\n\nRun {} attempt {} of the workflow {}, line {}, event {}, \
         conclusion {}: {} s of wall clock, {} job minutes; the record is kept {} days.\n\n",
        run["id"],
        run["attempt"],
        text(&run["workflow"]),
        text(&run["line"]),
        text(&run["event"]),
        text(&run["conclusion"]),
        text(&record["wall_seconds"]),
        record["minutes"],
        record["retention_days"],
    );
    if record["over_80_percent"] == true {
        let over: Vec<String> = (record["over"].as_array().into_iter().flatten())
            .map(text)
            .collect();
        summary.push_str(&format!("The run {OVER}: {}.\n\n", over.join(", ")));
    }
    if record["workflow_read"] == false {
        summary.push_str("The workflow file was not read, so no job has a known limit.\n\n");
    }
    summary.push_str("| Job | Runner | Seconds | Minutes | Limit (min) | Conclusion | Result |\n");
    summary.push_str("| --- | --- | ---: | ---: | ---: | --- | --- |\n");
    for job in record["jobs"].as_array().into_iter().flatten() {
        summary.push_str(&format!(
            "| {} | {} | {} | {} | {} | {} | {} |\n",
            text(&job["name"]),
            text(&job["runner"]),
            text(&job["seconds"]),
            text(&job["minutes"]),
            text(&job["timeout_minutes"]),
            text(&job["conclusion"]),
            text(&job["result"]),
        ));
    }
    let stopped: Vec<String> = (record["jobs"].as_array().into_iter().flatten())
        .filter(|job| job["timeout"] == "deadline")
        .map(|job| text(&job["name"]))
        .collect();
    if !stopped.is_empty() {
        summary.push('\n');
    }
    for name in stopped {
        summary.push_str(&format!(
            "Job {name} was stopped at the deadline of its main command.\n"
        ));
    }
    let own = &record["record_run"];
    if !own.is_null() {
        summary.push_str(&format!(
            "\nThis record took {} s of wall clock and {} job minutes until its upload.\n\n",
            text(&own["wall_seconds"]),
            own["minutes"]
        ));
        summary.push_str("| Job of this record | Runner | Seconds | Minutes |\n");
        summary.push_str("| --- | --- | ---: | ---: |\n");
        for job in own["jobs"].as_array().into_iter().flatten() {
            summary.push_str(&format!(
                "| {} | {} | {} | {} |\n",
                text(&job["name"]),
                text(&job["runner"]),
                text(&job["seconds"]),
                text(&job["minutes"]),
            ));
        }
    }
    summary
}

/// The run ID of the input `text` of a manual run.
pub fn run_id(text: &str) -> Result<u64, String> {
    let digits = !text.is_empty() && text.bytes().all(|byte| byte.is_ascii_digit());
    if !digits || text.starts_with('0') {
        return Err(format!(
            "{:?} is not a run ID",
            crate::suite::printable(text)
        ));
    }
    text.parse()
        .map_err(|_| format!("{text} is not a run ID: it is too large"))
}

/// The command line of `cargo xtask run-record`.
fn cli() -> clap::Command {
    let about = (crate::COMMANDS.iter())
        .find(|command| command.name == "run-record")
        .map_or("", |command| command.about);
    let path = |name: &'static str, help: &'static str| {
        Arg::new(name)
            .long(name)
            .value_name("PATH")
            .help(help)
            .value_parser(value_parser!(PathBuf))
    };
    clap::Command::new("run-record")
        .bin_name("cargo xtask run-record")
        .no_binary_name(true)
        .about(about)
        .arg(
            Arg::new("id")
                .long("id")
                .value_name("TEXT")
                .help("Check the run ID of a manual run and print it")
                .conflicts_with_all(["input", "workflow", "own", "now", "output"]),
        )
        .arg(path("input", "The run and its jobs, as jq writes them").required_unless_present("id"))
        .arg(path("workflow", "The workflow file at the head of the run"))
        .arg(path("own", "The run of the record workflow itself").requires("now"))
        .arg(
            Arg::new("now")
                .long("now")
                .value_name("SECONDS")
                .help("The current time in seconds since 1970")
                .requires("own")
                .value_parser(value_parser!(u64)),
        )
        .arg(
            path("output", "New directory for the record and the summary")
                .required_unless_present("id"),
        )
}

/// Reads the input at `path`.
fn read_input(path: &Path) -> Result<Input, String> {
    let text = fs::read_to_string(path)
        .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    serde_json::from_str(&text).map_err(|error| format!("{}: {error}", path.display()))
}

/// Writes the record and the summary of the command line `matches`; the
/// output directory.
fn write(matches: &clap::ArgMatches) -> Result<PathBuf, String> {
    let path = |name: &str| matches.get_one::<PathBuf>(name);
    let input = read_input(path("input").expect("required without --id"))?;
    let limits = match path("workflow") {
        None => None,
        Some(file) => {
            let text = fs::read_to_string(file)
                .map_err(|error| format!("cannot read {}: {error}", file.display()))?;
            Some(limits(&text).map_err(|error| format!("{}: {error}", file.display()))?)
        }
    };
    let own = match path("own") {
        None => None,
        Some(file) => Some(read_input(file)?),
    };
    let now = matches.get_one::<u64>("now").copied().unwrap_or_default();
    let record = record(
        &input,
        limits.as_deref(),
        own.as_ref().map(|own| (own, now)),
    );
    let output = path("output").expect("required without --id");
    image::create_new(output)?;
    let write = |name: &str, text: String| {
        let file = output.join(name);
        fs::write(&file, text).map_err(|error| format!("cannot write {}: {error}", file.display()))
    };
    write(RECORD_FILE, format!("{record:#}\n"))?;
    write(SUMMARY_FILE, summary(&record))?;
    Ok(output.clone())
}

/// Entry point of `cargo xtask run-record`.
pub fn command(args: &[&str]) -> ExitCode {
    let matches = match cli().try_get_matches_from(args) {
        Ok(matches) => matches,
        Err(error) => {
            let _ = error.print();
            return ExitCode::from(u8::try_from(error.exit_code()).unwrap_or(2));
        }
    };
    let result = match matches.get_one::<String>("id") {
        Some(text) => run_id(text).map(|id| println!("{id}")),
        None => write(&matches).map(|output| {
            println!("record written to {}", output.join(RECORD_FILE).display());
            println!("summary written to {}", output.join(SUMMARY_FILE).display());
        }),
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!(
                "cargo xtask run-record failed: {}",
                crate::suite::printable(&error)
            );
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests;
