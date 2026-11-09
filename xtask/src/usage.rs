//! `cargo xtask usage`: the usage summary of the CI of a month, from the
//! data of the GitHub API and of the container registry that the workflow
//! `usage` collects.
//!
//! ```sh
//! cargo xtask usage --input INPUT.json --output-dir DIR
//! ```
//!
//! # Input
//!
//! `--input` names a JSON object ([`Input`]) with no other fields: the
//! `period`, with the `month` as `YYYY-MM`, its `start` and `end` in seconds
//! since 1970, the same as text in `from` and `until`, and whether the month
//! is `partial`, as it is until it has ended; the `rate_limit` of the API
//! for the token, with the `remaining` requests before and after the
//! workflow read the data; the `repositories`, each with its runs (`id`,
//! `created_at`, `path` of the workflow, `event`, `run_attempt`) and the
//! jobs of every attempt of each run (`id`, `labels`, `runner_group_name`,
//! `runner_name`, `started_at`, `completed_at`), its artifacts
//! (`size_in_bytes`, `expired`) and its cache usage; and the `packages` of
//! the container registry, each with its tags and the blobs, the config and
//! the layers, of the manifest of each tag (`digest`, `size`).
//!
//! # Summary
//!
//! The command creates `DIR`, which must not exist, and writes
//! [`USAGE_FILE`] and [`SUMMARY_FILE`] into it. A run counts once, by its
//! ID, and only when it was created in the period, from `start` up to but
//! not including `end`; a job counts once, by its ID. The minutes of a job
//! are its seconds on a runner rounded up to whole minutes
//! ([`crate::record::minutes`]), which approximates the minutes that GitHub
//! bills; a job that ran on no runner takes none, and a job that has not
//! ended is listed and takes none. They are summed by the runner class of
//! the job ([`crate::record::runner_class`]) for each repository and for
//! all of them, and listed by workflow and by runner label. The storage is
//! the bytes of the artifacts that have not expired, of every repository,
//! and of the blobs of the packages, each blob counted once, against
//! [`STORAGE`]; the cache of each repository is set against [`CACHE`]. Each
//! item of [`THRESHOLDS`] is compared with its threshold, and the summary
//! names each item above its threshold in neutral words; no threshold makes
//! the command fail. The summary is the same in Markdown, with the text of
//! the data escaped.
//!
//! The command prints only the paths that it writes and exits with 0, or
//! with 2 after a usage error or a failure, which it reports on standard
//! error.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Arg, value_parser};
use serde::Deserialize;
use serde_json::{Value, json};

use crate::image;
use crate::record::{cell, minutes, runner_class};

/// The version of the format of the summary.
pub const FORMAT: u32 = 1;
/// The summary as JSON in the output directory.
pub const USAGE_FILE: &str = "usage.json";
/// The summary as Markdown in the output directory.
pub const SUMMARY_FILE: &str = "summary.md";
/// The storage against which the artifacts and the packages are set, in
/// bytes.
pub const STORAGE: u64 = 50_000_000_000;
/// The cache of a repository that GitHub keeps, in bytes.
pub const CACHE: u64 = 10_000_000_000;
/// The runner classes whose minutes the summary gives, in its order.
pub const CLASSES: [&str; 3] = ["standard hosted", "larger hosted", "self-hosted"];

/// What a threshold is compared with.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Measure {
    /// The minutes of a runner class in all the repositories.
    Minutes(&'static str),
    /// The bytes of the artifacts and the packages.
    Storage,
    /// The bytes of the cache of each repository.
    Cache,
}

/// The thresholds: what each is compared with, the threshold, which the
/// value must exceed to be above it, and why it is set there.
pub const THRESHOLDS: [(Measure, u64, &str); 5] = [
    (
        Measure::Minutes("larger hosted"),
        0,
        "the CI uses larger runners only as a fallback that was measured first",
    ),
    (
        Measure::Minutes("self-hosted"),
        0,
        "the CI uses no self-hosted runner",
    ),
    (
        Measure::Minutes("standard hosted"),
        40_000,
        "a sign of unusual growth: about ten times a month at the rate of early November 2026, as standard runners of public repositories are not billed",
    ),
    (
        Measure::Storage,
        40_000_000_000,
        "80% of the storage of 50 GB",
    ),
    (
        Measure::Cache,
        8_000_000_000,
        "80% of the cache of 10 GB of a repository",
    ),
];

/// The data of a month, as `jq` writes it.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Input {
    pub period: Period,
    pub rate_limit: RateLimit,
    pub repositories: Vec<Repository>,
    pub packages: Vec<Package>,
}

/// The period of the summary.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Period {
    pub month: String,
    pub start: u64,
    pub end: u64,
    pub from: String,
    pub until: String,
    pub partial: bool,
}

/// The rate limit of the API for the token of the workflow.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RateLimit {
    pub limit: u64,
    pub remaining_before: u64,
    pub remaining_after: u64,
}

/// The data of one repository.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Repository {
    pub repository: String,
    pub runs: Vec<Run>,
    pub artifacts: Vec<Artifact>,
    pub cache: Cache,
}

/// A workflow run with the jobs of all its attempts.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Run {
    pub id: u64,
    pub created_at: u64,
    pub path: String,
    pub event: String,
    pub run_attempt: u64,
    pub jobs: Vec<Job>,
}

/// A job of a run.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Job {
    pub id: u64,
    pub labels: Vec<String>,
    pub runner_group_name: Option<String>,
    pub runner_name: Option<String>,
    pub started_at: Option<u64>,
    pub completed_at: Option<u64>,
}

/// An artifact of a repository.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Artifact {
    pub size_in_bytes: u64,
    pub expired: bool,
}

/// The cache usage of a repository.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Cache {
    pub active_caches_count: u64,
    pub active_caches_size_in_bytes: u64,
}

/// A package of the container registry.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Package {
    pub name: String,
    pub tags: Vec<Tag>,
}

/// A tag of a package with the blobs of its manifest.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Tag {
    pub tag: String,
    pub blobs: Vec<Blob>,
}

/// A blob of a manifest: its config or one of its layers.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Blob {
    pub digest: String,
    pub size: u64,
}

/// The minutes of the classes of [`CLASSES`], as a JSON object.
fn by_class(minutes: &BTreeMap<&str, u64>) -> Value {
    let pairs = CLASSES.map(|class| {
        (
            class.to_string(),
            json!(minutes.get(class).copied().unwrap_or(0)),
        )
    });
    Value::Object(pairs.into_iter().collect())
}

/// The summary of `input` as JSON.
pub fn usage(input: &Input) -> Value {
    let period = &input.period;
    let mut all_minutes: BTreeMap<&str, u64> = BTreeMap::new();
    let mut artifact_bytes = 0;
    let mut repositories = Vec::new();
    for repository in &input.repositories {
        let mut seen_runs = BTreeSet::new();
        let mut seen_jobs = BTreeSet::new();
        let mut minutes_by_class: BTreeMap<&str, u64> = BTreeMap::new();
        let mut by_workflow: BTreeMap<&str, (u64, u64)> = BTreeMap::new();
        let mut by_label: BTreeMap<(String, &str), u64> = BTreeMap::new();
        let mut unfinished = Vec::new();
        let mut jobs = 0;
        let runs = (repository.runs.iter())
            .filter(|run| period.start <= run.created_at && run.created_at < period.end)
            .filter(|run| seen_runs.insert(run.id));
        for run in runs {
            let workflow = by_workflow.entry(run.path.as_str()).or_default();
            workflow.0 += 1;
            for job in run.jobs.iter().filter(|job| seen_jobs.insert(job.id)) {
                jobs += 1;
                let class = runner_class(
                    job.runner_name.as_deref(),
                    &job.labels,
                    job.runner_group_name.as_deref(),
                );
                if class == "none" {
                    continue;
                }
                let Some((start, end)) = job.started_at.zip(job.completed_at) else {
                    unfinished.push(json!({"run": run.id, "job": job.id}));
                    continue;
                };
                let used = minutes(end.saturating_sub(start));
                *minutes_by_class.entry(class).or_default() += used;
                *all_minutes.entry(class).or_default() += used;
                workflow.1 += used;
                *by_label.entry((job.labels.join(", "), class)).or_default() += used;
            }
        }
        let unexpired = repository
            .artifacts
            .iter()
            .filter(|artifact| !artifact.expired);
        let bytes: u64 = unexpired
            .clone()
            .map(|artifact| artifact.size_in_bytes)
            .sum();
        artifact_bytes += bytes;
        repositories.push(json!({
            "repository": repository.repository,
            "runs": seen_runs.len(),
            "jobs": jobs,
            "minutes": by_class(&minutes_by_class),
            "unfinished_jobs": unfinished,
            "by_workflow": (by_workflow.iter())
                .map(|(path, (runs, minutes))| json!({"path": path, "runs": runs, "minutes": minutes}))
                .collect::<Vec<_>>(),
            "by_label": (by_label.iter())
                .map(|((labels, class), minutes)| json!({"labels": labels, "class": class, "minutes": minutes}))
                .collect::<Vec<_>>(),
            "artifacts": unexpired.count(),
            "artifact_bytes": bytes,
            "cache_entries": repository.cache.active_caches_count,
            "cache_bytes": repository.cache.active_caches_size_in_bytes,
            "cache_limit": CACHE,
        }));
    }
    let mut blobs: BTreeMap<&str, u64> = BTreeMap::new();
    let mut packages = Vec::new();
    for package in &input.packages {
        let mut own: BTreeMap<&str, u64> = BTreeMap::new();
        for blob in package.tags.iter().flat_map(|tag| &tag.blobs) {
            own.insert(&blob.digest, blob.size);
            blobs.insert(&blob.digest, blob.size);
        }
        packages.push(json!({
            "name": package.name,
            "tags": package.tags.iter().map(|tag| &tag.tag).collect::<Vec<_>>(),
            "blobs": own.len(),
            "bytes": own.values().sum::<u64>(),
        }));
    }
    let package_bytes: u64 = blobs.values().sum();
    let storage = artifact_bytes + package_bytes;
    let mut thresholds = Vec::new();
    for (measure, threshold, basis) in THRESHOLDS {
        let mut item = |name: String, value: u64| {
            thresholds.push(json!({
                "item": name,
                "value": value,
                "threshold": threshold,
                "above": value > threshold,
                "basis": basis,
            }));
        };
        match measure {
            Measure::Minutes(class) => item(
                format!("{class} minutes of all the repositories"),
                all_minutes.get(class).copied().unwrap_or(0),
            ),
            Measure::Storage => item(
                "bytes of the artifacts and the packages".to_string(),
                storage,
            ),
            Measure::Cache => {
                for repository in &input.repositories {
                    item(
                        format!("bytes of the cache of {}", repository.repository),
                        repository.cache.active_caches_size_in_bytes,
                    );
                }
            }
        }
    }
    json!({
        "format": FORMAT,
        "period": {
            "month": period.month,
            "start": period.start,
            "end": period.end,
            "from": period.from,
            "until": period.until,
            "partial": period.partial,
        },
        "rate_limit": {
            "limit": input.rate_limit.limit,
            "remaining_before": input.rate_limit.remaining_before,
            "remaining_after": input.rate_limit.remaining_after,
        },
        "minutes": by_class(&all_minutes),
        "repositories": repositories,
        "artifact_bytes": artifact_bytes,
        "packages": packages,
        "package_bytes": package_bytes,
        "storage_bytes": storage,
        "storage_limit": STORAGE,
        "thresholds": thresholds,
    })
}

/// The Markdown summary of `usage`.
pub fn summary(usage: &Value) -> String {
    let text = |value: &Value| match value {
        Value::String(text) => cell(text),
        Value::Null => "-".to_string(),
        other => cell(&other.to_string()),
    };
    let list = |value: &Value| value.as_array().cloned().unwrap_or_default();
    let period = &usage["period"];
    let mut out = format!(
        "## CI usage of {}\n\nThe period runs from {} to {}",
        text(&period["month"]),
        text(&period["from"]),
        text(&period["until"]),
    );
    if period["partial"] == true {
        out.push_str(", the time of this summary, before the end of the month");
    }
    out.push_str(&format!(
        ". Minutes are the seconds of each job on its runner rounded up to whole \
         minutes, job by job, which approximates the minutes that GitHub bills; a \
         job that ran on no runner takes none. The API allowed {} requests an hour; \
         {} remained before the data was read and {} after.\n\n",
        usage["rate_limit"]["limit"],
        usage["rate_limit"]["remaining_before"],
        usage["rate_limit"]["remaining_after"],
    ));
    out.push_str("### Minutes by runner class\n\n");
    out.push_str("| Repository | Runs | Jobs | Standard hosted | Larger hosted | Self-hosted | Unfinished jobs |\n");
    out.push_str("| --- | ---: | ---: | ---: | ---: | ---: | ---: |\n");
    let classes = |minutes: &Value| CLASSES.map(|class| minutes[class].to_string()).join(" | ");
    for repository in list(&usage["repositories"]) {
        out.push_str(&format!(
            "| {} | {} | {} | {} | {} |\n",
            text(&repository["repository"]),
            repository["runs"],
            repository["jobs"],
            classes(&repository["minutes"]),
            list(&repository["unfinished_jobs"]).len(),
        ));
    }
    out.push_str(&format!(
        "| All | | | {} | |\n\n",
        classes(&usage["minutes"])
    ));
    out.push_str("### Minutes by workflow\n\n| Repository | Workflow | Runs | Minutes |\n");
    out.push_str("| --- | --- | ---: | ---: |\n");
    for repository in list(&usage["repositories"]) {
        for workflow in list(&repository["by_workflow"]) {
            out.push_str(&format!(
                "| {} | {} | {} | {} |\n",
                text(&repository["repository"]),
                text(&workflow["path"]),
                workflow["runs"],
                workflow["minutes"],
            ));
        }
    }
    out.push_str("\n### Minutes by runner label\n\n| Repository | Labels | Class | Minutes |\n");
    out.push_str("| --- | --- | --- | ---: |\n");
    for repository in list(&usage["repositories"]) {
        for label in list(&repository["by_label"]) {
            out.push_str(&format!(
                "| {} | {} | {} | {} |\n",
                text(&repository["repository"]),
                text(&label["labels"]),
                text(&label["class"]),
                label["minutes"],
            ));
        }
    }
    out.push_str("\n### Storage\n\n| Item | Bytes |\n| --- | ---: |\n");
    for repository in list(&usage["repositories"]) {
        out.push_str(&format!(
            "| {} artifacts of {} that have not expired | {} |\n",
            repository["artifacts"],
            text(&repository["repository"]),
            repository["artifact_bytes"],
        ));
    }
    for package in list(&usage["packages"]) {
        out.push_str(&format!(
            "| The package {}, {} tags with {} blobs, each blob counted once | {} |\n",
            text(&package["name"]),
            list(&package["tags"]).len(),
            package["blobs"],
            package["bytes"],
        ));
    }
    out.push_str(&format!(
        "| All, each blob counted once, against {} | {} |\n\n",
        usage["storage_limit"], usage["storage_bytes"],
    ));
    out.push_str(
        "### Caches\n\n| Repository | Entries | Bytes | Limit |\n| --- | ---: | ---: | ---: |\n",
    );
    for repository in list(&usage["repositories"]) {
        out.push_str(&format!(
            "| {} | {} | {} | {} |\n",
            text(&repository["repository"]),
            repository["cache_entries"],
            repository["cache_bytes"],
            repository["cache_limit"],
        ));
    }
    out.push_str("\n### Thresholds\n\n| Item | Value | Threshold | Above | Basis |\n");
    out.push_str("| --- | ---: | ---: | --- | --- |\n");
    let thresholds = list(&usage["thresholds"]);
    for threshold in &thresholds {
        out.push_str(&format!(
            "| {} | {} | {} | {} | {} |\n",
            text(&threshold["item"]),
            threshold["value"],
            threshold["threshold"],
            if threshold["above"] == true {
                "yes"
            } else {
                "no"
            },
            text(&threshold["basis"]),
        ));
    }
    let above: Vec<&Value> = thresholds
        .iter()
        .filter(|threshold| threshold["above"] == true)
        .collect();
    out.push('\n');
    if above.is_empty() {
        out.push_str("No item is above its threshold.\n");
    }
    for threshold in above {
        out.push_str(&format!(
            "The {} are above their threshold.\n",
            text(&threshold["item"])
        ));
    }
    out
}

/// The command line of `cargo xtask usage`.
fn cli() -> clap::Command {
    let about = (crate::COMMANDS.iter())
        .find(|command| command.name == "usage")
        .map_or("", |command| command.about);
    let path = |name: &'static str, help: &'static str| {
        Arg::new(name)
            .long(name)
            .value_name("PATH")
            .help(help)
            .required(true)
            .value_parser(value_parser!(PathBuf))
    };
    clap::Command::new("usage")
        .bin_name("cargo xtask usage")
        .no_binary_name(true)
        .about(about)
        .arg(path("input", "The data of the month, as jq writes it"))
        .arg(path("output-dir", "New directory for the summary"))
}

/// Reads the input at `input` and writes the summary into the new
/// directory `output`; the files that it wrote.
pub fn write(input: &Path, output: &Path) -> Result<[PathBuf; 2], String> {
    let text = fs::read_to_string(input)
        .map_err(|error| format!("cannot read {}: {error}", input.display()))?;
    let data: Input =
        serde_json::from_str(&text).map_err(|error| format!("{}: {error}", input.display()))?;
    if data.period.start >= data.period.end {
        return Err(format!(
            "{}: the period ends at {}, not after its start at {}",
            input.display(),
            data.period.end,
            data.period.start
        ));
    }
    let usage = usage(&data);
    image::create_new(output)?;
    let files = [output.join(USAGE_FILE), output.join(SUMMARY_FILE)];
    for (file, text) in files.iter().zip([format!("{usage:#}\n"), summary(&usage)]) {
        fs::write(file, text)
            .map_err(|error| format!("cannot write {}: {error}", file.display()))?;
    }
    Ok(files)
}

/// Entry point of `cargo xtask usage`.
pub fn command(args: &[&str]) -> ExitCode {
    let matches = match cli().try_get_matches_from(args) {
        Ok(matches) => matches,
        Err(error) => {
            let _ = error.print();
            return ExitCode::from(u8::try_from(error.exit_code()).unwrap_or(2));
        }
    };
    let path = |name: &str| matches.get_one::<PathBuf>(name).expect("required");
    match write(path("input"), path("output-dir")) {
        Ok(files) => {
            for file in files {
                println!("{}", file.display());
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!(
                "cargo xtask usage failed: {}",
                crate::suite::printable(&error)
            );
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests;
