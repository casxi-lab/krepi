//! The disk of a run of the gate, as "Shard plan and disk guard" in
//! `docs/formal-verification.md` describes: the shard plan, with what runs
//! of CI measured for each part of the gate; the guard that refuses a run
//! without 1.5 times the disk peak of its parts free; the reading of the
//! free space every second; and the removal of what a run no longer needs.

use std::collections::BTreeSet;
use std::fs;
use std::io::{self, ErrorKind};
use std::path::{Path, PathBuf};
use std::sync::mpsc::{Receiver, RecvTimeoutError};
use std::thread::{self, JoinHandle};
use std::time::Duration;

use serde::Deserialize;
use serde_json::Value;

use super::registry::Target;
use super::{merge, qualify, run};

/// The schema of the shard plan.
pub const SCHEMA: u32 = 1;

/// The disk peak of a part without an entry, 8 GiB: more than ten times any
/// that a run of the gate has shown.
pub const DEFAULT_PEAK: u64 = 8 << 30;

/// How often a run reads the free space of its file system.
pub const SAMPLE: Duration = Duration::from_secs(1);

/// The shard plan, `verification/shards.json`.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
#[expect(dead_code, reason = "the schema is read before the plan")]
pub struct Plan {
    pub schema: u32,
    pub parts: Vec<Part>,
}

/// What a run of CI measured for a part of the gate, named by its unit: its
/// disk peak, the seconds and the cgroup memory peak of its receipt, and the
/// run and its commit.
#[derive(Debug, Clone, Deserialize)]
#[serde(deny_unknown_fields)]
#[expect(
    dead_code,
    reason = "the review reads the measurement, the guard the disk peak"
)]
pub struct Part {
    pub part: String,
    pub disk_peak: u64,
    pub seconds: f64,
    pub cgroup_memory_peak: u64,
    pub run_id: String,
    pub commit: String,
}

/// The shard plan `text` of schema [`SCHEMA`].
pub fn parse(text: &str) -> Result<Plan, String> {
    let not = |error: serde_json::Error| format!("not a shard plan: {error}");
    let value: Value = serde_json::from_str(text).map_err(not)?;
    let schema = &value["schema"];
    if schema != SCHEMA {
        return Err(format!("schema {schema} where {SCHEMA} is expected"));
    }
    serde_json::from_value(value).map_err(not)
}

/// The problems of the shard plan `text` at `path` with the registry's
/// `targets`: a plan that cannot be read, a part listed twice, and a part
/// that is neither the qualification nor a registered target; and the
/// shards of the formal targets that it has no entry for, which are no
/// problem.
pub fn check(path: &str, text: &str, targets: &[Target]) -> (Vec<String>, Vec<String>) {
    let plan = match parse(text) {
        Ok(plan) => plan,
        Err(error) => return (vec![format!("{path}: {error}")], Vec::new()),
    };
    let units = BTreeSet::from_iter(targets.iter().map(|t| run::target_unit(&t.name)));
    let (mut problems, mut parts) = (Vec::new(), BTreeSet::new());
    for part in plan.parts.iter().map(|entry| &entry.part) {
        let problem = if !parts.insert(part) {
            "is listed twice"
        } else if part != qualify::PHASE && !units.contains(part) {
            "is neither the qualification nor a registered target"
        } else {
            continue;
        };
        problems.push(format!("{path}: part {part} {problem}"));
    }
    let missing = merge::shards(targets).into_keys();
    (problems, missing.filter(|s| !parts.contains(s)).collect())
}

/// Why a run of `parts` that had `free` bytes available at its start does
/// not start: it needs 1.5 times the sum of their disk peaks in `plan`
/// free, the largest for a part listed twice and [`DEFAULT_PEAK`] for one
/// without an entry.
pub fn refusal(plan: &Plan, parts: &[String], free: u64) -> Option<String> {
    let peak = |part: &String| {
        let entries = plan.parts.iter().filter(|entry| entry.part == *part);
        entries.map(|e| e.disk_peak).max().unwrap_or(DEFAULT_PEAK)
    };
    let peak = parts.iter().map(peak).fold(0, u64::saturating_add);
    (u128::from(free) * 2 < u128::from(peak) * 3).then(|| {
        format!(
            "the file system of the run directory had {free} bytes available at the start, less than 1.5 times the disk peak of the parts of the run, {peak} bytes"
        )
    })
}

/// Starts a thread that reads the bytes available on the file system of
/// `path` with `free`, at once and then every `every` until `stop` is
/// disconnected, and returns the least reading, if it read any.
pub fn sample(
    path: PathBuf,
    free: fn(&Path) -> Option<u64>,
    every: Duration,
    stop: Receiver<()>,
) -> io::Result<JoinHandle<Option<u64>>> {
    thread::Builder::new()
        .name("free space".to_string())
        .spawn(move || {
            let mut least = None;
            loop {
                least = free(&path).into_iter().chain(least).min();
                if !matches!(stop.recv_timeout(every), Err(RecvTimeoutError::Timeout)) {
                    return least;
                }
            }
        })
}

/// Removes each of `paths` that exists, a directory with what it holds,
/// without following a symbolic link; one that cannot be removed is an
/// error.
pub fn remove(paths: &[PathBuf]) -> Result<(), String> {
    for path in paths {
        let removed = match fs::symlink_metadata(path) {
            Ok(data) if data.is_dir() => fs::remove_dir_all(path),
            Ok(_) => fs::remove_file(path),
            Err(error) => Err(error),
        };
        if let Err(error) = removed
            && error.kind() != ErrorKind::NotFound
        {
            return Err(format!("cannot remove {}: {error}", path.display()));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::os::unix::fs::PermissionsExt;
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::mpsc;
    use std::time::Instant;

    use super::*;
    use crate::formal::{process, registry};
    use crate::scratch::Scratch;

    /// The path of the plans of the tests.
    const PATH: &str = "P";

    /// A plan with an entry for each of `parts`, with its disk peak.
    fn plan(parts: &[(&str, u64)]) -> String {
        let parts = Vec::from_iter(parts.iter().map(|(part, peak)| {
            serde_json::json!({"part": part, "disk_peak": peak, "seconds": 1.0,
                "cgroup_memory_peak": 1, "run_id": "1", "commit": "c"})
        }));
        serde_json::json!({"schema": 1, "parts": parts}).to_string()
    }

    #[test]
    fn the_shard_plan_has_its_schema_and_parts_of_the_qualification_or_registered_targets() {
        let targets = registry::parse(
            r#"{"schema": 2, "targets": [{"name": "a"}, {"name": "p", "state": "planned"}]}"#,
        )
        .expect("a registry")
        .targets;
        let checked = |text: &str| check(PATH, text, &targets);
        let none = Vec::<String>::new();
        let entries = plan(&[("qualification", 1), ("target/a", 2)]);
        assert_eq!(checked(&entries), (none.clone(), none.clone()));
        let missing = vec!["target/a".to_string()];
        let entries = plan(&[("qualification", 1)]);
        assert_eq!(checked(&entries), (none.clone(), missing.clone()));
        // A planned target may have an entry, and is never missing.
        assert_eq!(checked(&plan(&[("target/p", 1)])), (none.clone(), missing));
        for (entries, problem) in [
            (
                plan(&[("target/x", 1)]),
                "P: part target/x is neither the qualification nor a registered target",
            ),
            (
                plan(&[("qualification", 1), ("qualification", 2)]),
                "P: part qualification is listed twice",
            ),
            (
                r#"{"schema": 2, "parts": []}"#.to_string(),
                "P: schema 2 where 1 is expected",
            ),
        ] {
            assert_eq!(checked(&entries).0, [problem], "{entries}");
        }
        let unknown = plan(&[("qualification", 1)]).replace("\"run_id\"", "\"run\"");
        for (text, error) in [(unknown.as_str(), "unknown field `run`"), ("{", "")] {
            let (problems, missing) = checked(text);
            assert_eq!(problems.len(), 1, "{text}");
            assert!(
                problems[0].starts_with("P: not a shard plan: ") && problems[0].contains(error),
                "{problems:?}"
            );
            assert_eq!(missing, none);
        }
    }

    #[test]
    fn a_run_needs_one_and_a_half_times_the_disk_peak_of_its_parts_free() {
        let read = |parts: &[(&str, u64)]| parse(&plan(parts)).expect("a plan");
        let plan = read(&[("qualification", 1_000), ("target/a", 2_000)]);
        let parts = |names: &[&str]| Vec::from_iter(names.iter().map(|name| name.to_string()));
        let text = |free: u64, peak: u64| {
            format!(
                "the file system of the run directory had {free} bytes available at the start, less than 1.5 times the disk peak of the parts of the run, {peak} bytes"
            )
        };
        let both = parts(&["qualification", "target/a"]);
        assert_eq!(refusal(&plan, &both, 4_499), Some(text(4_499, 3_000)));
        assert_eq!(refusal(&plan, &both, 4_500), None);
        // A part listed twice, which the check refuses, counts its largest.
        let twice = read(&[("qualification", 1_000), ("qualification", 2_000)]);
        let qualification = parts(&["qualification"]);
        assert_eq!(
            refusal(&twice, &qualification, 2_999),
            Some(text(2_999, 2_000))
        );
        assert_eq!(refusal(&twice, &qualification, 3_000), None);
        // A part without an entry counts the default peak.
        let three = parts(&["qualification", "target/a", "target/b"]);
        let peak = 3_000 + DEFAULT_PEAK;
        assert_eq!(refusal(&plan, &three, 4_500), Some(text(4_500, peak)));
        assert_eq!(refusal(&plan, &three, peak / 2 * 3), None);
        // The sum saturates, and the rule does not overflow.
        let large = read(&[("qualification", u64::MAX), ("target/a", 1)]);
        let refused = refusal(&large, &both, u64::MAX);
        assert_eq!(refused, Some(text(u64::MAX, u64::MAX)));
    }

    #[test]
    fn the_reading_of_the_free_space_keeps_the_least_until_it_is_stopped() {
        static READS: AtomicU64 = AtomicU64::new(0);
        fn free(_: &Path) -> Option<u64> {
            Some(100 - READS.fetch_add(1, Ordering::SeqCst).min(50))
        }
        let (stop, stopped) = mpsc::channel();
        let thread = sample(PathBuf::from("."), free, process::PAUSE, stopped);
        let thread = thread.expect("the thread starts");
        // A bound for a thread that hangs, not on how long a reading takes.
        let deadline = Instant::now() + Duration::from_secs(60);
        while READS.load(Ordering::SeqCst) < 3 {
            assert!(Instant::now() < deadline, "the thread reads no more");
            thread::sleep(process::PAUSE);
        }
        drop(stop);
        let least = thread.join().expect("the thread ends");
        let reads = READS.load(Ordering::SeqCst);
        assert_eq!(least, Some(100 - (reads - 1).min(50)));
    }

    #[test]
    fn remove_takes_files_and_directories_but_not_what_a_link_names() {
        let scratch = Scratch::new("remove");
        scratch.write("work/file", "file");
        scratch.write("work/nested/deep/file", "file");
        scratch.write("outside/kept", "kept");
        let (work, outside) = (scratch.0.join("work"), scratch.0.join("outside"));
        std::os::unix::fs::symlink(&outside, work.join("link")).expect("create a link");
        std::os::unix::fs::symlink(&outside, scratch.0.join("link")).expect("create a link");
        let paths = [
            work.join("file"),
            work.clone(),
            scratch.0.join("link"),
            scratch.0.join("missing"),
        ];
        assert_eq!(remove(&paths), Ok(()));
        assert!(!work.exists() && fs::symlink_metadata(scratch.0.join("link")).is_err());
        assert!(outside.join("kept").is_file());
        // A directory whose entries cannot be removed is an error.
        scratch.write("locked/file", "file");
        let locked = scratch.0.join("locked");
        let mode = |mode| fs::set_permissions(&locked, fs::Permissions::from_mode(mode));
        mode(0o500).expect("lock the directory");
        let error = remove(std::slice::from_ref(&locked)).expect_err("an error");
        mode(0o755).expect("let the scratch directory be removed");
        let start = format!("cannot remove {}: ", locked.display());
        assert!(error.starts_with(&start), "{error}");
    }
}
