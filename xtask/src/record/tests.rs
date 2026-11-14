//! The record of two runs of krepi read back from the GitHub API, and of
//! runs written for each rule: the line, the runner class, the minutes, the
//! limits and `TIMEOUT`, the 80% mark, the retention, the run of the record
//! workflow, the summary, the input of a manual run and the command.
//!
//! The two input fixtures are the output of the `jq` program of the
//! workflow `run record` on `gh api repos/casxi-lab/krepi/actions/runs/<id>`,
//! `.../attempts/1/jobs` and `repos/casxi-lab/krepi/check-runs/<job>/annotations`,
//! read on 2026-11-09: `input-42556330562.json`, the check of a push to
//! `main`, and `input-42549850982.json`, a run of the formal workflow on a
//! pull request that a later push cancelled. The two record fixtures are
//! records of format 1 that the record workflow uploaded on 2026-11-09 as
//! the artifacts `run-record-42610570435-1` and `run-record-42611144263-1`:
//! the runs of the pull request line and of the full line of a pull request
//! in which the job `image` and the job `full image` ran past a limit of one
//! minute.

use super::*;
use crate::scratch::Scratch;

const MAIN: &str = include_str!("fixtures/input-42556330562.json");
const CANCELLED: &str = include_str!("fixtures/input-42549850982.json");
const PROBE: &str = include_str!("fixtures/record-42610570435.json");
const PROBE_FULL: &str = include_str!("fixtures/record-42611144263.json");

/// The jobs and limits of the formal workflow at the head of the cancelled
/// run, as far as the record reads them.
const FORMAL: &str = "\
name: formal
on: pull_request
jobs:
  gate:
    name: formal run
    timeout-minutes: 195
  leanchecker:
    name: leanchecker ${{ matrix.mode }}
    timeout-minutes: 120
  comparator:
    name: lake comparator
    timeout-minutes: 30
";

fn input(text: &str) -> Input {
    serde_json::from_str(text).expect("the fixture reads")
}

/// A job that ran on a standard runner for `seconds` from 1000.
fn job(name: &str, conclusion: &str, seconds: u64) -> JobData {
    JobData {
        id: 1,
        name: name.to_string(),
        conclusion: Some(conclusion.to_string()),
        labels: vec!["ubuntu-24.04-arm".to_string()],
        runner_group_name: Some("GitHub Actions".to_string()),
        runner_name: Some("GitHub Actions 1".to_string()),
        started_at: Some(1000),
        completed_at: Some(1000 + seconds),
        annotations: Vec::new(),
    }
}

/// A run of `workflow` on `event` and `branch` with `jobs`.
fn run(workflow: &str, event: &str, branch: &str, jobs: Vec<JobData>) -> Input {
    Input {
        run: RunData {
            id: 7,
            attempt: 1,
            workflow: workflow.to_string(),
            path: format!(".github/workflows/{workflow}.yml"),
            event: event.to_string(),
            head_branch: Some(branch.to_string()),
            head_sha: "0".repeat(40),
            conclusion: Some("failure".to_string()),
        },
        jobs,
    }
}

#[test]
fn a_main_run_of_the_check_is_recorded() {
    // The check workflow of that commit sets no limit.
    let workflow = "on: push\njobs:\n  check:\n    name: cargo xtask check\n    runs-on: x\n";
    let limits = limits(workflow).expect("the workflow reads");
    let record = record(&input(MAIN), Some(&limits), None);
    assert_eq!(
        record,
        json!({
            "format": 2,
            "run": {
                "id": 42556330562u64,
                "attempt": 1,
                "workflow": "check",
                "path": ".github/workflows/check.yml",
                "event": "push",
                "head_branch": "main",
                "head_sha": "e88909c63ae9696640047df39e0d376ad744037b",
                "conclusion": "success",
                "line": "main",
            },
            "workflow_read": true,
            "wall_seconds": 193,
            "minutes": 4,
            "limit_seconds": null,
            "over_80_percent": null,
            "over": null,
            "retention_days": 90,
            "jobs": [{
                "id": 128962751974u64,
                "name": "cargo xtask check",
                "runner": "standard hosted",
                "labels": ["ubuntu-24.04-arm"],
                "runner_group": "GitHub Actions",
                "started_at": 1794194736u64,
                "completed_at": 1794194929u64,
                "seconds": 193,
                "minutes": 4,
                "timeout_minutes": 360,
                "conclusion": "success",
                "result": "success",
                "timeout": null,
                "annotations": [],
            }],
            "record_run": null,
        })
    );
}

#[test]
fn a_cancelled_pull_request_run_is_recorded() {
    let limits = limits(FORMAL).expect("the workflow reads");
    let record = record(&input(CANCELLED), Some(&limits), None);
    assert_eq!(record["run"]["line"], "none");
    assert_eq!(record["run"]["conclusion"], "cancelled");
    assert_eq!(record["retention_days"], 30);
    // The gate ran from 02:14:54 to 02:36:45; the skipped jobs ran on no
    // runner, take no minutes and do not count for the wall clock.
    assert_eq!(record["wall_seconds"], 1311);
    assert_eq!(record["minutes"], 22);
    let jobs = record["jobs"].as_array().expect("the jobs");
    let fields = |job: &Value| {
        let keys = [
            "name",
            "runner",
            "seconds",
            "minutes",
            "timeout_minutes",
            "result",
        ];
        keys.map(|key| job[key].clone())
    };
    assert_eq!(
        jobs.iter().map(fields).collect::<Vec<_>>(),
        [
            [
                json!("formal run"),
                json!("standard hosted"),
                json!(1311),
                json!(22),
                json!(195),
                json!("cancelled")
            ],
            [
                json!("lake comparator"),
                json!("none"),
                json!(null),
                json!(0),
                json!(30),
                json!("skipped")
            ],
            [
                json!("leanchecker ${{ matrix.mode }}"),
                json!("none"),
                json!(null),
                json!(0),
                json!(120),
                json!("skipped"),
            ],
        ]
    );
    assert_eq!(
        jobs[0]["annotations"],
        json!([{
            "level": "failure",
            "title": "",
            "message": "Canceling since a higher priority waiting request for formal-gate-21 exists",
        }])
    );
    // Without the workflow, no job has a known limit.
    let unread = super::record(&input(CANCELLED), None, None);
    assert_eq!(unread["workflow_read"], false);
    assert_eq!(unread["jobs"][0]["timeout_minutes"], Value::Null);
    assert_eq!(unread["jobs"][0]["result"], "cancelled");
}

#[test]
fn a_job_at_its_limit_that_did_not_succeed_is_a_timeout() {
    let workflow = "jobs:\n  check:\n    name: cargo xtask check\n    timeout-minutes: 15\n  \
                    suite:\n    timeout-minutes: 10\n  summary:\n    name: check summary\n    \
                    timeout-minutes: ${{ 3 }}\n";
    let limits = limits(workflow).expect("the workflow reads");
    assert_eq!(
        limits,
        [
            ("cargo xtask check".to_string(), Some(15)),
            ("suite".to_string(), Some(10)),
            ("check summary".to_string(), None),
        ]
    );
    let result = |name: &str, conclusion: &str, seconds: u64| {
        let input = run(
            "check",
            "pull_request",
            "topic",
            vec![job(name, conclusion, seconds)],
        );
        super::record(&input, Some(&limits), None)["jobs"][0]["result"].clone()
    };
    assert_eq!(result("cargo xtask check", "failure", 900), "TIMEOUT");
    assert_eq!(result("cargo xtask check", "cancelled", 905), "TIMEOUT");
    assert_eq!(result("cargo xtask check", "failure", 899), "failure");
    assert_eq!(result("cargo xtask check", "success", 900), "success");
    // A job of a matrix takes the limit of its job.
    assert_eq!(result("suite (a, b)", "failure", 600), "TIMEOUT");
    assert_eq!(result("suites", "failure", 600), "failure");
    // A limit that is an expression is unknown.
    assert_eq!(result("check summary", "failure", 3600), "failure");
    assert!(super::limits("jobs: []\n").is_err());
    assert!(super::limits("jobs: [\n").is_err());
}

/// The record `text` of format 1 with the input and the limits from which
/// it was written: the run, each job with a runner name when it ran on a
/// runner, and the limit that it recorded for each job.
fn rebuilt(text: &str) -> (Value, Input, Vec<(String, Option<u64>)>) {
    let written: Value = serde_json::from_str(text).expect("the record is JSON");
    let string = |value: &Value| value.as_str().map(str::to_string);
    let number = |value: &Value| value.as_u64().expect("a number");
    let run = &written["run"];
    let jobs = written["jobs"].as_array().expect("the jobs");
    let input = Input {
        run: RunData {
            id: number(&run["id"]),
            attempt: number(&run["attempt"]),
            workflow: string(&run["workflow"]).expect("the workflow"),
            path: string(&run["path"]).expect("the path"),
            event: string(&run["event"]).expect("the event"),
            head_branch: string(&run["head_branch"]),
            head_sha: string(&run["head_sha"]).expect("the head"),
            conclusion: string(&run["conclusion"]),
        },
        jobs: (jobs.iter())
            .map(|job| JobData {
                id: number(&job["id"]),
                name: string(&job["name"]).expect("the name"),
                conclusion: string(&job["conclusion"]),
                labels: (job["labels"].as_array().into_iter().flatten())
                    .filter_map(string)
                    .collect(),
                runner_group_name: string(&job["runner_group"]),
                runner_name: (job["runner"] != "none").then(|| "GitHub Actions 1".to_string()),
                started_at: job["started_at"].as_u64(),
                completed_at: job["completed_at"].as_u64(),
                annotations: (job["annotations"].as_array().into_iter().flatten())
                    .map(|note| Annotation {
                        level: string(&note["level"]).expect("the level"),
                        title: string(&note["title"]),
                        message: string(&note["message"]).expect("the message"),
                    })
                    .collect(),
            })
            .collect(),
    };
    let limits = (jobs.iter())
        .map(|job| {
            let name = string(&job["name"]).expect("the name");
            (name, job["timeout_minutes"].as_u64())
        })
        .collect();
    (written, input, limits)
}

#[test]
fn the_probe_records_stay_timeout_under_the_deadline_rule() {
    let results = [
        (
            PROBE,
            vec![
                ("image", "TIMEOUT"),
                ("cargo xtask check", "success"),
                ("suite", "skipped"),
                ("check summary", "failure"),
            ],
        ),
        (
            PROBE_FULL,
            vec![
                ("full head contains main", "success"),
                ("full cargo xtask check --slow", "success"),
                ("full image", "TIMEOUT"),
                ("full suite --slow", "skipped"),
            ],
        ),
    ];
    for (text, expected) in results {
        let (written, input, limits) = rebuilt(text);
        assert_eq!(written["format"], 1);
        let again = record(&input, Some(&limits), None);
        assert_eq!(again["format"], FORMAT);
        // Everything that the record of format 1 holds stays as it was,
        // apart from the run of the record workflow, which is not rebuilt.
        for key in [
            "run",
            "workflow_read",
            "wall_seconds",
            "minutes",
            "limit_seconds",
            "over_80_percent",
            "over",
            "retention_days",
        ] {
            assert_eq!(again[key], written[key], "{key}");
        }
        let jobs = again["jobs"].as_array().expect("the jobs");
        let old = written["jobs"].as_array().expect("the jobs");
        assert_eq!(jobs.len(), old.len());
        for ((job, old), (name, result)) in jobs.iter().zip(old).zip(&expected) {
            let mut job = job.clone();
            let reason = job.as_object_mut().and_then(|job| job.remove("timeout"));
            assert_eq!(job, *old);
            assert_eq!(
                (&job["name"], &job["result"]),
                (&json!(name), &json!(result))
            );
            // The job ran past its limit of one minute.
            let expected = if *result == "TIMEOUT" {
                assert_eq!(job["timeout_minutes"], 1);
                json!("limit")
            } else {
                Value::Null
            };
            assert_eq!(reason, Some(expected), "{name}");
        }
        assert!(!summary(&again).contains("deadline"));
    }
}

/// A failure annotation that reports the exit status `code`.
fn exit(code: &str) -> Annotation {
    Annotation {
        level: "failure".to_string(),
        title: Some(String::new()),
        message: format!("Process completed with exit code {code}."),
    }
}

#[test]
fn a_command_stopped_at_its_deadline_is_a_timeout() {
    assert_eq!(exit("124").message, DEADLINE_EXIT);
    let limits = [("image".to_string(), Some(5))];
    let judge = |conclusion: Option<&str>, seconds: u64, notes: Vec<Annotation>| {
        let mut job = job("image", "unused", seconds);
        job.conclusion = conclusion.map(str::to_string);
        job.annotations = notes;
        let record = record(
            &run("check", "pull_request", "topic", vec![job]),
            Some(&limits),
            None,
        );
        let job = &record["jobs"][0];
        (job["result"].clone(), job["timeout"].clone())
    };
    let timed_out = |reason: &str| (json!("TIMEOUT"), json!(reason));
    let kept = |conclusion: &str| (json!(conclusion), Value::Null);
    // Below its limit of 300 s.
    assert_eq!(
        judge(Some("failure"), 200, vec![exit("124")]),
        timed_out("deadline")
    );
    assert_eq!(
        judge(Some("cancelled"), 200, vec![exit("124")]),
        timed_out("deadline")
    );
    assert_eq!(judge(None, 200, vec![exit("124")]), timed_out("deadline"));
    assert_eq!(
        judge(Some("failure"), 200, vec![exit("1"), exit("124")]),
        timed_out("deadline")
    );
    assert_eq!(
        judge(Some("success"), 200, vec![exit("124")]),
        kept("success")
    );
    assert_eq!(
        judge(Some("failure"), 200, vec![exit("1")]),
        kept("failure")
    );
    assert_eq!(judge(Some("failure"), 200, vec![]), kept("failure"));
    for level in ["warning", "notice"] {
        let mut note = exit("124");
        note.level = level.to_string();
        assert_eq!(judge(Some("failure"), 200, vec![note]), kept("failure"));
    }
    let mut near = exit("1240");
    assert_eq!(
        judge(Some("failure"), 200, vec![near.clone()]),
        kept("failure")
    );
    near.message = "Process completed with exit code 124".to_string();
    assert_eq!(judge(Some("failure"), 200, vec![near]), kept("failure"));
    // At its limit the limit is the reason.
    assert_eq!(
        judge(Some("failure"), 300, vec![exit("124")]),
        timed_out("limit")
    );
    assert_eq!(judge(Some("cancelled"), 300, vec![]), timed_out("limit"));
    // The summary names a job stopped at its deadline.
    let mut stopped = job("image", "failure", 200);
    stopped.annotations = vec![exit("124")];
    let record = record(
        &run("check", "pull_request", "topic", vec![stopped]),
        Some(&limits),
        None,
    );
    assert_eq!(record["jobs"][0]["timeout_minutes"], 5);
    let summary = summary(&record);
    assert!(
        summary.ends_with(
            "| image | standard hosted | 200 | 4 | 5 | failure | TIMEOUT |\n\n\
             Job image was stopped at the deadline of its main command.\n"
        ),
        "{summary}"
    );
}

/// The rule of format 1: a job that ran at least as long as its limit and
/// did not succeed.
fn limit_rule(job: &JobData, seconds: Option<u64>, limit: Option<u64>) -> bool {
    let reached = seconds
        .zip(limit)
        .map(|(seconds, minutes)| seconds >= minutes * 60);
    reached == Some(true) && job.conclusion.as_deref() != Some("success")
}

#[test]
fn the_deadline_rule_contains_the_limit_rule() {
    let limit_note = Annotation {
        level: "failure".to_string(),
        title: Some(String::new()),
        message: "The job has exceeded the maximum execution time of 5m0s".to_string(),
    };
    let notes = [vec![], vec![exit("1")], vec![exit("124")], vec![limit_note]];
    let mut cases = 0;
    for limit in [None, Some(5)] {
        for seconds in [None, Some(0), Some(299), Some(300), Some(301)] {
            for conclusion in [Some("success"), Some("failure"), Some("cancelled"), None] {
                for notes in &notes {
                    let mut job = job("a", "unused", seconds.unwrap_or(0));
                    job.conclusion = conclusion.map(str::to_string);
                    job.annotations = notes.clone();
                    if seconds.is_none() {
                        job.runner_name = None;
                    }
                    assert_eq!(super::seconds(&job, None), seconds);
                    let old = limit_rule(&job, seconds, limit);
                    let new = timeout(&job, seconds, limit);
                    let case = format!("{limit:?} {seconds:?} {conclusion:?} {notes:?}");
                    // Every TIMEOUT of the old rule is one of the new rule,
                    // for the same reason.
                    if old {
                        assert_eq!(new, Some("limit"), "{case}");
                    }
                    // A TIMEOUT that only the new rule finds is a job that
                    // did not succeed and has the annotation of a deadline.
                    if new.is_some() && !old {
                        assert_eq!(new, Some("deadline"), "{case}");
                        assert_ne!(conclusion, Some("success"), "{case}");
                        assert!(notes.contains(&exit("124")), "{case}");
                    }
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 160);
}

#[test]
fn a_job_named_by_an_expression_takes_the_limit_of_its_template() {
    // The jobs of the formal workflows, as the record reads them and as the
    // committed files give them: a job of a matrix is named by its mode.
    let read = |path: &str| fs::read_to_string(crate::repo::root().join(path)).expect("a workflow");
    let committed = read(".github/workflows/formal.yml");
    let measure = read(".github/workflows/formal-measure.yml");
    let measured = |comparator: Option<u64>| {
        [
            ("leanchecker fresh", Some(120)),
            ("leanchecker prefix", Some(120)),
            ("leanchecker ${{ matrix.mode }}", Some(120)),
            ("leanchecker ", Some(120)),
            ("lake comparator", comparator),
            ("leanchecker", None),
            ("lake", None),
        ]
    };
    let gates = |gate: Option<u64>, before: Option<u64>| {
        [
            ("formal limits", before),
            ("formal run", gate),
            ("formal planned", None),
        ]
    };
    // The fixture has the measurement jobs beside the gate. The committed
    // workflow of the gate has the jobs of the limits and of the planned
    // targets: the qualification job has a limit of its own, the planned
    // targets take theirs from the first, an expression, which gives no
    // limit; the measurement jobs have a workflow of their own.
    for (text, names) in [
        (
            FORMAL,
            [&measured(Some(30))[..], &gates(Some(195), None)].concat(),
        ),
        (committed.as_str(), gates(Some(192), Some(5)).to_vec()),
        (measure.as_str(), measured(Some(45)).to_vec()),
    ] {
        let limits = limits(text).expect("the workflow reads");
        for (name, limit) in names {
            assert_eq!(job_limit(&limits, name), limit, "{name}");
        }
    }
    // The committed file runs the gate as parts: the shards take their
    // limits from the matrix, and the merge has a limit of its own.
    let committed = limits(&committed).expect("the workflow reads");
    let shard = ("formal shard ${{ matrix.name }}".to_string(), None);
    assert!(committed.contains(&shard));
    for (name, limit) in [("formal shard t", None), ("formal merge", Some(15))] {
        assert_eq!(job_limit(&committed, name), limit, "{name}");
    }
    let limit = |limits: &[(&str, Option<u64>)], name: &str| {
        let limits: Vec<(String, Option<u64>)> = (limits.iter())
            .map(|(display, limit)| (display.to_string(), *limit))
            .collect();
        job_limit(&limits, name)
    };
    // Each expression stands for some text, possibly empty, between the
    // literal text around it.
    let one = [("a ${{ x }} b", Some(1))];
    assert_eq!(limit(&one, "a 1 b"), Some(1));
    assert_eq!(limit(&one, "a  b"), Some(1));
    assert_eq!(limit(&one, "a 1 c"), None);
    assert_eq!(limit(&one, "b 1 b"), None);
    let two = [("x ${{ a }} y ${{ b }} z", Some(4))];
    assert_eq!(limit(&two, "x 1 y 2 z"), Some(4));
    assert_eq!(limit(&two, "x  y  z"), Some(4));
    assert_eq!(limit(&two, "x 1 z"), None);
    // The literal text at both ends must not overlap.
    let ends = [("ab${{ x }}ba", Some(6))];
    assert_eq!(limit(&ends, "abba"), Some(6));
    assert_eq!(limit(&ends, "aba"), None);
    // An exact name wins over a name with an expression.
    let exact = [("a ${{ x }}", Some(1)), ("a b", Some(2))];
    assert_eq!(limit(&exact, "a b"), Some(2));
    assert_eq!(limit(&exact, "a c"), Some(1));
    // Names with expressions that give different limits give none.
    let different = [("a ${{ x }}", Some(1)), ("${{ y }} b", Some(2))];
    assert_eq!(limit(&different, "a b"), None);
    assert_eq!(limit(&different, "a c"), Some(1));
    assert_eq!(limit(&different, "c b"), Some(2));
    let same = [("a ${{ x }}", Some(3)), ("${{ y }} b", Some(3))];
    assert_eq!(limit(&same, "a b"), Some(3));
    // A limit that is an expression is unknown here too.
    assert_eq!(limit(&[("a ${{ x }}", None)], "a b"), None);
    // GitHub adds the values of a matrix that the name does not use.
    let matrix = [("name ${{ github.event_name }}", Some(7))];
    assert_eq!(limit(&matrix, "name push (1, 2)"), Some(7));
    assert_eq!(limit(&matrix, "name push (1, (2))"), Some(7));
    assert_eq!(limit(&[("other", Some(8))], "name push (1, 2)"), None);
    // A `${{` without its end is text.
    let open = [("a ${{ b", Some(5))];
    assert_eq!(limit(&open, "a ${{ b"), Some(5));
    assert_eq!(limit(&open, "a c"), None);
    // The record of a job of the matrix of the formal workflow.
    let mut checked = job("leanchecker fresh", "failure", 7200);
    checked.annotations = vec![exit("124")];
    let input = run("formal", "pull_request", "topic", vec![checked]);
    let limits = limits(FORMAL).expect("the workflow reads");
    let record = record(&input, Some(&limits), None);
    assert_eq!(record["jobs"][0]["timeout_minutes"], 120);
    assert_eq!(record["jobs"][0]["timeout"], "limit");
}

#[test]
fn a_job_whose_limit_is_an_expression_takes_the_minutes_of_its_notice() {
    let workflow = "jobs:\n  shard:\n    name: formal shard ${{ matrix.name }}\n    \
                    timeout-minutes: ${{ matrix.job }}\n  merge:\n    name: formal merge\n    \
                    timeout-minutes: 15\n";
    let limits = limits(workflow).expect("the workflow reads");
    let note = |level: &str, title: Option<&str>, message: &str| Annotation {
        level: level.to_string(),
        title: title.map(str::to_string),
        message: message.to_string(),
    };
    let notice = |minutes: &str| note("notice", Some(LIMIT_NOTICE), minutes);
    // The limit and the result of the job `name` with the annotations
    // `notes`, which ran for 65 minutes and failed.
    let judged = |name: &str, notes: Vec<Annotation>, limits: Option<&[(String, Option<u64>)]>| {
        let mut ran = job(name, "failure", 3_900);
        ran.annotations = notes;
        let input = run("formal", "pull_request", "topic", vec![ran]);
        let record = super::record(&input, limits, None);
        let job = &record["jobs"][0];
        (job["timeout_minutes"].clone(), job["result"].clone())
    };
    let shard = "formal shard t";
    let read = Some(&limits[..]);
    assert_eq!(LIMIT_NOTICE, "timeout-minutes");
    // The notice gives the limit of the job, which ran as long as it or not.
    let found = judged(shard, vec![notice("65")], read);
    assert_eq!(found, (json!(65), json!("TIMEOUT")));
    let found = judged(shard, vec![notice("66")], read);
    assert_eq!(found, (json!(66), json!("failure")));
    // Without one, the limit stays unknown.
    assert_eq!(
        judged(shard, Vec::new(), read),
        (Value::Null, json!("failure"))
    );
    // Only the first notice of that title whose message is a whole number.
    let notes = vec![
        note("warning", Some(LIMIT_NOTICE), "1"),
        note("notice", Some("timeout"), "2"),
        note("notice", None, "3"),
        notice("65 minutes"),
        notice("-1"),
        notice("65"),
        notice("70"),
    ];
    assert_eq!(judged(shard, notes, read), (json!(65), json!("TIMEOUT")));
    // A literal limit wins, and without the workflow file no limit is known.
    let found = judged("formal merge", vec![notice("200")], read);
    assert_eq!(found, (json!(15), json!("TIMEOUT")));
    let found = judged(shard, vec![notice("65")], None);
    assert_eq!(found, (Value::Null, json!("failure")));
}

#[test]
fn a_run_over_80_percent_of_its_limit_is_marked() {
    let over = |workflow: &str, event: &str, seconds: u64| {
        let input = run(workflow, event, "topic", vec![job("a", "success", seconds)]);
        let record = record(&input, None, None);
        (record["over_80_percent"].clone(), record["over"].clone())
    };
    // The pull request line: 80% of 20 minutes is 960 s.
    assert_eq!(
        over("check", "pull_request", 960),
        (json!(false), json!([]))
    );
    assert_eq!(
        over("check", "pull_request", 961),
        (json!(true), json!(["run", "job a"]))
    );
    // The full line: 80% of 3,600 s is 2,880 s.
    assert_eq!(
        over("full", "pull_request", 2880),
        (json!(false), json!([]))
    );
    assert_eq!(
        over("full", "pull_request", 2881),
        (json!(true), json!(["run", "job a"]))
    );
    // The other lines have no limit.
    assert_eq!(over("check", "push", 5000), (Value::Null, Value::Null));
    assert_eq!(
        over("nightly", "schedule", 5000),
        (Value::Null, Value::Null)
    );
    // A run whose jobs are short but follow each other.
    let mut second = job("b", "success", 500);
    second.started_at = Some(1500);
    second.completed_at = Some(2000);
    let input = run(
        "check",
        "pull_request",
        "topic",
        vec![job("a", "success", 500), second],
    );
    let record = record(&input, None, None);
    assert_eq!(record["wall_seconds"], 1000);
    assert_eq!(record["over"], json!(["run"]));
    let summary = summary(&record);
    assert!(
        summary.contains(&format!("The run {OVER}: run.\n")),
        "{summary}"
    );
    assert!(
        !super::summary(&super::record(
            &run("check", "push", "main", vec![]),
            None,
            None
        ))
        .contains(OVER)
    );
}

#[test]
fn the_lines_runners_and_retention_follow_the_run() {
    for (workflow, event, expected) in [
        ("check", "pull_request", "pull request"),
        ("check", "push", "main"),
        ("full", "pull_request", "full"),
        ("nightly", "schedule", "nightly"),
        ("nightly", "workflow_dispatch", "nightly"),
        ("weekly", "schedule", "weekly"),
        ("formal", "push", "none"),
        ("run record", "workflow_run", "none"),
    ] {
        assert_eq!(line(workflow, event), expected, "{workflow} {event}");
    }
    let standard = job("a", "success", 1);
    assert_eq!(runner(&standard), "standard hosted");
    let mut larger = standard.clone();
    larger.runner_group_name = Some("Larger".to_string());
    assert_eq!(runner(&larger), "larger hosted");
    let mut own = standard.clone();
    own.labels.push("self-hosted".to_string());
    assert_eq!(runner(&own), "self-hosted");
    let mut none = standard;
    none.runner_name = None;
    assert_eq!(runner(&none), "none");
    assert_eq!(retention("pull_request", Some("main")), 30);
    assert_eq!(retention("pull_request", Some("topic")), 30);
    assert_eq!(retention("push", Some("main")), 90);
    assert_eq!(retention("schedule", Some("main")), 90);
    assert_eq!(retention("workflow_dispatch", Some("main")), 90);
    assert_eq!(retention("workflow_dispatch", Some("topic")), 30);
    assert_eq!(retention("push", None), 30);
    assert_eq!([0, 1, 60, 61, 193].map(minutes), [0, 1, 1, 2, 4]);
}

#[test]
fn the_run_of_the_record_counts_until_now() {
    let mut running = job("run record", "success", 0);
    running.conclusion = None;
    running.completed_at = None;
    let own = run("run record", "workflow_run", "main", vec![running]);
    let record = record(&input(MAIN), None, Some((&own, 1000 + 61)));
    // Each job of the record workflow's run has its runner class, seconds
    // and minutes, as the jobs of the recorded run do.
    assert_eq!(
        record["record_run"],
        json!({
            "id": 7,
            "attempt": 1,
            "wall_seconds": 61,
            "minutes": 2,
            "jobs": [{
                "id": 1,
                "name": "run record",
                "runner": "standard hosted",
                "labels": ["ubuntu-24.04-arm"],
                "runner_group": "GitHub Actions",
                "started_at": 1000,
                "completed_at": null,
                "seconds": 61,
                "minutes": 2,
            }],
        })
    );
    let summary = summary(&record);
    assert!(
        summary.ends_with(
            "\nThis record took 61 s of wall clock and 2 job minutes until its upload.\n\n\
             | Job of this record | Runner | Seconds | Minutes |\n\
             | --- | --- | ---: | ---: |\n\
             | run record | standard hosted | 61 | 2 |\n"
        ),
        "{summary}"
    );
}

#[test]
fn the_summary_escapes_the_text_of_the_run() {
    let input = run(
        "check",
        "pull_request",
        "topic",
        vec![job("a | b `c`\n::warning::d", "success", 30)],
    );
    let summary = summary(&record(&input, None, None));
    assert_eq!(
        summary,
        "## Run record\n\nRun 7 attempt 1 of the workflow check, line pull request, event \
         pull_request, conclusion failure: 30 s of wall clock, 1 job minutes; the record is kept \
         30 days.\n\nThe workflow file was not read, so no job has a known limit.\n\n\
         | Job | Runner | Seconds | Minutes | Limit (min) | Conclusion | Result |\n\
         | --- | --- | ---: | ---: | ---: | --- | --- |\n\
         | a \\| b 'c'\\\\n::warning::d | standard hosted | 30 | 1 | - | success | success |\n"
    );
    assert_eq!(
        summary
            .lines()
            .filter(|line| line.starts_with("::"))
            .count(),
        0
    );
}

#[test]
fn the_input_of_a_manual_run_is_a_run_id() {
    assert_eq!(run_id("42556330562"), Ok(42_556_330_562));
    assert_eq!(run_id("18446744073709551615"), Ok(u64::MAX));
    for wrong in [
        "", "0", "01", " 1", "1 ", "+1", "-1", "1e3", "abc", "1;true", "1\n2", "١",
    ] {
        assert!(run_id(wrong).is_err(), "{wrong:?}");
    }
    let error = run_id("18446744073709551616").expect_err("too large");
    assert!(error.ends_with("it is too large"), "{error}");
    assert_eq!(
        run_id("1\n2"),
        Err("\"1\\\\n2\" is not a run ID".to_string())
    );
    let id = cli()
        .try_get_matches_from(["--id", "12"])
        .expect("the option");
    assert_eq!(id.get_one::<String>("id").map(String::as_str), Some("12"));
    for wrong in [
        &["--id", "1", "--input", "a"][..],
        &["--input", "a"],
        &["--output", "a"],
        &["--input", "a", "--output", "b", "--own", "c"],
        &["--input", "a", "--output", "b", "--now", "1"],
    ] {
        let error = cli()
            .try_get_matches_from(wrong)
            .expect_err("a usage error");
        assert_eq!(error.exit_code(), 2, "{wrong:?}");
    }
}

#[test]
fn the_command_writes_the_record_and_the_summary_into_a_new_directory() {
    let scratch = Scratch::temporary("run-record");
    scratch.write("input.json", CANCELLED);
    scratch.write("formal.yml", FORMAL);
    scratch.write("own.json", MAIN);
    let file = |name: &str| scratch.0.join(name).to_string_lossy().into_owned();
    let (input_file, workflow, own, output) = (
        file("input.json"),
        file("formal.yml"),
        file("own.json"),
        file("out"),
    );
    let args = [
        "--input",
        &input_file,
        "--workflow",
        &workflow,
        "--own",
        &own,
        "--now",
        "1794194929",
        "--output",
        &output,
    ];
    let matches = cli().try_get_matches_from(args).expect("the options");
    assert_eq!(write(&matches), Ok(PathBuf::from(&output)));
    let text = fs::read_to_string(scratch.0.join("out").join(RECORD_FILE)).expect("the record");
    let written: Value = serde_json::from_str(&text).expect("JSON");
    let limits = limits(FORMAL).expect("the workflow reads");
    let expected = record(
        &input(CANCELLED),
        Some(&limits),
        Some((&input(MAIN), 1_794_194_929)),
    );
    assert_eq!(written, expected);
    assert_eq!(written["record_run"]["wall_seconds"], 193);
    let own_job = &written["record_run"]["jobs"][0];
    assert_eq!(own_job["runner"], "standard hosted");
    assert_eq!(
        (&own_job["seconds"], &own_job["minutes"]),
        (&json!(193), &json!(4))
    );
    let markdown =
        fs::read_to_string(scratch.0.join("out").join(SUMMARY_FILE)).expect("the summary");
    assert_eq!(markdown, summary(&expected));
    // The directory must be new.
    let again = write(&matches).expect_err("the directory exists");
    assert!(
        again.ends_with("exists; the directory must be new"),
        "{again}"
    );
    // An input of another form.
    scratch.write("input.json", "{\"run\": {}}");
    let other = format!("{output}-2");
    let args = ["--input", &input_file, "--output", &other];
    let matches = cli().try_get_matches_from(args).expect("the options");
    assert!(write(&matches).is_err_and(|error| error.contains("missing field")));
    // A field that the record does not read, such as an object with URLs.
    let extra = MAIN.replacen("\"attempt\"", "\"actor\": {}, \"attempt\"", 1);
    assert!(
        serde_json::from_str::<Input>(&extra)
            .is_err_and(|error| error.to_string().contains("unknown field `actor`"))
    );
}

#[test]
fn a_job_with_an_empty_runner_name_ran_on_no_runner() {
    let labels = vec!["ubuntu-24.04-arm".to_string()];
    for (name, group) in [(None, None), (Some(""), Some("")), (Some(""), None)] {
        assert_eq!(runner_class(name, &labels, group), "none");
        assert!(!ran_on_a_runner(name));
    }
    let standard = runner_class(Some("GitHub Actions 1"), &labels, Some("GitHub Actions"));
    assert_eq!(standard, "standard hosted");
    let larger = runner_class(Some("Larger 1"), &labels, Some("Larger"));
    assert_eq!(larger, "larger hosted");
    // A runner with a name but no group is not a standard runner.
    let unnamed_group = runner_class(Some("GitHub Actions 1"), &labels, Some(""));
    assert_eq!(unnamed_group, "larger hosted");
}

#[test]
fn the_record_gives_a_job_with_an_empty_runner_name_no_time() {
    let mut cancelled = job("formal run", "cancelled", 1);
    (cancelled.id, cancelled.started_at, cancelled.completed_at) = (2, Some(2000), Some(2001));
    cancelled.runner_name = Some(String::new());
    cancelled.runner_group_name = Some(String::new());
    let input = run(
        "formal",
        "push",
        "main",
        vec![job("a", "success", 61), cancelled],
    );
    let record = record(&input, None, None);
    assert_eq!(record["jobs"][1]["runner"], "none");
    assert_eq!(record["jobs"][1]["seconds"], json!(null));
    assert_eq!(record["jobs"][1]["minutes"], 0);
    assert_eq!(record["minutes"], 2);
    assert_eq!(record["wall_seconds"], 61);
}
