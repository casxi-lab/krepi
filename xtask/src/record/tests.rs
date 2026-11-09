//! The record of two runs of krepi read back from the GitHub API, and of
//! runs written for each rule: the line, the runner class, the minutes, the
//! limits and `TIMEOUT`, the 80% mark, the retention, the run of the record
//! workflow, the summary, the input of a manual run and the command.
//!
//! The two fixtures are the output of the `jq` program of the workflow
//! `run record` on `gh api repos/casxi-lab/krepi/actions/runs/<id>`,
//! `.../attempts/1/jobs` and `repos/casxi-lab/krepi/check-runs/<job>/annotations`,
//! read on 2026-11-09: `input-42556330562.json`, the check of a push to
//! `main`, and `input-42549850982.json`, a run of the formal workflow on a
//! pull request that a later push cancelled.

use super::*;
use crate::scratch::Scratch;

const MAIN: &str = include_str!("fixtures/input-42556330562.json");
const CANCELLED: &str = include_str!("fixtures/input-42549850982.json");

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
            "format": 1,
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
    assert_eq!(
        record["record_run"],
        json!({"id": 7, "attempt": 1, "wall_seconds": 61, "minutes": 2})
    );
    let summary = summary(&record);
    assert!(
        summary.ends_with(
            "\nThis record took 61 s of wall clock and 2 job minutes until its upload.\n"
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
