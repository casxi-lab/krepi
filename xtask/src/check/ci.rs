//! Tests of the committed workflows: those of the CI lines, the pull request
//! line and the main line in `check.yml`, the full line, the nightly line
//! and the weekly line, of the record workflow, the retention of the
//! artifacts of every workflow, and the uploads of the jobs of the gate in
//! the formal workflows, the names of their parts and the steps that the two
//! workflows share. They run in the `test` step; the rules hold for these
//! files only and are not part of the workflows step.

use yaml_rust2::{Yaml, YamlLoader};

use crate::repo::Tree;

/// The workflow files of the lines and of the record workflow.
const LINES: [&str; 5] = [
    ".github/workflows/check.yml",
    ".github/workflows/full.yml",
    ".github/workflows/nightly.yml",
    ".github/workflows/weekly.yml",
    ".github/workflows/run-record.yml",
];
/// The longest chain of jobs of the pull request line, in minutes.
const PULL_REQUEST_LIMIT: i64 = 20;
/// The longest chain of jobs of the full line, in minutes.
const FULL_LIMIT: i64 = 60;
/// The label that starts the full line.
const FULL_LABEL: &str = "full-check";
/// The job that the rules of `main` require.
const REQUIRED: &str = "cargo xtask check";

/// The tracked workflow files with their YAML documents.
fn workflows() -> Vec<(String, Yaml)> {
    let tree = Tree::load(&crate::repo::root()).expect("the tracked files");
    (tree.texts())
        .filter(|(path, _)| crate::workflows::is_workflow(path))
        .map(|(path, text)| (path.to_string(), parse(text)))
        .collect()
}

fn parse(text: &str) -> Yaml {
    let mut documents = YamlLoader::load_from_str(text).expect("a workflow is YAML");
    documents.remove(0)
}

/// The document of the workflow file `path`.
fn workflow(path: &str) -> Yaml {
    let all = workflows();
    let found = all.into_iter().find(|(file, _)| file == path);
    found.unwrap_or_else(|| panic!("{path} is tracked")).1
}

/// The jobs of `document` by their keys.
fn jobs(document: &Yaml) -> Vec<(&str, &Yaml)> {
    let jobs = document["jobs"].as_hash().expect("the jobs");
    (jobs.iter())
        .map(|(key, job)| (key.as_str().expect("a job key"), job))
        .collect()
}

/// The keys of the jobs that `job` needs.
fn needs(job: &Yaml) -> Vec<&str> {
    match &job["needs"] {
        Yaml::String(one) => vec![one.as_str()],
        Yaml::Array(many) => many.iter().filter_map(Yaml::as_str).collect(),
        _ => Vec::new(),
    }
}

/// The sum of the `timeout-minutes` along the longest chain of `needs` in
/// `document`, or why there is none.
fn longest_chain(document: &Yaml) -> Result<i64, String> {
    let all = jobs(document);
    fn chain(all: &[(&str, &Yaml)], key: &str, depth: usize) -> Result<i64, String> {
        let (_, job) = (all.iter())
            .find(|(other, _)| *other == key)
            .ok_or_else(|| format!("no job {key}"))?;
        if depth > all.len() {
            return Err(format!("the needs of {key} form a cycle"));
        }
        let own = (job["timeout-minutes"].as_i64())
            .ok_or_else(|| format!("job {key} has no timeout-minutes"))?;
        let mut longest = 0;
        for need in needs(job) {
            longest = longest.max(chain(all, need, depth + 1)?);
        }
        Ok(own + longest)
    }
    let mut longest = 0;
    for (key, _) in &all {
        longest = longest.max(chain(&all, key, 0)?);
    }
    Ok(longest)
}

/// The steps of every job of `document`.
fn steps(document: &Yaml) -> Vec<&Yaml> {
    (jobs(document).into_iter())
        .flat_map(|(_, job)| job["steps"].as_vec().into_iter().flatten())
        .collect()
}

/// The scripts of the steps of `document`.
fn scripts(document: &Yaml) -> Vec<&str> {
    (steps(document).into_iter())
        .filter_map(|step| step["run"].as_str())
        .collect()
}

#[test]
fn every_job_of_the_lines_has_a_limit_and_the_chains_keep_theirs() {
    for path in LINES {
        let document = workflow(path);
        for (key, job) in jobs(&document) {
            let minutes = job["timeout-minutes"].as_i64();
            assert!(
                minutes.is_some_and(|minutes| minutes > 0),
                "{path}: job {key}"
            );
        }
    }
    let pull_request = longest_chain(&workflow(LINES[0])).expect("the pull request line");
    assert!(pull_request <= PULL_REQUEST_LIMIT, "{pull_request} minutes");
    let full = longest_chain(&workflow(LINES[1])).expect("the full line");
    assert!(full <= FULL_LIMIT, "{full} minutes");
    // The chain follows `needs`, through a list and through a single job.
    let chained = parse(
        "jobs:\n  a:\n    timeout-minutes: 15\n  b:\n    timeout-minutes: 5\n  \
         c:\n    needs: b\n    timeout-minutes: 12\n  d:\n    needs: [a, c]\n    \
         timeout-minutes: 3\n",
    );
    assert_eq!(longest_chain(&chained), Ok(20));
    let missing = parse("jobs:\n  a:\n    timeout-minutes: 1\n  b:\n    needs: a\n");
    assert_eq!(
        longest_chain(&missing),
        Err("job b has no timeout-minutes".to_string())
    );
    let unknown = parse("jobs:\n  a:\n    needs: z\n    timeout-minutes: 1\n");
    assert_eq!(longest_chain(&unknown), Err("no job z".to_string()));
}

/// The problems of the full line in `document`: its only trigger must be
/// `pull_request` of the type `labeled`, and every job must require the
/// label [`FULL_LABEL`].
fn full_line_problems(document: &Yaml) -> Vec<String> {
    let mut problems = Vec::new();
    let on = document["on"].as_hash();
    let events: Vec<&str> = (on.into_iter().flatten())
        .filter_map(|(event, _)| event.as_str())
        .collect();
    if events != ["pull_request"] {
        problems.push(format!(
            "the triggers are {events:?}, not pull_request alone"
        ));
    }
    let types = &document["on"]["pull_request"]["types"];
    if types
        .as_vec()
        .map(|types| types.iter().filter_map(Yaml::as_str).collect::<Vec<_>>())
        != Some(vec!["labeled"])
    {
        problems.push("the pull request types are not labeled alone".to_string());
    }
    let condition = format!("github.event.label.name == '{FULL_LABEL}'");
    for (key, job) in jobs(document) {
        let holds = job["if"].as_str().is_some_and(|text| {
            let text = text.trim();
            let text = (text.strip_prefix("${{"))
                .and_then(|text| text.strip_suffix("}}"))
                .unwrap_or(text);
            text.trim() == condition
        });
        if !holds {
            problems.push(format!("job {key} does not require the label {FULL_LABEL}"));
        }
    }
    problems
}

#[test]
fn the_full_line_runs_only_on_its_label() {
    assert_eq!(
        full_line_problems(&workflow(LINES[1])),
        Vec::<String>::new()
    );
    let good = "on:\n  pull_request:\n    types: [labeled]\njobs:\n  a:\n    \
                if: github.event.label.name == 'full-check'\n  b:\n    \
                if: ${{ github.event.label.name == 'full-check' }}\n";
    assert_eq!(full_line_problems(&parse(good)), Vec::<String>::new());
    let cases = [
        (
            good.replace("[labeled]", "[labeled, synchronize]"),
            "the pull request types are not labeled alone",
        ),
        (
            good.replace("    types: [labeled]\n", ""),
            "the pull request types are not labeled alone",
        ),
        (
            good.replace("on:\n", "on:\n  workflow_dispatch:\n"),
            "the triggers are [\"workflow_dispatch\", \"pull_request\"], not pull_request alone",
        ),
        (
            good.replace(
                "    if: github.event.label.name == 'full-check'\n",
                "    runs-on: x\n",
            ),
            "job a does not require the label full-check",
        ),
        (
            good.replace("== 'full-check' }}", "== 'other' }}"),
            "job b does not require the label full-check",
        ),
        (
            good.replace(
                "if: github.event.label.name == 'full-check'\n",
                "if: github.event.label.name == 'full-check' || always()\n",
            ),
            "job a does not require the label full-check",
        ),
    ];
    for (text, problem) in cases {
        assert_eq!(full_line_problems(&parse(&text)), [problem], "{text}");
    }
}

#[test]
fn only_the_full_and_nightly_lines_run_the_slow_tests() {
    let mut slow = Vec::new();
    for (path, document) in workflows() {
        if scripts(&document)
            .iter()
            .any(|script| script.contains("--slow"))
        {
            slow.push(path);
        }
    }
    assert_eq!(slow, [LINES[1], LINES[2]]);
    for path in [LINES[1], LINES[2]] {
        let all = scripts(&workflow(path)).join("\n");
        assert!(all.contains("cargo xtask check --slow"), "{path}");
        assert!(all.contains("cargo xtask suite --slow"), "{path}");
    }
    // The pull request line selects its suites by the merge base; the
    // weekly line runs every suite.
    let check = scripts(&workflow(LINES[0])).join("\n");
    assert!(
        check.contains("cargo xtask suite \"${args[@]}\""),
        "{check}"
    );
    assert!(check.contains("args+=(--base \"$BASE_SHA\")"), "{check}");
    let weekly = scripts(&workflow(LINES[3])).join("\n");
    assert!(weekly.contains("cargo xtask suite --images"), "{weekly}");
    // The nightly and weekly lines run on main only.
    for path in [LINES[2], LINES[3]] {
        for (key, job) in jobs(&workflow(path)) {
            let condition = job["if"].as_str();
            assert_eq!(
                condition,
                Some("github.ref == 'refs/heads/main'"),
                "{path}: {key}"
            );
        }
    }
}

#[test]
fn the_record_workflow_lists_every_other_workflow() {
    let all = workflows();
    let record = &all
        .iter()
        .find(|(path, _)| path == LINES[4])
        .expect("tracked")
        .1;
    let mut listed: Vec<&str> = (record["on"]["workflow_run"]["workflows"].as_vec())
        .expect("the workflows")
        .iter()
        .filter_map(Yaml::as_str)
        .collect();
    listed.sort_unstable();
    let mut names: Vec<&str> = (all.iter())
        .filter(|(path, _)| path != LINES[4])
        .map(|(path, document)| {
            document["name"]
                .as_str()
                .unwrap_or_else(|| panic!("{path}"))
        })
        .collect();
    names.sort_unstable();
    assert_eq!(listed, names);
    assert_eq!(record["name"].as_str(), Some("run record"));
    let types = record["on"]["workflow_run"]["types"]
        .as_vec()
        .expect("types");
    assert_eq!(types, &[Yaml::String("completed".to_string())]);
    // A manual run takes the ID of the run to record, on main only.
    let input = &record["on"]["workflow_dispatch"]["inputs"]["run"];
    assert_eq!(input["required"].as_bool(), Some(true));
    let (_, job) = jobs(record)[0];
    assert_eq!(
        job["if"].as_str(),
        Some("github.event_name == 'workflow_run' || github.ref == 'refs/heads/main'")
    );
    let permissions = job["permissions"].as_hash().expect("the permissions");
    for (scope, level) in permissions {
        assert_eq!(level.as_str(), Some("read"), "{scope:?}");
    }
    assert!(
        scripts(record)
            .iter()
            .any(|script| script.contains("cargo xtask run-record --id \"$INPUT_RUN\""))
    );
}

#[test]
fn the_pull_request_line_keeps_its_required_check_and_its_summary() {
    let all = workflows();
    let named: Vec<(&str, &str)> = (all.iter())
        .flat_map(|(path, document)| {
            (jobs(document).into_iter())
                .filter(|(_, job)| job["name"].as_str() == Some(REQUIRED))
                .map(move |(key, _)| (path.as_str(), key))
        })
        .collect();
    assert_eq!(named, [(LINES[0], "check")]);
    let check = workflow(LINES[0]);
    assert!(check["on"]["pull_request"].as_hash().is_some());
    let summary = &check["jobs"]["summary"];
    assert_eq!(summary["name"].as_str(), Some("check summary"));
    assert_eq!(needs(summary), ["check", "image", "suite"]);
    assert_eq!(summary["if"].as_str(), Some("always()"));
    assert_eq!(needs(&check["jobs"]["suite"]), ["image"]);
    let group = check["concurrency"]["group"].as_str().expect("the group");
    assert!(
        group.contains("github.event.pull_request.number"),
        "{group}"
    );
    assert_eq!(
        check["concurrency"]["cancel-in-progress"].as_str(),
        Some("${{ github.event_name == 'pull_request' }}")
    );
    let full = workflow(LINES[1]);
    let group = full["concurrency"]["group"].as_str().expect("the group");
    assert!(group.contains("github.event.label.name"), "{group}");
    for path in [LINES[2], LINES[3]] {
        let document = workflow(path);
        assert_eq!(
            document["concurrency"]["cancel-in-progress"].as_bool(),
            Some(false)
        );
    }
}

/// The retention of the artifacts of a job that runs on `main` and
/// elsewhere: 90 days for a run on `main`, 30 days for the others.
const BY_REF: &str = "${{ github.ref == 'refs/heads/main' && 90 || 30 }}";
/// The retention that the record workflow takes from the record of the run
/// that it records.
const BY_RECORD: &str = "${{ steps.record.outputs.retention }}";

/// Every upload step of the tracked workflows: the file, the key of the
/// job, the name of the step and its `retention-days` as written.
const RETENTION: [(&str, &str, &str, &str); 28] = [
    (
        ".github/workflows/check.yml",
        "check",
        "Upload the receipt",
        BY_REF,
    ),
    (
        ".github/workflows/check.yml",
        "check",
        "Upload the QEMU boot suite receipts",
        BY_REF,
    ),
    (
        ".github/workflows/check.yml",
        "image",
        "Upload the images",
        BY_REF,
    ),
    (
        ".github/workflows/check.yml",
        "suite",
        "Upload the suite report",
        BY_REF,
    ),
    (
        ".github/workflows/formal-calibration.yml",
        "calibration",
        "Upload the receipt, the summary and the logs",
        BY_REF,
    ),
    (
        ".github/workflows/formal-calibration.yml",
        "shard",
        "Upload the receipt, the summary and the logs of the shard",
        BY_REF,
    ),
    (
        ".github/workflows/formal-calibration.yml",
        "merge",
        "Upload the merge record",
        BY_REF,
    ),
    (
        ".github/workflows/formal-calibration.yml",
        "mutants",
        "Upload the list of survivors, the receipt and the logs",
        BY_REF,
    ),
    (
        ".github/workflows/formal-canary.yml",
        "canary",
        "Upload the canary record",
        "90",
    ),
    (
        ".github/workflows/formal-image-build.yml",
        "build",
        "Upload the build record",
        "30",
    ),
    (
        ".github/workflows/formal-image-publish.yml",
        "publish",
        "Upload the build record",
        "90",
    ),
    (
        ".github/workflows/formal.yml",
        "gate",
        "Upload the receipt and the logs",
        BY_REF,
    ),
    (
        ".github/workflows/formal.yml",
        "shard",
        "Upload the receipt, the summary and the logs of the shard",
        BY_REF,
    ),
    (
        ".github/workflows/formal.yml",
        "merge",
        "Upload the merge record",
        BY_REF,
    ),
    (
        ".github/workflows/formal.yml",
        "leanchecker",
        "Upload the measurement",
        BY_REF,
    ),
    (
        ".github/workflows/formal.yml",
        "planned",
        "Upload the receipt and the logs of the planned targets",
        BY_REF,
    ),
    (
        ".github/workflows/formal.yml",
        "comparator",
        "Upload the results",
        BY_REF,
    ),
    (
        ".github/workflows/full.yml",
        "check",
        "Upload the receipt",
        BY_REF,
    ),
    (
        ".github/workflows/full.yml",
        "image",
        "Upload the images",
        BY_REF,
    ),
    (
        ".github/workflows/full.yml",
        "suite",
        "Upload the suite report",
        BY_REF,
    ),
    (
        ".github/workflows/nightly.yml",
        "check",
        "Upload the receipt",
        BY_REF,
    ),
    (
        ".github/workflows/nightly.yml",
        "image",
        "Upload the images",
        BY_REF,
    ),
    (
        ".github/workflows/nightly.yml",
        "suite",
        "Upload the suite report",
        BY_REF,
    ),
    (
        ".github/workflows/release.yml",
        "assets",
        "Upload the assets",
        BY_REF,
    ),
    (
        ".github/workflows/run-record.yml",
        "record",
        "Upload the record",
        BY_RECORD,
    ),
    (
        ".github/workflows/usage.yml",
        "summary",
        "Upload the summary and its data",
        BY_REF,
    ),
    (
        ".github/workflows/weekly.yml",
        "image",
        "Upload the images",
        BY_REF,
    ),
    (
        ".github/workflows/weekly.yml",
        "suite",
        "Upload the suite report",
        BY_REF,
    ),
];

/// The events of the `on` of `document`, whether it is one event, a list
/// or a mapping.
fn events(document: &Yaml) -> Vec<&str> {
    match &document["on"] {
        Yaml::String(event) => vec![event.as_str()],
        Yaml::Array(events) => events.iter().filter_map(Yaml::as_str).collect(),
        Yaml::Hash(events) => events.keys().filter_map(Yaml::as_str).collect(),
        _ => Vec::new(),
    }
}

/// Whether the condition `if` of `job` is `github.ref == 'refs/heads/main'`,
/// written with or without `${{ }}`.
fn on_main(job: &Yaml) -> bool {
    job["if"].as_str().is_some_and(|text| {
        let text = text.trim();
        let text = (text.strip_prefix("${{"))
            .and_then(|text| text.strip_suffix("}}"))
            .unwrap_or(text);
        text.trim() == "github.ref == 'refs/heads/main'"
    })
}

/// Whether `job` of `document` runs on `main` only: the workflow runs on
/// pushes to `main`, on a schedule, which runs the default branch, or on a
/// manual run, and then the job requires `main`.
fn main_only(document: &Yaml, job: &Yaml) -> bool {
    let events = events(document);
    let known = |event: &&str| ["push", "schedule", "workflow_dispatch"].contains(event);
    let push = &document["on"]["push"];
    let branches = push["branches"]
        .as_vec()
        .map(|branches| branches.iter().filter_map(Yaml::as_str).collect::<Vec<_>>());
    !events.is_empty()
        && events.iter().all(known)
        && (!events.contains(&"push") || branches == Some(vec!["main"]))
        && (!events.contains(&"workflow_dispatch") || on_main(job))
}

/// The values of `retention-days` that the rule allows for an upload of
/// `job` in `document`: in the record workflow, the retention of the
/// recorded run alone; elsewhere [`BY_REF`], 90 for a job that runs on
/// `main` only and 30 in a workflow that runs on pull requests only.
fn allowed_retention(document: &Yaml, job: &Yaml) -> Vec<&'static str> {
    let events = events(document);
    if events.contains(&"workflow_run") {
        return vec![BY_RECORD];
    }
    let mut allowed = vec![BY_REF];
    if main_only(document, job) {
        allowed.push("90");
    }
    if events == ["pull_request"] {
        allowed.push("30");
    }
    allowed
}

/// The upload steps of `document`: the key of the job, the name of the
/// step and its `retention-days` as text, if it has one.
fn uploads(document: &Yaml) -> Vec<(&str, &Yaml, &str, Option<String>)> {
    let mut found = Vec::new();
    for (key, job) in jobs(document) {
        for step in job["steps"].as_vec().into_iter().flatten() {
            if !uses(step, "actions/upload-artifact") {
                continue;
            }
            let days = match &step["with"]["retention-days"] {
                Yaml::String(text) => Some(text.clone()),
                Yaml::Integer(days) => Some(days.to_string()),
                _ => None,
            };
            let name = step["name"].as_str().unwrap_or("(unnamed)");
            found.push((key, job, name, days));
        }
    }
    found
}

/// The problems of the retention of the uploads of `document`: each upload
/// writes a `retention-days` that the rule allows.
fn retention_problems(document: &Yaml) -> Vec<String> {
    let mut problems = Vec::new();
    for (key, job, name, days) in uploads(document) {
        match days {
            None => problems.push(format!("job {key}, step {name}: no retention-days")),
            Some(days) if !allowed_retention(document, job).contains(&days.as_str()) => {
                problems.push(format!(
                    "job {key}, step {name}: retention-days {days} does not follow the rule"
                ));
            }
            Some(_) => {}
        }
    }
    problems
}

#[test]
fn every_upload_keeps_its_artifact_by_the_retention_rule() {
    let mut found = Vec::new();
    for (path, document) in workflows() {
        assert_eq!(
            retention_problems(&document),
            Vec::<String>::new(),
            "{path}"
        );
        for (key, _, name, days) in uploads(&document) {
            found.push((path.clone(), key.to_string(), name.to_string(), days));
        }
    }
    found.sort();
    let mut expected: Vec<_> = (RETENTION.iter())
        .map(|(path, key, name, days)| {
            let days = Some(days.to_string());
            (path.to_string(), key.to_string(), name.to_string(), days)
        })
        .collect();
    expected.sort();
    assert_eq!(found, expected);
    // Each row of the table keeps to the rule of its workflow.
    let pull_request = "on:\n  pull_request:\n    branches: [main]\n";
    let both = "on:\n  pull_request:\n  push:\n    branches: [main]\n";
    let main = "on:\n  push:\n    branches: [main]\n  schedule:\n    - cron: \"1 2 * * *\"\n";
    let manual = "on:\n  workflow_dispatch:\n";
    let record = "on:\n  workflow_run:\n    workflows: [a]\n  workflow_dispatch:\n";
    let upload = |on: &str, condition: &str, days: &str| {
        parse(&format!(
            "{on}jobs:\n  a:\n{condition}    steps:\n      - name: Upload\n        \
             uses: actions/upload-artifact@1\n        with:\n          name: a\n{days}"
        ))
    };
    let days = |value: &str| format!("          retention-days: {value}\n");
    let main_job = "    if: github.ref == 'refs/heads/main'\n";
    for (on, condition, value) in [
        (both, "", BY_REF),
        (pull_request, "", BY_REF),
        (pull_request, "", "30"),
        (main, "", "90"),
        (main, "", BY_REF),
        (manual, main_job, "90"),
        (
            manual,
            "    if: ${{ github.ref == 'refs/heads/main' }}\n",
            "90",
        ),
        (record, "", BY_RECORD),
    ] {
        let document = upload(on, condition, &days(value));
        assert_eq!(
            retention_problems(&document),
            Vec::<String>::new(),
            "{on}{value}"
        );
    }
    let wrong = |value: &str| {
        format!("job a, step Upload: retention-days {value} does not follow the rule")
    };
    for (on, condition, value, problem) in [
        (
            both,
            "",
            None,
            "job a, step Upload: no retention-days".to_string(),
        ),
        (both, "", Some("30"), wrong("30")),
        (main, "", Some("30"), wrong("30")),
        (both, "", Some("90"), wrong("90")),
        (pull_request, "", Some("90"), wrong("90")),
        (manual, "", Some("90"), wrong("90")),
        ("on:\n  push:\n", "", Some("90"), wrong("90")),
        ("on: push\n", "", Some("90"), wrong("90")),
        (both, "", Some(BY_RECORD), wrong(BY_RECORD)),
        (record, "", Some(BY_REF), wrong(BY_REF)),
        (record, "", Some("90"), wrong("90")),
    ] {
        let document = upload(on, condition, &value.map(days).unwrap_or_default());
        assert_eq!(retention_problems(&document), [problem], "{on}{value:?}");
    }
}

/// Whether `step` uses the action `action`, such as
/// `actions/upload-artifact`, pinned to some commit.
fn uses(step: &Yaml, action: &str) -> bool {
    (step["uses"].as_str()).is_some_and(|uses| {
        uses.strip_prefix(action)
            .is_some_and(|rest| rest.starts_with('@'))
    })
}

/// The problems of the downloads of `document`: each takes the name of its
/// artifact from an output of a job that its job needs, and that output is
/// the name of an upload of that job, so that a rerun of the downloading
/// job alone finds the artifact of the attempt that wrote it.
fn download_problems(document: &Yaml) -> Vec<String> {
    let all = jobs(document);
    let mut problems = Vec::new();
    for (key, job) in &all {
        let downloads = (job["steps"].as_vec().into_iter().flatten())
            .filter(|step| uses(step, "actions/download-artifact"));
        for step in downloads {
            let name = step["with"]["name"].as_str().unwrap_or_default();
            let output = (name.strip_prefix("${{ needs."))
                .and_then(|rest| rest.strip_suffix(" }}"))
                .and_then(|rest| rest.split_once(".outputs."));
            let Some((from, output)) = output else {
                problems.push(format!(
                    "job {key} downloads {name:?}, not an output of a job that it needs"
                ));
                continue;
            };
            if !needs(job).contains(&from) {
                problems.push(format!("job {key} does not need job {from}"));
                continue;
            }
            let upstream = (all.iter())
                .find(|(other, _)| *other == from)
                .map(|(_, job)| *job);
            let value = upstream.and_then(|job| job["outputs"][output].as_str());
            let uploaded = (upstream.into_iter())
                .flat_map(|job| job["steps"].as_vec().into_iter().flatten())
                .filter(|step| uses(step, "actions/upload-artifact"))
                .any(|step| value.is_some() && step["with"]["name"].as_str() == value);
            if !uploaded {
                problems.push(format!(
                    "the output {output} of job {from} is not the name of one of its uploads"
                ));
            }
        }
    }
    problems
}

#[test]
fn a_download_takes_the_name_of_its_artifact_from_the_job_that_uploaded_it() {
    let mut downloads = 0;
    for path in LINES {
        let document = workflow(path);
        assert_eq!(download_problems(&document), Vec::<String>::new(), "{path}");
        downloads += (steps(&document).into_iter())
            .filter(|step| uses(step, "actions/download-artifact"))
            .count();
    }
    assert_eq!(downloads, 4);
    let good = "jobs:\n  image:\n    outputs:\n      artifact: images-${{ github.run_attempt }}\n    \
                steps:\n      - uses: actions/upload-artifact@1\n        with:\n          \
                name: images-${{ github.run_attempt }}\n  suite:\n    needs: image\n    steps:\n      \
                - uses: actions/download-artifact@2\n        with:\n          \
                name: ${{ needs.image.outputs.artifact }}\n";
    assert_eq!(download_problems(&parse(good)), Vec::<String>::new());
    let cases = [
        (
            good.replace(
                "name: ${{ needs.image.outputs.artifact }}",
                "name: images-${{ github.run_attempt }}",
            ),
            "job suite downloads \"images-${{ github.run_attempt }}\", not an output of a job that \
             it needs",
        ),
        (
            good.replace("    needs: image\n", ""),
            "job suite does not need job image",
        ),
        (
            good.replace("artifact: images-", "artifact: other-"),
            "the output artifact of job image is not the name of one of its uploads",
        ),
        (
            good.replace("outputs.artifact }}", "outputs.missing }}"),
            "the output missing of job image is not the name of one of its uploads",
        ),
    ];
    for (text, problem) in cases {
        assert_eq!(download_problems(&parse(&text)), [problem], "{text}");
    }
}

/// The workflow of the gate.
const FORMAL: &str = ".github/workflows/formal.yml";
/// The workflow of the calibration target.
const CALIBRATION: &str = ".github/workflows/formal-calibration.yml";
/// The jobs of the gate in the formal workflows: the file and the key.
const GATE_JOBS: [(&str, &str); 7] = [
    (FORMAL, "gate"),
    (FORMAL, "shard"),
    (FORMAL, "merge"),
    (FORMAL, "planned"),
    (CALIBRATION, "calibration"),
    (CALIBRATION, "shard"),
    (CALIBRATION, "merge"),
];
/// What their uploads may hold: receipts, summaries, the records of the
/// run and the logs of the run packed into `logs.tar.gz`.
const GATE_UPLOADS: [&str; 13] = [
    "artifacts/formal/runs/*/receipt.json",
    "artifacts/formal/summary.md",
    "artifacts/formal/merge/record.json",
    "artifacts/formal/merge/summary.md",
    "artifacts/formal/logs.tar.gz",
    "artifacts/formal/job.txt",
    "artifacts/formal/event.json",
    "artifacts/formal/guard.txt",
    "artifacts/formal/vectors.txt",
    "artifacts/formal/vectors-tests.txt",
    "artifacts/formal/vectors-fixture.txt",
    "artifacts/formal/vectors/",
    "artifacts/formal/samples.tsv",
];
/// The archive of the logs of a run.
const PACKED_LOGS: &str = "artifacts/formal/logs.tar.gz";

/// The paths that the upload `step` names, one on each line.
fn upload_paths(step: &Yaml) -> Vec<&str> {
    let paths = step["with"]["path"].as_str().unwrap_or_default();
    (paths.lines().map(str::trim))
        .filter(|path| !path.is_empty())
        .collect()
}

/// The problems of the uploads of `job`: a path that [`GATE_UPLOADS`] does
/// not list, and an archive of logs that no step of the job writes.
fn gate_upload_problems(job: &Yaml) -> Vec<String> {
    let written = (scripts_of(job).into_iter())
        .any(|script| script.contains(&format!("tar -czf {PACKED_LOGS}")));
    let mut problems = Vec::new();
    for step in steps_using(job, "actions/upload-artifact") {
        let paths = upload_paths(step);
        for path in &paths {
            if !GATE_UPLOADS.contains(path) {
                problems.push(format!("uploads {path}"));
            }
        }
        if paths.contains(&PACKED_LOGS) && !written {
            problems.push("uploads logs.tar.gz, which no step writes".to_string());
        }
    }
    problems
}

/// The artifact that the first upload of `job` names.
fn upload_name(job: &Yaml) -> &str {
    let uploads = steps_using(job, "actions/upload-artifact");
    let name = (uploads.first().copied()).and_then(|step| step["with"]["name"].as_str());
    name.expect("an upload with a name")
}

/// The script of the step of `job` with the id `id`.
fn script_with_id<'a>(job: &'a Yaml, id: &str) -> &'a str {
    let mut steps = job["steps"].as_vec().into_iter().flatten();
    let found = steps.find(|step| step["id"].as_str() == Some(id));
    let script = found.and_then(|step| step["run"].as_str());
    script.unwrap_or_else(|| panic!("a step {id} with a script"))
}

#[test]
fn the_jobs_of_the_gate_upload_receipts_summaries_records_and_packed_logs() {
    let documents = [FORMAL, CALIBRATION].map(|path| (path, workflow(path)));
    for (path, key) in GATE_JOBS {
        let (_, document) = (documents.iter())
            .find(|(file, _)| *file == path)
            .expect("a formal workflow");
        let job = &document["jobs"][key];
        let uploads = steps_using(job, "actions/upload-artifact");
        assert_eq!(uploads.len(), 1, "{path}: {key}");
        assert_eq!(
            gate_upload_problems(job),
            Vec::<String>::new(),
            "{path}: {key}"
        );
        // Every job but the merge runs the gate and uploads its logs packed.
        let packed = upload_paths(uploads[0]).contains(&PACKED_LOGS);
        assert_eq!(packed, key != "merge", "{path}: {key}");
    }
    // The logs of a run are not uploaded as they are.
    let logs = parse(
        "steps:\n  - uses: actions/upload-artifact@1\n    with:\n      path: |\n        \
         artifacts/formal/runs/*/receipt.json\n        artifacts/formal/runs/*/logs/\n",
    );
    assert_eq!(
        gate_upload_problems(&logs),
        ["uploads artifacts/formal/runs/*/logs/"]
    );
    // An archive needs a step that writes it.
    let unwritten = format!(
        "steps:\n  - run: tar -czf other.tar.gz logs\n  - uses: actions/upload-artifact@1\n    \
         with:\n      path: {PACKED_LOGS}\n"
    );
    assert_eq!(
        gate_upload_problems(&parse(&unwritten)),
        ["uploads logs.tar.gz, which no step writes"]
    );
    let written = unwritten.replace("other.tar.gz", PACKED_LOGS);
    assert_eq!(gate_upload_problems(&parse(&written)), Vec::<String>::new());
}

#[test]
fn the_parts_of_a_run_are_named_for_the_merge_that_downloads_them() {
    let head = "${{ github.event.pull_request.head.sha || github.sha }}";
    let attempt = "${{ github.run_attempt }}";
    let formal = workflow(FORMAL);
    let calibration = workflow(CALIBRATION);
    let (gate, shard, merge) = (
        &formal["jobs"]["gate"],
        &formal["jobs"]["shard"],
        &formal["jobs"]["merge"],
    );
    // Each part names its artifact by the part, with `-` for `/`, the commit
    // and the attempt.
    let qualification = format!("formal-part-qualification-{head}-{attempt}");
    assert_eq!(upload_name(gate), qualification);
    let target = format!("formal-part-target-${{{{ matrix.name }}}}-{head}-{attempt}");
    assert_eq!(upload_name(shard), target);
    for (job, id) in [(gate, "gate"), (shard, "shard")] {
        assert!(
            script_with_id(job, id).contains("--env GITHUB_RUN_ATTEMPT"),
            "{id}"
        );
    }
    // The merge runs after them, unless the run was cancelled, on the
    // runner, with a limit that the record of the run reads.
    assert_eq!(needs(merge), ["gate", "shard"]);
    assert_eq!(
        merge["if"].as_str(),
        Some("${{ !cancelled() && github.event_name != 'workflow_dispatch' }}")
    );
    assert!(merge["timeout-minutes"].as_i64().is_some());
    assert!(
        scripts_of(merge)
            .iter()
            .all(|script| !script.contains("docker"))
    );
    // It downloads every attempt of every part of the run below one path,
    // without merging them: a single artifact into the path itself, several
    // each into a directory of its own, where the merge step finds the
    // receipts at any depth.
    let downloads = steps_using(merge, "actions/download-artifact");
    assert_eq!(downloads.len(), 1);
    let with = &downloads[0]["with"];
    let pattern = format!("formal-part-*-{head}-*");
    assert_eq!(with["pattern"].as_str(), Some(pattern.as_str()));
    assert_eq!(with["path"].as_str(), Some("artifacts/formal/parts"));
    assert!(with["name"].is_badvalue() && with["merge-multiple"].is_badvalue());
    // Its first step records the start of the job for the merge.
    let steps = merge["steps"].as_vec().expect("the steps");
    let first = steps[0]["run"].as_str().unwrap_or_default();
    let started = format!("{}=", crate::formal::merge::STARTED);
    assert!(
        first.contains(&started) && first.contains("\"$GITHUB_ENV\""),
        "{first}"
    );
    let merged = script_with_id(merge, "merge");
    assert!(merged.contains("deadline.sh --stop-commands"), "{merged}");
    assert!(
        merged.contains("formal merge \"${receipts[@]}\""),
        "{merged}"
    );
    // The calibration names the part of its qualification job with its own
    // prefix, which the artifact of the planned example does not have.
    let job = &calibration["jobs"]["calibration"];
    let rows = job["strategy"]["matrix"]["include"]
        .as_vec()
        .expect("the matrix");
    let prefix = "calibration-formal-part-";
    assert_eq!(
        rows[0]["artifact"].as_str(),
        Some("calibration-formal-part-qualification")
    );
    assert!(
        !rows[1]["artifact"]
            .as_str()
            .expect("an artifact")
            .starts_with(prefix)
    );
    let artifact = format!("${{{{ matrix.artifact }}}}-{head}-{attempt}");
    assert_eq!(upload_name(job), artifact);
    let merge = &calibration["jobs"]["merge"];
    assert_eq!(needs(merge), ["calibration", "shard"]);
    assert_eq!(
        merge["if"].as_str(),
        Some("${{ !cancelled() && needs.calibration.result != 'skipped' }}")
    );
    // Each merge has a group of its own. The merge of an older run whose
    // parts a newer event cancelled still runs and fails; only the latest
    // run of a pull request counts.
    for (document, group) in [
        (&formal, "formal-merge-"),
        (&calibration, "formal-calibration-merge-"),
    ] {
        let concurrency = &document["jobs"]["merge"]["concurrency"];
        let own = concurrency["group"]
            .as_str()
            .is_some_and(|text| text.starts_with(group));
        assert!(own, "{group}");
        assert_eq!(
            concurrency["cancel-in-progress"].as_str(),
            Some("${{ github.event_name == 'pull_request' }}")
        );
    }
}

#[test]
fn the_calibration_shard_and_merge_run_the_steps_of_those_of_formal() {
    let formal = workflow(FORMAL);
    let calibration = workflow(CALIBRATION);
    let emit = |steps: &Yaml| {
        let mut text = String::new();
        let mut emitter = yaml_rust2::YamlEmitter::new(&mut text);
        emitter.dump(steps).expect("the steps");
        text
    };
    // The steps as parsed, so their comments may differ: in the calibration,
    // the flag of its layout and the prefixes of its artifacts, at most once
    // each, as counted below.
    let replaced = [
        (" --calibration", ""),
        ("calibration-formal-part-", "formal-part-"),
        ("formal-calibration-merge-", "formal-merge-"),
    ];
    for (key, counts) in [("shard", [1, 1, 0]), ("merge", [1, 1, 1])] {
        let own = emit(&formal["jobs"][key]["steps"]);
        let mut copied = emit(&calibration["jobs"][key]["steps"]);
        let found = replaced.map(|(from, _)| copied.matches(from).count());
        assert_eq!(found, counts, "{key}");
        for (from, to) in replaced {
            copied = copied.replace(from, to);
        }
        assert_eq!(copied, own, "{key}");
    }
    // The jobs as well, but for their names, their needs and conditions, the
    // matrix of the shards and the concurrency group.
    let settings = |job: &Yaml| {
        let mut job = job.as_hash().expect("a job").clone();
        for key in ["name", "needs", "if", "steps"] {
            job.remove(&Yaml::String(key.to_string()));
        }
        for (key, own) in [("strategy", "matrix"), ("concurrency", "group")] {
            let inner = job.get_mut(&Yaml::String(key.to_string()));
            if let Some(inner) = inner.and_then(Yaml::as_mut_hash) {
                inner.remove(&Yaml::String(own.to_string()));
            }
        }
        job
    };
    for key in ["shard", "merge"] {
        let (own, copied) = (&formal["jobs"][key], &calibration["jobs"][key]);
        assert_eq!(settings(copied), settings(own), "{key}");
    }
    // The shards run on the events of the qualification job.
    let jobs = &calibration["jobs"];
    assert_eq!(jobs["shard"]["if"], jobs["calibration"]["if"]);
    assert!(jobs["shard"]["if"].as_str().is_some());
}

/// The script that runs a main command of a step under its deadline.
const DEADLINE: &str = ".github/scripts/deadline.sh";
/// The main commands of the jobs of the lines, as `cargo xtask <command>`.
const MAIN_COMMANDS: [&str; 3] = ["check", "image", "suite"];

/// The lines of `script` that are not blank, each line that ends in `\`
/// joined to the next.
fn logical_lines(script: &str) -> Vec<String> {
    let mut lines = Vec::new();
    let mut current = String::new();
    for line in script.lines() {
        match line.trim_end().strip_suffix('\\') {
            Some(start) => current.push_str(start),
            None => {
                current.push_str(line);
                lines.push(std::mem::take(&mut current));
            }
        }
    }
    lines.push(current);
    lines.retain(|line| !line.trim().is_empty());
    lines
}

/// The main command that the line `line` runs, if it runs one.
fn main_command(line: &str) -> Option<&str> {
    let words: Vec<&str> = line.split_whitespace().collect();
    words.windows(3).find_map(|words| {
        let main = words[0] == "cargo" && words[1] == "xtask" && MAIN_COMMANDS.contains(&words[2]);
        main.then_some(words[2])
    })
}

/// How the line `line` runs its command under [`DEADLINE`]: whether it
/// turns workflow commands off, its deadline in minutes and its kill-after
/// in seconds; or why it does not run it so.
fn deadline_of(line: &str) -> Result<(bool, i64, i64), String> {
    let words: Vec<&str> = line.split_whitespace().collect();
    let rest = (words.strip_prefix(&["exec", "bash", DEADLINE][..]))
        .ok_or_else(|| format!("does not run as the last command `exec bash {DEADLINE}`"))?;
    let (stop, rest) = match rest.split_first() {
        Some((&"--stop-commands", rest)) => (true, rest),
        _ => (false, rest),
    };
    let wrong = || "does not have a deadline in minutes and a kill-after in seconds".to_string();
    let [deadline, kill, "cargo", "xtask", ..] = rest else {
        return Err(wrong());
    };
    let number = |text: &str, unit: char| text.strip_suffix(unit)?.parse::<i64>().ok();
    let minutes = number(deadline, 'm').ok_or_else(wrong)?;
    let seconds = number(kill, 's').ok_or_else(wrong)?;
    Ok((stop, minutes, seconds))
}

/// The problems of the main commands of the jobs of `document`, with their
/// number. Each runs as the last command of its step under [`DEADLINE`],
/// with `exec` so that the script receives the signals of the runner, with
/// `--stop-commands` for the suite alone, and at a deadline that with its
/// kill-after ends before the limit of its job and, when `tight`, one or two
/// minutes before that limit. No other command of a script calls `timeout`.
fn deadline_problems(document: &Yaml, tight: bool) -> (usize, Vec<String>) {
    let mut problems = Vec::new();
    let mut count = 0;
    for (key, job) in jobs(document) {
        let limit = job["timeout-minutes"].as_i64();
        for script in
            (job["steps"].as_vec().into_iter().flatten()).filter_map(|step| step["run"].as_str())
        {
            let lines = logical_lines(script);
            let named: Vec<usize> = (0..lines.len())
                .filter(|at| main_command(&lines[*at]).is_some())
                .collect();
            let timeout = |line: &&String| line.split_whitespace().any(|word| word == "timeout");
            let other = lines.iter().filter(|line| main_command(line).is_none());
            if other.clone().any(|line| timeout(&line)) {
                problems.push(format!("job {key}: a script calls timeout itself"));
            }
            if named.is_empty() {
                continue;
            }
            count += named.len();
            if named != [lines.len() - 1] {
                problems.push(format!(
                    "job {key}: a main command is not the last command of its step"
                ));
                continue;
            }
            let line = &lines[lines.len() - 1];
            let main = main_command(line).expect("a main command");
            let (stop, minutes, seconds) = match deadline_of(line) {
                Ok(deadline) => deadline,
                Err(problem) => {
                    problems.push(format!("job {key}: cargo xtask {main} {problem}"));
                    continue;
                }
            };
            if stop != (main == "suite") {
                problems.push(format!(
                    "job {key}: cargo xtask {main} {} workflow commands off",
                    if stop { "turns" } else { "does not turn" }
                ));
            }
            match limit {
                None => problems.push(format!("job {key} has no timeout-minutes")),
                Some(limit) if minutes * 60 + seconds >= limit * 60 => problems.push(format!(
                    "job {key}: the deadline of cargo xtask {main} and its kill-after reach the \
                     limit of {limit} minutes"
                )),
                Some(limit) if tight && !(1..=2).contains(&(limit - minutes)) => {
                    problems.push(format!(
                        "job {key}: the deadline of cargo xtask {main} is not one or two minutes \
                         before the limit of {limit} minutes"
                    ));
                }
                Some(_) => {}
            }
        }
    }
    (count, problems)
}

#[test]
fn every_main_command_of_the_lines_runs_under_its_deadline() {
    let mut count = 0;
    for path in &LINES[..4] {
        let (main, problems) = deadline_problems(&workflow(path), true);
        assert_eq!(problems, Vec::<String>::new(), "{path}");
        count += main;
    }
    // The check, the images and the suite of the pull request, full and
    // nightly lines, and the images and the suite of the weekly line.
    assert_eq!(count, 11);
    // The script passes both stop signals on to `timeout`, which it starts
    // with SIGINT not ignored, and waits for the command.
    let tree = Tree::load(&crate::repo::root()).expect("the tracked files");
    let script = tree.text(DEADLINE).expect("the script is tracked");
    for text in [
        "trap 'forward INT' INT",
        "trap 'forward TERM' TERM",
        "env --default-signal=INT,QUIT timeout --signal=TERM",
        "wait \"$pid\"",
    ] {
        assert!(script.contains(text), "{text}");
    }
    let good = "jobs:\n  check:\n    timeout-minutes: 15\n    steps:\n      - run: |\n          \
                echo start\n          exec bash .github/scripts/deadline.sh 13m 90s \\\n            \
                cargo xtask check --receipt r.json\n  suite:\n    timeout-minutes: 10\n    \
                steps:\n      - run: exec bash .github/scripts/deadline.sh --stop-commands 8m 60s \
                cargo xtask suite\n";
    assert_eq!(deadline_problems(&parse(good), true), (2, Vec::new()));
    let cases = [
        (
            good.replace(
                "exec bash .github/scripts/deadline.sh 13m 90s",
                "timeout --kill-after=90s 13m",
            ),
            "job check: cargo xtask check does not run as the last command `exec bash \
             .github/scripts/deadline.sh`",
        ),
        (
            good.replace(
                "exec bash .github/scripts/deadline.sh 13m",
                "bash .github/scripts/deadline.sh 13m",
            ),
            "job check: cargo xtask check does not run as the last command `exec bash \
             .github/scripts/deadline.sh`",
        ),
        (
            good.replace(
                "--receipt r.json\n",
                "--receipt r.json\n          echo done\n",
            ),
            "job check: a main command is not the last command of its step",
        ),
        (
            good.replace("echo start", "timeout 5 sleep 1"),
            "job check: a script calls timeout itself",
        ),
        (
            good.replace("13m 90s", "15m 90s"),
            "job check: the deadline of cargo xtask check and its kill-after reach the limit of \
             15 minutes",
        ),
        (
            good.replace("13m 90s", "13m 120s"),
            "job check: the deadline of cargo xtask check and its kill-after reach the limit of \
             15 minutes",
        ),
        (
            good.replace("13m 90s", "10m 90s"),
            "job check: the deadline of cargo xtask check is not one or two minutes before the \
             limit of 15 minutes",
        ),
        (
            good.replace("13m 90s", "13 90s"),
            "job check: cargo xtask check does not have a deadline in minutes and a kill-after \
             in seconds",
        ),
        (
            good.replace("--stop-commands 8m", "8m"),
            "job suite: cargo xtask suite does not turn workflow commands off",
        ),
        (
            good.replace("deadline.sh 13m", "deadline.sh --stop-commands 13m"),
            "job check: cargo xtask check turns workflow commands off",
        ),
        (
            good.replace("    timeout-minutes: 15\n", ""),
            "job check has no timeout-minutes",
        ),
    ];
    for (text, problem) in cases {
        assert_eq!(
            deadline_problems(&parse(&text), true).1,
            [problem],
            "{text}"
        );
    }
    // Away from the lines, the deadline may be earlier.
    let early = good.replace("13m 90s", "10m 90s");
    assert_eq!(deadline_problems(&parse(&early), false), (2, Vec::new()));
}

#[test]
fn the_deadline_script_passes_on_a_stop_signal_and_waits_for_the_command() {
    use std::process::{Command, Stdio};
    use std::time::{Duration, Instant};
    // The script needs GNU `env` and GNU `timeout`, as on the runners;
    // elsewhere the test has nothing to run.
    let output = |program: &str, args: &[&str]| {
        let output = Command::new(program)
            .args(args)
            .stdin(Stdio::null())
            .output();
        output.ok().filter(|output| output.status.success())
    };
    let gnu_env = output("env", &["--default-signal=INT", "true"]).is_some();
    let gnu_timeout = output("timeout", &["--version"])
        .is_some_and(|output| String::from_utf8_lossy(&output.stdout).contains("GNU coreutils"));
    if !gnu_env || !gnu_timeout {
        eprintln!("skipped: GNU env and GNU timeout are not on the path");
        return;
    }
    // A command that, on SIGINT, takes a second to write a file and then
    // exits with 3.
    let scratch = crate::scratch::Scratch::temporary("deadline");
    scratch.write(
        "command.sh",
        "trap 'sleep 1; echo stopped > \"$1\"; exit 3' INT\necho started > \"$2\"\n\
         while :; do sleep 0.1; done\n",
    );
    let path = |name: &str| scratch.0.join(name);
    let said = || std::fs::read_to_string(path("stderr")).unwrap_or_default();
    // The script starts with SIGINT not ignored, as the process of a step.
    let mut script = Command::new("env")
        .arg("--default-signal=INT")
        .arg("bash")
        .arg(crate::repo::root().join(DEADLINE))
        .args(["30s", "5s", "bash"])
        .args([path("command.sh"), path("stopped"), path("started")])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(std::fs::File::create(path("stderr")).expect("create the error file"))
        .spawn()
        .expect("start the script");
    let deadline = Instant::now() + Duration::from_secs(20);
    while !path("started").exists() {
        let ended = script.try_wait().expect("look at the script").is_some();
        assert!(!ended && Instant::now() < deadline, "{}", said());
        std::thread::sleep(Duration::from_millis(10));
    }
    // SAFETY: kill touches no memory of this process; the script is a child
    // of it that has not been collected.
    unsafe { libc::kill(script.id() as libc::pid_t, libc::SIGINT) };
    let status = script.wait().expect("collect the script");
    // The script ended after the command had written its file, with the
    // status of the command.
    assert!(path("stopped").exists(), "{}", said());
    assert_eq!(status.code(), Some(3), "{}", said());
}

/// The workflow that saves the caches.
const CACHE: &str = ".github/workflows/cache.yml";
/// The key of the cargo cache.
const CARGO_KEY: &str = "cargo-${{ runner.os }}-${{ runner.arch }}-${{ hashFiles('rust-toolchain.toml', \
                         'kernel/Cargo.lock', 'user/Cargo.lock', 'xtask/Cargo.lock', 'tools/Cargo.lock') }}";
/// The paths of the cargo cache, as the steps write them.
const CARGO_PATHS: &str =
    "~/.cargo/registry/index/\n~/.cargo/registry/cache/\nxtask/target/\ntools/target/\n";
/// The key of the tools cache.
const TOOLS_KEY: &str = "tools-${{ runner.os }}-${{ runner.arch }}-${{ hashFiles('rust-toolchain.toml', 'toolchains.toml') }}";
/// The paths of the tools cache, as the steps write them, for the Rust
/// toolchain of the arm64 Linux runners.
const TOOLS_PATHS: &str = "~/.cache/krepi-ci/apt/\n~/.rustup/toolchains/1.99.0-aarch64-unknown-linux-gnu/\n\
                           ~/.rustup/update-hashes/1.99.0-aarch64-unknown-linux-gnu\n";
/// The largest entry of each kind, in bytes.
const CACHE_LIMITS: [(&str, u64); 2] = [
    ("CARGO_CACHE_LIMIT", 2_000_000_000),
    ("TOOLS_CACHE_LIMIT", 800_000_000),
];

/// The steps of `job` that use the action `action`.
fn steps_using<'a>(job: &'a Yaml, action: &str) -> Vec<&'a Yaml> {
    (job["steps"].as_vec().into_iter().flatten())
        .filter(|step| uses(step, action))
        .collect()
}

#[test]
fn the_caches_are_restored_by_the_lines_and_saved_only_from_main() {
    let mut restores = Vec::new();
    let mut saves = Vec::new();
    for (path, document) in workflows() {
        for (key, job) in jobs(&document) {
            assert!(
                steps_using(job, "actions/cache").is_empty(),
                "{path}: {key}"
            );
            for (action, found) in [
                ("actions/cache/restore", &mut restores),
                ("actions/cache/save", &mut saves),
            ] {
                for step in steps_using(job, action) {
                    // Each step names one of the two kinds, with its paths.
                    let with = &step["with"];
                    let kind = match with["key"].as_str() {
                        Some(CARGO_KEY) => "cargo",
                        Some(TOOLS_KEY) => "tools",
                        other => panic!("{path}: {key}: the key {other:?}"),
                    };
                    let paths = if kind == "cargo" {
                        CARGO_PATHS
                    } else {
                        TOOLS_PATHS
                    };
                    assert_eq!(with["path"].as_str(), Some(paths), "{path}: {key}");
                    assert!(with["restore-keys"].is_badvalue(), "{path}: {key}");
                    found.push((path.clone(), key.to_string(), kind));
                }
            }
            // A job that writes to the caches through the API runs no code
            // of the repository and lives in the workflow that saves them.
            if job["permissions"]["actions"].as_str() == Some("write") {
                assert_eq!((path.as_str(), key), (CACHE, "prune"));
                assert!(steps_using(job, "actions/checkout").is_empty());
                for script in scripts_of(job) {
                    let builds = ["cargo xtask", "cargo build", "cargo run", "--manifest-path"];
                    assert!(!builds.iter().any(|text| script.contains(text)), "{script}");
                    let starts = |line: &str| line.trim_start().starts_with("cargo ");
                    assert!(!script.lines().any(starts), "{script}");
                }
            }
        }
    }
    // The lines restore both kinds in every job that builds or installs.
    let restored: Vec<(&str, &str)> = (restores.iter())
        .map(|(path, key, _)| (path.as_str(), key.as_str()))
        .collect();
    let mut expected = Vec::new();
    for (path, keys) in [
        (LINES[0], &["check", "image", "suite"][..]),
        (LINES[1], &["check", "image", "suite"]),
        (LINES[2], &["check", "image", "suite"]),
        (LINES[3], &["image", "suite"]),
        (CACHE, &["build"]),
    ] {
        for key in keys {
            expected.extend([(path, *key), (path, *key)]);
        }
    }
    let mut sorted = restored.clone();
    sorted.sort_unstable();
    expected.sort_unstable();
    assert_eq!(sorted, expected);
    let saved: Vec<_> = saves
        .iter()
        .map(|(path, key, kind)| (path.as_str(), key.as_str(), *kind))
        .collect();
    assert_eq!(
        saved,
        [(CACHE, "build", "tools"), (CACHE, "build", "cargo")]
    );
    // The lines restore only.
    for path in &LINES[..4] {
        assert_eq!(
            workflow(path)["cache-mode"].as_str(),
            Some("read"),
            "{path}"
        );
    }
    // The workflow that saves runs on pushes to main and on a schedule,
    // and only on main.
    let cache = workflow(CACHE);
    assert_eq!(events(&cache), ["push", "schedule"]);
    let branches = &cache["on"]["push"]["branches"];
    assert_eq!(branches.as_vec().map(Vec::len), Some(1));
    assert_eq!(branches[0].as_str(), Some("main"));
    let build = &cache["jobs"]["build"];
    assert!(on_main(build));
    let prune = &cache["jobs"]["prune"];
    assert_eq!(
        prune["if"].as_str(),
        Some("github.ref == 'refs/heads/main' && needs.build.result == 'success'")
    );
    assert_eq!(deadline_problems(&cache, false), (1, Vec::new()));
    // A push that changes a file of a key builds the caches again.
    let tree = Tree::load(&crate::repo::root()).expect("the tracked files");
    let locks: Vec<String> = (crate::check::WORKSPACES.iter())
        .map(|workspace| format!("{workspace}/Cargo.lock"))
        .collect();
    for lock in &locks {
        assert!(tree.exists(lock), "{lock}");
        assert!(CARGO_KEY.contains(&format!("'{lock}'")), "{lock}");
    }
    let hashed = |key: &str| key.matches("'").count() / 2;
    assert_eq!(hashed(CARGO_KEY), locks.len() + 1);
    assert_eq!(hashed(TOOLS_KEY), 2);
    let mut watched: Vec<&str> = (cache["on"]["push"]["paths"].as_vec().into_iter().flatten())
        .filter_map(Yaml::as_str)
        .collect();
    watched.sort_unstable();
    let mut files = vec![CACHE, "rust-toolchain.toml", "toolchains.toml"];
    files.extend(locks.iter().map(String::as_str));
    files.sort_unstable();
    assert_eq!(watched, files);
    assert!(CARGO_KEY.contains("'rust-toolchain.toml'"));
    for file in ["'rust-toolchain.toml'", "'toolchains.toml'"] {
        assert!(TOOLS_KEY.contains(file), "{file}");
    }
    // The paths of the toolchain name the channel of `rust-toolchain.toml`.
    let toolchain: toml::Table =
        toml::from_str(tree.text("rust-toolchain.toml").expect("tracked")).expect("TOML");
    let channel = toolchain["toolchain"]["channel"]
        .as_str()
        .expect("the channel");
    let host = format!("{channel}-aarch64-unknown-linux-gnu");
    assert!(TOOLS_PATHS.contains(&format!("~/.rustup/toolchains/{host}/\n")));
    assert!(TOOLS_PATHS.contains(&format!("~/.rustup/update-hashes/{host}\n")));
    // So does the report of the sizes of the paths.
    let check = tree.text(LINES[0]).expect("tracked");
    assert!(
        check.contains(&format!("~/.rustup/toolchains/{host}/\n")),
        "{check}"
    );
    // The limits of the entries.
    for (name, limit) in CACHE_LIMITS {
        let set = cache["env"][name]
            .as_str()
            .and_then(|text| text.parse::<u64>().ok());
        assert!(
            set.is_some_and(|set| set > 0 && set <= limit),
            "{name}: {set:?}"
        );
    }
}

/// The scripts of the steps of `job`.
fn scripts_of(job: &Yaml) -> Vec<&str> {
    (job["steps"].as_vec().into_iter().flatten())
        .filter_map(|step| step["run"].as_str())
        .collect()
}

/// The option that makes apt keep its packages in the directory of the
/// tools cache.
const APT_ARCHIVES: &str = "-o Dir::Cache::Archives=\"$HOME/.cache/krepi-ci/apt\"";
/// The commands that end a step that installs with apt. apt, which runs as
/// root, leaves beside the packages a lock and a partial directory that the
/// runner user cannot read, and `du` and the save of the workflow cache
/// would fail on them.
const APT_CLEANUP: [&str; 2] = [
    "sudo rm -rf ~/.cache/krepi-ci/apt/partial ~/.cache/krepi-ci/apt/lock",
    "sudo chown -R \"$(id -u):$(id -g)\" ~/.cache/krepi-ci/apt",
];

#[test]
fn every_apt_install_leaves_the_packages_alone_in_the_tools_cache() {
    let mut count = 0;
    for (path, document) in workflows() {
        for (key, job) in jobs(&document) {
            for script in scripts_of(job) {
                if !script.contains("apt-get install") {
                    continue;
                }
                count += 1;
                assert!(script.contains(APT_ARCHIVES), "{path}: {key}");
                let lines = logical_lines(script);
                let last: Vec<&str> = (lines.iter().rev().take(2).rev())
                    .map(|line| line.trim())
                    .collect();
                assert_eq!(last, APT_CLEANUP, "{path}: {key}");
            }
        }
    }
    // The two jobs that install in each of the pull request, full and
    // nightly lines, the suite of the weekly line and `cache build`.
    assert_eq!(count, 8);
}

/// The workflow that drafts a release.
const RELEASE: &str = ".github/workflows/release.yml";

#[test]
fn the_release_workflow_runs_on_main_by_hand_and_only_drafts() {
    let release = workflow(RELEASE);
    assert_eq!(events(&release), ["workflow_dispatch"]);
    let input = &release["on"]["workflow_dispatch"]["inputs"]["run"];
    assert_eq!(input["required"].as_bool(), Some(true));
    let all = jobs(&release);
    assert_eq!(
        all.iter().map(|(key, _)| *key).collect::<Vec<_>>(),
        ["assets", "draft"]
    );
    for (key, job) in &all {
        assert!(on_main(job), "{key}");
        let permissions = job["permissions"].as_hash().expect("the permissions");
        let grants: Vec<(&str, &str)> = (permissions.iter())
            .map(|(scope, level)| {
                (
                    scope.as_str().expect("a scope"),
                    level.as_str().expect("a level"),
                )
            })
            .collect();
        if *key == "draft" {
            assert_eq!(grants, [("contents", "write")]);
        } else {
            assert!(
                grants.iter().all(|(_, level)| *level == "read"),
                "{grants:?}"
            );
        }
    }
    // The assets are written by the repository's code with read permissions.
    let assets = &release["jobs"]["assets"];
    let script = scripts_of(assets).join("\n");
    assert!(
        script.contains("cargo xtask release-assets --run"),
        "{script}"
    );
    assert!(
        script.contains("cargo xtask run-record --id \"$INPUT_RUN\""),
        "{script}"
    );
    // The job with the write permission runs no code of the repository and
    // creates a draft only, between two checks that its tag does not exist.
    let draft = &release["jobs"]["draft"];
    assert_eq!(needs(draft), ["assets"]);
    assert!(steps_using(draft, "actions/checkout").is_empty());
    let script = scripts_of(draft).join("\n");
    for text in [
        "cargo ",
        "gh release",
        "draft=false",
        "PATCH",
        "--method PUT",
        "/git/refs",
    ] {
        assert!(!script.contains(text), "{text}");
    }
    let created = script
        .find("--method POST \"repos/$GITHUB_REPOSITORY/releases\"")
        .expect("the release is created");
    assert!(script.contains("-F draft=true -F prerelease=true -f make_latest=false"));
    let checks: Vec<usize> = script
        .match_indices("if [ \"$(tags)\" != 0 ]; then")
        .map(|(at, _)| at)
        .collect();
    assert_eq!(checks.len(), 2, "{script}");
    assert!(checks[0] < created && created < checks[1]);
    assert!(script.contains("sha256sum --check --strict SHA256SUMS"));
    let downloads = steps_using(draft, "actions/download-artifact");
    assert_eq!(downloads.len(), 1);
    assert_eq!(
        downloads[0]["with"]["name"].as_str(),
        Some("${{ needs.assets.outputs.artifact }}")
    );
    // That name is the name of the upload of the job that wrote the assets.
    let uploads = steps_using(assets, "actions/upload-artifact");
    assert_eq!(uploads.len(), 1);
    let name = uploads[0]["with"]["name"].as_str();
    assert!(name.is_some());
    assert_eq!(name, assets["outputs"]["artifact"].as_str());
}

/// The workflow of the monthly usage summary.
const USAGE: &str = ".github/workflows/usage.yml";

#[test]
fn the_usage_workflow_runs_monthly_and_by_hand_with_read_permissions() {
    let usage = workflow(USAGE);
    assert_eq!(events(&usage), ["schedule", "workflow_dispatch"]);
    // One schedule, on the second day of each month.
    let schedules = usage["on"]["schedule"].as_vec().expect("the schedule");
    assert_eq!(schedules.len(), 1);
    let cron = schedules[0]["cron"].as_str().expect("a cron");
    let fields: Vec<&str> = cron.split_whitespace().collect();
    assert_eq!(fields.len(), 5, "{cron}");
    assert_eq!(fields[2..], ["2", "*", "*"], "{cron}");
    let month = &usage["on"]["workflow_dispatch"]["inputs"]["month"];
    assert_eq!(month["required"].as_bool(), Some(false));
    let all = jobs(&usage);
    assert_eq!(all.len(), 1);
    let (_, job) = all[0];
    assert!(on_main(job));
    let permissions = job["permissions"].as_hash().expect("the permissions");
    assert!(!permissions.is_empty());
    for (scope, level) in permissions {
        assert_eq!(level.as_str(), Some("read"), "{scope:?}");
    }
    // The step that reads the data turns workflow commands off before it
    // reads anything and on again when it ends, and the summary is written
    // by the command.
    let read = (job["steps"].as_vec().into_iter().flatten())
        .find(|step| step["name"].as_str() == Some("Read the usage"))
        .and_then(|step| step["run"].as_str())
        .expect("the step that reads the data");
    let lines: Vec<&str> = read.lines().collect();
    assert_eq!(
        lines[..3],
        [
            "token=$(openssl rand -hex 16)",
            "echo \"::stop-commands::$token\"",
            "trap 'echo \"::$token::\"' EXIT",
        ]
    );
    assert!(read.contains("/actions/runs?created="));
    assert!(read.contains("jobs?filter=all"));
    assert!(read.contains("https://ghcr.io/token?scope=repository:$package:pull"));
    let scripts = scripts_of(job).join("\n");
    assert!(scripts.contains("cargo xtask usage --input artifacts/usage/input.json"));
    assert_eq!(
        usage["env"]["REPOSITORIES"].as_str(),
        Some("casxi-lab/krepi casxi-lab/kosmo casxi-lab/kalyx")
    );
}
