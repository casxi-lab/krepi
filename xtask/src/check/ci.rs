//! Tests of the committed workflows: those of the CI lines, the pull request
//! line and the main line in `check.yml`, the full line, the nightly line
//! and the weekly line, of the record workflow, and the retention of the
//! artifacts of every workflow. They run in the `test` step; the rules hold
//! for these files only and are not part of the workflows step.

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
const RETENTION: [(&str, &str, &str, &str); 19] = [
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
        "leanchecker",
        "Upload the measurement",
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
        ".github/workflows/run-record.yml",
        "record",
        "Upload the record",
        BY_RECORD,
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
