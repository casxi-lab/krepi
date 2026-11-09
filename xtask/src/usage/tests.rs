//! The summary of data written for each rule: the minutes and the runner
//! classes, the period, the storage, the caches, the thresholds, the
//! escaping of the summary, the input and the command.

use super::*;
use crate::scratch::Scratch;

/// The start of the period: 2026-11-01T00:00:00Z.
const START: u64 = 1_793_491_200;
/// The end of the period, 30 days later.
const END: u64 = START + 30 * 86_400;

/// A job that ran on a standard runner for `seconds` from the start.
fn job(id: u64, seconds: u64) -> Job {
    Job {
        id,
        labels: vec!["ubuntu-24.04-arm".to_string()],
        runner_group_name: Some("GitHub Actions".to_string()),
        runner_name: Some("GitHub Actions 1".to_string()),
        started_at: Some(START + 10),
        completed_at: Some(START + 10 + seconds),
    }
}

/// A run of the workflow `path` created at `created_at` with `jobs`.
fn run(id: u64, created_at: u64, path: &str, jobs: Vec<Job>) -> Run {
    Run {
        id,
        created_at,
        path: path.to_string(),
        event: "push".to_string(),
        run_attempt: 1,
        jobs,
    }
}

/// A repository `name` with `runs`, no artifact and no cache.
fn repository(name: &str, runs: Vec<Run>) -> Repository {
    Repository {
        repository: name.to_string(),
        runs,
        artifacts: Vec::new(),
        cache: Cache {
            active_caches_count: 0,
            active_caches_size_in_bytes: 0,
        },
    }
}

/// The data of the period with `repositories` and no package.
fn input(repositories: Vec<Repository>) -> Input {
    Input {
        period: Period {
            month: "2026-11".to_string(),
            start: START,
            end: END,
            from: "2026-11-01T00:00:00Z".to_string(),
            until: "2026-12-01T00:00:00Z".to_string(),
            partial: false,
        },
        rate_limit: RateLimit {
            limit: 15_000,
            remaining_before: 14_990,
            remaining_after: 14_100,
        },
        repositories,
        packages: Vec::new(),
    }
}

/// The value of the threshold item that starts with `item`.
fn threshold(usage: &Value, item: &str) -> (u64, bool) {
    let found = (usage["thresholds"].as_array().into_iter().flatten())
        .find(|threshold| {
            threshold["item"]
                .as_str()
                .is_some_and(|text| text.starts_with(item))
        })
        .unwrap_or_else(|| panic!("no threshold {item}"));
    (
        found["value"].as_u64().expect("a value"),
        found["above"].as_bool().expect("a flag"),
    )
}

#[test]
fn each_job_counts_its_seconds_rounded_up_to_minutes_by_its_runner_class() {
    let check = ".github/workflows/check.yml";
    let mut none = job(5, 600);
    none.runner_name = None;
    let mut larger = job(6, 30);
    larger.runner_group_name = Some("Larger".to_string());
    let mut own = job(7, 61);
    own.labels.push("self-hosted".to_string());
    let mut unfinished = job(8, 0);
    unfinished.completed_at = None;
    let runs = vec![run(
        1,
        START,
        check,
        vec![
            job(1, 59),
            job(2, 60),
            job(3, 61),
            job(4, 0),
            none,
            larger,
            own,
            unfinished,
        ],
    )];
    let usage = usage(&input(vec![repository("casxi-lab/krepi", runs)]));
    let krepi = &usage["repositories"][0];
    // 1 + 1 + 2 + 0 standard minutes; a job on no runner takes none.
    assert_eq!(
        krepi["minutes"],
        json!({"standard hosted": 4, "larger hosted": 1, "self-hosted": 2})
    );
    assert_eq!(usage["minutes"], krepi["minutes"]);
    assert_eq!(krepi["jobs"], 8);
    assert_eq!(krepi["unfinished_jobs"], json!([{"run": 1, "job": 8}]));
    assert_eq!(
        krepi["by_label"],
        json!([
            {"labels": "ubuntu-24.04-arm", "class": "larger hosted", "minutes": 1},
            {"labels": "ubuntu-24.04-arm", "class": "standard hosted", "minutes": 4},
            {"labels": "ubuntu-24.04-arm, self-hosted", "class": "self-hosted", "minutes": 2},
        ])
    );
    assert_eq!(threshold(&usage, "larger hosted"), (1, true));
    assert_eq!(threshold(&usage, "self-hosted"), (2, true));
    assert_eq!(threshold(&usage, "standard hosted"), (4, false));
}

#[test]
fn a_run_counts_once_and_only_in_its_period() {
    let check = ".github/workflows/check.yml";
    let codeql = "dynamic/github-code-scanning/codeql";
    let mut x64 = job(4, 200);
    x64.labels = vec!["ubuntu-latest".to_string()];
    let runs = vec![
        run(1, START, check, vec![job(1, 60)]),
        // The same run, listed for two days, and a job listed twice.
        run(1, START, check, vec![job(1, 60)]),
        run(2, END - 1, check, vec![job(2, 60), job(2, 60)]),
        // Before and after the period.
        run(3, START - 1, check, vec![job(3, 600)]),
        run(5, END, check, vec![job(5, 600)]),
        run(4, START + 100, codeql, vec![x64]),
    ];
    let usage = usage(&input(vec![repository("casxi-lab/krepi", runs)]));
    let krepi = &usage["repositories"][0];
    assert_eq!(krepi["runs"], 3);
    assert_eq!(krepi["jobs"], 3);
    assert_eq!(krepi["minutes"]["standard hosted"], 2 + 4);
    assert_eq!(
        krepi["by_workflow"],
        json!([
            {"path": check, "runs": 2, "minutes": 2},
            {"path": codeql, "runs": 1, "minutes": 4},
        ])
    );
    assert_eq!(
        krepi["by_label"][1],
        json!({"labels": "ubuntu-latest", "class": "standard hosted", "minutes": 4})
    );
    // The minutes of the repositories add up.
    let other = repository(
        "casxi-lab/kalyx",
        vec![run(9, START, check, vec![job(9, 3600)])],
    );
    let both = super::usage(&input(vec![
        repository(
            "casxi-lab/krepi",
            vec![run(1, START, check, vec![job(1, 60)])],
        ),
        other,
    ]));
    assert_eq!(both["minutes"]["standard hosted"], 61);
}

#[test]
fn storage_counts_unexpired_artifacts_and_each_blob_once() {
    let mut krepi = repository("casxi-lab/krepi", Vec::new());
    krepi.artifacts = vec![
        Artifact {
            size_in_bytes: 1_000,
            expired: false,
        },
        Artifact {
            size_in_bytes: 7_000,
            expired: true,
        },
        Artifact {
            size_in_bytes: 500,
            expired: false,
        },
    ];
    let mut data = input(vec![krepi]);
    let blob = |digest: &str, size: u64| Blob {
        digest: format!("sha256:{digest}"),
        size,
    };
    // Two tags share the base layer and their config.
    data.packages = vec![Package {
        name: "casxi-lab/krepi-formal".to_string(),
        tags: vec![
            Tag {
                tag: "a".to_string(),
                blobs: vec![blob("c", 10), blob("base", 100), blob("a", 1_000)],
            },
            Tag {
                tag: "b".to_string(),
                blobs: vec![blob("c", 10), blob("base", 100), blob("b", 2_000)],
            },
        ],
    }];
    let usage = usage(&data);
    assert_eq!(usage["repositories"][0]["artifacts"], 2);
    assert_eq!(usage["artifact_bytes"], 1_500);
    assert_eq!(
        usage["packages"],
        json!([{"name": "casxi-lab/krepi-formal", "tags": ["a", "b"], "blobs": 4, "bytes": 3_110}])
    );
    assert_eq!(usage["package_bytes"], 3_110);
    assert_eq!(usage["storage_bytes"], 4_610);
    assert_eq!(usage["storage_limit"], STORAGE);
    assert_eq!(threshold(&usage, "bytes of the artifacts"), (4_610, false));
}

#[test]
fn each_threshold_is_above_only_past_its_value() {
    let check = ".github/workflows/check.yml";
    let at = |minutes: u64, storage: u64, cache: u64| {
        let mut krepi = repository(
            "casxi-lab/krepi",
            vec![run(1, START, check, vec![job(1, minutes * 60)])],
        );
        krepi.artifacts = vec![Artifact {
            size_in_bytes: storage,
            expired: false,
        }];
        krepi.cache.active_caches_size_in_bytes = cache;
        let usage = usage(&input(vec![
            krepi,
            repository("casxi-lab/kosmo", Vec::new()),
        ]));
        [
            threshold(&usage, "standard hosted").1,
            threshold(&usage, "bytes of the artifacts").1,
            threshold(&usage, "bytes of the cache of casxi-lab/krepi").1,
            threshold(&usage, "bytes of the cache of casxi-lab/kosmo").1,
        ]
    };
    assert_eq!(at(40_000, 40_000_000_000, 8_000_000_000), [false; 4]);
    assert_eq!(
        at(40_001, 40_000_000_001, 8_000_000_001),
        [true, true, true, false]
    );
    let usage = usage(&input(Vec::new()));
    assert_eq!(usage["thresholds"].as_array().map(Vec::len), Some(4));
    let summary = summary(&usage);
    assert!(
        summary.ends_with("\nNo item is above its threshold.\n"),
        "{summary}"
    );
    let mut krepi = repository("casxi-lab/krepi", Vec::new());
    krepi.cache.active_caches_size_in_bytes = 9_000_000_000;
    let summary = super::summary(&super::usage(&input(vec![krepi])));
    assert!(
        summary
            .ends_with("\nThe bytes of the cache of casxi-lab/krepi are above their threshold.\n"),
        "{summary}"
    );
}

#[test]
fn the_summary_escapes_the_text_of_the_data() {
    let path = ".github/workflows/a|b`c`\n::warning::d.yml";
    let mut data = input(vec![repository(
        "casxi-lab/krepi",
        vec![run(1, START, path, vec![job(1, 60)])],
    )]);
    data.period.partial = true;
    data.period.until = "2026-11-09T20:00:00Z".to_string();
    let summary = summary(&usage(&data));
    assert!(
        summary.contains(
            "| casxi-lab/krepi | .github/workflows/a\\|b'c'\\\\n::warning::d.yml | 1 | 1 |\n"
        ),
        "{summary}"
    );
    assert!(!summary.lines().any(|line| line.starts_with("::")));
    assert!(summary.starts_with(
        "## CI usage of 2026-11\n\nThe period runs from 2026-11-01T00:00:00Z to \
         2026-11-09T20:00:00Z, the time of this summary, before the end of the month. \
         Minutes are"
    ));
    assert!(summary.contains("The API allowed 15000 requests an hour; 14990 remained"));
}

#[test]
fn the_command_reads_a_strict_input_into_a_new_directory() {
    let scratch = Scratch::temporary("usage");
    let text = json!({
        "period": {
            "month": "2026-11", "start": START, "end": END,
            "from": "2026-11-01T00:00:00Z", "until": "2026-12-01T00:00:00Z", "partial": false,
        },
        "rate_limit": {"limit": 15000, "remaining_before": 14990, "remaining_after": 14100},
        "repositories": [{
            "repository": "casxi-lab/krepi",
            "runs": [{
                "id": 1, "created_at": START, "path": ".github/workflows/check.yml",
                "event": "push", "run_attempt": 1,
                "jobs": [{
                    "id": 1, "labels": ["ubuntu-24.04-arm"], "runner_group_name": "GitHub Actions",
                    "runner_name": "GitHub Actions 1", "started_at": START, "completed_at": START + 61,
                }],
            }],
            "artifacts": [{"size_in_bytes": 10, "expired": false}],
            "cache": {"active_caches_count": 1, "active_caches_size_in_bytes": 20},
        }],
        "packages": [{"name": "casxi-lab/krepi-formal", "tags": [
            {"tag": "a", "blobs": [{"digest": "sha256:a", "size": 30}]},
        ]}],
    });
    scratch.write("input.json", &text.to_string());
    let input_file = scratch.0.join("input.json");
    let output = scratch.0.join("out");
    let files = write(&input_file, &output).expect("the summary");
    assert_eq!(files, [output.join(USAGE_FILE), output.join(SUMMARY_FILE)]);
    let written: Value =
        serde_json::from_str(&fs::read_to_string(&files[0]).expect("the summary")).expect("JSON");
    let data: Input = serde_json::from_value(text.clone()).expect("the input");
    assert_eq!(written, usage(&data));
    assert_eq!(written["minutes"]["standard hosted"], 2);
    assert_eq!(written["storage_bytes"], 40);
    assert_eq!(
        fs::read_to_string(&files[1]).expect("the summary"),
        summary(&written)
    );
    // The directory must be new.
    let again = write(&input_file, &output).expect_err("the directory exists");
    assert!(
        again.ends_with("exists; the directory must be new"),
        "{again}"
    );
    // A field that the summary does not read, and a period that ends
    // before it starts.
    let mut extra = text.clone();
    extra["repositories"][0]["runs"][0]["actor"] = json!({});
    scratch.write("input.json", &extra.to_string());
    let error = write(&input_file, &scratch.0.join("other")).expect_err("an unknown field");
    assert!(error.contains("unknown field `actor`"), "{error}");
    let mut backwards = text;
    backwards["period"]["end"] = json!(START);
    scratch.write("input.json", &backwards.to_string());
    let error = write(&input_file, &scratch.0.join("other")).expect_err("an empty period");
    assert!(
        error.ends_with("not after its start at 1793491200"),
        "{error}"
    );
    // The command line.
    let args = ["--input", "a"];
    let error = cli().try_get_matches_from(args).expect_err("a usage error");
    assert_eq!(error.exit_code(), 2);
}
