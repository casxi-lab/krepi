//! The manifest rules, each row of the mapping in a test of its own, the
//! union of rows, the selection of each line, the changed paths of a Git
//! repository, the digest check of the images, the judge of a case over
//! hand-written runs, and runs of the command on a fake QEMU.

use std::os::unix::fs::PermissionsExt;
use std::sync::atomic::AtomicI32;

use super::*;
use crate::scratch::Scratch;

/// The test image's line, written by hand.
const LINE: &[u8] = b"krepi test image: PL011 output, then PSCI SYSTEM_OFF\r\n";

/// A case with `runs` runs.
fn case(name: &str, smoke: bool, slow: bool, runs: u32) -> Case {
    Case {
        name: name.to_string(),
        smoke,
        slow,
        runs,
        timeout: 30,
    }
}

/// A suite of the test image that lists `paths`, with a smoke case, a case
/// that is neither smoke nor slow and a slow case.
fn suite(name: &str, paths: &[&str]) -> Suite {
    Suite {
        name: name.to_string(),
        image: "test-elf".to_string(),
        paths: paths.iter().map(|path| path.to_string()).collect(),
        cases: vec![
            case("smoke", true, false, 1),
            case("plain", false, false, 1),
            case("long", false, true, 3),
        ],
    }
}

/// The names of the cases that run, per suite.
fn names(plans: &[Plan]) -> Vec<(String, Vec<String>)> {
    (plans.iter())
        .map(|plan| {
            let cases = plan.cases.iter().map(|chosen| chosen.case.name.clone());
            (plan.suite.name.clone(), cases.collect())
        })
        .collect()
}

fn strings(paths: &[&str]) -> Vec<String> {
    paths.iter().map(|path| path.to_string()).collect()
}

#[test]
fn the_manifest_holds_the_suite_of_the_test_image() {
    let text = fs::read_to_string(crate::repo::root().join(MANIFEST)).expect("the manifest");
    let suites = load(&text).expect("the manifest keeps the rules");
    assert_eq!(
        suites,
        [Suite {
            name: "test-elf".to_string(),
            image: "test-elf".to_string(),
            paths: Vec::new(),
            cases: vec![case("boot", true, false, 1), case("repeat", false, true, 3)],
        }]
    );
}

#[test]
fn a_manifest_against_the_rules_is_refused() {
    let good = "[[suite]]\nname = \"a\"\nimage = \"test-elf\"\npaths = [\"kernel/x/\"]\n\
                [[suite.case]]\nname = \"c\"\nsmoke = true\nslow = false\nruns = 1\ntimeout = 30\n";
    assert_eq!(load(good).expect("a good manifest").len(), 1);
    let twice = format!("{good}{good}");
    let cases = [
        (good.replace("paths", "path"), "unknown field `path`"),
        (
            good.replace("timeout = 30\n", ""),
            "missing field `timeout`",
        ),
        (
            good.replace("runs = 1", "runs = 1\nwindow = 2"),
            "unknown field `window`",
        ),
        ("suite = []\n".to_string(), "no suite"),
        (twice, "the suite a occurs twice"),
        (
            good.replace("\"a\"", "\"A b\""),
            "the suite name \"A b\" is not plain",
        ),
        (
            good.replace("image = \"test-elf\"", "image = \"kernel\""),
            "suite a: no image source kernel",
        ),
        (
            good.replace("kernel/x/", "docs/"),
            "suite a: the path docs/ is not below kernel/ or user/",
        ),
        (
            good[..good.find("[[suite.case]]").expect("a case")].to_string(),
            "missing field `case`",
        ),
        (
            good[..good.find("[[suite.case]]").expect("a case")].to_string() + "case = []\n",
            "suite a: no case",
        ),
        (
            good.replace("slow = false", "slow = true"),
            "a smoke case is not slow",
        ),
        (good.replace("runs = 1", "runs = 0"), "runs is not 1 to 10"),
        (good.replace("runs = 1", "runs = 11"), "runs is not 1 to 10"),
        (
            good.replace("timeout = 30", "timeout = 0"),
            "timeout is not 1 to 600 seconds",
        ),
        (
            good.replace("timeout = 30", "timeout = 601"),
            "timeout is not 1 to 600 seconds",
        ),
        (good.replace("\"c\"", "\"c_d\""), "the name is not plain"),
    ];
    for (text, problem) in cases {
        let error = load(&text).expect_err("a manifest against a rule");
        assert!(error.starts_with("suites.toml: "), "{error}");
        assert!(error.contains(problem), "{problem}: {error}");
    }
    let doubled = good.replace(
        "timeout = 30\n",
        "timeout = 30\n[[suite.case]]\nname = \"c\"\nsmoke = false\nslow = false\nruns = 1\ntimeout = 9\n",
    );
    assert!(load(&doubled).is_err_and(|error| error.contains("the case occurs twice")));
}

/// The suites of the mapping tests: `a` lists a board directory, `b` lists
/// nothing.
fn mapped_suites() -> [Suite; 2] {
    [suite("a", &["kernel/boards/a/"]), suite("b", &[])]
}

/// The suites of [`mapped_suites`] that `paths` select, apart from their
/// smoke cases.
fn selected(paths: &[&str]) -> Vec<String> {
    let suites = mapped_suites();
    let plans = choose(&suites, Some(&strings(paths)), false);
    (plans.iter())
        .filter(|plan| matches!(&plan.why, Why::Paths(by) if !by.is_empty()))
        .map(|plan| plan.suite.name.clone())
        .collect()
}

/// Both suites of [`mapped_suites`].
fn every() -> Vec<String> {
    strings(&["a", "b"])
}

#[test]
fn mapping_row_1_the_host_tooling_selects_every_suite() {
    assert_eq!(selected(&["tools/src/qemu_run.rs"]), every());
    assert_eq!(mapping("tools/src/qemu_run.rs"), Selects::Every("tools/"));
}

#[test]
fn mapping_row_2_the_repository_tasks_select_every_suite() {
    assert_eq!(selected(&["xtask/src/suite.rs"]), every());
    assert_eq!(mapping("xtask/src/suite.rs"), Selects::Every("xtask/"));
}

#[test]
fn mapping_row_3_the_toolchain_files_and_the_cargo_configuration_select_every_suite() {
    for path in [
        "rust-toolchain.toml",
        "toolchains.toml",
        ".cargo/config.toml",
    ] {
        assert_eq!(selected(&[path]), every(), "{path}");
    }
}

#[test]
fn mapping_row_4_the_manifest_and_the_workflows_but_the_formal_ones_select_every_suite() {
    for path in [
        "suites.toml",
        ".github/workflows/check.yml",
        ".github/workflows/x/y.yaml",
    ] {
        assert_eq!(selected(&[path]), every(), "{path}");
    }
}

#[test]
fn mapping_row_5_the_kernel_and_user_space_select_the_suites_that_list_the_path() {
    assert_eq!(selected(&["kernel/boards/a/src/main.rs"]), ["a"]);
    assert_eq!(
        mapping("kernel/arch/src/lib.rs"),
        Selects::Listed("kernel/")
    );
    assert_eq!(selected(&["kernel/arch/src/lib.rs"]), Vec::<String>::new());
    assert_eq!(selected(&["user/Cargo.toml"]), Vec::<String>::new());
}

#[test]
fn mapping_row_6_any_other_path_selects_no_suite() {
    for path in [
        "docs/conventions/testing.md",
        "verification/open.json",
        "README.md",
        ".github/workflows/formal.yml",
        ".github/workflows/formal-canary.yml",
        "kernel",
        "toolsx/a",
    ] {
        assert_eq!(mapping(path), Selects::Nothing, "{path}");
        assert_eq!(selected(&[path]), Vec::<String>::new(), "{path}");
    }
}

#[test]
fn paths_of_several_rows_select_the_union_of_their_suites() {
    assert_eq!(selected(&["docs/a.md", "kernel/boards/a/x"]), ["a"]);
    let suites = mapped_suites();
    let plans = choose(
        &suites,
        Some(&strings(&["kernel/boards/a/x", "xtask/y"])),
        false,
    );
    assert_eq!(
        plans[0].why,
        Why::Paths(vec![
            (
                "kernel/boards/a/x".to_string(),
                "kernel/boards/a/".to_string()
            ),
            ("xtask/y".to_string(), "xtask/".to_string()),
        ])
    );
}

#[test]
fn each_line_runs_its_cases() {
    let suites = [suite("a", &["kernel/boards/a/"]), suite("b", &[])];
    let both = |cases: &[&str]| {
        let cases: Vec<String> = cases.iter().map(|case| case.to_string()).collect();
        vec![("a".to_string(), cases.clone()), ("b".to_string(), cases)]
    };
    // A pull request: the smoke cases always, the other cases that are not
    // slow of the suites that its paths select.
    let docs = strings(&["docs/a.md"]);
    assert_eq!(
        names(&choose(&suites, Some(&docs), false)),
        both(&["smoke"])
    );
    let board = strings(&["kernel/boards/a/x"]);
    assert_eq!(
        names(&choose(&suites, Some(&board), false)),
        [
            ("a".to_string(), strings(&["smoke", "plain"])),
            ("b".to_string(), strings(&["smoke"])),
        ]
    );
    let tools = strings(&["tools/x"]);
    assert_eq!(
        names(&choose(&suites, Some(&tools), false)),
        both(&["smoke", "plain"])
    );
    // The full line and the nightly line: every case of every suite.
    assert_eq!(
        names(&choose(&suites, None, true)),
        both(&["smoke", "plain", "long"])
    );
    // The main line and the weekly line: every case that is not slow.
    assert_eq!(
        names(&choose(&suites, None, false)),
        both(&["smoke", "plain"])
    );
    // The reasons that the report gives.
    let plans = choose(&suites, Some(&board), true);
    let reasons: Vec<Vec<&str>> = plans[0].cases.iter().map(|c| c.reasons.clone()).collect();
    assert_eq!(
        reasons,
        [
            vec!["smoke case", "the changed paths select its suite"],
            vec!["the changed paths select its suite"],
            vec!["the changed paths select its suite", "slow cases run"],
        ]
    );
    assert_eq!(plans[1].cases.len(), 1);
    assert_eq!(plans[1].why, Why::Paths(Vec::new()));
    let every = choose(&suites, None, true);
    assert_eq!(every[0].why, Why::Every);
    assert_eq!(
        every[0].cases[2].reasons,
        ["every suite runs", "slow cases run"]
    );
    // The manifest of the repository: the slow case runs only with --slow.
    let text = fs::read_to_string(crate::repo::root().join(MANIFEST)).expect("the manifest");
    let manifest = load(&text).expect("the manifest");
    for (changed, slow, expected) in [
        (Some(docs.as_slice()), false, &["boot"][..]),
        (Some(tools.as_slice()), false, &["boot"]),
        (None, true, &["boot", "repeat"]),
        (None, false, &["boot"]),
    ] {
        let plans = choose(&manifest, changed, slow);
        assert_eq!(names(&plans), [("test-elf".to_string(), strings(expected))]);
    }
}

/// Runs git in `dir` without the configuration of the host.
fn git_in(dir: &Path, args: &[&str]) {
    let status = Command::new("git")
        .args(args)
        .current_dir(dir)
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_AUTHOR_NAME", "a")
        .env("GIT_AUTHOR_EMAIL", "a@example.com")
        .env("GIT_COMMITTER_NAME", "a")
        .env("GIT_COMMITTER_EMAIL", "a@example.com")
        .status()
        .expect("run git");
    assert!(status.success(), "git {args:?}");
}

#[test]
fn the_changed_paths_are_those_since_the_merge_base() {
    let scratch = Scratch::temporary("suite-git");
    let dir = &scratch.0;
    git_in(dir, &["init", "--quiet", "--initial-branch=main"]);
    scratch.write("tools/a.rs", "a\n");
    scratch.write("docs/b.md", "b\n");
    scratch.write("kernel/c.rs", "c\n");
    git_in(dir, &["add", "--all"]);
    git_in(dir, &["commit", "--quiet", "-m", "base"]);
    git_in(dir, &["switch", "--quiet", "-c", "topic"]);
    // A rename, a deletion and a change on the branch.
    git_in(dir, &["mv", "tools/a.rs", "kernel/a.rs"]);
    git_in(dir, &["rm", "--quiet", "docs/b.md"]);
    scratch.write("kernel/c.rs", "c, changed\n");
    git_in(dir, &["commit", "--quiet", "--all", "-m", "topic"]);
    // main moves on after the branch left it, with a change of its own.
    git_in(dir, &["switch", "--quiet", "main"]);
    scratch.write("xtask/d.rs", "d\n");
    git_in(dir, &["add", "--all"]);
    git_in(dir, &["commit", "--quiet", "-m", "main"]);
    git_in(dir, &["switch", "--quiet", "topic"]);
    let base =
        String::from_utf8(git(dir, &["rev-parse", "main~1"]).expect("the base")).expect("UTF-8");
    let (merge_base, paths) = changed(dir, "main").expect("the changed paths");
    assert_eq!(merge_base, base.trim());
    // Both sides of the rename count; the change on main does not.
    assert_eq!(
        paths,
        ["docs/b.md", "kernel/a.rs", "kernel/c.rs", "tools/a.rs"]
    );
    assert!(changed(dir, "--all").is_err());
    assert!(changed(dir, "no-such-branch").is_err_and(|error| error.starts_with("git merge-base")));
}

/// Writes the images of [`image::SOURCES`] into `dir` with a commit.
fn images(dir: &Path) -> Record {
    image::write(dir, &image::SOURCES, &"0".repeat(40)).expect("write the images")
}

#[test]
fn an_image_is_taken_only_with_its_expected_digest() {
    let scratch = Scratch::temporary("suite-images");
    let dir = scratch.0.join("images");
    let record = images(&dir);
    let digest = record.images[0].sha256.clone();
    let needed: BTreeSet<&str> = ["test-elf"].into();
    let expect = |digest: &str| vec![("test-elf".to_string(), digest.to_string())];
    let ready = take_images(&dir, &needed, &expect(&digest)).expect("the image is ready");
    assert_eq!(
        ready,
        [Ready {
            name: "test-elf".to_string(),
            path: dir.join("test-elf.elf"),
            bytes: 8_760,
            sha256: digest.clone(),
            expected: Some(digest.clone()),
        }]
    );
    // Another expected digest.
    let other = "1".repeat(64);
    let problems = take_images(&dir, &needed, &expect(&other)).expect_err("another digest");
    assert_eq!(
        problems,
        [format!(
            "test-elf: the SHA-256 of the file is {digest}, not the expected {other}"
        )]
    );
    // No expected digest, and an image that the record does not name.
    let problems = take_images(&dir, &needed, &[]).expect_err("no digest");
    assert_eq!(problems, ["no --expect test-elf=<SHA-256> is given"]);
    let kernel: BTreeSet<&str> = ["kernel"].into();
    let problems = take_images(&dir, &kernel, &expect(&digest)).expect_err("no entry");
    assert!(
        problems[0].ends_with("names no image kernel"),
        "{problems:?}"
    );
    // A file that no longer matches the record, nor the digest.
    fs::write(dir.join("test-elf.elf"), b"another image").expect("replace the image");
    let problems = take_images(&dir, &needed, &expect(&digest)).expect_err("a changed file");
    assert_eq!(problems.len(), 2, "{problems:?}");
    assert!(
        problems[0].starts_with("test-elf: the file has 13 bytes"),
        "{problems:?}"
    );
    // A record that names a file outside the directory.
    let text = record
        .render()
        .replace("\"test-elf.elf\"", "\"../test-elf.elf\"");
    fs::write(dir.join(image::RECORD), text).expect("rewrite the record");
    let problems = take_images(&dir, &needed, &expect(&digest)).expect_err("a path");
    assert_eq!(
        problems,
        ["the file \"../test-elf.elf\" of test-elf is not a plain name"]
    );
    fs::remove_file(dir.join(image::RECORD)).expect("remove the record");
    let problems = take_images(&dir, &needed, &expect(&digest)).expect_err("no record");
    assert!(problems[0].starts_with("cannot read "), "{problems:?}");
}

/// The receipt of the runner for a good run of the test image with the
/// digest `image` and the transcript `transcript`.
fn receipt(image: &str, transcript: &[u8]) -> Value {
    json!({
        "schema_version": 1,
        "exit_reason": "guest_shutdown",
        "image": {"path": "/x/test-elf.elf", "bytes": 8760, "sha256": image},
        "transcript": {"file": "transcript.bin", "bytes": transcript.len(), "sha256": sha256(transcript)},
    })
}

fn good(image: &str) -> Run {
    Run {
        receipt: receipt(image, LINE),
        transcript: LINE.to_vec(),
    }
}

/// The names of the checks that failed.
fn failed(checks: &[Check]) -> Vec<&str> {
    (checks.iter())
        .filter(|check| check.failure.is_some())
        .map(|check| check.name.as_str())
        .collect()
}

#[test]
fn the_judge_passes_good_runs_and_fails_each_fault() {
    let digest = "a".repeat(64);
    let one = case("boot", true, false, 1);
    let three = case("repeat", false, true, 3);
    let checks = judge("test-elf", &digest, &one, &[good(&digest)]);
    let names: Vec<&str> = checks.iter().map(|check| check.name.as_str()).collect();
    assert_eq!(names, ["run 1 receipt", "run 1 transcript", "runs"]);
    assert_eq!(failed(&checks), Vec::<&str>::new());
    let runs = vec![good(&digest), good(&digest), good(&digest)];
    let checks = judge("test-elf", &digest, &three, &runs);
    assert_eq!(checks.len(), 9);
    assert_eq!(failed(&checks), Vec::<&str>::new());
    // Each fault of a receipt.
    for (key, value) in [
        ("errors", json!(["a write failed"])),
        ("exit_reason", json!("deadline")),
        ("image", json!({"sha256": "b".repeat(64)})),
        ("transcript", json!({"sha256": "c".repeat(64)})),
    ] {
        let mut run = good(&digest);
        run.receipt[key] = value;
        let checks = judge("test-elf", &digest, &one, &[run]);
        assert_eq!(failed(&checks), ["run 1 receipt"], "{key}");
    }
    // Another transcript, which the receipt describes.
    let other = b"krepi test image: PL011 output\r\n";
    let run = Run {
        receipt: receipt(&digest, other),
        transcript: other.to_vec(),
    };
    let checks = judge("test-elf", &digest, &one, std::slice::from_ref(&run));
    assert_eq!(failed(&checks), ["run 1 transcript"]);
    // Too few runs, and runs that disagree.
    let checks = judge("test-elf", &digest, &three, &runs[..2]);
    assert_eq!(failed(&checks), ["runs"]);
    let mut late = good(&digest);
    late.receipt["exit_reason"] = json!("deadline");
    let checks = judge(
        "test-elf",
        &digest,
        &three,
        &[good(&digest), late, good(&digest)],
    );
    assert_eq!(failed(&checks), ["run 2 receipt", "equal exit reasons"]);
    let checks = judge(
        "test-elf",
        &digest,
        &three,
        &[good(&digest), run, good(&digest)],
    );
    assert_eq!(
        failed(&checks),
        ["run 2 transcript", "identical transcripts"]
    );
    // An image without an expected output passes no transcript.
    let checks = judge("kernel", &digest, &one, &[good(&digest)]);
    assert_eq!(failed(&checks), ["run 1 transcript"]);
}

/// A fake QEMU in `scratch` that answers `--version` and otherwise prints
/// `output` and exits with `status`.
fn fake_qemu(scratch: &Scratch, output: &str, status: u8) -> PathBuf {
    let path = scratch.0.join("qemu");
    scratch.write(
        "qemu",
        &format!(
            "#!/bin/sh\nif [ \"$1\" = --version ]; then\n  echo 'QEMU emulator version 0.0.0'\n  \
             exit 0\nfi\nprintf '{output}'\nexit {status}\n"
        ),
    );
    fs::set_permissions(&path, fs::Permissions::from_mode(0o755))
        .expect("make the script executable");
    path
}

/// An interrupt flag that no signal sets.
fn flag() -> &'static AtomicI32 {
    Box::leak(Box::new(AtomicI32::new(0)))
}

/// Runs the command with `args` on the manifest `manifest` in a Git
/// repository of its own: its status, its report and the lines it printed.
fn command_run(scratch: &Scratch, manifest: &str, args: &[&str]) -> (u8, Value, Vec<String>) {
    let root = scratch.0.join("repository");
    fs::create_dir_all(&root).expect("the repository");
    fs::write(root.join(MANIFEST), manifest).expect("the manifest");
    git_in(&root, &["init", "--quiet"]);
    git_in(&root, &["add", "--all"]);
    git_in(&root, &["commit", "--quiet", "-m", "manifest"]);
    let choice = parse(args).expect("the options");
    let flag = flag();
    let mut out = Out {
        failed: false,
        kept: Some(Vec::new()),
    };
    let code = run(
        &root,
        &choice,
        &Timing::QEMU_VIRT,
        &mut || Ok(flag),
        &mut out,
    );
    let output = choice.output.expect("an output directory");
    let text = fs::read_to_string(output.join(SUMMARY_FILE)).expect("the report");
    let report = serde_json::from_str(&text).expect("the report is JSON");
    (code, report, out.kept.unwrap_or_default())
}

#[test]
fn the_command_runs_the_selected_cases_and_reports_them() {
    let scratch = Scratch::temporary("suite-run");
    let line = "krepi test image: PL011 output, then PSCI SYSTEM_OFF\\r\\n";
    let qemu = fake_qemu(&scratch, line, 0);
    let manifest = fs::read_to_string(crate::repo::root().join(MANIFEST)).expect("the manifest");
    let output = scratch.0.join("out");
    let (output, qemu) = (
        output.to_str().expect("UTF-8"),
        qemu.to_str().expect("UTF-8"),
    );
    let (code, report, lines) = command_run(
        &scratch,
        &manifest,
        &["--qemu", qemu, "--output-dir", output],
    );
    assert_eq!(code, 0, "{report:#}");
    let summary = Path::new(output).join(SUMMARY_FILE);
    assert_eq!(
        lines,
        [
            "every suite runs".to_string(),
            "suite test-elf: every suite runs".to_string(),
            "test-elf/boot-1: guest_shutdown, 54 bytes of serial output".to_string(),
            "test-elf/boot: PASS (every suite runs)".to_string(),
            format!("PASS: {}", summary.display()),
        ]
    );
    assert_eq!(report["status"], "PASS");
    assert_eq!(report["format"], 1);
    assert_eq!(report["selection"]["slow"], false);
    assert_eq!(report["selection"]["base"], Value::Null);
    let suites = report["suites"].as_array().expect("the suites");
    assert_eq!(suites.len(), 1);
    assert_eq!(suites[0]["name"], "test-elf");
    assert_eq!(suites[0]["selected"], "every suite runs");
    // Only the selected case is listed.
    let cases = suites[0]["cases"].as_array().expect("the cases");
    assert_eq!(cases.len(), 1);
    assert_eq!(cases[0]["name"], "boot");
    assert_eq!(cases[0]["status"], "PASS");
    assert_eq!(cases[0]["reasons"], json!(["every suite runs"]));
    assert_eq!(cases[0]["results"][0]["exit_reason"], "guest_shutdown");
    let directory = Path::new(output).join("test-elf/boot-1");
    assert_eq!(
        fs::read(directory.join(qemu_run::TRANSCRIPT_FILE)).expect("the transcript"),
        LINE
    );
    let images = report["images"].as_array().expect("the images");
    assert_eq!(images[0]["name"], "test-elf");
    assert_eq!(images[0]["expected"], Value::Null);
    assert!(Path::new(output).join("images/images.json").is_file());
    // With --slow, three more runs of the slow case.
    let output = scratch.0.join("slow");
    let output = output.to_str().expect("UTF-8");
    let args = ["--slow", "--qemu", qemu, "--output-dir", output];
    let (code, report, _) = command_run(&Scratch::temporary("suite-run-slow"), &manifest, &args);
    assert_eq!(code, 0, "{report:#}");
    let cases = report["suites"][0]["cases"].as_array().expect("the cases");
    let names: Vec<&str> = cases
        .iter()
        .map(|case| case["name"].as_str().unwrap_or(""))
        .collect();
    assert_eq!(names, ["boot", "repeat"]);
    assert_eq!(cases[1]["results"].as_array().map(Vec::len), Some(3));
    assert_eq!(
        cases[1]["reasons"],
        json!(["every suite runs", "slow cases run"])
    );
}

#[test]
fn a_wrong_guest_fails_and_a_wrong_image_is_not_booted() {
    let manifest = fs::read_to_string(crate::repo::root().join(MANIFEST)).expect("the manifest");
    // A guest that writes another line fails its case.
    let scratch = Scratch::temporary("suite-fail");
    let qemu = fake_qemu(&scratch, "another line\\r\\n", 0);
    let output = scratch.0.join("out");
    let (output, qemu) = (
        output.to_str().expect("UTF-8"),
        qemu.to_str().expect("UTF-8"),
    );
    let (code, report, _) = command_run(
        &scratch,
        &manifest,
        &["--qemu", qemu, "--output-dir", output],
    );
    assert_eq!(code, 1, "{report:#}");
    assert_eq!(report["status"], "FAIL");
    let checks = &report["suites"][0]["cases"][0]["checks"];
    assert_eq!(checks[1]["name"], "run 1 transcript");
    assert_eq!(checks[1]["status"], "FAIL");
    // A missing QEMU is an error of the case.
    let scratch = Scratch::temporary("suite-error");
    let missing = scratch.0.join("no-qemu");
    let output = scratch.0.join("out");
    let (output, missing) = (
        output.to_str().expect("UTF-8"),
        missing.to_str().expect("UTF-8"),
    );
    let (code, report, _) = command_run(
        &scratch,
        &manifest,
        &["--qemu", missing, "--output-dir", output],
    );
    assert_eq!(code, 2, "{report:#}");
    assert_eq!(report["status"], "ERROR");
    // An image whose digest is not the expected one: no run starts.
    let scratch = Scratch::temporary("suite-digest");
    let qemu = fake_qemu(&scratch, "x", 0);
    let dir = scratch.0.join("images");
    images(&dir);
    let expect = format!("test-elf={}", "1".repeat(64));
    let output = scratch.0.join("out");
    let (output, qemu, dir) = (
        output.to_str().expect("UTF-8"),
        qemu.to_str().expect("UTF-8"),
        dir.to_str().expect("UTF-8"),
    );
    let args = [
        "--images",
        dir,
        "--expect",
        &expect,
        "--qemu",
        qemu,
        "--output-dir",
        output,
    ];
    let (code, report, _) = command_run(&scratch, &manifest, &args);
    assert_eq!(code, 2, "{report:#}");
    assert_eq!(report["status"], "ERROR");
    assert_eq!(report["suites"], json!([]));
    let errors = report["errors"].as_array().expect("the errors");
    assert!(
        errors[0]
            .as_str()
            .unwrap_or("")
            .contains("not the expected"),
        "{errors:?}"
    );
    let mut names: Vec<String> = (fs::read_dir(output).expect("the output"))
        .map(|entry| {
            entry
                .expect("an entry")
                .file_name()
                .to_string_lossy()
                .into_owned()
        })
        .collect();
    names.sort();
    assert_eq!(names, [SUMMARY_FILE]);
}

#[test]
fn the_command_line_takes_the_options_of_each_line() {
    let digest = "0123456789abcdef".repeat(4);
    let expect = format!("test-elf={digest}");
    let choice = parse(&[
        "--base", "abc", "--images", "i", "--expect", &expect, "--slow",
    ])
    .expect("the options");
    assert_eq!(
        choice,
        Choice {
            base: Some("abc".to_string()),
            slow: true,
            images: Some(PathBuf::from("i")),
            expect: vec![("test-elf".to_string(), digest.clone())],
            qemu: None,
            output: None,
        }
    );
    assert_eq!(parse(&[]).expect("no option").base, None);
    for wrong in [
        &["--expect", expect.as_str()][..],
        &["--images", "i", "--expect", "test-elf"],
        &["--images", "i", "--expect", "test-elf=ABC"],
        &["--images", "i", "--expect", "=0"],
        &["--slow", "--slow"],
        &["extra"],
    ] {
        let error = parse(wrong).expect_err("a usage error");
        assert_eq!(error.exit_code(), 2, "{wrong:?}");
    }
    assert_eq!(parse(&["--help"]).expect_err("the help").exit_code(), 0);
}
