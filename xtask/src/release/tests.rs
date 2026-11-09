//! The assets of a run written for the purpose, and each check on its own
//! input.

use super::*;
use crate::formal::toolchain::sha256;
use crate::scratch::Scratch;

const COMMIT: &str = "0123456789abcdef0123456789abcdef01234567";
const IMAGE: &str = "an image";

/// A successful run of the workflow check on a push to main.
fn run() -> RunData {
    RunData {
        id: 42,
        attempt: 1,
        workflow: "check".to_string(),
        path: WORKFLOW.to_string(),
        event: "push".to_string(),
        head_branch: Some("main".to_string()),
        head_sha: COMMIT.to_string(),
        conclusion: Some("success".to_string()),
    }
}

/// The record of one image `file` with `bytes` of the commit `commit`.
fn record(file: &str, bytes: &str, commit: &str) -> String {
    let record = image::Record {
        format: image::FORMAT,
        images: vec![image::Image {
            name: "test-elf".to_string(),
            file: file.to_string(),
            bytes: bytes.len() as u64,
            sha256: sha256(bytes.as_bytes()),
            commit: commit.to_string(),
        }],
    };
    record.render()
}

/// A receipt of the check with `fields` in place of the good ones.
fn receipt(format: u32, commit: &str, result: &str) -> String {
    format!(
        "{{\"format\": {format}, \"command\": \"cargo xtask check\", \"commit\": \"{commit}\", \
         \"result\": \"{result}\"}}\n"
    )
}

/// A scratch directory with the images and the receipt of a good run.
fn good() -> Scratch {
    let scratch = Scratch::temporary("release");
    scratch.write("images/test-elf.elf", IMAGE);
    scratch.write("images/images.json", &record("test-elf.elf", IMAGE, COMMIT));
    scratch.write(
        "check-receipt.json",
        &receipt(receipt::FORMAT, COMMIT, "passed"),
    );
    scratch
}

/// The assets of `run` from `scratch` into `out`.
fn assets(scratch: &Scratch, run: &RunData) -> Result<Vec<PathBuf>, String> {
    write(
        run,
        &scratch.0.join("images"),
        &scratch.0.join("check-receipt.json"),
        &scratch.0.join("out"),
    )
}

#[test]
fn a_good_run_gives_its_assets_with_their_digests() {
    let scratch = good();
    let written = assets(&scratch, &run()).expect("the assets");
    let out = scratch.0.join("out");
    let names = [
        "check-receipt.json",
        "images.json",
        "test-elf.elf",
        "SHA256SUMS",
    ];
    assert_eq!(written, names.map(|name| out.join(name)));
    let read = |name: &str| fs::read(out.join(name)).expect("an asset");
    assert_eq!(read("test-elf.elf"), IMAGE.as_bytes());
    assert_eq!(
        read("images.json"),
        fs::read(scratch.0.join("images/images.json")).expect("the record")
    );
    assert_eq!(
        read("check-receipt.json"),
        fs::read(scratch.0.join("check-receipt.json")).expect("the receipt")
    );
    let sums: String = names[..3]
        .iter()
        .map(|name| format!("{}  {name}\n", sha256(&read(name))))
        .collect();
    assert_eq!(String::from_utf8(read(SUMS)).expect("text"), sums);
    // The directory must be new.
    let again = assets(&scratch, &run()).expect_err("the directory exists");
    assert!(
        again.ends_with("exists; the directory must be new"),
        "{again}"
    );
}

/// A change of a good run.
type Change = fn(&mut RunData);

#[test]
fn each_check_of_the_run_fails_on_its_own() {
    let cases: [(Change, &str); 7] = [
        (
            |run| run.path = ".github/workflows/full.yml".to_string(),
            "the run is of the workflow file \".github/workflows/full.yml\", not of .github/workflows/check.yml",
        ),
        (
            |run| run.event = "pull_request".to_string(),
            "the run was triggered by \"pull_request\", not by a push",
        ),
        (
            |run| run.head_branch = Some("topic".to_string()),
            "the run is on the branch \"topic\", not on main",
        ),
        (
            |run| run.head_branch = None,
            "the run is on the branch none, not on main",
        ),
        (
            |run| run.conclusion = Some("failure".to_string()),
            "the run did not succeed: its conclusion is \"failure\"",
        ),
        (
            |run| run.head_sha = "0123456".to_string(),
            "the head \"0123456\" of the run is not a commit",
        ),
        (
            |run| run.head_sha = COMMIT.to_uppercase(),
            "the head \"0123456789ABCDEF0123456789ABCDEF01234567\" of the run is not a commit",
        ),
    ];
    assert_eq!(run_problem(&run()), None);
    for (change, problem) in cases {
        let mut wrong = run();
        change(&mut wrong);
        let scratch = good();
        assert_eq!(assets(&scratch, &wrong), Err(problem.to_string()));
        assert!(!scratch.0.join("out").exists());
    }
}

#[test]
fn each_check_of_the_images_and_the_receipt_fails_on_its_own() {
    let other = "fedcba9876543210fedcba9876543210fedcba98";
    let cases: [(&str, &str, &str); 11] = [
        (
            "images/test-elf.elf",
            "another image",
            "has 13 bytes with SHA-256",
        ),
        (
            "images/test-elf.elf",
            "an imagf",
            "has 8 bytes with SHA-256",
        ),
        (
            "images/images.json",
            &record("test-elf.elf", IMAGE, other),
            "is of the commit",
        ),
        (
            "images/images.json",
            &record("../test-elf.elf", IMAGE, COMMIT),
            "is not a plain name",
        ),
        (
            "images/images.json",
            &record("SHA256SUMS", IMAGE, COMMIT),
            "the file SHA256SUMS of the image \"test-elf\" is taken",
        ),
        (
            "images/images.json",
            &record("missing.elf", IMAGE, COMMIT),
            "is not a regular file",
        ),
        (
            "images/extra.txt",
            "x",
            "holds \"extra.txt\", which images.json does not name",
        ),
        (
            "check-receipt.json",
            &receipt(receipt::FORMAT, COMMIT, "failed"),
            "the result is \"failed\", not passed",
        ),
        (
            "check-receipt.json",
            &receipt(receipt::FORMAT, other, "passed"),
            "the commit is \"fedcba9876543210fedcba9876543210fedcba98\", not the run's commit",
        ),
        (
            "check-receipt.json",
            &receipt(1, COMMIT, "passed"),
            "the format is 1, not the format 2 of the check receipt",
        ),
        (
            "check-receipt.json",
            "not JSON",
            "check-receipt.json: expected",
        ),
    ];
    for (file, text, problem) in cases {
        let scratch = good();
        scratch.write(file, text);
        let error = assets(&scratch, &run()).expect_err(problem);
        assert!(error.contains(problem), "{file}: {error}");
        assert!(!scratch.0.join("out").exists(), "{file}");
    }
    // A record of another format and an image file that is a link.
    let scratch = good();
    let text = record("test-elf.elf", IMAGE, COMMIT).replace("\"format\": 1", "\"format\": 9");
    scratch.write("images/images.json", &text);
    let error = assets(&scratch, &run()).expect_err("another format");
    assert!(error.contains("format 9 is not the format 1"), "{error}");
    let scratch = good();
    let image = scratch.0.join("images/test-elf.elf");
    fs::rename(&image, scratch.0.join("elsewhere")).expect("move the image");
    std::os::unix::fs::symlink(scratch.0.join("elsewhere"), &image).expect("link the image");
    let error = assets(&scratch, &run()).expect_err("a link");
    assert!(error.contains("is not a regular file"), "{error}");
}

#[test]
fn the_command_reads_the_run_and_reports_a_failure() {
    let scratch = good();
    let run_file = scratch.0.join("run.json");
    let text = serde_json::json!({
        "id": 42, "attempt": 1, "workflow": "check", "path": WORKFLOW, "event": "push",
        "head_branch": "main", "head_sha": COMMIT, "conclusion": "success",
    });
    fs::write(&run_file, text.to_string()).expect("write the run");
    assert_eq!(read_run(&run_file), Ok(run()));
    let file = |name: &str| scratch.0.join(name).to_string_lossy().into_owned();
    let args = [
        "--run".to_string(),
        file("run.json"),
        "--images".to_string(),
        file("images"),
        "--receipt".to_string(),
        file("check-receipt.json"),
        "--output-dir".to_string(),
        file("out"),
    ];
    let args: Vec<&str> = args.iter().map(String::as_str).collect();
    assert_eq!(command(&args), ExitCode::SUCCESS);
    assert!(scratch.0.join("out").join(SUMS).is_file());
    // The output directory exists now, and an option is missing.
    assert_eq!(command(&args), ExitCode::from(2));
    assert_eq!(command(&args[..6]), ExitCode::from(2));
    // A run with a field that the command does not read.
    fs::write(
        &run_file,
        text.to_string().replacen('{', "{\"actor\": {}, ", 1),
    )
    .expect("write");
    assert!(read_run(&run_file).is_err_and(|error| error.contains("unknown field `actor`")));
}
