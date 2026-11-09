//! `cargo xtask release-assets`: the assets of a draft release, which are the
//! check receipt and the images of one run of the workflow `check` on a push
//! to `main`, with their SHA-256 digests.
//!
//! ```sh
//! cargo xtask release-assets --run RUN.json --images DIR --receipt FILE \
//!     --output-dir DIR
//! ```
//!
//! `--run` names the run as the workflow `release` writes it with `jq` from
//! the API, the same object as the `run` of the input of
//! `cargo xtask run-record` ([`RunData`]): it must be a run of
//! [`WORKFLOW`] on a push to `main` that succeeded, with a commit of 40
//! lowercase hexadecimal digits. `--images` names the directory of the
//! artifact of the images of that run: its `images.json` must read as the
//! record of `cargo xtask image`, name the commit of the run for each
//! image, and give each image a file of the directory by a plain name, with
//! the size and SHA-256 of that file; the directory holds no other file.
//! `--receipt` names the check receipt of that run, which must have the
//! receipt format of `cargo xtask check`, the commit of the run and the
//! result `passed`.
//!
//! The command creates the directory `--output-dir`, which must not exist,
//! copies the images, `images.json` and the receipt, as [`RECEIPT`], into
//! it, and writes [`SUMS`]: one line `<SHA-256>  <name>` for each of those
//! files, in the order of their names, which `sha256sum --check` reads. It
//! prints the path of each file that it writes and exits with 0, or with 2
//! after a usage error or a failure, which it reports on standard error.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Arg, value_parser};
use serde_json::Value;

use crate::record::RunData;
use crate::{image, receipt};

/// The workflow whose runs the assets come from.
pub const WORKFLOW: &str = ".github/workflows/check.yml";
/// The name of the check receipt among the assets.
pub const RECEIPT: &str = "check-receipt.json";
/// The digests of the assets.
pub const SUMS: &str = "SHA256SUMS";

/// `text` with its control characters escaped, for a message.
fn shown(text: &str) -> String {
    format!("{:?}", crate::suite::printable(text))
}

/// Why `run` is not a run whose assets may be released, if it is not one.
pub fn run_problem(run: &RunData) -> Option<String> {
    let commit = |sha: &str| {
        sha.len() == 40
            && sha
                .bytes()
                .all(|byte| matches!(byte, b'0'..=b'9' | b'a'..=b'f'))
    };
    if run.path != WORKFLOW {
        Some(format!(
            "the run is of the workflow file {}, not of {WORKFLOW}",
            shown(&run.path)
        ))
    } else if run.event != "push" {
        Some(format!(
            "the run was triggered by {}, not by a push",
            shown(&run.event)
        ))
    } else if run.head_branch.as_deref() != Some("main") {
        let branch = run.head_branch.as_deref().map_or("none".to_string(), shown);
        Some(format!("the run is on the branch {branch}, not on main"))
    } else if run.conclusion.as_deref() != Some("success") {
        let conclusion = run.conclusion.as_deref().map_or("none".to_string(), shown);
        Some(format!(
            "the run did not succeed: its conclusion is {conclusion}"
        ))
    } else if !commit(&run.head_sha) {
        Some(format!(
            "the head {} of the run is not a commit",
            shown(&run.head_sha)
        ))
    } else {
        None
    }
}

/// Whether `name` is a plain file name: letters, digits, `.`, `_` and `-`,
/// other than `.` and `..`.
fn plain(name: &str) -> bool {
    let allowed = |byte: u8| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'_' | b'-');
    !name.is_empty() && name != "." && name != ".." && name.bytes().all(allowed)
}

/// The record of the images in `dir`, checked against the files of `dir`
/// and the commit `commit`.
fn checked_images(dir: &Path, commit: &str) -> Result<image::Record, String> {
    let path = dir.join(image::RECORD);
    let text = fs::read_to_string(&path)
        .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    let record =
        image::Record::parse(&text).map_err(|error| format!("{}: {error}", path.display()))?;
    if record.images.is_empty() {
        return Err(format!("{} names no image", path.display()));
    }
    let mut files = vec![image::RECORD.to_string()];
    for image in &record.images {
        let name = &image.file;
        if !plain(name) {
            return Err(format!(
                "the file {} of the image {} is not a plain name",
                shown(name),
                shown(&image.name)
            ));
        }
        if [image::RECORD, RECEIPT, SUMS].contains(&name.as_str()) || files.contains(name) {
            return Err(format!(
                "the file {name} of the image {} is taken",
                shown(&image.name)
            ));
        }
        if image.commit != commit {
            return Err(format!(
                "the image {} is of the commit {}, not of the run's commit {commit}",
                shown(&image.name),
                shown(&image.commit)
            ));
        }
        let file = dir.join(name);
        let regular = fs::symlink_metadata(&file).is_ok_and(|metadata| metadata.is_file());
        if !regular {
            return Err(format!(
                "the image file {} is not a regular file",
                file.display()
            ));
        }
        let (sha256, bytes) = image::digest(&file)?;
        if (sha256.as_str(), bytes) != (image.sha256.as_str(), image.bytes) {
            return Err(format!(
                "the image file {} has {bytes} bytes with SHA-256 {sha256}, not the {} bytes \
                 with SHA-256 {} of {}",
                file.display(),
                image.bytes,
                shown(&image.sha256),
                image::RECORD
            ));
        }
        files.push(name.clone());
    }
    let entries =
        fs::read_dir(dir).map_err(|error| format!("cannot read {}: {error}", dir.display()))?;
    for entry in entries {
        let entry = entry.map_err(|error| format!("cannot read {}: {error}", dir.display()))?;
        let name = entry.file_name().to_string_lossy().into_owned();
        if !files.contains(&name) {
            return Err(format!(
                "{} holds {}, which {} does not name",
                dir.display(),
                shown(&name),
                image::RECORD
            ));
        }
    }
    Ok(record)
}

/// The check receipt `text`, checked against the commit `commit`.
fn checked_receipt(path: &Path, commit: &str) -> Result<String, String> {
    let text = fs::read_to_string(path)
        .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    let value: Value =
        serde_json::from_str(&text).map_err(|error| format!("{}: {error}", path.display()))?;
    let field = |name: &str| value.get(name).cloned().unwrap_or(Value::Null);
    if field("format") != receipt::FORMAT {
        return Err(format!(
            "{}: the format is {}, not the format {} of the check receipt",
            path.display(),
            field("format"),
            receipt::FORMAT
        ));
    }
    if field("commit") != commit {
        return Err(format!(
            "{}: the commit is {}, not the run's commit {commit}",
            path.display(),
            field("commit")
        ));
    }
    if field("result") != "passed" {
        return Err(format!(
            "{}: the result is {}, not passed",
            path.display(),
            field("result")
        ));
    }
    Ok(text)
}

/// Checks `run`, the images in `images` and the receipt at `receipt_path`,
/// and writes the assets with [`SUMS`] into the new directory `output`; the
/// files that it wrote, [`SUMS`] last.
pub fn write(
    run: &RunData,
    images: &Path,
    receipt_path: &Path,
    output: &Path,
) -> Result<Vec<PathBuf>, String> {
    if let Some(problem) = run_problem(run) {
        return Err(problem);
    }
    let record = checked_images(images, &run.head_sha)?;
    let receipt = checked_receipt(receipt_path, &run.head_sha)?;
    image::create_new(output)?;
    let mut names = vec![image::RECORD.to_string(), RECEIPT.to_string()];
    names.extend(record.images.iter().map(|image| image.file.clone()));
    for name in &names {
        let target = output.join(name);
        let written = if name == RECEIPT {
            fs::write(&target, &receipt)
        } else {
            fs::copy(images.join(name), &target).map(|_| ())
        };
        written.map_err(|error| format!("cannot write {}: {error}", target.display()))?;
    }
    names.sort_unstable();
    let mut sums = String::new();
    for name in &names {
        let (sha256, _) = image::digest(&output.join(name))?;
        sums.push_str(&format!("{sha256}  {name}\n"));
    }
    let file = output.join(SUMS);
    fs::write(&file, sums).map_err(|error| format!("cannot write {}: {error}", file.display()))?;
    let mut written: Vec<PathBuf> = names.iter().map(|name| output.join(name)).collect();
    written.push(file);
    Ok(written)
}

/// The command line of `cargo xtask release-assets`.
fn cli() -> clap::Command {
    let about = (crate::COMMANDS.iter())
        .find(|command| command.name == "release-assets")
        .map_or("", |command| command.about);
    let path = |name: &'static str, help: &'static str| {
        Arg::new(name)
            .long(name)
            .value_name("PATH")
            .help(help)
            .required(true)
            .value_parser(value_parser!(PathBuf))
    };
    clap::Command::new("release-assets")
        .bin_name("cargo xtask release-assets")
        .no_binary_name(true)
        .about(about)
        .arg(path(
            "run",
            "The run of the workflow check, as jq writes it",
        ))
        .arg(path("images", "The directory of the images of the run"))
        .arg(path("receipt", "The check receipt of the run"))
        .arg(path("output-dir", "New directory for the assets"))
}

/// Reads the run at `path`.
fn read_run(path: &Path) -> Result<RunData, String> {
    let text = fs::read_to_string(path)
        .map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    serde_json::from_str(&text).map_err(|error| format!("{}: {error}", path.display()))
}

/// Entry point of `cargo xtask release-assets`.
pub fn command(args: &[&str]) -> ExitCode {
    let matches = match cli().try_get_matches_from(args) {
        Ok(matches) => matches,
        Err(error) => {
            let _ = error.print();
            return ExitCode::from(u8::try_from(error.exit_code()).unwrap_or(2));
        }
    };
    let path = |name: &str| matches.get_one::<PathBuf>(name).expect("required");
    let result = read_run(path("run"))
        .and_then(|run| write(&run, path("images"), path("receipt"), path("output-dir")));
    match result {
        Ok(written) => {
            for file in written {
                println!("{}", file.display());
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!(
                "cargo xtask release-assets failed: {}",
                crate::suite::printable(&error)
            );
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests;
