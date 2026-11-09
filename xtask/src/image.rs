//! `cargo xtask image`: the images that the QEMU suites boot, with a record
//! of their digests.
//!
//! ```sh
//! cargo xtask image --output-dir DIR
//! ```
//!
//! The command creates `DIR`, which must not exist, with its missing
//! parents, writes into it the file of each image source of [`SOURCES`] and
//! then the record [`RECORD`]: a JSON object with the `format` [`FORMAT`]
//! and `images`, one entry per image in the order of [`SOURCES`] with its
//! `name`, its `file` in `DIR`, its `bytes`, the lowercase hexadecimal
//! SHA-256 of the file as written (`sha256`) and the `commit` that
//! `git rev-parse HEAD` names in the repository root. It prints a line with
//! the size and digest of each image and the path of the record, and exits
//! with 0, or with 2 after a usage error or a failure, which it reports on
//! standard error; `--help` prints the help and exits with 0.
//!
//! The one source today is the test image of the host tooling crate,
//! `test-elf`, which `krepi_tools::test_elf::write` writes. A downstream job
//! takes the image with the digest that the record gives, as
//! `cargo xtask suite --images` does.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode};

use clap::{Arg, value_parser};
use serde::{Deserialize, Serialize};

use crate::formal::toolchain::sha256;

/// The version of the record format.
pub const FORMAT: u32 = 1;

/// The record in the output directory.
pub const RECORD: &str = "images.json";

/// A source of an image: its name, the file it is written to and the
/// function that writes it to a new file.
pub struct Source {
    pub name: &'static str,
    pub file: &'static str,
    pub write: fn(&Path) -> Result<(), String>,
}

/// Every image source, in the order of the record.
pub const SOURCES: [Source; 1] = [Source {
    name: "test-elf",
    file: "test-elf.elf",
    write: |path| krepi_tools::test_elf::write(path).map_err(|failure| failure.0),
}];

/// The record of the images of one run.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Record {
    pub format: u32,
    pub images: Vec<Image>,
}

/// One image of the record.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Image {
    pub name: String,
    pub file: String,
    pub bytes: u64,
    pub sha256: String,
    pub commit: String,
}

impl Record {
    /// The JSON text of the record, with two-space indentation and a final
    /// newline.
    pub fn render(&self) -> String {
        let value = serde_json::to_value(self).expect("the record is plain data");
        format!("{value:#}\n")
    }
}

/// The lowercase hexadecimal SHA-256 and the size of the file `path`.
pub fn digest(path: &Path) -> Result<(String, u64), String> {
    let bytes =
        fs::read(path).map_err(|error| format!("cannot read {}: {error}", path.display()))?;
    Ok((sha256(&bytes), bytes.len() as u64))
}

/// Creates the new directory `output` with its missing parents.
pub fn create_new(output: &Path) -> Result<(), String> {
    let exists = |what: &str| format!("{} {what}; the directory must be new", output.display());
    if fs::symlink_metadata(output).is_ok() {
        return Err(exists("exists"));
    }
    if let Some(parent) = output.parent().filter(|dir| !dir.as_os_str().is_empty()) {
        fs::create_dir_all(parent)
            .map_err(|error| format!("cannot create {}: {error}", parent.display()))?;
    }
    fs::create_dir(output).map_err(|error| match error.kind() {
        std::io::ErrorKind::AlreadyExists => exists("exists"),
        _ => format!("cannot create {}: {error}", output.display()),
    })
}

/// Writes every image of `sources` and the record into the new directory
/// `output`, each image with the commit `commit`; the record.
pub fn write(output: &Path, sources: &[Source], commit: &str) -> Result<Record, String> {
    create_new(output)?;
    let mut images = Vec::new();
    for source in sources {
        let path = output.join(source.file);
        (source.write)(&path)?;
        let (sha256, bytes) = digest(&path)?;
        images.push(Image {
            name: source.name.to_string(),
            file: source.file.to_string(),
            bytes,
            sha256,
            commit: commit.to_string(),
        });
    }
    let record = Record {
        format: FORMAT,
        images,
    };
    let path = output.join(RECORD);
    fs::write(&path, record.render())
        .map_err(|error| format!("cannot write {}: {error}", path.display()))?;
    Ok(record)
}

/// The commit that `git rev-parse HEAD` names in `root`.
pub fn commit(root: &Path) -> Result<String, String> {
    let output = Command::new("git")
        .args(["rev-parse", "HEAD"])
        .current_dir(root)
        .output()
        .map_err(|error| format!("cannot run git rev-parse: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "git rev-parse HEAD failed: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

/// The command line of `cargo xtask image`.
fn cli() -> clap::Command {
    let about = (crate::COMMANDS.iter())
        .find(|command| command.name == "image")
        .map_or("", |command| command.about);
    clap::Command::new("image")
        .bin_name("cargo xtask image")
        .no_binary_name(true)
        .about(about)
        .arg(
            Arg::new("output-dir")
                .long("output-dir")
                .value_name("DIR")
                .required(true)
                .help("New directory for the images and images.json; must not exist")
                .value_parser(value_parser!(PathBuf)),
        )
}

/// Entry point of `cargo xtask image`.
pub fn command(root: &Path, args: &[&str]) -> ExitCode {
    let matches = match cli().try_get_matches_from(args) {
        Ok(matches) => matches,
        Err(error) => {
            let _ = error.print();
            return ExitCode::from(u8::try_from(error.exit_code()).unwrap_or(2));
        }
    };
    let output = matches
        .get_one::<PathBuf>("output-dir")
        .expect("the option is required");
    match commit(root).and_then(|commit| write(output, &SOURCES, &commit)) {
        Ok(record) => {
            for image in &record.images {
                println!(
                    "{}: {} bytes, SHA-256 {}",
                    image.name, image.bytes, image.sha256
                );
            }
            println!("Record: {}", output.join(RECORD).display());
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("cargo xtask image failed: {error}");
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scratch::Scratch;

    /// The SHA-256 of the test image, from `shasum -a 256` of the file that
    /// `krepi_tools::test_elf::write` writes.
    const TEST_ELF_SHA256: &str =
        "976e92deeebc2bd2eb3c224f570facfef845c2c2adb987ef5960eb1061e7d7a6";

    #[test]
    fn the_record_names_each_image_with_its_digest_and_commit() {
        let scratch = Scratch::temporary("image");
        let output = scratch.0.join("a/b/images");
        let commit = "0123456789abcdef0123456789abcdef01234567";
        let record = write(&output, &SOURCES, commit).expect("write the images");
        let image = Image {
            name: "test-elf".to_string(),
            file: "test-elf.elf".to_string(),
            bytes: 8_760,
            sha256: TEST_ELF_SHA256.to_string(),
            commit: commit.to_string(),
        };
        assert_eq!(
            record,
            Record {
                format: 1,
                images: vec![image],
            }
        );
        // The digest is that of the file on disk, which is the test image.
        let bytes = fs::read(output.join("test-elf.elf")).expect("the image");
        assert_eq!(bytes, krepi_tools::test_elf::image());
        assert_eq!(
            digest(&output.join("test-elf.elf")),
            Ok((sha256(&bytes), 8_760))
        );
        let text = fs::read_to_string(output.join(RECORD)).expect("the record");
        assert_eq!(
            text,
            format!(
                "{{\n  \"format\": 1,\n  \"images\": [\n    {{\n      \"name\": \"test-elf\",\n      \
                 \"file\": \"test-elf.elf\",\n      \"bytes\": 8760,\n      \"sha256\": \
                 \"{TEST_ELF_SHA256}\",\n      \"commit\": \"{commit}\"\n    }}\n  ]\n}}\n"
            )
        );
        let mut names: Vec<String> = (fs::read_dir(&output).expect("the directory"))
            .map(|entry| {
                entry
                    .expect("an entry")
                    .file_name()
                    .into_string()
                    .expect("UTF-8")
            })
            .collect();
        names.sort();
        assert_eq!(names, ["images.json", "test-elf.elf"]);
    }

    #[test]
    fn the_output_directory_must_be_new() {
        let scratch = Scratch::temporary("image-exists");
        let commit = "0".repeat(40);
        let error = write(&scratch.0, &SOURCES, &commit).expect_err("the directory exists");
        assert!(
            error.ends_with("exists; the directory must be new"),
            "{error}"
        );
        // Nothing was written into it.
        assert_eq!(fs::read_dir(&scratch.0).expect("the directory").count(), 0);
        let file = scratch.0.join("file");
        fs::write(&file, "").expect("a file");
        let error = write(&file, &SOURCES, &commit).expect_err("a file exists");
        assert!(error.contains("exists"), "{error}");
        let failing = [Source {
            name: "broken",
            file: "broken.elf",
            write: |_| Err("no image".to_string()),
        }];
        let output = scratch.0.join("new");
        assert_eq!(
            write(&output, &failing, &commit),
            Err("no image".to_string())
        );
        assert!(!output.join(RECORD).exists());
    }
}
