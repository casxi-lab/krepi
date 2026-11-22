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
//! The first source is the test image of the host tooling crate,
//! `test-elf`, which `krepi_tools::test_elf::write` writes. The others are
//! the kernel images that the QEMU boot suite boots, the QEMU virt default
//! image and the test images of its cases, each named by its Cargo target
//! and written to `<target>.elf`: the command builds them in `kernel/` with
//! the build command of `cargo xtask qemu-boot`
//! (`krepi_tools::qemu_boot::build_command`), once for all of them, and
//! copies the executable that Cargo's artifact message gives for each
//! target, so that a later run of that suite in the same checkout finds them
//! built. A downstream job takes each image with the digest that the record
//! gives, as `cargo xtask suite --images` does.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};

use clap::{Arg, value_parser};
use krepi_tools::qemu_boot;
use serde::{Deserialize, Serialize};

use crate::formal::toolchain::sha256;

/// The version of the record format.
pub const FORMAT: u32 = 1;

/// The record in the output directory.
pub const RECORD: &str = "images.json";

/// A source of an image: its name, the file it is written to and where the
/// image comes from.
#[derive(Clone, Copy)]
pub struct Source {
    pub name: &'static str,
    pub file: &'static str,
    pub origin: Origin,
}

/// Where the image of a source comes from.
#[derive(Clone, Copy)]
pub enum Origin {
    /// This function writes it to a new file.
    Writer(fn(&Path) -> Result<(), String>),
    /// It is the executable of the Cargo target of the source's name, built
    /// by the build command of the QEMU boot suite.
    Kernel,
}

impl Source {
    /// The kernel image of the Cargo target `name`, in the file `file`.
    const fn kernel(name: &'static str, file: &'static str) -> Source {
        Source {
            name,
            file,
            origin: Origin::Kernel,
        }
    }
}

/// The test image of the host tooling crate.
pub const TEST_ELF: Source = Source {
    name: "test-elf",
    file: "test-elf.elf",
    origin: Origin::Writer(|path| krepi_tools::test_elf::write(path).map_err(|failure| failure.0)),
};

/// Every image source, in the order of the record: the test image, then the
/// default image and the test images of the QEMU boot suite in the order of
/// its cases.
pub const SOURCES: [Source; 15] = [
    TEST_ELF,
    Source::kernel("krepi-qemu-virt", "krepi-qemu-virt.elf"),
    Source::kernel("el1-brk", "el1-brk.elf"),
    Source::kernel("injected-serror", "injected-serror.elf"),
    Source::kernel("el1-fp-trap", "el1-fp-trap.elf"),
    Source::kernel("timer-irq", "timer-irq.elf"),
    Source::kernel("irq-registers", "irq-registers.elf"),
    Source::kernel("sp-el0-brk", "sp-el0-brk.elf"),
    Source::kernel("unexpected-irq", "unexpected-irq.elf"),
    Source::kernel("clean-code-to-pou", "clean-code-to-pou.elf"),
    Source::kernel("invalidate-to-poc", "invalidate-to-poc.elf"),
    Source::kernel("invalidate-tlb-page", "invalidate-tlb-page.elf"),
    Source::kernel("code-publication", "code-publication.elf"),
    Source::kernel("boot-memory", "boot-memory.elf"),
    Source::kernel("kernel-memory", "kernel-memory.elf"),
];

/// The source named `name`, if there is one.
pub fn source(name: &str) -> Option<&'static Source> {
    SOURCES.iter().find(|source| source.name == name)
}

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
    /// The record in `text`, which must have the format [`FORMAT`] and name
    /// each image once.
    pub fn parse(text: &str) -> Result<Record, String> {
        let record: Record = serde_json::from_str(text).map_err(|error| error.to_string())?;
        if record.format != FORMAT {
            return Err(format!(
                "format {} is not the format {FORMAT} that this xtask reads",
                record.format
            ));
        }
        for (at, image) in record.images.iter().enumerate() {
            if record.images[..at]
                .iter()
                .any(|other| other.name == image.name)
            {
                return Err(format!("the image {} is named twice", image.name));
            }
        }
        Ok(record)
    }

    /// The entry of the image `name`, if the record has one.
    pub fn image(&self, name: &str) -> Option<&Image> {
        self.images.iter().find(|image| image.name == name)
    }

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

/// Builds the kernel images in `kernel` with the build command of the QEMU
/// boot suite, its standard error passed on: the messages of Cargo.
fn build(kernel: &Path) -> Result<String, String> {
    let command = qemu_boot::build_command();
    let output = Command::new(&command[0])
        .args(&command[1..])
        .current_dir(kernel)
        .stdin(Stdio::null())
        .stderr(Stdio::inherit())
        .output()
        .map_err(|error| format!("cannot run {} in {}: {error}", command[0], kernel.display()))?;
    if !output.status.success() {
        return Err(format!(
            "the build of the kernel images failed with {}",
            output.status
        ));
    }
    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
}

/// Writes every image of `sources` and the record into the new directory
/// `output`, each image with the commit `commit`, the kernel images built
/// once in `kernel/` of the repository `root`; the record.
pub fn write(
    root: &Path,
    output: &Path,
    sources: &[Source],
    commit: &str,
) -> Result<Record, String> {
    create_new(output)?;
    let kernel = sources
        .iter()
        .any(|source| matches!(source.origin, Origin::Kernel));
    let messages = if kernel {
        build(&root.join("kernel"))?
    } else {
        String::new()
    };
    let mut images = Vec::new();
    for source in sources {
        let path = output.join(source.file);
        match source.origin {
            Origin::Writer(write) => write(&path)?,
            Origin::Kernel => {
                let built = qemu_boot::executable_from_messages(&messages, source.name)
                    .ok_or_else(|| format!("the build named no executable of {}", source.name))?;
                fs::copy(&built, &path).map_err(|error| {
                    format!(
                        "cannot copy {} to {}: {error}",
                        built.display(),
                        path.display()
                    )
                })?;
            }
        }
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
    match commit(root).and_then(|commit| write(root, output, &SOURCES, &commit)) {
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
    use crate::repo::root;
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
        let record = write(&root(), &output, &[TEST_ELF], commit).expect("write the images");
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
                images: vec![image.clone()],
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
        assert_eq!(Record::parse(&text), Ok(record.clone()));
        assert_eq!(record.image("test-elf"), Some(&image));
        assert_eq!(record.image("kernel"), None);
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
        let error = write(&root(), &scratch.0, &SOURCES, &commit).expect_err("it exists");
        assert!(
            error.ends_with("exists; the directory must be new"),
            "{error}"
        );
        // Nothing was written into it.
        assert_eq!(fs::read_dir(&scratch.0).expect("the directory").count(), 0);
        let file = scratch.0.join("file");
        fs::write(&file, "").expect("a file");
        let error = write(&root(), &file, &SOURCES, &commit).expect_err("a file exists");
        assert!(error.contains("exists"), "{error}");
        let failing = [Source {
            name: "broken",
            file: "broken.elf",
            origin: Origin::Writer(|_| Err("no image".to_string())),
        }];
        let output = scratch.0.join("new");
        assert_eq!(
            write(&root(), &output, &failing, &commit),
            Err("no image".to_string())
        );
        assert!(!output.join(RECORD).exists());
        // A kernel image whose build cannot run or fails: no record either.
        let kernel = [Source::kernel("x", "x.elf")];
        let output = scratch.0.join("images");
        let error = write(&scratch.0, &output, &kernel, &commit).expect_err("no kernel/");
        assert!(error.starts_with("cannot run "), "{error}");
        assert!(!output.join(RECORD).exists());
        fs::create_dir(scratch.0.join("kernel")).expect("a directory without a workspace");
        let output = scratch.0.join("again");
        let error = write(&scratch.0, &output, &kernel, &commit).expect_err("no workspace");
        assert!(
            error.starts_with("the build of the kernel images failed"),
            "{error}"
        );
        assert!(!output.join(RECORD).exists());
    }

    #[test]
    fn a_record_of_another_form_is_refused() {
        let image = |name: &str| {
            format!(
                "{{\"name\": \"{name}\", \"file\": \"f\", \"bytes\": 1, \"sha256\": \"00\", \
                 \"commit\": \"c\"}}"
            )
        };
        let record = |format: u32, images: &[String]| {
            format!(
                "{{\"format\": {format}, \"images\": [{}]}}",
                images.join(", ")
            )
        };
        let one = record(1, &[image("a")]);
        assert_eq!(Record::parse(&one).expect("one image").images.len(), 1);
        let twice = record(1, &[image("a"), image("a")]);
        assert_eq!(
            Record::parse(&twice),
            Err("the image a is named twice".to_string())
        );
        let other = record(2, &[]);
        assert!(Record::parse(&other).is_err_and(|error| error.starts_with("format 2 ")));
        let extra = one.replace("\"bytes\"", "\"size\": 1, \"bytes\"");
        assert!(Record::parse(&extra).is_err());
        assert!(Record::parse("[]").is_err());
        assert_eq!(
            source("test-elf").map(|source| source.file),
            Some("test-elf.elf")
        );
        assert!(source("kernel").is_none());
    }

    #[test]
    fn the_kernel_sources_are_the_images_of_the_qemu_boot_suite() {
        let names: Vec<&str> = SOURCES.iter().map(|source| source.name).collect();
        let mut kernel = vec![qemu_boot::DEFAULT_IMAGE];
        kernel.extend(qemu_boot::test_images());
        assert_eq!(names[0], "test-elf");
        assert_eq!(names[1..], kernel);
        for source in &SOURCES[1..] {
            assert!(matches!(source.origin, Origin::Kernel), "{}", source.name);
            assert_eq!(source.file, format!("{}.elf", source.name));
        }
        assert!(matches!(SOURCES[0].origin, Origin::Writer(_)));
    }
}
