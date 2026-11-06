//! The gate inputs, defined here once, and what a run does with them through
//! Git: the snapshot, the check that they are clean, and the export of the
//! snapshot commit, checked file by file against the commit.

use std::collections::BTreeMap;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::Path;

use serde::{Deserialize, Serialize};

use super::Layout;
use super::toolchain::environment::text;

/// The Cargo configuration that Cargo reads in the repository.
pub const CARGO_CONFIG: &str = ".cargo/config.toml";

/// The gate inputs, as repository-relative paths, the inputs of extraction
/// first; a path may lie below another.
pub fn gate_inputs(layout: &Layout) -> [&'static str; 8] {
    [
        layout.kernel,
        layout.qualification,
        CARGO_CONFIG,
        "verification",
        "xtask",
        crate::workflows::DIR,
        crate::toolchain::RUST_TOOLCHAIN,
        crate::toolchain::MANIFEST,
    ]
}

/// The Git object of a gate input at a commit.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Entry {
    pub mode: String,
    #[serde(rename = "type")]
    pub kind: String,
    pub oid: String,
}

/// The object of each gate input at a commit, or `None` for a gate input
/// that the commit does not have.
pub type Snapshot = BTreeMap<String, Option<Entry>>;

/// The records of `git ls-tree`, by path.
pub type Files = BTreeMap<String, Entry>;

/// Runs Git in the repository root with `args`, reading `stdin` if given,
/// and returns its standard output, or why it did not succeed.
pub trait Git {
    fn git(&mut self, args: &[&str], stdin: Option<&Path>) -> Result<Vec<u8>, String>;
}

/// Runs `git <args> -- <inputs>`.
fn git_on(git: &mut dyn Git, args: &[&str], inputs: &[&str]) -> Result<Vec<u8>, String> {
    let args: Vec<&str> = args.iter().chain(&["--"]).chain(inputs).copied().collect();
    git.git(&args, None)
}

/// The records of `git ls-tree -z`.
fn tree_records(output: &[u8]) -> Result<Files, String> {
    let mut records = Files::new();
    for record in output
        .split(|&byte| byte == 0)
        .filter(|record| !record.is_empty())
    {
        let record = std::str::from_utf8(record)
            .map_err(|_| "git ls-tree printed a path that is not UTF-8".to_string())?;
        let mut fields = record.splitn(4, [' ', '\t']).map(str::to_string);
        let (Some(mode), Some(kind), Some(oid), Some(path)) =
            (fields.next(), fields.next(), fields.next(), fields.next())
        else {
            return Err(format!("unexpected git ls-tree record `{record}`"));
        };
        records.insert(path, Entry { mode, kind, oid });
    }
    Ok(records)
}

/// The commit checked out, its root tree and the object of each of `inputs`
/// at that commit.
pub fn snapshot(git: &mut dyn Git, inputs: &[&str]) -> Result<(String, String, Snapshot), String> {
    let mut name = |revision: &str| {
        git.git(&["rev-parse", "--verify", revision], None)
            .map(|output| String::from_utf8_lossy(&output).trim().to_string())
    };
    let commit = name("HEAD^{commit}")?;
    let tree = name(&format!("{commit}^{{tree}}"))?;
    // `-t` also lists the trees on the way to each input.
    let mut records = tree_records(&git_on(git, &["ls-tree", "-z", "-t", &commit], inputs)?)?;
    let snapshot = inputs
        .iter()
        .map(|path| (path.to_string(), records.remove(*path)))
        .collect();
    Ok((commit, tree, snapshot))
}

/// The records of `git status` below `inputs`: staged and unstaged changes
/// and untracked files that are not ignored.
pub fn changes(git: &mut dyn Git, inputs: &[&str]) -> Result<Vec<String>, String> {
    let status = ["status", "--porcelain=v1", "-z", "--untracked-files=all"];
    let output = git_on(git, &status, inputs)?;
    Ok(output
        .split(|&byte| byte == 0)
        .filter(|record| !record.is_empty())
        .map(|record| String::from_utf8_lossy(record).into_owned())
        .collect())
}

/// The paths of `files` whose extension is `py`, in any ASCII case.
pub fn python_files(files: &Files) -> Vec<&str> {
    let python = |path: &&str| {
        Path::new(path)
            .extension()
            .is_some_and(|extension| extension.eq_ignore_ascii_case("py"))
    };
    files.keys().map(String::as_str).filter(python).collect()
}

/// Exports `inputs`, the gate inputs that `commit` has, into the new
/// directory `dest` with `git archive`, and returns the files of those
/// inputs at `commit` once the export holds each of them. The lists for Git
/// go into `work`.
pub fn export(
    git: &mut dyn Git,
    commit: &str,
    inputs: &[&str],
    work: &Path,
    dest: &Path,
) -> Result<Files, String> {
    fs::create_dir(dest).map_err(|error| format!("cannot create {}: {error}", dest.display()))?;
    // Without a path, Git would list and export the whole tree.
    if inputs.is_empty() {
        return Ok(Files::new());
    }
    let files = tree_records(&git_on(git, &["ls-tree", "-r", "-z", commit], inputs)?)?;
    let archive = git_on(git, &["archive", "--format=tar", commit], inputs)?;
    let mut unpacker = tar::Archive::new(archive.as_slice());
    unpacker.set_preserve_mtime(false);
    unpacker
        .unpack(dest)
        .map_err(|error| format!("cannot unpack the archive: {error}"))?;
    let differences = compare(git, &files, dest, work)?;
    if differences.is_empty() {
        return Ok(files);
    }
    let differences = differences.join(", ");
    Err(format!(
        "the export differs from the snapshot: {differences}"
    ))
}

/// How the export in `dest` differs from `files`: a missing path, a path of
/// another mode, or a content without the object name of the snapshot. Git
/// computes the object names without filters, from a list of paths written
/// into `work`; the target of each symbolic link is first written into a
/// file of its own there.
fn compare(
    git: &mut dyn Git,
    files: &Files,
    dest: &Path,
    work: &Path,
) -> Result<Vec<String>, String> {
    let mut differences = Vec::new();
    let mut hashed = Vec::new();
    let links = work.join("links");
    for (path, entry) in files {
        let exported = dest.join(path);
        let mode = match fs::symlink_metadata(&exported) {
            Err(_) => {
                differences.push(format!("{path} is missing"));
                continue;
            }
            Ok(found) if found.is_symlink() => "120000",
            Ok(found) if found.is_file() && found.permissions().mode() & 0o111 != 0 => "100755",
            Ok(found) if found.is_file() => "100644",
            Ok(_) => "other",
        };
        if mode != entry.mode {
            differences.push(format!("{path} has mode {mode}, not {}", entry.mode));
        } else if mode == "120000" {
            let target = fs::read_link(&exported)
                .map_err(|error| format!("cannot read the link {path}: {error}"))?;
            fs::create_dir_all(&links)
                .map_err(|error| format!("cannot create {}: {error}", links.display()))?;
            let copy = links.join(hashed.len().to_string());
            fs::write(&copy, target.as_os_str().as_encoded_bytes())
                .map_err(|error| format!("cannot write {}: {error}", copy.display()))?;
            hashed.push((path, entry, copy));
        } else {
            hashed.push((path, entry, exported));
        }
    }
    let mut list = String::new();
    for (_, _, path) in &hashed {
        list.push_str(&text(path)?);
        list.push('\n');
    }
    let paths = work.join("hash-paths");
    fs::write(&paths, list)
        .map_err(|error| format!("cannot write {}: {error}", paths.display()))?;
    let hash = ["hash-object", "--no-filters", "--stdin-paths"];
    let output = git.git(&hash, Some(&paths))?;
    let names = String::from_utf8_lossy(&output);
    let names: Vec<&str> = names.lines().collect();
    // A path with a line break gives more lines than paths.
    if names.len() != hashed.len() {
        let (names, paths) = (names.len(), hashed.len());
        return Err(format!(
            "git hash-object printed {names} object names for {paths} paths"
        ));
    }
    for ((path, entry, _), name) in hashed.iter().zip(names) {
        if name != entry.oid {
            differences.push(format!("{path} has the object {name}, not {}", entry.oid));
        }
    }
    Ok(differences)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::formal::fixture::Fixture;

    const COMMIT: &str = "HEAD";

    fn inputs() -> [&'static str; 8] {
        gate_inputs(&Layout::PRODUCTION)
    }

    #[test]
    fn the_gate_inputs_are_defined_once() {
        let layout = Layout::PRODUCTION;
        assert_eq!(
            gate_inputs(&layout),
            [
                "kernel",
                "verification/qualification",
                ".cargo/config.toml",
                "verification",
                "xtask",
                ".github/workflows",
                "rust-toolchain.toml",
                "toolchains.toml",
            ]
        );
        assert_eq!(
            &gate_inputs(&layout)[..2],
            [layout.kernel, layout.qualification]
        );
    }

    #[test]
    fn the_snapshot_records_an_absent_input_as_null() {
        let mut fixture = Fixture::new("snapshot");
        let (commit, tree, taken) = snapshot(&mut fixture, &inputs()).expect("Git runs");
        assert_eq!(commit, fixture.git(&["rev-parse", "HEAD"]).trim());
        assert_eq!(tree, fixture.git(&["rev-parse", "HEAD^{tree}"]).trim());
        assert_eq!(
            taken.keys().map(String::as_str).collect::<Vec<_>>(),
            [
                ".cargo/config.toml",
                ".github/workflows",
                "kernel",
                "rust-toolchain.toml",
                "toolchains.toml",
                "verification",
                "verification/qualification",
                "xtask",
            ]
        );
        // The fixture has no qualification crate.
        assert_eq!(taken["verification/qualification"], None);
        let kernel = taken["kernel"].clone().expect("the kernel is tracked");
        assert_eq!(
            (kernel.mode.as_str(), kernel.kind.as_str()),
            ("040000", "tree")
        );
        assert_eq!(
            kernel.oid,
            fixture
                .git(&["rev-parse", &format!("{commit}:kernel")])
                .trim()
        );
        let config = taken[".cargo/config.toml"].clone().expect("tracked");
        assert_eq!(
            (config.mode.as_str(), config.kind.as_str()),
            ("100644", "blob")
        );
        // Another commit with another kernel has another snapshot.
        fixture.write("kernel/abi/src/lib.rs", "//! Changed.\n");
        fixture.commit_all();
        let (later, _, changed) = snapshot(&mut fixture, &inputs()).expect("Git runs");
        assert_ne!(later, commit);
        assert_ne!(changed["kernel"], taken["kernel"]);
        assert_eq!(changed["xtask"], taken["xtask"]);
    }

    #[test]
    fn a_modified_or_untracked_gate_input_is_not_clean() {
        let mut fixture = Fixture::new("changes");
        assert_eq!(changes(&mut fixture, &inputs()), Ok(Vec::new()));
        // A file outside the gate inputs does not count.
        fixture.write("README.md", "Changed.\n");
        fixture.write("notes.txt", "Untracked.\n");
        assert_eq!(changes(&mut fixture, &inputs()), Ok(Vec::new()));
        fixture.write("xtask/README", "Changed.\n");
        fixture.write("verification/new.json", "{}\n");
        fixture.write("kernel/abi/src/staged.rs", "\n");
        fixture.git(&["add", "kernel/abi/src/staged.rs"]);
        assert_eq!(
            changes(&mut fixture, &inputs()),
            Ok(vec![
                "A  kernel/abi/src/staged.rs".to_string(),
                " M xtask/README".to_string(),
                "?? verification/new.json".to_string(),
            ])
        );
        // A rename names the path that it gives and then the one it came
        // from.
        fixture.git(&[
            "mv",
            "verification/targets.json",
            "verification/targets.old",
        ]);
        let found = changes(&mut fixture, &inputs()).expect("status runs");
        assert_eq!(found.len(), 5, "{found:?}");
        let rename = found
            .iter()
            .position(|record| record == "R  verification/targets.old")
            .expect("the rename is listed");
        assert_eq!(found[rename + 1], "verification/targets.json");
        // A path moved out of the gate inputs is a deletion there.
        fixture.git(&["mv", "rust-toolchain.toml", "rust-toolchain.old"]);
        let found = changes(&mut fixture, &inputs()).expect("status runs");
        assert!(
            found.contains(&"D  rust-toolchain.toml".to_string()),
            "{found:?}"
        );
    }

    #[test]
    fn an_ignored_file_below_a_gate_input_is_clean() {
        let mut fixture = Fixture::new("ignored");
        fixture.write(".gitignore", "/artifacts/\n/verification/.lake/\n");
        fixture.commit_all();
        fixture.write("verification/.lake/build/out.olean", "built\n");
        assert_eq!(changes(&mut fixture, &inputs()), Ok(Vec::new()));
    }

    #[test]
    fn the_export_is_the_snapshot() {
        let mut fixture = Fixture::new("export");
        fixture.write("xtask/run.sh", "#!/bin/sh\n");
        fixture.chmod("xtask/run.sh", 0o755);
        fixture.symlink("verification/link", "targets.json");
        fixture.commit_all();
        // An untracked file is not exported.
        fixture.write("xtask/untracked", "\n");
        let work = fixture.root().join("artifacts/work");
        fs::create_dir_all(&work).expect("create the work directory");
        let dest = work.join("source");
        let present: Vec<&str> = inputs()
            .into_iter()
            .filter(|path| *path != "verification/qualification")
            .collect();
        let files = export(&mut fixture, COMMIT, &present, &work, &dest).expect("the export");
        assert_eq!(files["xtask/run.sh"].mode, "100755");
        assert_eq!(files["verification/link"].mode, "120000");
        let mode = fs::metadata(dest.join("xtask/run.sh"))
            .expect("exported")
            .permissions()
            .mode();
        assert_ne!(mode & 0o111, 0);
        assert_eq!(
            fs::read_link(dest.join("verification/link")).expect("a link"),
            Path::new("targets.json")
        );
        assert!(!dest.join("xtask/untracked").exists());
        assert!(!dest.join("README.md").exists());
        // The export is compared with the files of the snapshot.
        let mut other = files.clone();
        let oid = other
            .get_mut("xtask/README")
            .map(|entry| std::mem::replace(&mut entry.oid, "0".repeat(40)))
            .expect("tracked");
        other.get_mut("xtask/run.sh").expect("tracked").mode = "100644".to_string();
        let missing = other["xtask/README"].clone();
        other.insert("xtask/missing".to_string(), missing);
        assert_eq!(
            compare(&mut fixture, &other, &dest, &work),
            Ok(vec![
                "xtask/missing is missing".to_string(),
                "xtask/run.sh has mode 100755, not 100644".to_string(),
                format!("xtask/README has the object {oid}, not {}", "0".repeat(40)),
            ])
        );
        // A snapshot without any gate input exports nothing.
        let empty = work.join("empty");
        assert_eq!(
            export(&mut fixture, COMMIT, &[], &work, &empty),
            Ok(Files::new())
        );
        assert_eq!(fs::read_dir(&empty).expect("created").count(), 0);
    }

    #[test]
    fn an_export_ignore_attribute_fails_the_export() {
        let mut fixture = Fixture::new("export-ignore");
        fixture.write(
            ".gitattributes",
            "/xtask/README export-ignore\n/toolchains.toml export-subst\n",
        );
        fixture.write("toolchains.toml", "# $Format:%H$\n");
        fixture.commit_all();
        let work = fixture.root().join("artifacts/work");
        fs::create_dir_all(&work).expect("create the work directory");
        let present = ["xtask", "toolchains.toml"];
        let error = export(&mut fixture, COMMIT, &present, &work, &work.join("source"))
            .expect_err("the export differs");
        assert!(
            error.starts_with("the export differs from the snapshot: "),
            "{error}"
        );
        assert!(error.contains("xtask/README is missing"), "{error}");
        assert!(error.contains("toolchains.toml has the object "), "{error}");
    }

    #[test]
    fn python_files_are_found_below_every_gate_input() {
        let entry = Entry {
            mode: "100644".to_string(),
            kind: "blob".to_string(),
            oid: "0".repeat(40),
        };
        let files: Files = [
            "xtask/helper.py",
            "verification/Tool.PY",
            "kernel/a/build.Py",
            "xtask/python.rs",
            "xtask/.py",
            "xtask/py",
            "xtask/notes.pyc",
        ]
        .into_iter()
        .map(|path| (path.to_string(), entry.clone()))
        .collect();
        assert_eq!(
            python_files(&files),
            [
                "kernel/a/build.Py",
                "verification/Tool.PY",
                "xtask/helper.py"
            ]
        );
    }
}
