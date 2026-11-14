//! The gate inputs, defined here once, and what a run does with them through
//! Git: the snapshot, the check that they are clean, and the export of the
//! snapshot commit, checked file by file against the commit. Also the change
//! since a merge base, the targets that it affects and `cargo xtask formal impact`.

use std::collections::BTreeMap;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::Path;
use std::process::ExitCode;

use clap::{Arg, ArgMatches};
use serde::{Deserialize, Serialize};

use super::Layout;
use super::lean;
use super::registry::{self, State, Target};
use super::toolchain::environment::text;

/// The Cargo configuration that Cargo reads in the repository.
pub const CARGO_CONFIG: &str = ".cargo/config.toml";

/// The inputs of extraction: the first `EXTRACTION` gate inputs.
pub const EXTRACTION: usize = 3;

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
pub(super) fn tree_records(output: &[u8]) -> Result<Files, String> {
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

/// Why the gate inputs `files` reject a run: Python sources, Lean files of
/// the generated namespace, or Cargo configuration below the root. Cargo
/// reads the configuration of every directory from where it runs up; only
/// the snapshot's root has one.
pub fn rejected(files: &Files, layout: &Layout) -> Vec<String> {
    let generated = Path::new(layout.project).join(layout.generated);
    let configs = [".cargo/config", CARGO_CONFIG];
    let python = |path: &Path| {
        path.extension()
            .is_some_and(|ext| ext.eq_ignore_ascii_case("py"))
    };
    let lean = |path: &Path| {
        path.starts_with(&generated) && path.extension().is_some_and(|ext| ext == "lean")
    };
    let cargo =
        |path: &Path| !path.starts_with(".cargo") && configs.iter().any(|end| path.ends_with(end));
    let found = |rule: &dyn Fn(&Path) -> bool| {
        (files.keys().map(String::as_str))
            .filter(|path| rule(Path::new(path)))
            .collect::<Vec<_>>()
    };
    [
        ("Python sources", found(&python)),
        ("Lean files of the generated namespace", found(&lean)),
        ("Cargo configuration below the root", found(&cargo)),
    ]
    .into_iter()
    .filter(|(_, found)| !found.is_empty())
    .map(|(what, found)| format!("the gate inputs hold {what}: {}", found.join(", ")))
    .collect()
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

/// The paths changed from the merge base of two commits to the second, the
/// head, each with Git's status letter, without rename detection: a moved
/// file is the deletion of one path and the addition of another.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Change {
    pub merge_base: String,
    pub head: String,
    pub paths: Vec<(String, String)>,
}

impl Change {
    /// The changed paths that lie within one of `inputs`.
    pub fn within<'a>(&'a self, inputs: &[&str]) -> Vec<&'a str> {
        let paths = self.paths.iter().map(|(_, path)| path.as_str());
        let within = |path: &&str| inputs.iter().any(|dir| crate::repo::is_within(path, dir));
        paths.filter(within).collect()
    }

    /// The changed paths within the gate inputs of `layout`; without one,
    /// the change leaves the gate unaffected.
    pub fn affecting(&self, layout: &Layout) -> Vec<&str> {
        self.within(&gate_inputs(layout))
    }

    /// The text of `path` at the merge base and at the head, empty on the
    /// side that lacks it as the change adds or deletes it.
    pub fn texts(&self, git: &mut dyn Git, path: &str) -> Result<[String; 2], String> {
        let status = self.paths.iter().find(|(_, changed)| changed == path);
        let status = status.map_or("", |(status, _)| status.as_str());
        let mut text = |commit: &str, absent: &str| match status == absent {
            true => Ok(String::new()),
            false => text_at(git, commit, path),
        };
        Ok([text(&self.merge_base, "A")?, text(&self.head, "D")?])
    }
}

/// The change from the merge base of `base` and `head` to `head`.
pub fn since_merge_base(git: &mut dyn Git, base: &str, head: &str) -> Result<Change, String> {
    let merge_base = git.git(&["merge-base", base, head], None)?;
    let merge_base = String::from_utf8_lossy(&merge_base).trim().to_string();
    let diff = ["diff", "--name-status", "--no-renames", "-z"];
    let diff = git.git(&[&diff[..], &[merge_base.as_str(), head]].concat(), None)?;
    let diff = String::from_utf8_lossy(&diff);
    let mut fields = diff.split_terminator('\0').map(String::from);
    let paths = std::iter::from_fn(|| Some((fields.next()?, fields.next()?))).collect();
    Ok(Change {
        merge_base,
        head: head.to_string(),
        paths,
    })
}

/// The text of `path` at `commit`, with any byte that is not UTF-8 replaced.
pub fn text_at(git: &mut dyn Git, commit: &str, path: &str) -> Result<String, String> {
    let blob = git.git(&["cat-file", "blob", &format!("{commit}:{path}")], None)?;
    Ok(String::from_utf8_lossy(&blob).into_owned())
}

/// The targets of the registry `text` by name, none for an empty text.
pub(super) fn targets(text: &str) -> Result<BTreeMap<String, Target>, String> {
    let registry = (!text.is_empty()).then(|| registry::parse(text));
    let targets = (registry.transpose()?).map_or_else(Vec::new, |registry| registry.targets);
    Ok(targets.into_iter().map(|t| (t.name.clone(), t)).collect())
}

/// The targets registered at the head of `change`, with their states, that
/// it affects: all when it changes an input of extraction, and otherwise
/// each with another entry than at the merge base or a changed proof module.
pub fn impacted(
    git: &mut dyn Git,
    layout: &Layout,
    change: &Change,
) -> Result<Vec<(String, State)>, String> {
    let texts = change.texts(git, layout.registry)?;
    let [before, after] = texts.map(|text| targets(&text));
    let (before, after) = (before?, after?);
    let extraction = !change.within(&gate_inputs(layout)[..EXTRACTION]).is_empty();
    let module = |name: &String| format!("{}/{}", layout.project, lean::module_file(name));
    let affected = |(name, target): &(&String, &Target)| {
        let mut files = target.proof_modules.iter().map(module);
        let changed = |file: String| change.paths.iter().any(|(_, path)| *path == file);
        extraction || before.get(*name) != Some(target) || files.any(changed)
    };
    let affected = after.iter().filter(affected);
    let affected = affected.map(|(name, target)| (name.clone(), target.state));
    Ok(affected.collect())
}

/// The command line of `cargo xtask formal impact`, with `about`.
pub fn cli(about: &'static str) -> clap::Command {
    let base = Arg::new("base").long("base").value_name("REV");
    let command = clap::Command::new("impact").about(about);
    command.arg(base.required(true))
}

/// Entry point of `cargo xtask formal impact` in the repository `root`: it
/// prints [`impact_lines`] and exits with 1 when Git or a registry fails.
pub fn command(root: &Path, layout: &Layout, matches: &ArgMatches) -> ExitCode {
    let base = (matches.get_one::<String>("base")).expect("a required option");
    let lines = impact_lines(&mut super::guard::Standalone(root), layout, base);
    (lines.iter().flatten()).for_each(|line| println!("{line}"));
    let error = (lines.as_ref().err()).map(|error| eprintln!("formal impact: {error}"));
    ExitCode::from(u8::from(error.is_some()))
}

/// The lines of `cargo xtask formal impact --base <base>`: the merge base of
/// `base` and `HEAD`, each changed path, the decision and each target that
/// the change affects, with paths and names escaped so that none splits a line.
fn impact_lines(git: &mut dyn Git, layout: &Layout, base: &str) -> Result<Vec<String>, String> {
    if base.is_empty() || base.starts_with('-') {
        return Err(format!("{base:?} is not a revision"));
    }
    let change = since_merge_base(git, base, "HEAD")?;
    let mut lines = vec![format!("merge base {}", change.merge_base)];
    let paths = change.paths.iter();
    lines.extend(paths.map(|(status, path)| format!("changed {status} {}", path.escape_debug())));
    let decision = ["unaffected", "affected"][usize::from(!change.affecting(layout).is_empty())];
    lines.push(format!("decision {decision}"));
    for (name, state) in impacted(git, layout, &change)? {
        let state = format!("{state:?}").to_lowercase();
        lines.push(format!("target {} {state}", name.escape_debug()));
    }
    Ok(lines)
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
            &gate_inputs(&layout)[..EXTRACTION],
            [layout.kernel, layout.qualification, CARGO_CONFIG]
        );
    }

    /// The commit at the head of `fixture`.
    fn head_of(fixture: &Fixture) -> String {
        fixture.git(&["rev-parse", "HEAD"]).trim().to_string()
    }

    /// A fixture with `files` committed, and the change of a commit of what
    /// `change` writes on it.
    fn changed_by(
        label: &str,
        files: &[(&str, &str)],
        change: impl FnOnce(&Fixture),
    ) -> (Fixture, Change) {
        let mut fixture = Fixture::new(label);
        (files.iter()).for_each(|(path, text)| fixture.write(path, text));
        fixture.commit_all();
        let base = head_of(&fixture);
        change(&fixture);
        fixture.commit_all();
        let change = since_merge_base(&mut fixture, &base, "HEAD").expect("Git runs");
        assert_eq!(change.merge_base, base);
        (fixture, change)
    }

    /// The paths, with their statuses, that `change` changes in a fixture
    /// with a crate of the user-space workspace, and those of them that
    /// affect the gate inputs.
    fn decided(label: &str, change: impl FnOnce(&Fixture)) -> (Vec<(String, String)>, Vec<String>) {
        let app = [("user/app/src/main.rs", "fn main() {}\n")];
        let (_, change) = changed_by(label, &app, change);
        let affecting = change.affecting(&Layout::PRODUCTION);
        let affecting = Vec::from_iter(affecting.into_iter().map(String::from));
        (change.paths, affecting)
    }

    /// `(status, path)` pairs.
    fn changed(paths: &[(&str, &str)]) -> Vec<(String, String)> {
        let pair = |(status, path): &(&str, &str)| (status.to_string(), path.to_string());
        paths.iter().map(pair).collect()
    }

    #[test]
    fn a_change_of_the_user_space_workspace_alone_is_unaffected() {
        let (paths, affecting) = decided("user-space", |fixture| {
            fixture.write("user/app/src/main.rs", "fn main() { let _ = 1; }\n");
            fixture.write("user/app/Cargo.toml", "[package]\nname = \"app\"\n");
        });
        let expected = [("A", "user/app/Cargo.toml"), ("M", "user/app/src/main.rs")];
        assert_eq!(paths, changed(&expected));
        assert_eq!(affecting, Vec::<String>::new());
    }

    #[test]
    fn a_change_of_the_kernel_workspace_is_affected() {
        let (paths, affecting) = decided("kernel", |fixture| {
            fixture.write("kernel/abi/src/lib.rs", "//! Changed.\n");
        });
        assert_eq!(paths, changed(&[("M", "kernel/abi/src/lib.rs")]));
        assert_eq!(affecting, ["kernel/abi/src/lib.rs"]);
    }

    #[test]
    fn a_change_below_verification_is_affected() {
        let (paths, affecting) = decided("verification", |fixture| {
            fixture.write("verification/Krepi/Spec/A.lean", "module\n");
        });
        assert_eq!(paths, changed(&[("A", "verification/Krepi/Spec/A.lean")]));
        assert_eq!(affecting, ["verification/Krepi/Spec/A.lean"]);
    }

    #[test]
    fn a_change_of_a_toolchain_manifest_is_affected() {
        let (paths, affecting) = decided("toolchain", |fixture| {
            fixture.write("rust-toolchain.toml", "[toolchain]\nchannel = \"1.99.1\"\n");
            fixture.write("toolchains.toml", "# Other tool versions.\n");
        });
        let expected = [("M", "rust-toolchain.toml"), ("M", "toolchains.toml")];
        assert_eq!(paths, changed(&expected));
        assert_eq!(affecting, ["rust-toolchain.toml", "toolchains.toml"]);
    }

    #[test]
    fn a_change_below_xtask_is_affected() {
        let (paths, affecting) = decided("xtask", |fixture| {
            fixture.write("xtask/README", "Changed.\n");
        });
        assert_eq!(paths, changed(&[("M", "xtask/README")]));
        assert_eq!(affecting, ["xtask/README"]);
    }

    #[test]
    fn a_change_of_a_workflow_is_affected() {
        let (paths, affecting) = decided("workflow", |fixture| {
            fixture.write(".github/workflows/check.yml", "name: changed\n");
        });
        assert_eq!(paths, changed(&[("M", ".github/workflows/check.yml")]));
        assert_eq!(affecting, [".github/workflows/check.yml"]);
    }

    #[test]
    fn a_file_moved_from_the_kernel_to_the_user_space_workspace_is_affected() {
        // Without rename detection, the move is a deletion in the kernel
        // workspace and an addition in the user-space workspace.
        let (paths, affecting) = decided("moved", |fixture| {
            fixture.git(&["mv", "kernel/abi/src/lib.rs", "user/app/src/lib.rs"]);
        });
        let expected = [("D", "kernel/abi/src/lib.rs"), ("A", "user/app/src/lib.rs")];
        assert_eq!(paths, changed(&expected));
        assert_eq!(affecting, ["kernel/abi/src/lib.rs"]);
    }

    #[test]
    fn a_user_space_change_is_unaffected_after_main_changed_the_kernel() {
        // A comparison of the base itself with the head would take the change
        // of the kernel on main for one of the pull request.
        let mut fixture = Fixture::new("diverged");
        let fork = head_of(&fixture);
        fixture.write("kernel/abi/src/lib.rs", "//! Changed on main.\n");
        fixture.commit_all();
        let main = head_of(&fixture);
        fixture.git(&["checkout", "--quiet", "-b", "topic", &fork]);
        fixture.write("user/app/src/main.rs", "fn main() {}\n");
        fixture.commit_all();
        let change = since_merge_base(&mut fixture, &main, "HEAD").expect("Git runs");
        assert_eq!(change.merge_base, fork);
        assert_eq!(change.paths, changed(&[("A", "user/app/src/main.rs")]));
        assert_eq!(change.affecting(&Layout::PRODUCTION), Vec::<&str>::new());
    }

    #[test]
    fn paths_beside_a_gate_input_are_not_within_it() {
        let (paths, affecting) = decided("beside", |fixture| {
            fixture.write("kernelx/a.rs", "\n");
            fixture.write("xtaskfoo/b", "\n");
        });
        let expected = [("A", "kernelx/a.rs"), ("A", "xtaskfoo/b")];
        assert_eq!(paths, changed(&expected));
        assert_eq!(affecting, Vec::<String>::new());
    }

    const REGISTRY: &str = "verification/targets.json";
    const PROOF: &str = "verification/Krepi/Proofs/A.lean";

    /// The registry of the impact fixture: the formal target `a`, with the
    /// proof module `Krepi.Proofs.A`, and the planned target `b`.
    const TARGETS: &str = r#"{"schema": 2, "targets": [
        {"name": "a", "proof_modules": ["Krepi.Proofs.A"]},
        {"name": "b", "state": "planned"}
    ]}
"#;

    /// The targets that `change` affects in a fixture with the registry
    /// [`TARGETS`] and the proof module of `a`.
    fn impact(label: &str, change: impl FnOnce(&Fixture)) -> Vec<(String, State)> {
        let files = [(REGISTRY, TARGETS), (PROOF, "module\n")];
        let (mut fixture, change) = changed_by(label, &files, change);
        impacted(&mut fixture, &Layout::PRODUCTION, &change).expect("the registry")
    }

    /// `(name, state)` pairs.
    fn listed(targets: &[(&str, State)]) -> Vec<(String, State)> {
        targets
            .iter()
            .map(|(name, state)| (name.to_string(), *state))
            .collect()
    }

    #[test]
    fn impact_lists_every_target_when_an_extraction_input_changes() {
        let all = listed(&[("a", State::Formal), ("b", State::Planned)]);
        let inputs = [
            "kernel/abi/src/lib.rs",
            "verification/qualification/src/lib.rs",
            CARGO_CONFIG,
        ];
        for path in inputs {
            let found = impact("extraction", |fixture| fixture.write(path, "// changed\n"));
            assert_eq!(found, all, "{path}");
        }
    }

    #[test]
    fn impact_lists_a_target_whose_entry_changed() {
        // A target of another entry and a new one, but not one removed.
        let edited = TARGETS.replace(
            r#"{"name": "a", "proof_modules": ["Krepi.Proofs.A"]},"#,
            r#"{"name": "c"},"#,
        );
        let edited = edited.replace(r#""planned"}"#, r#""planned", "budget": 60}"#);
        let found = impact("entry", |fixture| fixture.write(REGISTRY, &edited));
        assert_eq!(
            found,
            listed(&[("b", State::Planned), ("c", State::Formal)])
        );
        // Another form of the same entries.
        let value: serde_json::Value = serde_json::from_str(TARGETS).expect("JSON");
        let found = impact("form", |fixture| {
            fixture.write(REGISTRY, &value.to_string())
        });
        assert_eq!(found, []);
    }

    #[test]
    fn impact_lists_a_target_whose_proof_module_changed() {
        let found = impact("proof", |fixture| {
            fixture.write(PROOF, "module\n-- a proof\n")
        });
        assert_eq!(found, listed(&[("a", State::Formal)]));
    }

    #[test]
    fn impact_lists_no_target_for_other_changes() {
        // Gate inputs that are no inputs of extraction, and other paths.
        let found = impact("other", |fixture| {
            fixture.write("xtask/README", "Changed.\n");
            fixture.write("verification/Krepi/Spec/S.lean", "module\n");
            fixture.write("README.md", "Changed.\n");
        });
        assert_eq!(found, []);
    }

    #[test]
    fn impact_refuses_a_base_that_starts_with_a_hyphen_or_is_unknown() {
        let mut fixture = Fixture::new("refused");
        let layout = Layout::PRODUCTION;
        for base in ["-x", "--output=x", ""] {
            let refused = Err(format!("{base:?} is not a revision"));
            assert_eq!(impact_lines(&mut fixture, &layout, base), refused);
        }
        let error = impact_lines(&mut fixture, &layout, "unknown").expect_err("no revision");
        assert!(error.contains("unknown"), "{error}");
        // The command exits with 1 on an error and with 0 otherwise.
        let impact = |base: &str| {
            let matches = cli("").try_get_matches_from(["impact", "--base", base]);
            command(fixture.root(), &layout, &matches.expect("a command line"))
        };
        assert_eq!(impact("unknown"), ExitCode::FAILURE);
        assert_eq!(impact("HEAD"), ExitCode::SUCCESS);
    }

    #[test]
    fn the_impact_lines_give_the_paths_the_decision_and_the_targets() {
        // A path with a line break is printed escaped, on its line.
        let files = [(REGISTRY, TARGETS), (PROOF, "module\n")];
        let (mut fixture, change) = changed_by("lines", &files, |fixture| {
            fixture.write(PROOF, "module\n-- a proof\n");
            fixture.write("user/a\nb.rs", "\n");
        });
        let base = change.merge_base;
        assert_eq!(
            impact_lines(&mut fixture, &Layout::PRODUCTION, &base),
            Ok(vec![
                format!("merge base {base}"),
                "changed A user/a\\nb.rs".to_string(),
                format!("changed M {PROOF}"),
                "decision affected".to_string(),
                "target a formal".to_string(),
            ])
        );
        let head = head_of(&fixture);
        assert_eq!(
            impact_lines(&mut fixture, &Layout::PRODUCTION, &head),
            Ok(vec![
                format!("merge base {head}"),
                "decision unaffected".to_string()
            ])
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
            rejected(&files, &Layout::PRODUCTION),
            ["the gate inputs hold Python sources: \
              kernel/a/build.Py, verification/Tool.PY, xtask/helper.py"]
        );
    }
}
