//! The Lake project `verification/` as the gate builds it: the stage in which
//! one unit builds, the arguments of its Lake commands and the reading of
//! their output.
//!
//! A stage is a directory of the run laid out as the repository: the
//! project files of `verification/`, the Lean files that the unit installs,
//! and the two links below `artifacts/formal/lake` through which the
//! project's dependency on the Aeneas Lean library, and through it on
//! Mathlib, resolves to the tool installation. The links are not copies:
//! the installation is read where it is. Lake writes the build outputs of
//! the stage's own modules into `verification/.lake` of the stage, and
//! Lake's artifact cache is off, so no build of a stage reuses an output
//! from outside the run.

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

/// The axioms that every Lean development may use. Anything else that
/// `#print axioms` reports for a theorem must be allowed for it by name.
pub const STANDARD_AXIOMS: [&str; 3] = ["propext", "Classical.choice", "Quot.sound"];

/// The directory of the links to the installation, relative to the root of
/// a stage, as `lakefile.toml` names it.
const LINKS: &str = "artifacts/formal/lake";

/// The project files that a stage copies from the export.
pub const PROJECT_FILES: [&str; 3] = ["lakefile.toml", "lean-toolchain", "lake-manifest.json"];

/// Creates the stage `stage`, which must not exist, from the Lake project
/// `project` of the export, whose directory name it keeps, with the links
/// to `backend`, the Aeneas Lean library of the installation, and to its
/// packages.
pub fn create_stage(project: &Path, stage: &Path, backend: &Path) -> Result<(), String> {
    let at = |path: &Path, error: std::io::Error| format!("{}: {error}", path.display());
    fs::create_dir(stage)
        .map_err(|error| format!("cannot create the stage {}", at(stage, error)))?;
    let name = project
        .file_name()
        .ok_or_else(|| format!("{} names no directory", project.display()))?;
    let staged = stage.join(name);
    fs::create_dir(&staged).map_err(|error| at(&staged, error))?;
    for file in PROJECT_FILES {
        let (from, to) = (project.join(file), staged.join(file));
        fs::copy(&from, &to).map_err(|error| format!("cannot copy {}", at(&from, error)))?;
    }
    let links = stage.join(LINKS);
    fs::create_dir_all(&links).map_err(|error| at(&links, error))?;
    for (name, target) in [
        ("aeneas", backend.to_path_buf()),
        ("packages", backend.join(".lake/packages")),
    ] {
        let link = links.join(name);
        std::os::unix::fs::symlink(&target, &link).map_err(|error| at(&link, error))?;
    }
    Ok(())
}

/// Copies `file`, relative to `from`, to the same path below `to`, with its
/// directories.
pub fn copy_into(from: &Path, to: &Path, file: &str) -> Result<(), String> {
    let (source, destination) = (from.join(file), to.join(file));
    if let Some(parent) = destination.parent() {
        fs::create_dir_all(parent).map_err(|error| format!("{}: {error}", parent.display()))?;
    }
    fs::copy(&source, &destination)
        .map(|_| ())
        .map_err(|error| format!("cannot copy {}: {error}", source.display()))
}

/// The arguments of `lake` that build `module` with warnings as errors, so
/// that `sorry` fails the build too, and without Lake's cache.
pub fn build_args(module: &str) -> Vec<String> {
    ["build", "--no-cache", "--wfail", module]
        .map(str::to_string)
        .into()
}

/// The arguments of `lake` that check the Lean file `file`, relative to the
/// project, in the environment of the project.
pub fn check_args(file: &str) -> Vec<String> {
    ["env", "lean", file].map(str::to_string).into()
}

/// The source file of a project module, relative to the project.
pub fn module_file(module: &str) -> String {
    format!("{}.lean", module.replace('.', "/"))
}

/// The lines of a Lean or Lake log that report an error, trimmed.
pub fn errors(output: &str) -> Vec<String> {
    output
        .lines()
        .filter(|line| line.contains("error:"))
        .map(|line| line.trim().to_string())
        .collect()
}

/// Parses `#print axioms` output, which may wrap long axiom lists.
pub fn parse_axioms(output: &str) -> BTreeMap<String, Vec<String>> {
    const DEPENDS: &str = "' depends on axioms: [";
    const NONE: &str = "' does not depend on any axioms";
    let mut result = BTreeMap::new();
    let joined = output.replace('\n', " ");
    let mut rest = joined.as_str();
    while let Some(start) = rest.find('\'') {
        let after = &rest[start + 1..];
        // A name may itself end with primes, so the entry ends at the first
        // marker rather than at the next quote.
        let none = after.find(NONE);
        let depends = after.find(DEPENDS).filter(|d| none.is_none_or(|n| *d < n));
        let (name, tail, axioms) = if let Some(d) = depends {
            let list = &after[d + DEPENDS.len()..];
            let close = list.find(']').unwrap_or(list.len());
            let axioms = list[..close]
                .split(',')
                .map(|axiom| axiom.trim().to_string())
                .filter(|axiom| !axiom.is_empty())
                .collect();
            (&after[..d], &list[close..], axioms)
        } else if let Some(n) = none {
            (&after[..n], &after[n + NONE.len()..], Vec::new())
        } else {
            break;
        };
        if name.chars().any(char::is_whitespace) {
            rest = after;
            continue;
        }
        result.insert(name.to_string(), axioms);
        rest = tail;
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::scratch::Scratch;

    #[test]
    fn axiom_lists_are_parsed_across_lines() {
        let output = "'A.b' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n'C' does not depend on any axioms\n'D.e' depends on axioms: [sorryAx]\n";
        let parsed = parse_axioms(output);
        assert_eq!(parsed["A.b"], ["propext", "Classical.choice", "Quot.sound"]);
        assert!(parsed["C"].is_empty());
        assert_eq!(parsed["D.e"], ["sorryAx"]);
    }

    #[test]
    fn primed_names_are_parsed() {
        let output = "'A.zero_le'' depends on axioms: [propext]\n'B.x'' does not depend on any axioms\n'C.y' depends on axioms: [Quot.sound]\n";
        let parsed = parse_axioms(output);
        assert_eq!(parsed["A.zero_le'"], ["propext"]);
        assert!(parsed["B.x'"].is_empty());
        assert_eq!(parsed["C.y"], ["Quot.sound"]);
        assert_eq!(parsed.len(), 3);
    }

    #[test]
    fn a_stage_holds_the_project_files_and_links_the_installation() {
        let scratch = Scratch::new("stage");
        let project = scratch.0.join("export/verification");
        for file in PROJECT_FILES {
            scratch.write(&format!("export/verification/{file}"), file);
        }
        scratch.write("export/verification/Krepi/Proof.lean", "");
        let backend = scratch.0.join("tools/backend");
        let stage = scratch.0.join("stage");
        create_stage(&project, &stage, &backend).expect("a new stage");
        let staged = stage.join("verification");
        for file in PROJECT_FILES {
            assert_eq!(
                fs::read_to_string(staged.join(file)).expect("a project file"),
                file
            );
        }
        // Only the project files are copied.
        assert!(!staged.join("Krepi").exists());
        let link = |name: &str| fs::read_link(stage.join(LINKS).join(name)).expect("a link");
        assert_eq!(link("aeneas"), backend);
        assert_eq!(link("packages"), backend.join(".lake/packages"));
        // A stage is new.
        let error = create_stage(&project, &stage, &backend).expect_err("a used stage");
        assert!(error.starts_with("cannot create the stage "), "{error}");
        copy_into(&project, &staged, "Krepi/Proof.lean").expect("copy a module");
        assert!(staged.join("Krepi/Proof.lean").is_file());
    }

    #[test]
    fn the_lake_commands_have_their_arguments() {
        assert_eq!(
            build_args("KrepiGen.Qual.F.Funs"),
            ["build", "--no-cache", "--wfail", "KrepiGen.Qual.F.Funs"]
        );
        assert_eq!(check_args("Audit.lean"), ["env", "lean", "Audit.lean"]);
        assert_eq!(
            module_file("Krepi.Qualification.F"),
            "Krepi/Qualification/F.lean"
        );
        assert_eq!(
            errors(
                "✖ [2/2] Building X\nerror: X.lean:1:0: bad\n  warning: no\n error: build failed\n"
            ),
            ["error: X.lean:1:0: bad", "error: build failed"]
        );
    }
}
