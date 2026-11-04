//! The manifests step: crate licenses, release profiles and the dependency
//! direction between the two workspaces.

use std::path::Path;

use toml::{Table, Value};

use crate::repo::{self, Entry, Tree};

/// The kernel workspace. Its crates may only reach paths inside it.
pub const KERNEL: &str = "kernel";
/// The user-space workspace.
pub const USER: &str = "user";
/// The ABI crate: the only kernel-workspace crate that user space may use.
pub const ABI: &str = "kernel/abi";
/// The license of every crate in the repository.
pub const LICENSE: &str = "MIT";

/// The manifests step.
pub fn run(root: &Path) -> Result<(), String> {
    let problems = check(&Tree::load(root)?);
    if problems.is_empty() {
        Ok(())
    } else {
        Err(problems.join("\n"))
    }
}

/// Every manifest problem in `tree`.
pub fn check(tree: &Tree) -> Vec<String> {
    let mut problems = Vec::new();
    let mut manifests = Vec::new();
    for (path, text) in tree.texts() {
        if path == "Cargo.toml" || path.ends_with("/Cargo.toml") {
            match text.parse::<Table>() {
                Ok(table) => manifests.push((path, table)),
                Err(error) => problems.push(format!("{path}: not valid TOML: {error}")),
            }
        }
    }
    for (path, table) in &manifests {
        if table.contains_key("package") {
            check_license(path, table, &manifests, &mut problems);
        }
        check_dependencies(path, table, &mut problems);
    }
    for workspace in [KERNEL, USER] {
        check_workspace_root(workspace, &manifests, &mut problems);
    }
    check_kernel_sources(tree, &mut problems);
    problems
}

fn check_license(
    path: &str,
    table: &Table,
    manifests: &[(&str, Table)],
    problems: &mut Vec<String>,
) {
    let license = table
        .get("package")
        .and_then(|package| package.get("license"));
    let inherited = license
        .and_then(|value| value.get("workspace"))
        .and_then(Value::as_bool)
        == Some(true);
    let resolved = if inherited {
        workspace_root(path, manifests).and_then(|(_, root)| {
            root.get("workspace")
                .and_then(|workspace| workspace.get("package"))
                .and_then(|package| package.get("license"))
                .and_then(Value::as_str)
        })
    } else {
        license.and_then(Value::as_str)
    };
    if resolved != Some(LICENSE) {
        problems.push(format!(
            "{path}: the package license must be {LICENSE}, found {}",
            resolved.unwrap_or("none")
        ));
    }
}

/// The nearest manifest at or above the directory of `path` that declares a
/// workspace.
fn workspace_root<'a>(
    path: &str,
    manifests: &'a [(&'a str, Table)],
) -> Option<&'a (&'a str, Table)> {
    let mut dir = repo::parent(path).to_string();
    loop {
        let candidate = if dir.is_empty() {
            "Cargo.toml".to_string()
        } else {
            format!("{dir}/Cargo.toml")
        };
        if let Some(found) = manifests
            .iter()
            .find(|(manifest, table)| *manifest == candidate && table.contains_key("workspace"))
        {
            return Some(found);
        }
        if dir.is_empty() {
            return None;
        }
        dir = repo::parent(&dir).to_string();
    }
}

fn check_workspace_root(workspace: &str, manifests: &[(&str, Table)], problems: &mut Vec<String>) {
    let path = format!("{workspace}/Cargo.toml");
    let Some((_, table)) = manifests.iter().find(|(manifest, _)| *manifest == path) else {
        problems.push(format!(
            "{path}: missing; the {workspace} workspace has no root manifest"
        ));
        return;
    };
    if !table.contains_key("workspace") {
        problems.push(format!("{path}: must declare [workspace]"));
    }
    let overflow_checks = table
        .get("profile")
        .and_then(|profile| profile.get("release"))
        .and_then(|release| release.get("overflow-checks"))
        .and_then(Value::as_bool);
    if overflow_checks != Some(true) {
        problems.push(format!(
            "{path}: [profile.release] must set overflow-checks = true"
        ));
    }
}

/// The `path` of every dependency entry: the dependency tables at the top
/// level, under `[target.*]` and `[workspace]`, and every `[patch.*]` table.
fn dependency_paths(table: &Table) -> Vec<(String, String)> {
    const KINDS: [&str; 3] = ["dependencies", "dev-dependencies", "build-dependencies"];
    let mut sections: Vec<(String, &Table)> = Vec::new();
    for kind in KINDS {
        if let Some(section) = table.get(kind).and_then(Value::as_table) {
            sections.push((kind.to_string(), section));
        }
    }
    if let Some(targets) = table.get("target").and_then(Value::as_table) {
        for (cfg, target) in targets {
            for kind in KINDS {
                if let Some(section) = target.get(kind).and_then(Value::as_table) {
                    sections.push((format!("target.{cfg}.{kind}"), section));
                }
            }
        }
    }
    if let Some(section) = table
        .get("workspace")
        .and_then(|workspace| workspace.get("dependencies"))
        .and_then(Value::as_table)
    {
        sections.push(("workspace.dependencies".to_string(), section));
    }
    if let Some(patches) = table.get("patch").and_then(Value::as_table) {
        for (source, section) in patches {
            if let Some(section) = section.as_table() {
                sections.push((format!("patch.{source}"), section));
            }
        }
    }
    let mut paths = Vec::new();
    for (section, entries) in sections {
        for (name, entry) in entries {
            if let Some(path) = entry.get("path").and_then(Value::as_str) {
                paths.push((format!("[{section}] {name}"), path.to_string()));
            }
        }
    }
    paths
}

fn check_dependencies(path: &str, table: &Table, problems: &mut Vec<String>) {
    let dir = repo::parent(path);
    let in_kernel = repo::is_within(dir, KERNEL);
    let in_user = repo::is_within(dir, USER);
    if !in_kernel && !in_user {
        return;
    }
    for (entry, relative) in dependency_paths(table) {
        let resolved = repo::join(dir, &relative);
        let allowed = match &resolved {
            None => false,
            Some(target) if in_kernel => repo::is_within(target, KERNEL),
            Some(target) => !repo::is_within(target, KERNEL) || target == ABI,
        };
        if !allowed {
            let rule = if in_kernel {
                "kernel-workspace crates may only depend on paths inside kernel/"
            } else {
                "user-space crates may reach the kernel workspace only through the ABI crate (kernel/abi)"
            };
            problems.push(format!("{path}: {entry} has path `{relative}`; {rule}"));
        }
    }
}

/// The string literal at the start of `text`, after optional whitespace.
fn leading_literal(text: &str) -> Option<&str> {
    let rest = text.trim_start().strip_prefix('"')?;
    rest.find('"').map(|end| &rest[..end])
}

/// Symbolic links and literal source paths in the kernel workspace stay
/// inside it.
fn check_kernel_sources(tree: &Tree, problems: &mut Vec<String>) {
    for (path, entry) in tree.entries() {
        if !repo::is_within(path, KERNEL) {
            continue;
        }
        let dir = repo::parent(path);
        match entry {
            Entry::Symlink(target) => {
                if !repo::join(dir, target)
                    .is_some_and(|resolved| repo::is_within(&resolved, KERNEL))
                {
                    problems.push(format!(
                        "{path}: symbolic link to `{target}` leaves kernel/"
                    ));
                }
            }
            Entry::File(_) if path.ends_with(".rs") => {
                let Some(text) = tree.text(path) else {
                    continue;
                };
                for (number, line) in text.lines().enumerate() {
                    for literal in source_paths(line) {
                        if !repo::join(dir, literal)
                            .is_some_and(|resolved| repo::is_within(&resolved, KERNEL))
                        {
                            problems.push(format!(
                                "{path}:{}: the source path `{literal}` leaves kernel/",
                                number + 1
                            ));
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

/// The literal paths given to `include!`, `include_bytes!`, `include_str!`
/// and `#[path = ...]` on one line of Rust source.
fn source_paths(line: &str) -> Vec<&str> {
    let mut found = Vec::new();
    for marker in ["include!(", "include_bytes!(", "include_str!("] {
        for (at, _) in line.match_indices(marker) {
            if let Some(literal) = leading_literal(&line[at + marker.len()..]) {
                found.push(literal);
            }
        }
    }
    for (at, _) in line.match_indices("#[path") {
        let rest = line[at + "#[path".len()..].trim_start();
        if let Some(rest) = rest.strip_prefix('=')
            && let Some(literal) = leading_literal(rest)
        {
            found.push(literal);
        }
    }
    found
}

#[cfg(test)]
mod tests {
    use super::*;

    const KERNEL_ROOT: &str = "[workspace]\nmembers = [\"abi\", \"core\"]\n\n[workspace.package]\nlicense = \"MIT\"\n\n[profile.release]\noverflow-checks = true\n";
    const USER_ROOT: &str = "[workspace]\nmembers = [\"sdk\"]\n\n[workspace.package]\nlicense = \"MIT\"\n\n[workspace.dependencies]\nkrepi-abi = { path = \"../kernel/abi\" }\n\n[profile.release]\noverflow-checks = true\n";
    const ABI_CRATE: &str = "[package]\nname = \"krepi-abi\"\nlicense.workspace = true\n";
    const CORE_CRATE: &str = "[package]\nname = \"core-crate\"\nlicense = \"MIT\"\n\n[dependencies]\nkrepi-abi = { path = \"../abi\" }\n";
    const SDK_CRATE: &str = "[package]\nname = \"krepi-sdk\"\nlicense.workspace = true\n\n[dependencies]\nkrepi-abi.workspace = true\n";
    const XTASK_CRATE: &str = "[package]\nname = \"xtask\"\nlicense = \"MIT\"\n\n[workspace]\n";

    fn valid() -> Vec<(&'static str, String)> {
        vec![
            ("kernel/Cargo.toml", KERNEL_ROOT.to_string()),
            ("kernel/abi/Cargo.toml", ABI_CRATE.to_string()),
            ("kernel/core/Cargo.toml", CORE_CRATE.to_string()),
            (
                "kernel/core/src/lib.rs",
                "include!(\"generated.rs\");\n".to_string(),
            ),
            ("user/Cargo.toml", USER_ROOT.to_string()),
            ("user/sdk/Cargo.toml", SDK_CRATE.to_string()),
            ("xtask/Cargo.toml", XTASK_CRATE.to_string()),
        ]
    }

    fn problems_with(change: impl FnOnce(&mut Vec<(&'static str, String)>)) -> Vec<String> {
        let mut files = valid();
        change(&mut files);
        let borrowed: Vec<(&str, &str)> = files
            .iter()
            .map(|(path, text)| (*path, text.as_str()))
            .collect();
        check(&Tree::from_files(&borrowed))
    }

    fn replace(files: &mut [(&'static str, String)], path: &str, text: &str) {
        let file = files
            .iter_mut()
            .find(|(name, _)| *name == path)
            .expect("file exists");
        file.1 = text.to_string();
    }

    #[test]
    fn the_valid_layout_passes() {
        assert_eq!(problems_with(|_| {}), Vec::<String>::new());
    }

    #[test]
    fn rejects_a_license_other_than_mit() {
        let problems = problems_with(|files| {
            replace(
                files,
                "kernel/core/Cargo.toml",
                &CORE_CRATE.replace("\"MIT\"", "\"Apache-2.0\""),
            );
        });
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(problems[0].contains("license must be MIT"), "{problems:?}");
    }

    #[test]
    fn rejects_an_inherited_license_other_than_mit() {
        let problems = problems_with(|files| {
            replace(
                files,
                "user/Cargo.toml",
                &USER_ROOT.replace("\"MIT\"", "\"GPL-2.0\""),
            );
        });
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(
            problems[0].starts_with("user/sdk/Cargo.toml"),
            "{problems:?}"
        );
    }

    #[test]
    fn rejects_a_release_profile_without_overflow_checks() {
        let problems = problems_with(|files| {
            replace(
                files,
                "kernel/Cargo.toml",
                &KERNEL_ROOT.replace("overflow-checks = true", "opt-level = 3"),
            );
        });
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(problems[0].contains("overflow-checks"), "{problems:?}");
    }

    #[test]
    fn rejects_a_kernel_build_dependency_on_user_space() {
        let problems = problems_with(|files| {
            let text = format!(
                "{CORE_CRATE}\n[build-dependencies]\nkrepi-sdk = {{ path = \"../../user/sdk\" }}\n"
            );
            replace(files, "kernel/core/Cargo.toml", &text);
        });
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(
            problems[0].contains("[build-dependencies] krepi-sdk"),
            "{problems:?}"
        );
    }

    #[test]
    fn rejects_kernel_paths_that_leave_the_tree_in_other_tables() {
        let problems = problems_with(|files| {
            let text = format!(
                "{CORE_CRATE}\n[target.'cfg(test)'.dev-dependencies]\nx = {{ path = \"../../xtask\" }}\n\n[patch.crates-io]\ny = {{ path = \"../../../outside\" }}\n"
            );
            replace(files, "kernel/core/Cargo.toml", &text);
        });
        assert_eq!(problems.len(), 2, "{problems:?}");
    }

    #[test]
    fn rejects_a_user_dependency_on_a_kernel_crate_other_than_the_abi() {
        let problems = problems_with(|files| {
            let text = format!("{SDK_CRATE}core-crate = {{ path = \"../../kernel/core\" }}\n");
            replace(files, "user/sdk/Cargo.toml", &text);
        });
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(
            problems[0].contains("only through the ABI crate"),
            "{problems:?}"
        );
    }

    #[test]
    fn rejects_kernel_symlinks_and_source_paths_that_leave_the_tree() {
        let mut files = valid();
        replace(
            &mut files,
            "kernel/core/src/lib.rs",
            "include!(\"../../../user/x.rs\");\nconst B: &[u8] = include_bytes!(\"inside.bin\");\n#[path = \"../../../xtask/src/main.rs\"]\nmod m;\n",
        );
        let borrowed: Vec<(&str, &str)> = files
            .iter()
            .map(|(path, text)| (*path, text.as_str()))
            .collect();
        let mut tree = Tree::from_files(&borrowed);
        tree.insert("kernel/core/link", Entry::Symlink("../../user".to_string()));
        tree.insert("kernel/core/inner", Entry::Symlink("src".to_string()));
        let problems = check(&tree);
        assert_eq!(problems.len(), 3, "{problems:?}");
        assert!(
            problems
                .iter()
                .any(|problem| problem.starts_with("kernel/core/link"))
        );
        assert!(
            problems
                .iter()
                .any(|problem| problem.contains(":1: the source path"))
        );
        assert!(
            problems
                .iter()
                .any(|problem| problem.contains(":3: the source path"))
        );
    }
}
