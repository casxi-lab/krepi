//! The manifests step: crate licenses, release profiles, the dependency
//! direction between the two workspaces and, as Cargo resolves it, the
//! kernel workspace's freedom from external crates and the shape of its
//! root manifest.

use std::fs;
use std::path::Path;
use std::process::Command;

use serde_json::Value as Json;
use toml::{Table, Value};

use crate::check;
use crate::repo::{self, Entry, Tree};

/// The kernel workspace. Its crates may only reach paths inside it.
pub const KERNEL: &str = "kernel";
/// The root package of the kernel workspace, which its root manifest
/// declares once the workspace has one.
pub const KERNEL_PACKAGE: &str = "krepi-kernel";
/// The user-space workspace.
pub const USER: &str = "user";
/// The ABI crate: the only kernel-workspace crate that user space may use.
pub const ABI: &str = "kernel/abi";
/// The license of every crate in the repository.
pub const LICENSE: &str = "MIT";

/// The manifests step.
pub fn run(root: &Path) -> Result<(), String> {
    let mut problems = check(&Tree::load(root)?);
    problems.extend(check_kernel_workspace(root));
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
    check_cargo_configs(tree, &mut problems);
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

/// The problems of the path dependencies of the kernel manifests among
/// `paths`, read below `root`, as [`check`] finds them in the checkout.
pub fn kernel_dependency_problems<'a>(
    root: &Path,
    paths: impl IntoIterator<Item = &'a String>,
) -> Result<Vec<String>, String> {
    let mut problems = Vec::new();
    for path in paths {
        if repo::is_within(path, KERNEL) && path.ends_with("/Cargo.toml") {
            let text = fs::read_to_string(root.join(path))
                .map_err(|error| format!("cannot read {path}: {error}"))?;
            let table = (text.parse::<Table>())
                .map_err(|error| format!("{path}: not valid TOML: {error}"))?;
            check_dependencies(path, &table, &mut problems);
        }
    }
    Ok(problems)
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

/// The arguments of Cargo that resolve the kernel workspace offline, from its
/// `Cargo.lock` and with every feature of its members, run from the
/// repository root; the proof gate runs the same command in its export of
/// the repository, for the workspace `kernel` of its layout.
pub fn kernel_metadata_args(kernel: &str) -> Vec<String> {
    let manifest = format!("{kernel}/Cargo.toml");
    [
        "metadata",
        "--format-version",
        "1",
        "--locked",
        "--offline",
        "--all-features",
        "--manifest-path",
        &manifest,
    ]
    .map(str::to_string)
    .to_vec()
}

/// Asks Cargo to resolve the kernel workspace below `root` with
/// [`kernel_metadata_args`] and returns what it reports. A registry or Git
/// package that is not cached, or a stale `Cargo.lock`, fails the
/// resolution.
pub fn kernel_metadata(root: &Path) -> Result<Json, String> {
    let args = kernel_metadata_args(KERNEL);
    let program = check::cargo();
    let shown = format!("{} {}", program.to_string_lossy(), args.join(" "));
    println!("$ {shown}");
    let output = Command::new(&program)
        .args(&args)
        .current_dir(root)
        .output()
        .map_err(|error| format!("cannot run `{shown}`: {error}"))?;
    let stderr = String::from_utf8_lossy(&output.stderr);
    if !output.status.success() {
        let status = output.status;
        return Err(format!(
            "`{shown}` exited with {status}:\n{}",
            stderr.trim_end()
        ));
    }
    eprint!("{stderr}");
    serde_json::from_slice(&output.stdout)
        .map_err(|error| format!("`{shown}` printed no valid JSON: {error}"))
}

/// Resolves the kernel workspace below `root` with [`kernel_metadata`] and
/// checks what Cargo reports.
pub fn check_kernel_workspace(root: &Path) -> Vec<String> {
    let workspace = [KERNEL, KERNEL_PACKAGE];
    match kernel_metadata(root) {
        Ok(metadata) => check_kernel_metadata(&metadata, &root.join(KERNEL), workspace),
        Err(problem) => vec![problem],
    }
}

/// Problems in what `cargo metadata` reports for the kernel workspace in
/// `kernel`, `workspace` with its root package: its root must be `kernel`,
/// and every package must be a member of it, with its manifest and the
/// sources of its targets inside `kernel`; and the problems of
/// [`root_shape`] in its root manifest. Paths are compared with symbolic
/// links resolved; a path that cannot be resolved is a problem.
pub fn check_kernel_metadata(metadata: &Json, kernel: &Path, workspace: [&str; 2]) -> Vec<String> {
    let kernel = match fs::canonicalize(kernel) {
        Ok(kernel) => kernel,
        Err(error) => return vec![format!("cannot resolve {}: {error}", kernel.display())],
    };
    let resolve = |path: &Json| path.as_str().and_then(|path| fs::canonicalize(path).ok());
    let inside = |path: &Json| resolve(path).is_some_and(|path| path.starts_with(&kernel));
    let mut problems = Vec::new();
    let root = &metadata["workspace_root"];
    if resolve(root).as_ref() != Some(&kernel) {
        problems.push(format!(
            "kernel workspace: the root {root} does not resolve to kernel/"
        ));
    }
    let (Some(packages), Some(members)) = (
        metadata["packages"].as_array(),
        metadata["workspace_members"].as_array(),
    ) else {
        problems.push("kernel workspace: cargo metadata lists no packages or members".to_string());
        return problems;
    };
    for package in packages {
        let (name, id) = (&package["name"], &package["id"]);
        // Members have no source: registry and Git packages are never members.
        if !members.contains(id) {
            problems.push(format!(
                "kernel workspace: package {name} is not a member: {id}"
            ));
            continue;
        }
        let manifest = &package["manifest_path"];
        if !inside(manifest) {
            problems.push(format!(
                "kernel workspace: package {name} has a manifest that does not resolve inside kernel/: {manifest}"
            ));
        }
        for target in package["targets"].as_array().into_iter().flatten() {
            let (target, path) = (&target["name"], &target["src_path"]);
            if !inside(path) {
                problems.push(format!(
                    "kernel workspace: target {target} of package {name} has a source that does not resolve inside kernel/: {path}"
                ));
            }
        }
    }
    problems.extend(root_problems(packages, &kernel, workspace));
    problems
}

/// The tables of the root manifest of the kernel workspace, each with the
/// keys that it may hold.
const ROOT_TABLES: [(&str, &str); 5] = [
    (
        "package",
        "name version edition license publish description rust-version",
    ),
    ("workspace", "resolver members package"),
    ("lints", "rust"),
    ("profile", "release"),
    ("lib", "path"),
];

/// The kinds of the targets of the root package.
const ROOT_KINDS: [&str; 2] = ["lib", "test"];

/// The name of the package that the manifest `text` declares, if it has
/// `[package]`; an empty name when it has none.
pub fn root_package(text: &str) -> Result<Option<String>, String> {
    let table: Table = (text.parse()).map_err(|error| format!("not valid TOML: {error}"))?;
    let name = |package: &Value| {
        package
            .get("name")
            .and_then(Value::as_str)
            .unwrap_or("")
            .to_string()
    };
    Ok(table.get("package").map(name))
}

/// The problems of the shape of the root manifest of the kernel workspace,
/// `manifest`, whose package has targets of the `kinds` that `cargo
/// metadata` reports, as `(kind, source)`, and the library `lib`, as its
/// path and text. A manifest without `[package]`, of a virtual workspace,
/// passes. With it, the package is `root` of the workspace `kernel`, with
/// only the tables and keys of [`ROOT_TABLES`], unsafe code forbidden, only
/// targets of [`ROOT_KINDS`], even among those that Cargo finds by itself,
/// and an unconditional `#![no_std]` in its library.
pub fn root_shape(
    [kernel, root]: [&str; 2],
    manifest: &str,
    kinds: &[(String, String)],
    lib: Option<(&str, &str)>,
) -> Vec<String> {
    let path = format!("{kernel}/Cargo.toml");
    let table: Table = match manifest.parse() {
        Ok(table) => table,
        Err(error) => return vec![format!("{path}: not valid TOML: {error}")],
    };
    let Some(package) = table.get("package") else {
        return Vec::new();
    };
    let mut problems = Vec::new();
    let name = package.get("name").and_then(Value::as_str).unwrap_or("");
    if name != root {
        problems.push(format!(
            "{path}: the root package is named `{name}`, not `{root}`"
        ));
    }
    for (key, value) in &table {
        let Some((_, keys)) = ROOT_TABLES.iter().find(|(table, _)| table == key) else {
            problems.push(format!("{path}: the root manifest may not have [{key}]"));
            continue;
        };
        let Some(value) = value.as_table() else {
            problems.push(format!("{path}: `{key}` is not a table"));
            continue;
        };
        let allowed = |inner: &&String| keys.split(' ').any(|allowed| allowed == inner.as_str());
        for inner in value.keys().filter(|inner| !allowed(inner)) {
            problems.push(format!(
                "{path}: the root manifest may not have {key}.{inner}"
            ));
        }
    }
    let unsafe_code = (table.get("lints"))
        .and_then(|lints| lints.get("rust"))
        .and_then(|rust| rust.get("unsafe_code"))
        .and_then(Value::as_str);
    if unsafe_code != Some("forbid") {
        problems.push(format!(
            "{path}: the root manifest must set lints.rust.unsafe_code = \"forbid\""
        ));
    }
    for (kind, source) in kinds
        .iter()
        .filter(|(kind, _)| !ROOT_KINDS.contains(&kind.as_str()))
    {
        let what = match kind.as_str() {
            "custom-build" => "a build script".to_string(),
            kind => format!("a target of the kind {kind}"),
        };
        problems.push(format!(
            "{path}: the root package may not have {what}, {source}"
        ));
    }
    let unconditional = |attr: &syn::Attribute| {
        matches!(attr.style, syn::AttrStyle::Inner(_))
            && matches!(&attr.meta, syn::Meta::Path(path) if path.is_ident("no_std"))
    };
    let no_std = |text| syn::parse_file(text).map(|file| file.attrs.iter().any(unconditional));
    match lib.map(|(lib, text)| (lib, no_std(text))) {
        None => problems.push(format!("{path}: the root package has no library")),
        Some((_, Ok(true))) => {}
        Some((lib, Ok(false))) => problems.push(format!(
            "{lib}: the library of the root package must have an unconditional #![no_std]"
        )),
        Some((lib, Err(error))) => problems.push(format!("{lib}: does not parse: {error}")),
    }
    problems
}

/// The problems of [`root_shape`] for the root manifest in `kernel`, a
/// resolved path of `ws`, and the package of `packages` whose manifest it is.
fn root_problems(packages: &[Json], kernel: &Path, ws: [&str; 2]) -> Vec<String> {
    let manifest = kernel.join("Cargo.toml");
    let text = |path: &Path| {
        fs::read_to_string(path).map_err(|error| format!("cannot read {}: {error}", path.display()))
    };
    let resolved = |value: &Json| value.as_str().and_then(|path| fs::canonicalize(path).ok());
    let below = |path: &Path| match path.strip_prefix(kernel) {
        Ok(below) => format!("{}/{}", ws[0], below.display()),
        Err(_) => path.display().to_string(),
    };
    let root = (packages.iter())
        .find(|package| resolved(&package["manifest_path"]) == Some(manifest.clone()));
    let targets = root
        .into_iter()
        .flat_map(|root| root["targets"].as_array().into_iter().flatten());
    let (mut kinds, mut lib) = (Vec::new(), None);
    for target in targets {
        let source = resolved(&target["src_path"]).unwrap_or_default();
        for kind in (target["kind"].as_array().into_iter().flatten()).filter_map(Json::as_str) {
            lib = lib.or_else(|| (kind == "lib").then(|| source.clone()));
            kinds.push((kind.to_string(), below(&source)));
        }
    }
    match (text(&manifest), lib.map(|lib| (below(&lib), text(&lib)))) {
        (Err(error), _) | (_, Some((_, Err(error)))) => vec![error],
        (Ok(toml), Some((lib, Ok(text)))) => root_shape(ws, &toml, &kinds, Some((&lib, &text))),
        (Ok(toml), None) => root_shape(ws, &toml, &kinds, None),
    }
}

/// Whether the tracked `path`, without regard to ASCII case as a
/// case-insensitive file system reads it, is a `.cargo` entry that stands
/// for the directory (a link or a submodule) or a configuration file in a
/// `.cargo` directory, at the repository root or in a directory of the
/// kernel workspace.
fn is_kernel_cargo_config(path: &str) -> bool {
    let path = path.to_ascii_lowercase();
    let dir = path
        .strip_suffix("/config.toml")
        .or_else(|| path.strip_suffix("/config"))
        .unwrap_or(&path);
    let (outer, name) = dir.rsplit_once('/').unwrap_or(("", dir));
    name == ".cargo" && (outer.is_empty() || repo::is_within(outer, KERNEL))
}

/// Every string in `value`, at any depth.
fn strings(value: &Value, found: &mut Vec<String>) {
    match value {
        Value::String(text) => found.push(text.clone()),
        Value::Array(items) => items.iter().for_each(|item| strings(item, found)),
        Value::Table(table) => table.values().for_each(|item| strings(item, found)),
        _ => {}
    }
}

/// Tracked Cargo configuration that applies to the kernel workspace passes
/// rustc no crate and no library search path: no string in it, split at
/// whitespace, has a word that starts with `--extern` or `-L`.
fn check_cargo_configs(tree: &Tree, problems: &mut Vec<String>) {
    for (path, _) in tree
        .entries()
        .filter(|(path, _)| is_kernel_cargo_config(path))
    {
        let Some(Ok(table)) = tree.text(path).map(str::parse::<Table>) else {
            problems.push(format!(
                "{path}: Cargo configuration must be a regular file of valid TOML"
            ));
            continue;
        };
        let mut texts = Vec::new();
        strings(&Value::Table(table), &mut texts);
        for word in texts.iter().flat_map(|text| text.split_whitespace()) {
            if word.starts_with("--extern") || word.starts_with("-L") {
                problems.push(format!(
                    "{path}: `{word}` would pass rustc a crate or a library search path"
                ));
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use serde_json::json;

    use super::*;
    use crate::scratch::Scratch;

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

    fn config_problems(path: &'static str, entry: Entry) -> Vec<String> {
        let files: Vec<(&str, String)> = valid();
        let borrowed: Vec<(&str, &str)> = files
            .iter()
            .map(|(path, text)| (*path, text.as_str()))
            .collect();
        let mut tree = Tree::from_files(&borrowed);
        tree.insert(path, entry);
        check(&tree)
    }

    fn config(text: &str) -> Entry {
        Entry::File(text.as_bytes().to_vec())
    }

    #[test]
    fn accepts_the_cargo_configuration_of_the_repository() {
        let text = include_str!("../../.cargo/config.toml");
        assert_eq!(
            config_problems(".cargo/config.toml", config(text)),
            Vec::<String>::new()
        );
    }

    #[test]
    fn accepts_cargo_configuration_that_passes_no_crate() {
        let text = "[build]\nrustflags = [\"-C\", \"link-arg=-Tlink.ld\"]\n\n[alias]\nk = \"build --release\"\n";
        assert_eq!(
            config_problems("kernel/.cargo/config.toml", config(text)),
            Vec::<String>::new()
        );
    }

    #[test]
    fn rejects_extern_and_library_search_paths_in_cargo_configuration() {
        let text = "[build]\nrustflags = [\"--extern\", \"x=/tmp/libx.rlib\", \"-L/tmp\"]\n\n[target.aarch64-unknown-none]\nrustflags = \"--extern=y=/tmp/liby.rlib -L dependency=/tmp\"\n";
        let problems = config_problems("kernel/.cargo/config.toml", config(text));
        assert_eq!(problems.len(), 4, "{problems:?}");
        for word in [
            "`--extern`",
            "`-L/tmp`",
            "`--extern=y=/tmp/liby.rlib`",
            "`-L`",
        ] {
            assert!(
                problems.iter().any(|problem| problem.contains(word)),
                "{word}: {problems:?}"
            );
        }
    }

    #[test]
    fn rejects_cargo_configuration_whatever_the_case_of_its_name() {
        let text = "[build]\nrustflags = [\"-L/tmp\"]\n";
        for path in [
            ".cargo/config",
            "kernel/.Cargo/Config.toml",
            "Kernel/abi/.CARGO/CONFIG",
        ] {
            let problems = config_problems(path, config(text));
            assert_eq!(problems.len(), 1, "{path}: {problems:?}");
            assert!(problems[0].contains("`-L/tmp`"), "{problems:?}");
        }
    }

    #[test]
    fn rejects_cargo_configuration_behind_a_symbolic_link() {
        for path in [".cargo", "kernel/.cargo/config.toml"] {
            let problems = config_problems(path, Entry::Symlink("elsewhere".to_string()));
            assert_eq!(problems.len(), 1, "{problems:?}");
            assert!(problems[0].contains("regular file"), "{problems:?}");
        }
    }

    /// A path in this repository, which exists, as Cargo would print it.
    fn at(path: &str) -> Json {
        Json::from(repo::root().join(path).to_string_lossy().into_owned())
    }

    /// A package whose id is its name, with the given source, manifest and
    /// targets (kind and source), paths relative to the repository root.
    fn package(name: &str, source: Json, manifest: &str, targets: &[(&str, &str)]) -> Json {
        let targets: Vec<Json> = targets
            .iter()
            .map(|(kind, path)| json!({ "name": kind, "kind": [kind], "src_path": at(path) }))
            .collect();
        json!({ "name": name, "id": name, "source": source, "manifest_path": at(manifest), "targets": targets })
    }

    /// The member `m` of the kernel workspace.
    fn member(manifest: &str, targets: &[(&str, &str)]) -> Json {
        package("m", Json::Null, manifest, targets)
    }

    const LIB: [(&str, &str); 1] = [("lib", "kernel/abi/src/lib.rs")];

    fn local() -> Json {
        member("kernel/abi/Cargo.toml", &LIB)
    }

    /// The problems of a kernel workspace with the root `root`, whose only
    /// member is `m`, and the given packages.
    fn metadata_problems(root: &str, packages: &[Json]) -> Vec<String> {
        let metadata =
            json!({ "workspace_root": at(root), "workspace_members": ["m"], "packages": packages });
        check_kernel_metadata(
            &metadata,
            &repo::root().join(KERNEL),
            [KERNEL, KERNEL_PACKAGE],
        )
    }

    /// The single problem of a kernel workspace with `extra` next to a local
    /// member.
    fn only_problem(extra: Json) -> String {
        let problems = metadata_problems(KERNEL, &[local(), extra]);
        assert_eq!(problems.len(), 1, "{problems:?}");
        problems[0].clone()
    }

    #[test]
    fn metadata_of_local_members_passes() {
        let targets = [
            ("lib", "kernel/abi/src/lib.rs"),
            ("test", "kernel/abi/src/lib.rs"),
        ];
        let tested = member("kernel/abi/Cargo.toml", &targets);
        assert_eq!(
            metadata_problems(KERNEL, &[local(), tested]),
            Vec::<String>::new()
        );
    }

    #[test]
    fn metadata_rejects_a_registry_package() {
        let registry = json!("registry+https://github.com/rust-lang/crates.io-index");
        let problem = only_problem(package("x", registry, "kernel/abi/Cargo.toml", &LIB));
        assert!(
            problem.contains("package \"x\" is not a member"),
            "{problem}"
        );
    }

    #[test]
    fn metadata_rejects_a_git_package() {
        let git = json!("git+https://example.com/x.git#0123abc");
        let problem = only_problem(package("x", git, "kernel/abi/Cargo.toml", &LIB));
        assert!(
            problem.contains("package \"x\" is not a member"),
            "{problem}"
        );
    }

    #[test]
    fn metadata_rejects_a_local_package_that_is_not_a_member() {
        let problem = only_problem(package("x", Json::Null, "kernel/abi/Cargo.toml", &LIB));
        assert!(
            problem.contains("package \"x\" is not a member"),
            "{problem}"
        );
    }

    #[test]
    fn metadata_rejects_a_manifest_outside_kernel() {
        let problem = only_problem(member("xtask/Cargo.toml", &LIB));
        assert!(problem.contains("has a manifest"), "{problem}");
    }

    #[test]
    fn metadata_rejects_a_build_script_outside_kernel() {
        let targets = [("custom-build", "xtask/src/main.rs")];
        let problem = only_problem(member("kernel/abi/Cargo.toml", &targets));
        assert!(problem.contains("xtask/src/main.rs"), "{problem}");
    }

    #[test]
    fn metadata_rejects_a_library_outside_kernel() {
        let targets = [("lib", "xtask/src/main.rs")];
        let problem = only_problem(member("kernel/abi/Cargo.toml", &targets));
        assert!(problem.contains("target \"lib\""), "{problem}");
    }

    #[test]
    fn metadata_rejects_a_workspace_root_other_than_kernel() {
        for root in ["", "kernel/abi"] {
            let problems = metadata_problems(root, &[local()]);
            assert_eq!(problems.len(), 1, "{problems:?}");
            assert!(problems[0].contains("the root"), "{problems:?}");
        }
    }

    #[test]
    fn metadata_rejects_a_path_that_does_not_exist() {
        let missing = [("lib", "kernel/abi/src/missing.rs")];
        let problem = only_problem(member("kernel/abi/Cargo.toml", &missing));
        assert!(problem.contains("missing.rs"), "{problem}");
    }

    #[test]
    fn metadata_without_packages_fails() {
        let metadata = json!({ "workspace_root": at(KERNEL), "workspace_members": [] });
        let problems = check_kernel_metadata(
            &metadata,
            &repo::root().join(KERNEL),
            [KERNEL, KERNEL_PACKAGE],
        );
        assert_eq!(problems.len(), 1, "{problems:?}");
    }

    /// A root manifest of the kernel workspace in its shape.
    const ROOT: &str = "[package]\nname = \"krepi-kernel\"\nversion = \"0.1.0\"\nedition = \"2024\"\nlicense.workspace = true\npublish = false\ndescription = \"The core.\"\nrust-version = \"1.99\"\n\n[workspace]\nresolver = \"3\"\nmembers = [\"abi\"]\n\n[workspace.package]\nlicense = \"MIT\"\n\n[lib]\npath = \"src/lib.rs\"\n\n[lints.rust]\nunsafe_code = \"forbid\"\n\n[profile.release]\noverflow-checks = true\n";

    /// The library of the root package.
    const ROOT_LIB: &str = "//! The core.\n#![no_std]\n#![forbid(unsafe_code)]\n\npub fn f() {}\n";

    /// The problems of the shape of the root manifest `manifest`, whose
    /// package has the library [`ROOT_LIB`] and the further targets
    /// `kinds`.
    fn shape(manifest: &str, kinds: &[(&str, &str)]) -> Vec<String> {
        shape_with(manifest, kinds, ROOT_LIB)
    }

    fn shape_with(manifest: &str, kinds: &[(&str, &str)], lib: &str) -> Vec<String> {
        let kinds: Vec<(String, String)> =
            [("lib", "kernel/src/lib.rs"), ("test", "kernel/tests/t.rs")]
                .iter()
                .chain(kinds)
                .map(|(kind, source)| (kind.to_string(), source.to_string()))
                .collect();
        root_shape(
            [KERNEL, KERNEL_PACKAGE],
            manifest,
            &kinds,
            Some(("kernel/src/lib.rs", lib)),
        )
    }

    /// The problems of [`ROOT`] followed by `extra`.
    fn shape_after(extra: &str) -> Vec<String> {
        shape(&format!("{ROOT}\n{extra}"), &[])
    }

    #[test]
    fn a_root_manifest_in_its_shape_passes() {
        assert_eq!(shape(ROOT, &[]), Vec::<String>::new());
        // A virtual workspace has no root package, whatever it holds.
        let virtual_workspace = include_str!("../../kernel/Cargo.toml");
        assert_eq!(root_package(virtual_workspace), Ok(None));
        assert_eq!(
            root_shape([KERNEL, KERNEL_PACKAGE], virtual_workspace, &[], None),
            Vec::<String>::new()
        );
        assert_eq!(
            root_shape(
                [KERNEL, KERNEL_PACKAGE],
                "[workspace]\n\n[features]\nx = []\n",
                &[],
                None
            ),
            Vec::<String>::new()
        );
        assert_eq!(root_package(ROOT), Ok(Some(KERNEL_PACKAGE.to_string())));
    }

    #[test]
    fn a_root_package_of_another_name_fails() {
        let renamed = ROOT.replace("name = \"krepi-kernel\"", "name = \"kernel\"");
        assert_eq!(
            shape(&renamed, &[]),
            ["kernel/Cargo.toml: the root package is named `kernel`, not `krepi-kernel`"]
        );
        assert_eq!(root_package(&renamed), Ok(Some("kernel".to_string())));
    }

    #[test]
    fn a_root_manifest_with_a_dependency_table_fails() {
        assert_eq!(
            shape_after("[workspace.dependencies]\nkrepi-abi = { path = \"abi\" }\n"),
            ["kernel/Cargo.toml: the root manifest may not have workspace.dependencies"]
        );
        for table in ["dependencies", "dev-dependencies", "build-dependencies"] {
            assert_eq!(
                shape_after(&format!("[{table}]\nkrepi-abi = {{ path = \"abi\" }}\n")),
                [format!(
                    "kernel/Cargo.toml: the root manifest may not have [{table}]"
                )],
                "{table}"
            );
        }
    }

    #[test]
    fn a_root_manifest_with_target_tables_fails() {
        assert_eq!(
            shape_after("[target.'cfg(unix)'.dependencies]\nkrepi-abi = { path = \"abi\" }\n"),
            ["kernel/Cargo.toml: the root manifest may not have [target]"]
        );
    }

    #[test]
    fn a_root_manifest_with_features_fails() {
        assert_eq!(
            shape_after("[features]\ndefault = []\n"),
            ["kernel/Cargo.toml: the root manifest may not have [features]"]
        );
    }

    #[test]
    fn a_root_manifest_with_patches_fails() {
        assert_eq!(
            shape_after("[patch.crates-io]\nkrepi-abi = { path = \"abi\" }\n"),
            ["kernel/Cargo.toml: the root manifest may not have [patch]"]
        );
    }

    #[test]
    fn a_root_manifest_with_replacements_fails() {
        assert_eq!(
            shape_after("[replace]\n\"krepi-abi:0.1.0\" = { path = \"abi\" }\n"),
            ["kernel/Cargo.toml: the root manifest may not have [replace]"]
        );
    }

    #[test]
    fn a_root_package_with_a_binary_fails() {
        // Cargo finds `src/main.rs` by itself, and `cargo metadata` reports it.
        assert_eq!(
            shape(ROOT, &[("bin", "kernel/src/main.rs")]),
            [
                "kernel/Cargo.toml: the root package may not have a target of the kind bin, kernel/src/main.rs"
            ]
        );
        assert_eq!(
            shape_after("[[bin]]\nname = \"tool\"\npath = \"src/tool.rs\"\n"),
            ["kernel/Cargo.toml: the root manifest may not have [bin]"]
        );
    }

    #[test]
    fn a_root_package_with_an_example_fails() {
        assert_eq!(
            shape(ROOT, &[("example", "kernel/examples/e.rs")]),
            [
                "kernel/Cargo.toml: the root package may not have a target of the kind example, kernel/examples/e.rs"
            ]
        );
        assert_eq!(
            shape_after("[[example]]\nname = \"e\"\n"),
            ["kernel/Cargo.toml: the root manifest may not have [example]"]
        );
    }

    #[test]
    fn a_root_package_with_a_benchmark_fails() {
        assert_eq!(
            shape(ROOT, &[("bench", "kernel/benches/b.rs")]),
            [
                "kernel/Cargo.toml: the root package may not have a target of the kind bench, kernel/benches/b.rs"
            ]
        );
        assert_eq!(
            shape_after("[[bench]]\nname = \"b\"\n"),
            ["kernel/Cargo.toml: the root manifest may not have [bench]"]
        );
    }

    #[test]
    fn a_root_manifest_with_package_metadata_fails() {
        // Charon reads `[package.metadata.charon]`.
        assert_eq!(
            shape_after("[package.metadata.charon]\nextract_opaque_bodies = true\n"),
            ["kernel/Cargo.toml: the root manifest may not have package.metadata"]
        );
    }

    #[test]
    fn a_root_manifest_with_default_members_fails() {
        let manifest = ROOT.replace(
            "members = [\"abi\"]\n",
            "members = [\"abi\"]\ndefault-members = [\".\"]\n",
        );
        assert_eq!(
            shape(&manifest, &[]),
            ["kernel/Cargo.toml: the root manifest may not have workspace.default-members"]
        );
    }

    #[test]
    fn a_root_manifest_with_a_dev_profile_fails() {
        assert_eq!(
            shape_after("[profile.dev]\noverflow-checks = false\n"),
            ["kernel/Cargo.toml: the root manifest may not have profile.dev"]
        );
    }

    #[test]
    fn a_root_package_with_a_build_script_fails() {
        assert_eq!(
            shape(ROOT, &[("custom-build", "kernel/build.rs")]),
            ["kernel/Cargo.toml: the root package may not have a build script, kernel/build.rs"]
        );
    }

    #[test]
    fn a_root_manifest_that_does_not_forbid_unsafe_code_fails() {
        let manifest = ROOT.replace("unsafe_code = \"forbid\"", "unsafe_code = \"deny\"");
        let problem =
            "kernel/Cargo.toml: the root manifest must set lints.rust.unsafe_code = \"forbid\"";
        assert_eq!(shape(&manifest, &[]), [problem]);
        let manifest = ROOT.replace("[lints.rust]\nunsafe_code = \"forbid\"\n", "");
        assert_eq!(shape(&manifest, &[]), [problem]);
    }

    #[test]
    fn a_root_library_without_an_unconditional_no_std_fails() {
        let lib = ROOT_LIB.replace("#![no_std]", "#![cfg_attr(not(test), no_std)]");
        assert_eq!(
            shape_with(ROOT, &[], &lib),
            [
                "kernel/src/lib.rs: the library of the root package must have an unconditional #![no_std]"
            ]
        );
        let kinds = [("test".to_string(), "kernel/tests/t.rs".to_string())];
        assert_eq!(
            root_shape([KERNEL, KERNEL_PACKAGE], ROOT, &kinds, None),
            ["kernel/Cargo.toml: the root package has no library"]
        );
    }

    #[test]
    fn cargo_reports_the_targets_of_the_root_package_that_it_finds_by_itself() {
        let scratch = repository("root-package");
        scratch.write(
            "kernel/Cargo.toml",
            "[package]\nname = \"krepi-kernel\"\nversion = \"0.0.0\"\nedition = \"2024\"\n\n\
             [workspace]\nresolver = \"3\"\nmembers = [\"a\", \"b\"]\n\n\
             [lints.rust]\nunsafe_code = \"forbid\"\n",
        );
        scratch.write("kernel/src/lib.rs", "#![no_std]\n");
        scratch.lock();
        assert_eq!(check_kernel_workspace(&scratch.0), Vec::<String>::new());
        scratch.write("kernel/src/main.rs", "fn main() {}\n");
        scratch.write("kernel/build.rs", "fn main() {}\n");
        assert_eq!(
            check_kernel_workspace(&scratch.0),
            [
                "kernel/Cargo.toml: the root package may not have a target of the kind bin, kernel/src/main.rs",
                "kernel/Cargo.toml: the root package may not have a build script, kernel/build.rs"
            ]
        );
    }

    const MEMBER: &str =
        "[package]\nname = \"a\"\nedition = \"2024\"\n\n[dependencies]\nb = { path = \"../b\" }\n";

    /// A repository whose kernel workspace holds the crate `a`, which depends
    /// on the crate `b`, with the crate `outside` next to `kernel/`.
    fn repository(label: &str) -> Scratch {
        let scratch = Scratch::new(label);
        scratch.write(
            "kernel/Cargo.toml",
            "[workspace]\nresolver = \"3\"\nmembers = [\"a\", \"b\"]\n",
        );
        scratch.write("kernel/a/Cargo.toml", MEMBER);
        scratch.write("kernel/a/src/lib.rs", "");
        scratch.write(
            "kernel/b/Cargo.toml",
            "[package]\nname = \"b\"\nedition = \"2024\"\n",
        );
        scratch.write("kernel/b/src/lib.rs", "");
        // A workspace of its own, so that Cargo does not look for one in the
        // directories that hold the scratch directory.
        scratch.write(
            "outside/Cargo.toml",
            "[package]\nname = \"outside\"\nedition = \"2024\"\n\n[workspace]\n",
        );
        scratch.write("outside/src/lib.rs", "");
        scratch
    }

    #[test]
    fn cargo_accepts_a_kernel_workspace_of_its_own_crates() {
        let scratch = repository("local");
        scratch.lock();
        assert_eq!(check_kernel_workspace(&scratch.0), Vec::<String>::new());
    }

    #[test]
    fn cargo_accepts_the_kernel_workspace_through_a_symbolic_link() {
        let scratch = repository("linked");
        scratch.lock();
        let links = Scratch::new("links");
        let link = links.0.join("repository");
        std::os::unix::fs::symlink(&scratch.0, &link).expect("create a symbolic link");
        assert_eq!(check_kernel_workspace(&link), Vec::<String>::new());
    }

    #[test]
    fn cargo_finds_a_path_dependency_outside_kernel() {
        let scratch = repository("path");
        let text = format!("{MEMBER}outside = {{ path = \"../../outside\" }}\n");
        scratch.write("kernel/a/Cargo.toml", &text);
        scratch.lock();
        let problems = check_kernel_workspace(&scratch.0);
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(
            problems[0].contains("package \"outside\" is not a member"),
            "{problems:?}"
        );
    }

    #[test]
    fn cargo_finds_a_member_outside_kernel() {
        let scratch = repository("member");
        scratch.write(
            "kernel/Cargo.toml",
            "[workspace]\nresolver = \"3\"\nmembers = [\"a\", \"b\", \"../outside\"]\n",
        );
        scratch.write(
            "outside/Cargo.toml",
            "[package]\nname = \"outside\"\nedition = \"2024\"\nworkspace = \"../kernel\"\n",
        );
        scratch.lock();
        let problems = check_kernel_workspace(&scratch.0);
        assert_eq!(problems.len(), 2, "{problems:?}");
        assert!(problems[0].contains("package \"outside\""), "{problems:?}");
    }

    #[test]
    fn cargo_finds_a_patch_from_outside_kernel() {
        let scratch = repository("patch");
        scratch.write(
            "kernel/Cargo.toml",
            "[workspace]\nresolver = \"3\"\nmembers = [\"a\", \"b\"]\n\n[patch.crates-io]\noutside = { path = \"../outside\" }\n",
        );
        scratch.write(
            "kernel/a/Cargo.toml",
            &format!("{MEMBER}outside = \"0.0.0\"\n"),
        );
        scratch.lock();
        let problems = check_kernel_workspace(&scratch.0);
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(
            problems[0].contains("package \"outside\" is not a member"),
            "{problems:?}"
        );
    }

    #[test]
    fn cargo_finds_a_crate_excluded_from_the_kernel_workspace() {
        let scratch = repository("excluded");
        scratch.write(
            "kernel/Cargo.toml",
            "[workspace]\nresolver = \"3\"\nmembers = [\"a\"]\nexclude = [\"b\"]\n",
        );
        scratch.lock();
        let problems = check_kernel_workspace(&scratch.0);
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(
            problems[0].contains("package \"b\" is not a member"),
            "{problems:?}"
        );
    }

    #[test]
    fn cargo_finds_a_kernel_manifest_that_joins_another_workspace() {
        let scratch = repository("redirect");
        scratch.write(
            "kernel/Cargo.toml",
            "[package]\nname = \"k\"\nedition = \"2024\"\nworkspace = \"../other\"\n",
        );
        scratch.write("kernel/src/lib.rs", "");
        scratch.write(
            "other/Cargo.toml",
            "[workspace]\nresolver = \"3\"\nmembers = [\"../kernel\"]\n",
        );
        scratch.lock();
        let problems = check_kernel_workspace(&scratch.0);
        assert!(problems[0].contains("the root"), "{problems:?}");
        // The root manifest is a package's, out of its shape.
        assert_eq!(
            problems[1..],
            [
                "kernel/Cargo.toml: the root package is named `k`, not `krepi-kernel`",
                "kernel/Cargo.toml: the root manifest may not have package.workspace",
                "kernel/Cargo.toml: the root manifest must set lints.rust.unsafe_code = \"forbid\"",
                "kernel/src/lib.rs: the library of the root package must have an unconditional #![no_std]"
            ]
        );
    }

    #[test]
    fn cargo_accepts_a_build_script_inside_kernel() {
        let scratch = repository("build");
        scratch.write("kernel/b/build.rs", "fn main() {}\n");
        scratch.lock();
        assert_eq!(check_kernel_workspace(&scratch.0), Vec::<String>::new());
    }

    #[test]
    fn cargo_finds_a_library_that_leaves_kernel_through_dot_dot() {
        let scratch = repository("dot-dot");
        let text = MEMBER.replace(
            "edition = \"2024\"\n",
            "edition = \"2024\"\n\n[lib]\npath = \"../../outside/src/lib.rs\"\n",
        );
        scratch.write("kernel/a/Cargo.toml", &text);
        scratch.lock();
        let problems = check_kernel_workspace(&scratch.0);
        assert_eq!(problems.len(), 1, "{problems:?}");
        // Cargo prints the path below kernel/a, so only the resolved path
        // shows that it leaves kernel/.
        assert!(
            problems[0].contains("kernel/a/../../outside/src/lib.rs"),
            "{problems:?}"
        );
    }

    #[test]
    fn cargo_fails_closed_on_a_registry_crate_it_cannot_resolve_offline() {
        let scratch = repository("registry");
        scratch.lock();
        let text = format!("{MEMBER}krepi-no-such-crate = \"1\"\n");
        scratch.write("kernel/a/Cargo.toml", &text);
        let problems = check_kernel_workspace(&scratch.0);
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(
            problems[0].contains("no matching package named `krepi-no-such-crate`"),
            "{problems:?}"
        );
    }

    #[test]
    fn cargo_fails_closed_on_a_stale_lock_file() {
        let scratch = repository("stale");
        scratch.lock();
        scratch.write(
            "kernel/b/Cargo.toml",
            "[package]\nname = \"b\"\nversion = \"0.1.0\"\nedition = \"2024\"\n",
        );
        let problems = check_kernel_workspace(&scratch.0);
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(
            problems[0].contains("cannot update the lock file"),
            "{problems:?}"
        );
    }
}
