//! The pinned proof tools: the manifest `verification/toolchain.json`, the
//! checks that tie it to the Aeneas and Charon sources that the image is
//! built from, and the environment in which the proof gate runs each tool.
//!
//! # Manifest
//!
//! The fields are documented on the formal verification page of the
//! repository (`docs/formal-verification.md`, section Tools). This module
//! reads the fields that its checks and the environment use and ignores the
//! others; the image recipe reads the download pins itself.
//!
//! # Checks
//!
//! [`check_sources`] compares the manifest with the files of an Aeneas and a
//! Charon source tree and with the Aeneas patch: Lean is the toolchain that
//! Aeneas names in `backends/lean/lean-toolchain`, Charon is the commit of
//! `charon-pin`, the Rust nightly is the channel of Charon's
//! `charon/rust-toolchain`, the patch has the pinned SHA-256, and the Lake
//! lock of the Aeneas Lean library has the pinned SHA-256 and pins the
//! pinned Mathlib commit. It also checks that the trees are at the pinned
//! commits, that the Lean toolchain and the Lean archive of each host are
//! those of the pinned Lean version, that the Rust targets include the
//! extraction triple of the [`Layout`], and that the manifest has the two
//! host columns with their locale, installation and switch export digest.
//! The image build runs these checks through
//! `cargo xtask formal toolchain-check` before its first expensive step.
//!
//! # Environment
//!
//! [`environment::environment`] gives the variables of a tool command;
//! every other variable of the caller is dropped.

use std::collections::BTreeMap;
use std::fs;
use std::os::unix::fs::MetadataExt;
use std::path::Path;
use std::process::ExitCode;

use serde::Deserialize;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};

use super::Layout;
use super::receipt::Image;

/// The schema version of the manifest that this module reads.
pub const SCHEMA: u32 = 1;

/// The host columns of the manifest: the CI host first, then the host of
/// local development.
pub const HOSTS: [&str; 2] = ["linux-aarch64", "darwin-arm64"];

/// The directory in which the image installs the tools, which the CI host's
/// column names as its installation.
pub const IMAGE_PREFIX: &str = "/opt/krepi-formal";

/// The fields of `verification/toolchain.json` that this module reads.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct Manifest {
    pub schema: u32,
    pub lean: Lean,
    pub aeneas: Aeneas,
    pub charon: Charon,
    pub rust: Rust,
    pub hosts: BTreeMap<String, Host>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct Lean {
    /// The toolchain as `lean-toolchain` files name it, such as
    /// `leanprover/lean4:v4.35.0`.
    pub toolchain: String,
    /// The version as `lean --version` prints it, such as `4.35.0`.
    pub version: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct Aeneas {
    pub commit: String,
    /// The reviewed patch, relative to the repository root.
    pub patch: String,
    pub patch_sha256: String,
    /// The SHA-256 of `backends/lean/lake-manifest.json` at the commit.
    pub lake_manifest_sha256: String,
    /// The Mathlib commit that the Lake lock pins.
    pub mathlib_commit: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct Charon {
    pub commit: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct Rust {
    /// The rustup toolchain name of the nightly, such as
    /// `nightly-2026-09-17`.
    pub toolchain: String,
    /// Targets whose standard library is installed beside the host's.
    pub targets: Vec<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct Host {
    /// The value of `LANG` and `LC_ALL` for the tools on this host.
    pub locale: String,
    /// The directory of the tool installation, laid out as the image lays
    /// out [`IMAGE_PREFIX`]: absolute, or relative to the repository root.
    pub prefix: String,
    /// The Lean release archive of this host.
    pub lean: Download,
    /// The SHA-256 of what `opam switch export --full` writes for the switch
    /// built on this host, or `None` until a build on the host has
    /// produced it.
    pub switch_export_sha256: Option<String>,
}

/// A download of one host.
#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
pub struct Download {
    pub url: String,
}

/// Parses the manifest and checks its schema version.
pub fn parse(text: &str) -> Result<Manifest, String> {
    let manifest: Manifest =
        serde_json::from_str(text).map_err(|error| format!("not a tool manifest: {error}"))?;
    if manifest.schema != SCHEMA {
        return Err(format!(
            "schema {} is not the schema {SCHEMA} that this xtask reads",
            manifest.schema
        ));
    }
    Ok(manifest)
}

/// The lowercase hexadecimal SHA-256 of `bytes`.
pub fn sha256(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

/// The files that the checks compare with the manifest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Sources {
    /// The commit checked out in the Aeneas tree.
    pub aeneas_commit: String,
    /// `backends/lean/lean-toolchain` of the Aeneas tree.
    pub lean_toolchain: String,
    /// `charon-pin` of the Aeneas tree.
    pub charon_pin: String,
    /// `backends/lean/lake-manifest.json` of the Aeneas tree.
    pub lake_manifest: Vec<u8>,
    /// The commit checked out in the Charon tree.
    pub charon_commit: String,
    /// `charon/rust-toolchain` of the Charon tree.
    pub rust_toolchain: String,
    /// The patch that the manifest names, from the repository.
    pub patch: Vec<u8>,
}

/// The outcome of one check: what agreed, or why it does not.
pub type Finding = Result<String, String>;

/// Runs every check and names each finding.
pub fn check_sources(
    manifest: &Manifest,
    layout: &Layout,
    sources: &Sources,
) -> Vec<(&'static str, Finding)> {
    vec![
        (
            "aeneas commit",
            same_commit(
                "the Aeneas tree",
                &sources.aeneas_commit,
                &manifest.aeneas.commit,
            ),
        ),
        (
            "charon commit",
            same_commit(
                "the Charon tree",
                &sources.charon_commit,
                &manifest.charon.commit,
            ),
        ),
        ("lean", check_lean(manifest, &sources.lean_toolchain)),
        ("lean pins", check_lean_pins(manifest)),
        (
            "charon pin",
            check_charon_pin(manifest, &sources.charon_pin),
        ),
        (
            "rust nightly",
            check_nightly(manifest, &sources.rust_toolchain),
        ),
        ("patch", check_patch(manifest, &sources.patch)),
        (
            "lake lock",
            check_lake_lock(manifest, &sources.lake_manifest),
        ),
        ("rust targets", check_targets(manifest, layout)),
        ("hosts", check_hosts(manifest)),
    ]
}

fn same_commit(tree: &str, found: &str, pinned: &str) -> Finding {
    if found == pinned {
        Ok(format!("{tree} is at {pinned}"))
    } else {
        Err(format!(
            "{tree} is at {found}, but the manifest pins {pinned}"
        ))
    }
}

/// Lean is the toolchain that Aeneas's `backends/lean/lean-toolchain`
/// names.
pub fn check_lean(manifest: &Manifest, lean_toolchain: &str) -> Finding {
    let named = lean_toolchain.trim();
    let pinned = &manifest.lean.toolchain;
    if named == pinned {
        Ok(format!("Aeneas's lean-toolchain names {pinned}"))
    } else {
        Err(format!(
            "Aeneas's backends/lean/lean-toolchain names `{named}`, but the manifest pins Lean {pinned}"
        ))
    }
}

/// The Lean pins name one release: the toolchain is that of the pinned
/// version, and the archive of each host is an archive of that release, so
/// that the Lean that the image installs is the Lean that Aeneas names.
pub fn check_lean_pins(manifest: &Manifest) -> Finding {
    let version = &manifest.lean.version;
    let mut problems = Vec::new();
    let toolchain = format!("leanprover/lean4:v{version}");
    if manifest.lean.toolchain != toolchain {
        problems.push(format!(
            "the manifest pins the Lean toolchain {}, but the toolchain of the pinned Lean version {version} is {toolchain}",
            manifest.lean.toolchain
        ));
    }
    let release = format!("/v{version}/lean-{version}-");
    for (name, host) in &manifest.hosts {
        if !host.lean.url.contains(&release) {
            problems.push(format!(
                "the {name} column's Lean archive {} is not one of the release v{version}",
                host.lean.url
            ));
        }
    }
    if problems.is_empty() {
        Ok(format!(
            "the Lean toolchain and the archive of every host are those of Lean {version}"
        ))
    } else {
        Err(problems.join("; "))
    }
}

/// The commit that a `charon-pin` file names: its one line that is neither
/// empty nor a `#` comment.
pub fn pinned_charon(charon_pin: &str) -> Result<String, String> {
    let lines: Vec<&str> = charon_pin
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .collect();
    match lines.as_slice() {
        [commit] => Ok(commit.to_string()),
        _ => Err(format!(
            "Aeneas's charon-pin has {} lines that are not comments; it must have one",
            lines.len()
        )),
    }
}

/// Charon is the commit of Aeneas's `charon-pin`.
pub fn check_charon_pin(manifest: &Manifest, charon_pin: &str) -> Finding {
    let named = pinned_charon(charon_pin)?;
    let pinned = &manifest.charon.commit;
    if &named == pinned {
        Ok(format!("Aeneas's charon-pin names {pinned}"))
    } else {
        Err(format!(
            "Aeneas's charon-pin names {named}, but the manifest pins Charon {pinned}"
        ))
    }
}

/// The channel of a rustup `rust-toolchain` file in TOML form.
pub fn toolchain_channel(rust_toolchain: &str) -> Result<String, String> {
    let table: toml::Table = rust_toolchain
        .parse()
        .map_err(|error| format!("Charon's charon/rust-toolchain is not TOML: {error}"))?;
    table
        .get("toolchain")
        .and_then(|toolchain| toolchain.get("channel"))
        .and_then(toml::Value::as_str)
        .map(str::to_string)
        .ok_or_else(|| "Charon's charon/rust-toolchain has no toolchain.channel".to_string())
}

/// The Rust nightly is the channel of Charon's `charon/rust-toolchain`.
pub fn check_nightly(manifest: &Manifest, rust_toolchain: &str) -> Finding {
    let named = toolchain_channel(rust_toolchain)?;
    let pinned = &manifest.rust.toolchain;
    if &named == pinned {
        Ok(format!("Charon's rust-toolchain names {pinned}"))
    } else {
        Err(format!(
            "Charon's charon/rust-toolchain names {named}, but the manifest pins Rust {pinned}"
        ))
    }
}

/// The patch has the pinned SHA-256.
pub fn check_patch(manifest: &Manifest, patch: &[u8]) -> Finding {
    let found = sha256(patch);
    let pinned = &manifest.aeneas.patch_sha256;
    if &found == pinned {
        Ok(format!("{} has SHA-256 {pinned}", manifest.aeneas.patch))
    } else {
        Err(format!(
            "{} has SHA-256 {found}, but the manifest pins {pinned}",
            manifest.aeneas.patch
        ))
    }
}

/// The revision that a Lake manifest pins for the package `name`.
pub fn locked_revision(lake_manifest: &[u8], name: &str) -> Result<String, String> {
    let value: serde_json::Value = serde_json::from_slice(lake_manifest)
        .map_err(|error| format!("Aeneas's Lake lock is not JSON: {error}"))?;
    let packages = value
        .get("packages")
        .and_then(serde_json::Value::as_array)
        .ok_or("Aeneas's Lake lock has no `packages` list")?;
    let revisions: Vec<&str> = packages
        .iter()
        .filter(|package| package.get("name").and_then(serde_json::Value::as_str) == Some(name))
        .map(|package| {
            package
                .get("rev")
                .and_then(serde_json::Value::as_str)
                .unwrap_or_default()
        })
        .collect();
    match revisions.as_slice() {
        [revision] if !revision.is_empty() => Ok(revision.to_string()),
        [_] => Err(format!("Aeneas's Lake lock has no revision for `{name}`")),
        _ => Err(format!(
            "Aeneas's Lake lock has {} packages named `{name}`; it must have one",
            revisions.len()
        )),
    }
}

/// The Lake lock of the Aeneas Lean library has the pinned SHA-256 and pins
/// the pinned Mathlib commit. Both are reported when both differ.
pub fn check_lake_lock(manifest: &Manifest, lake_manifest: &[u8]) -> Finding {
    let mut problems = Vec::new();
    let found = sha256(lake_manifest);
    let pinned = &manifest.aeneas.lake_manifest_sha256;
    if &found != pinned {
        problems.push(format!(
            "Aeneas's backends/lean/lake-manifest.json has SHA-256 {found}, but the manifest pins {pinned}"
        ));
    }
    let mathlib = &manifest.aeneas.mathlib_commit;
    match locked_revision(lake_manifest, "mathlib") {
        Ok(locked) if &locked == mathlib => {}
        Ok(locked) => problems.push(format!(
            "Aeneas's Lake lock pins Mathlib {locked}, but the manifest pins {mathlib}"
        )),
        Err(problem) => problems.push(problem),
    }
    if problems.is_empty() {
        Ok(format!(
            "Aeneas's Lake lock has SHA-256 {pinned} and pins Mathlib {mathlib}"
        ))
    } else {
        Err(problems.join("; "))
    }
}

/// The Rust targets include the extraction triple of `layout`.
pub fn check_targets(manifest: &Manifest, layout: &Layout) -> Finding {
    if manifest
        .rust
        .targets
        .iter()
        .any(|target| target == layout.triple)
    {
        Ok(format!(
            "the manifest installs the standard library for {}",
            layout.triple
        ))
    } else {
        Err(format!(
            "the manifest's Rust targets {:?} lack the extraction triple {}",
            manifest.rust.targets, layout.triple
        ))
    }
}

/// Whether `text` is `length` lowercase hexadecimal digits: 64 for a
/// SHA-256, 40 for the name of a Git object.
pub fn is_hex(text: &str, length: usize) -> bool {
    let digit = |byte: u8| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte);
    text.len() == length && text.bytes().all(digit)
}

/// Whether `prefix` names a directory without `.` or `..` components or
/// empty ones, absolute or relative.
fn is_plain_path(prefix: &str) -> bool {
    let rest = prefix.strip_prefix('/').unwrap_or(prefix);
    !rest.is_empty()
        && rest
            .split('/')
            .all(|part| !part.is_empty() && part != "." && part != "..")
}

/// The manifest has exactly the columns of [`HOSTS`]. Each sets a UTF-8
/// locale and an installation prefix without `.` or `..` components, the CI
/// host's being the image's [`IMAGE_PREFIX`], and a switch export digest
/// that, when set, is a SHA-256.
pub fn check_hosts(manifest: &Manifest) -> Finding {
    let mut expected: Vec<&str> = HOSTS.to_vec();
    expected.sort_unstable();
    let found: Vec<&str> = manifest.hosts.keys().map(String::as_str).collect();
    if found != expected {
        return Err(format!(
            "the manifest has the host columns {found:?}; it must have {expected:?}"
        ));
    }
    let mut problems = Vec::new();
    let mut unpinned = Vec::new();
    for (name, host) in &manifest.hosts {
        if !host.locale.ends_with(".UTF-8") {
            problems.push(format!(
                "the {name} column sets the locale `{}`, which is not a UTF-8 locale",
                host.locale
            ));
        }
        if !is_plain_path(&host.prefix) {
            problems.push(format!(
                "the {name} column's prefix `{}` is not a directory path without `.` and `..`",
                host.prefix
            ));
        } else if name == HOSTS[0] && host.prefix != IMAGE_PREFIX {
            problems.push(format!(
                "the {name} column's prefix is {}, but the image installs the tools in {IMAGE_PREFIX}",
                host.prefix
            ));
        }
        match &host.switch_export_sha256 {
            Some(digest) if !is_hex(digest, 64) => problems.push(format!(
                "the {name} column's switch_export_sha256 `{digest}` is not a SHA-256 in lowercase hexadecimal"
            )),
            Some(_) => {}
            None => unpinned.push(name.as_str()),
        }
    }
    if !problems.is_empty() {
        return Err(problems.join("; "));
    }
    let mut detail = format!("the manifest has the host columns {found:?}");
    if !unpinned.is_empty() {
        detail.push_str(&format!(
            "; the switch export of {unpinned:?} is not pinned yet"
        ));
    }
    Ok(detail)
}

/// The patch path that the manifest names, checked to lie in the tooling
/// directory of `layout`.
pub fn patch_path<'a>(manifest: &'a Manifest, layout: &Layout) -> Result<&'a str, String> {
    let path = manifest.aeneas.patch.as_str();
    let inside = path
        .strip_prefix(layout.tooling)
        .and_then(|rest| rest.strip_prefix('/'))
        .is_some_and(|rest| {
            !rest.is_empty() && rest.split('/').all(|part| part != ".." && !part.is_empty())
        });
    if inside {
        Ok(path)
    } else {
        Err(format!(
            "the patch `{path}` is not a file below {}",
            layout.tooling
        ))
    }
}

/// The commit checked out in the Git tree at `dir`.
fn head(dir: &Path) -> Result<String, String> {
    let output = std::process::Command::new("git")
        .arg("-C")
        .arg(dir)
        .args(["rev-parse", "HEAD"])
        .output()
        .map_err(|error| format!("cannot run git in {}: {error}", dir.display()))?;
    if !output.status.success() {
        return Err(format!(
            "git rev-parse HEAD failed in {}: {}",
            dir.display(),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

/// The content of `path`, or empty after recording why it cannot be read.
fn read(path: &Path, problems: &mut Vec<String>) -> Vec<u8> {
    fs::read(path).unwrap_or_else(|error| {
        problems.push(format!("cannot read {}: {error}", path.display()));
        Vec::new()
    })
}

/// The text of `path`, or empty after recording why it cannot be read.
fn read_text(path: &Path, problems: &mut Vec<String>) -> String {
    String::from_utf8_lossy(&read(path, problems)).into_owned()
}

impl Sources {
    /// Reads the sources from the Aeneas tree `aeneas`, the Charon tree
    /// `charon` and the repository at `root` laid out as `layout`, or
    /// reports every file that cannot be read.
    pub fn read(
        root: &Path,
        layout: &Layout,
        manifest: &Manifest,
        aeneas: &Path,
        charon: &Path,
    ) -> Result<Sources, Vec<String>> {
        let mut problems = Vec::new();
        let lean_toolchain = read_text(&aeneas.join("backends/lean/lean-toolchain"), &mut problems);
        let charon_pin = read_text(&aeneas.join("charon-pin"), &mut problems);
        let lake_manifest = read(
            &aeneas.join("backends/lean/lake-manifest.json"),
            &mut problems,
        );
        let rust_toolchain = read_text(&charon.join("charon/rust-toolchain"), &mut problems);
        let patch = match patch_path(manifest, layout) {
            Ok(path) => read(&root.join(path), &mut problems),
            Err(problem) => {
                problems.push(problem);
                Vec::new()
            }
        };
        let mut commit = |dir: &Path| {
            head(dir).unwrap_or_else(|problem| {
                problems.push(problem);
                String::new()
            })
        };
        let aeneas_commit = commit(aeneas);
        let charon_commit = commit(charon);
        if problems.is_empty() {
            Ok(Sources {
                aeneas_commit,
                lean_toolchain,
                charon_pin,
                lake_manifest,
                charon_commit,
                rust_toolchain,
                patch,
            })
        } else {
            Err(problems)
        }
    }
}

/// Entry point of `cargo xtask formal toolchain-check`.
pub fn command(root: &Path, layout: &Layout, aeneas: &Path, charon: &Path) -> ExitCode {
    println!(
        "toolchain-check: {} against Aeneas {} and Charon {}",
        layout.toolchain,
        aeneas.display(),
        charon.display()
    );
    let manifest = match fs::read_to_string(root.join(layout.toolchain))
        .map_err(|error| format!("cannot read {}: {error}", layout.toolchain))
        .and_then(|text| parse(&text).map_err(|error| format!("{}: {error}", layout.toolchain)))
    {
        Ok(manifest) => manifest,
        Err(problem) => {
            eprintln!("{problem}");
            return ExitCode::FAILURE;
        }
    };
    let sources = match Sources::read(root, layout, &manifest, aeneas, charon) {
        Ok(sources) => sources,
        Err(problems) => {
            for problem in problems {
                eprintln!("{problem}");
            }
            return ExitCode::FAILURE;
        }
    };
    let findings = check_sources(&manifest, layout, &sources);
    let mut failed = 0;
    for (name, finding) in &findings {
        match finding {
            Ok(detail) => println!("ok    {name}: {detail}"),
            Err(problem) => {
                failed += 1;
                println!("FAIL  {name}: {problem}");
            }
        }
    }
    if failed == 0 {
        println!("toolchain-check passed: {} checks", findings.len());
        ExitCode::SUCCESS
    } else {
        eprintln!(
            "toolchain-check failed: {failed} of {} checks",
            findings.len()
        );
        ExitCode::FAILURE
    }
}

/// The repository and the reference `<repository>@<digest>` of the image
/// pin, which has schema 1, a plain repository, a digest and a commit.
pub fn image_pin(text: &str) -> Option<(String, String)> {
    let pin: Value = serde_json::from_str(text).ok()?;
    let field = |key: &str| pin[key].as_str().unwrap_or_default();
    let (repository, digest) = (field("repository"), field("digest"));
    let sha256 = is_hex(digest.strip_prefix("sha256:").unwrap_or_default(), 64);
    let plain = pin["schema"] == 1 && !repository.is_empty() && !repository.contains([':', '@']);
    let reference = format!("{repository}@{digest}");
    (plain && sha256 && is_hex(field("revision"), 40)).then(|| (repository.into(), reference))
}

const IMAGE_ITEMS: &str = "/opam/switch_export_sha256=/hosts/linux-aarch64/switch_export_sha256 \
    /aeneas/lake_manifest_sha256 /rust/rustup_init_sha256=/hosts/linux-aarch64/rustup_init/sha256 \
    /lean/sha256=/hosts/linux-aarch64/lean/sha256 /opam/sha256=/hosts/linux-aarch64/opam/sha256 \
    /rust/rustc_commit /opam/repository_commit /charon/version=/d/charon /aeneas/version=/d/aeneas \
    /aeneas/patch_sha256 /aeneas/mathlib_commit /rust/manifest_sha256 /opam/ocaml=/d/ocaml \
    /lean/version /aeneas/commit /charon/commit /rust/toolchain /rust/rustup_commit /opam/version \
    /lean/commit /rust/rustup /gmp/version /gmp/sha256 /schema=/d/schema";

/// Completes the record of the image of a run on the CI host and finds why
/// the run stops: the installation at `prefix` has no version manifest, or
/// one that differs from the tool `manifest` in [`IMAGE_ITEMS`] (image `=`
/// tool item; `/d` derived or fixed), the Rust targets or the components; the
/// job's reference is not the pin at `pin`; or the gate's user is root, owns the
/// prefix or has the group or other write bit, whatever its groups.
pub fn image(image: &mut Image, prefix: &Path, manifest: &str, pin: &Path) -> Vec<String> {
    let versions = fs::read_to_string(prefix.join("versions.json"));
    let parse = |text: &str| serde_json::from_str(text).unwrap_or(Value::Null);
    let [found, mut tools] = [versions.as_deref().unwrap_or_default(), manifest].map(parse);
    let get = |pointer| tools.pointer(pointer).and_then(Value::as_str);
    let both = |one, other| get(one).zip(get(other));
    tools["d"] = json!({"ocaml": get("/opam/compiler").and_then(|c| c.split_once('.')).map(|v| v.1),
        "charon": both("/charon/version", "/charon/commit").map(|(v, c)| format!("{v} ({c})")),
        "schema": 1, "aeneas": both("/aeneas/commit", "/aeneas/patch_sha256")
            .map(|(commit, patch)| format!("aeneas {commit:.7}+patch-{patch:.8}"))});
    let at = |pointer| found.pointer(pointer).unwrap_or(&Value::Null);
    let mut problems = Vec::new();
    for item in IMAGE_ITEMS.split_whitespace() {
        let (ours, theirs) = item.split_once('=').unwrap_or((item, item));
        let pinned = tools.pointer(theirs).unwrap_or(&Value::Null);
        if pinned.is_null() || at(ours) != pinned {
            problems.push(format!("{ours} is {}, not {pinned}", at(ours)));
        }
    }
    for pointer in ["/rust/targets", "/rust/components"] {
        let installed = at(pointer).to_string();
        let installed = installed.replace("-aarch64-unknown-linux-gnu\"", "\"");
        let names = tools.pointer(pointer).and_then(Value::as_array);
        for name in names.into_iter().flatten() {
            if !installed.contains(&name.to_string()) {
                problems.push(format!("{pointer} lacks {name}"));
            }
        }
    }
    if let Err(error) = &versions {
        problems = vec![format!("cannot read versions.json: {error}")];
    }
    let pinned = fs::read_to_string(pin).map(|text| image_pin(&text));
    if image.reference.is_some() && image.reference != pinned.ok().flatten().map(|pin| pin.1) {
        problems.push("the snapshot pins no image or another than the job's".into());
    }
    let open = |meta: fs::Metadata| meta.uid() == image.uid || meta.mode() & 0o022 != 0;
    image.writable = Some(image.uid == 0 || fs::metadata(prefix).map_or(true, open));
    if image.writable == Some(true) {
        problems.push(format!("user {} can write {}", image.uid, prefix.display()));
    }
    image.versions_sha256 = versions.as_ref().ok().map(|text| sha256(text.as_bytes()));
    image.versions = versions.ok();
    problems
}

/// The problems of the image references in the pull request workflows
/// `files`: one names the image `pin`, and so does each mention of its repository.
pub fn image_references(pin: &str, files: &[(&str, &str)]) -> Vec<String> {
    let Some((repository, reference)) = image_pin(pin) else {
        return vec!["the image pin lacks schema 1, a repository, a digest or a commit".into()];
    };
    let named = files.iter().any(|file| file.1.contains(&reference));
    let mut problems = Vec::from_iter((!named).then(|| format!("no workflow names {reference}")));
    for (path, text) in files {
        for (at, _) in text.to_ascii_lowercase().match_indices(&repository) {
            let rest = text[at..].strip_prefix(&reference);
            if rest.is_none_or(|rest| rest.starts_with(char::is_alphanumeric)) {
                let line = text[..at].matches('\n').count() + 1;
                problems.push(format!("{path}:{line}: not {reference}"));
            }
        }
    }
    problems
}

/// The environment of the tool commands.
pub mod environment {
    use std::collections::BTreeMap;
    use std::path::{Path, PathBuf};
    use std::process::Command;

    use super::{Host, Manifest};

    /// The directories at the end of every tool's `PATH`.
    pub const SYSTEM_PATH: &str = "/usr/bin:/bin:/usr/sbin:/sbin";

    /// The tool installation of a host, laid out as the image lays out
    /// [`IMAGE_PREFIX`](super::IMAGE_PREFIX).
    pub struct Installation {
        pub prefix: PathBuf,
    }

    impl Installation {
        /// The installation that the column `host` names: its prefix,
        /// resolved against the repository root `root` when relative.
        fn of(host: &Host, root: &Path) -> Installation {
            Installation {
                prefix: root.join(&host.prefix),
            }
        }

        /// The Lean toolchain's `bin`: `lean`, `lake` and `leanchecker`.
        pub fn lean_bin(&self) -> PathBuf {
            self.prefix.join("lean/bin")
        }

        /// The directory of `aeneas`, `charon` and `charon-driver`.
        fn tools_bin(&self) -> PathBuf {
            self.prefix.join("bin")
        }

        /// The Cargo home, whose `bin` holds the rustup proxies.
        fn cargo_home(&self) -> PathBuf {
            self.prefix.join("cargo")
        }

        /// The rustup home with the pinned nightly.
        fn rustup_home(&self) -> PathBuf {
            self.prefix.join("rustup")
        }

        /// The Aeneas Lean library, built, with the packages of its Lake
        /// lock in `.lake/packages`.
        pub fn backend(&self) -> PathBuf {
            self.prefix.join("backend")
        }
    }

    /// The installation that the manifest's column of `host` names, a
    /// relative prefix taken from the repository root `root`.
    pub fn installation(
        manifest: &Manifest,
        host: &str,
        root: &Path,
    ) -> Result<Installation, String> {
        let missing = || format!("the manifest has no {host} column");
        let column = manifest.hosts.get(host).ok_or_else(missing)?;
        Ok(Installation::of(column, root))
    }

    /// The directories of one gate run that tool commands use.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct RunDirs {
        /// A new, empty home directory.
        pub home: PathBuf,
        /// The temporary directory.
        pub tmp: PathBuf,
    }

    /// A command that the proof gate runs. The two extraction commands
    /// carry the Cargo target directory of their extraction alone.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum Tool<'a> {
        /// Charon extracting a crate through Cargo.
        Charon { target_dir: &'a Path },
        /// Aeneas translating what Charon extracted.
        Aeneas { target_dir: &'a Path },
        /// `lake build`.
        LakeBuild,
        /// `lake env lean` on one file.
        LakeEnvLean,
        /// `leanchecker`.
        Leanchecker,
        /// Git, as the gate calls it.
        Git,
        /// `cargo metadata`, as the gate calls it on the kernel workspace.
        CargoMetadata,
    }

    /// The variables of a tool command, by name.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct Environment(BTreeMap<&'static str, String>);

    impl Environment {
        #[cfg(test)]
        pub fn vars(&self) -> &BTreeMap<&'static str, String> {
            &self.0
        }

        /// The environment of exactly `vars`, for the tests of the code
        /// that runs commands.
        #[cfg(test)]
        pub fn of(vars: &[(&'static str, &str)]) -> Environment {
            Environment(
                vars.iter()
                    .map(|(name, value)| (*name, value.to_string()))
                    .collect(),
            )
        }

        /// Makes `command` run with exactly these variables: those of the
        /// caller, and any set on `command` before, are dropped.
        pub fn apply(&self, command: &mut Command) {
            command.env_clear().envs(&self.0);
        }
    }

    /// `path` as text, or why it is not UTF-8.
    pub fn text(path: &Path) -> Result<String, String> {
        path.to_str()
            .map(str::to_string)
            .ok_or_else(|| format!("the path {} is not UTF-8", path.display()))
    }

    /// The environment of `tool` on `host`, with the installation that the
    /// manifest's column of `host` names, a relative prefix taken from the
    /// repository root `root`, and the directories of `run`. Every tool gets
    /// Lake's artifact cache turned off, offline Cargo with the
    /// installation's Cargo and rustup homes and the pinned nightly, the
    /// host's locale, Git without system or global configuration and with
    /// every repository safe, so that Lake can run Git in the packages of an
    /// installation that another user owns, a `PATH` of the Lean toolchain,
    /// the tool directory, the rustup proxies and the system directories,
    /// and the run's home and temporary directories.
    /// The two extraction commands, Charon and Aeneas, also get incremental
    /// compilation turned off and the target directory of their extraction;
    /// Aeneas runs no Cargo and ignores both.
    pub fn environment(
        tool: Tool,
        manifest: &Manifest,
        host: &str,
        root: &Path,
        run: &RunDirs,
    ) -> Result<Environment, String> {
        let column = manifest
            .hosts
            .get(host)
            .ok_or_else(|| format!("the manifest has no {host} column"))?;
        let install = Installation::of(column, root);
        let path = [
            install.lean_bin(),
            install.tools_bin(),
            install.cargo_home().join("bin"),
        ]
        .iter()
        .map(|directory| text(directory))
        .chain([Ok(SYSTEM_PATH.to_string())])
        .collect::<Result<Vec<_>, _>>()?
        .join(":");
        let mut vars = BTreeMap::from([
            ("LAKE_ARTIFACT_CACHE", "false".to_string()),
            ("CARGO_NET_OFFLINE", "true".to_string()),
            ("CARGO_HOME", text(&install.cargo_home())?),
            ("RUSTUP_TOOLCHAIN", manifest.rust.toolchain.clone()),
            ("LANG", column.locale.clone()),
            ("LC_ALL", column.locale.clone()),
            ("GIT_CONFIG_NOSYSTEM", "1".to_string()),
            ("GIT_CONFIG_GLOBAL", "/dev/null".to_string()),
            ("GIT_CONFIG_COUNT", "1".to_string()),
            ("GIT_CONFIG_KEY_0", "safe.directory".to_string()),
            ("GIT_CONFIG_VALUE_0", "*".to_string()),
            ("PATH", path),
            ("RUSTUP_HOME", text(&install.rustup_home())?),
            ("HOME", text(&run.home)?),
            ("TMPDIR", text(&run.tmp)?),
        ]);
        if let Tool::Charon { target_dir } | Tool::Aeneas { target_dir } = tool {
            vars.insert("CARGO_INCREMENTAL", "0".to_string());
            vars.insert("CARGO_TARGET_DIR", text(target_dir)?);
        }
        Ok(Environment(vars))
    }
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use super::environment::{RunDirs, Tool, environment};
    use super::*;

    const COMMITTED: &str = include_str!("../../../verification/toolchain.json");
    const COMMITTED_PATCH: &[u8] =
        include_bytes!("../../../verification/tooling/aeneas-option-unwrap-mut-and-prefix.patch");

    /// A manifest with only the fields this module reads. Its digests were
    /// computed with `shasum -a 256` over [`PATCH`] and [`LOCK`]; the
    /// darwin-arm64 switch export digest is that of the committed manifest.
    const FIXTURE: &str = r#"{
  "schema": 1,
  "lean": { "toolchain": "leanprover/lean4:v4.35.0", "version": "4.35.0" },
  "aeneas": {
    "commit": "4acbb6d73abe9082e45cf49ba6d6229a2c7d5836",
    "patch": "verification/tooling/fixture.patch",
    "patch_sha256": "d8c386fcd53359eac69cd1ef60c99909d04c6a3e497bf616a8e79c1efc897484",
    "lake_manifest_sha256": "1d86d1dae78e721ca12ef3fef60c07f779b18b82f16b4f22ece0d9b9a0948cea",
    "mathlib_commit": "56a005855ea17e0b0958f73ec801ae140b0a1679"
  },
  "charon": { "commit": "6cc2b5f80b7edc2383cba3dab1f1e3b4059aebe2" },
  "rust": { "toolchain": "nightly-2026-09-17", "targets": ["aarch64-unknown-none"] },
  "hosts": {
    "darwin-arm64": {
      "locale": "en_US.UTF-8",
      "prefix": "artifacts/formal/tools",
      "lean": { "url": "https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-darwin_aarch64.tar.zst" },
      "switch_export_sha256": "6b3b9196c1cf5ff357ddc09d1a830198ff023db676f23934120c2026883bc821"
    },
    "linux-aarch64": {
      "locale": "C.UTF-8",
      "prefix": "/opt/krepi-formal",
      "lean": { "url": "https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux_aarch64.tar.zst" },
      "switch_export_sha256": null
    }
  }
}"#;

    const PATCH: &[u8] = b"patch fixture\n";

    /// A Lake lock of the shape that Lake writes, cut to two packages.
    const LOCK: &str = r#"{"version": "1.3.0",
 "packages":
 [{"name": "mathlib", "type": "git", "rev": "56a005855ea17e0b0958f73ec801ae140b0a1679"},
  {"name": "batteries", "type": "git", "rev": "66e469188fe07963e5cf666c7d4433f45b8131c5"}],
 "name": "aeneas"}
"#;

    /// [`LOCK`] with another Mathlib commit; SHA-256
    /// 92386fb40ac9a8aa2fe580b428cae973c2d9702f8eb00f4a37fb69151b5e066b.
    const OTHER_LOCK: &str = r#"{"version": "1.3.0",
 "packages":
 [{"name": "mathlib", "type": "git", "rev": "0000000000000000000000000000000000000001"},
  {"name": "batteries", "type": "git", "rev": "66e469188fe07963e5cf666c7d4433f45b8131c5"}],
 "name": "aeneas"}
"#;

    /// The files of the pinned trees as their commits hold them, with
    /// [`PATCH`] and [`LOCK`] for the patch and the Lake lock.
    fn sources() -> Sources {
        Sources {
            aeneas_commit: "4acbb6d73abe9082e45cf49ba6d6229a2c7d5836".to_string(),
            lean_toolchain: "leanprover/lean4:v4.35.0\n".to_string(),
            charon_pin: "# This is the commit from https://github.com/AeneasVerif/charon that should be used with this version of aeneas.\n6cc2b5f80b7edc2383cba3dab1f1e3b4059aebe2\n".to_string(),
            lake_manifest: LOCK.as_bytes().to_vec(),
            charon_commit: "6cc2b5f80b7edc2383cba3dab1f1e3b4059aebe2".to_string(),
            rust_toolchain: "[toolchain]\nchannel = \"nightly-2026-09-17\"\ncomponents = [ \"rustc-dev\", \"llvm-tools\", \"rust-src\", \"miri\" ]\ntargets = [\n    \"aarch64-apple-darwin\",\n    \"aarch64-unknown-linux-gnu\",\n]\n".to_string(),
            patch: PATCH.to_vec(),
        }
    }

    fn fixture() -> Manifest {
        parse(FIXTURE).expect("the fixture parses")
    }

    /// The names of the checks that fail.
    fn failing(manifest: &Manifest, sources: &Sources) -> Vec<&'static str> {
        check_sources(manifest, &Layout::PRODUCTION, sources)
            .into_iter()
            .filter(|(_, finding)| finding.is_err())
            .map(|(name, _)| name)
            .collect()
    }

    /// The one failing check and its problem.
    fn only_problem(manifest: &Manifest, sources: &Sources) -> (&'static str, String) {
        let findings = check_sources(manifest, &Layout::PRODUCTION, sources);
        let problems: Vec<_> = findings
            .into_iter()
            .filter_map(|(name, finding)| finding.err().map(|problem| (name, problem)))
            .collect();
        assert_eq!(problems.len(), 1, "{problems:?}");
        problems.into_iter().next().unwrap()
    }

    #[test]
    fn agreeing_sources_pass_every_check() {
        let findings = check_sources(&fixture(), &Layout::PRODUCTION, &sources());
        assert_eq!(findings.len(), 10);
        for (name, finding) in findings {
            assert!(finding.is_ok(), "{name}: {finding:?}");
        }
    }

    /// The fixture moved to another Lean release as a whole: toolchain,
    /// version and the archive of each host.
    fn on_lean(version: &str) -> Manifest {
        let mut manifest = fixture();
        manifest.lean.toolchain = format!("leanprover/lean4:v{version}");
        manifest.lean.version = version.to_string();
        for host in manifest.hosts.values_mut() {
            host.lean.url = host.lean.url.replace("4.35.0", version);
        }
        manifest
    }

    #[test]
    fn a_lean_pin_that_aeneas_does_not_name_fails() {
        let manifest = on_lean("4.34.0");
        let (name, problem) = only_problem(&manifest, &sources());
        assert_eq!(name, "lean");
        assert!(problem.contains("leanprover/lean4:v4.35.0"), "{problem}");
        assert!(problem.contains("v4.34.0"), "{problem}");
    }

    #[test]
    fn a_lean_toolchain_of_another_version_fails() {
        // Only the toolchain moves: Aeneas names it, but the image would
        // still install the pinned 4.35.0 archives.
        let mut manifest = fixture();
        manifest.lean.toolchain = "leanprover/lean4:v4.36.0".to_string();
        let mut tree = sources();
        tree.lean_toolchain = "leanprover/lean4:v4.36.0\n".to_string();
        let (name, problem) = only_problem(&manifest, &tree);
        assert_eq!(name, "lean pins");
        assert!(problem.contains("leanprover/lean4:v4.35.0"), "{problem}");
        // Only the version moves.
        let mut manifest = fixture();
        manifest.lean.version = "4.36.0".to_string();
        let (name, problem) = only_problem(&manifest, &sources());
        assert_eq!(name, "lean pins");
        assert!(problem.contains("linux-aarch64"), "{problem}");
        assert!(problem.contains("darwin-arm64"), "{problem}");
    }

    #[test]
    fn a_lean_archive_of_another_release_fails() {
        let mut manifest = fixture();
        let host = manifest.hosts.get_mut("darwin-arm64").unwrap();
        host.lean.url = host.lean.url.replace("4.35.0", "4.34.0");
        let (name, problem) = only_problem(&manifest, &sources());
        assert_eq!(name, "lean pins");
        assert!(problem.contains("darwin-arm64"), "{problem}");
        assert!(!problem.contains("linux-aarch64"), "{problem}");
    }

    #[test]
    fn a_charon_pin_that_aeneas_does_not_name_fails() {
        let mut manifest = fixture();
        let other = "798016509139eb51f0d764645f76d068d34ba5f6";
        manifest.charon.commit = other.to_string();
        let mut tree = sources();
        tree.charon_commit = other.to_string();
        let (name, problem) = only_problem(&manifest, &tree);
        assert_eq!(name, "charon pin");
        assert!(problem.contains(other), "{problem}");
    }

    #[test]
    fn a_nightly_that_charon_does_not_name_fails() {
        let mut manifest = fixture();
        manifest.rust.toolchain = "nightly-2026-09-18".to_string();
        let (name, problem) = only_problem(&manifest, &sources());
        assert_eq!(name, "rust nightly");
        assert!(problem.contains("nightly-2026-09-17"), "{problem}");
    }

    #[test]
    fn a_patch_digest_that_differs_fails() {
        let mut manifest = fixture();
        manifest.aeneas.patch_sha256 =
            "e12c89822e366d99c37850218d9d0d6155bcf88ebb3e1db2f8d70ddb793bde3e".to_string();
        let (name, problem) = only_problem(&manifest, &sources());
        assert_eq!(name, "patch");
        assert!(
            problem.contains("d8c386fcd53359eac69cd1ef60c99909d04c6a3e497bf616a8e79c1efc897484"),
            "{problem}"
        );
        let mut tree = sources();
        tree.patch = b"patch fixture, edited\n".to_vec();
        assert_eq!(only_problem(&fixture(), &tree).0, "patch");
    }

    #[test]
    fn a_mathlib_commit_that_the_lake_lock_does_not_pin_fails() {
        let mut manifest = fixture();
        manifest.aeneas.mathlib_commit = "0000000000000000000000000000000000000001".to_string();
        let (name, problem) = only_problem(&manifest, &sources());
        assert_eq!(name, "lake lock");
        assert!(problem.contains("pins Mathlib 56a00585"), "{problem}");
        assert!(!problem.contains("SHA-256"), "{problem}");
    }

    #[test]
    fn a_lake_lock_with_another_mathlib_reports_its_digest_and_its_mathlib() {
        let mut tree = sources();
        tree.lake_manifest = OTHER_LOCK.as_bytes().to_vec();
        let (name, problem) = only_problem(&fixture(), &tree);
        assert_eq!(name, "lake lock");
        assert!(
            problem.contains("92386fb40ac9a8aa2fe580b428cae973c2d9702f8eb00f4a37fb69151b5e066b"),
            "{problem}"
        );
        assert!(
            problem.contains("pins Mathlib 0000000000000000000000000000000000000001"),
            "{problem}"
        );
    }

    #[test]
    fn trees_at_other_commits_fail() {
        let mut tree = sources();
        tree.aeneas_commit = "d119a474f852781f8ae88a85424f2f8ba8407b82".to_string();
        assert_eq!(failing(&fixture(), &tree), ["aeneas commit"]);
        let mut tree = sources();
        tree.charon_commit = "798016509139eb51f0d764645f76d068d34ba5f6".to_string();
        assert_eq!(failing(&fixture(), &tree), ["charon commit"]);
    }

    #[test]
    fn rust_targets_without_the_extraction_triple_fail() {
        let mut manifest = fixture();
        manifest.rust.targets = vec!["riscv64gc-unknown-none-elf".to_string()];
        assert_eq!(failing(&manifest, &sources()), ["rust targets"]);
    }

    #[test]
    fn a_missing_or_extra_host_column_fails() {
        let mut manifest = fixture();
        manifest.hosts.remove("darwin-arm64");
        assert_eq!(failing(&manifest, &sources()), ["hosts"]);
        let mut manifest = fixture();
        let column = manifest.hosts["linux-aarch64"].clone();
        manifest.hosts.insert("linux-x86_64".to_string(), column);
        assert_eq!(failing(&manifest, &sources()), ["hosts"]);
        let mut manifest = fixture();
        manifest.hosts.get_mut("linux-aarch64").unwrap().locale = "C".to_string();
        assert_eq!(failing(&manifest, &sources()), ["hosts"]);
    }

    #[test]
    fn a_switch_export_digest_that_is_not_a_sha256_fails() {
        for digest in [
            "TODO-linux-opam-switch-export-sha256",
            "6B3B9196C1CF5FF357DDC09D1A830198FF023DB676F23934120C2026883BC821",
            "6b3b9196c1cf5ff357ddc09d1a830198ff023db676f23934120c2026883bc82",
        ] {
            let mut manifest = fixture();
            manifest
                .hosts
                .get_mut("linux-aarch64")
                .unwrap()
                .switch_export_sha256 = Some(digest.to_string());
            let (name, problem) = only_problem(&manifest, &sources());
            assert_eq!(name, "hosts");
            assert!(problem.contains(digest), "{problem}");
        }
        let findings = check_hosts(&fixture());
        assert!(
            findings
                .as_ref()
                .is_ok_and(|detail| detail.contains("not pinned yet")),
            "{findings:?}"
        );
    }

    #[test]
    fn a_prefix_other_than_the_image_installation_fails() {
        let mut manifest = fixture();
        manifest.hosts.get_mut("linux-aarch64").unwrap().prefix = "/opt/other".to_string();
        let (name, problem) = only_problem(&manifest, &sources());
        assert_eq!(name, "hosts");
        assert!(problem.contains(IMAGE_PREFIX), "{problem}");
        for prefix in ["", "../tools", "artifacts/./tools", "artifacts//tools", "/"] {
            let mut manifest = fixture();
            manifest.hosts.get_mut("darwin-arm64").unwrap().prefix = prefix.to_string();
            assert_eq!(failing(&manifest, &sources()), ["hosts"], "{prefix:?}");
        }
    }

    #[test]
    fn reads_the_one_commit_of_a_charon_pin() {
        assert_eq!(pinned_charon("# comment\n\n abc \n").as_deref(), Ok("abc"));
        assert!(pinned_charon("# only a comment\n").is_err());
        assert!(pinned_charon("abc\ndef\n").is_err());
    }

    #[test]
    fn rejects_a_rust_toolchain_without_a_channel() {
        assert!(toolchain_channel("[toolchain]\nprofile = \"minimal\"\n").is_err());
        assert!(toolchain_channel("nightly-2026-09-17\n").is_err());
    }

    #[test]
    fn rejects_a_lake_lock_without_one_mathlib() {
        let without = r#"{"packages": [{"name": "batteries", "rev": "66e4"}]}"#;
        assert!(locked_revision(without.as_bytes(), "mathlib").is_err());
        let twice =
            r#"{"packages": [{"name": "mathlib", "rev": "a"}, {"name": "mathlib", "rev": "b"}]}"#;
        assert!(locked_revision(twice.as_bytes(), "mathlib").is_err());
        assert!(locked_revision(b"not json", "mathlib").is_err());
    }

    #[test]
    fn rejects_a_patch_outside_the_tooling_directory() {
        for path in [
            "verification/patch.patch",
            "verification/tooling/../../x.patch",
            "/verification/tooling/x.patch",
            "verification/tooling/",
            "verification/tooling-other/x.patch",
        ] {
            let mut manifest = fixture();
            manifest.aeneas.patch = path.to_string();
            assert!(
                patch_path(&manifest, &Layout::PRODUCTION).is_err(),
                "{path}"
            );
        }
        assert_eq!(
            patch_path(&fixture(), &Layout::PRODUCTION),
            Ok("verification/tooling/fixture.patch")
        );
    }

    #[test]
    fn rejects_another_schema_version() {
        let text = FIXTURE.replace("\"schema\": 1", "\"schema\": 2");
        assert!(parse(&text).unwrap_err().contains("schema 2"));
    }

    #[test]
    fn the_committed_manifest_parses_and_pins_the_committed_patch() {
        let manifest = parse(COMMITTED).expect("the committed manifest parses");
        for finding in [
            check_lean_pins(&manifest),
            check_hosts(&manifest),
            check_targets(&manifest, &Layout::PRODUCTION),
        ] {
            assert!(finding.is_ok(), "{finding:?}");
        }
        assert_eq!(
            patch_path(&manifest, &Layout::PRODUCTION),
            Ok("verification/tooling/aeneas-option-unwrap-mut-and-prefix.patch")
        );
        let finding = check_patch(&manifest, COMMITTED_PATCH);
        assert!(finding.is_ok(), "{finding:?}");
    }

    /// The repository root that the environment tests resolve a relative
    /// prefix against.
    const ROOT: &str = "/work/repo";

    fn run_dirs() -> RunDirs {
        RunDirs {
            home: PathBuf::from("/work/run/home"),
            tmp: PathBuf::from("/work/run/tmp"),
        }
    }

    /// Every tool's variables on linux-aarch64 in the image.
    const EVERY_TOOL: [(&str, &str); 15] = [
        ("CARGO_HOME", "/opt/krepi-formal/cargo"),
        ("CARGO_NET_OFFLINE", "true"),
        ("GIT_CONFIG_COUNT", "1"),
        ("GIT_CONFIG_GLOBAL", "/dev/null"),
        ("GIT_CONFIG_KEY_0", "safe.directory"),
        ("GIT_CONFIG_NOSYSTEM", "1"),
        ("GIT_CONFIG_VALUE_0", "*"),
        ("HOME", "/work/run/home"),
        ("LAKE_ARTIFACT_CACHE", "false"),
        ("LANG", "C.UTF-8"),
        ("LC_ALL", "C.UTF-8"),
        (
            "PATH",
            "/opt/krepi-formal/lean/bin:/opt/krepi-formal/bin:/opt/krepi-formal/cargo/bin:/usr/bin:/bin:/usr/sbin:/sbin",
        ),
        ("RUSTUP_HOME", "/opt/krepi-formal/rustup"),
        ("RUSTUP_TOOLCHAIN", "nightly-2026-09-17"),
        ("TMPDIR", "/work/run/tmp"),
    ];

    /// The variables that the two extraction commands add.
    const EXTRACTION: [(&str, &str); 2] = [
        ("CARGO_INCREMENTAL", "0"),
        ("CARGO_TARGET_DIR", "/work/run/cases/arithmetic/target"),
    ];

    fn expected(extra: &[(&str, &str)]) -> BTreeMap<String, String> {
        EVERY_TOOL
            .iter()
            .chain(extra)
            .map(|(name, value)| (name.to_string(), value.to_string()))
            .collect()
    }

    fn owned(vars: &BTreeMap<&'static str, String>) -> BTreeMap<String, String> {
        vars.iter()
            .map(|(name, value)| (name.to_string(), value.clone()))
            .collect()
    }

    /// A tool, its command and the variables it gets beyond those of every
    /// tool.
    type Row<'a> = (&'a str, Tool<'a>, &'a [(&'a str, &'a str)]);

    #[test]
    fn every_tool_gets_exactly_its_variables() {
        let target = Path::new("/work/run/cases/arithmetic/target");
        let table: [Row; 7] = [
            ("charon", Tool::Charon { target_dir: target }, &EXTRACTION),
            ("aeneas", Tool::Aeneas { target_dir: target }, &EXTRACTION),
            ("lake build", Tool::LakeBuild, &[]),
            ("lake env lean", Tool::LakeEnvLean, &[]),
            ("leanchecker", Tool::Leanchecker, &[]),
            ("git", Tool::Git, &[]),
            ("cargo metadata", Tool::CargoMetadata, &[]),
        ];
        let manifest = parse(COMMITTED).expect("the committed manifest parses");
        for (name, tool, extra) in table {
            let env = environment(
                tool,
                &manifest,
                "linux-aarch64",
                Path::new(ROOT),
                &run_dirs(),
            )
            .expect("the environment is built");
            assert_eq!(owned(env.vars()), expected(extra), "{name}");
        }
    }

    #[test]
    fn the_locale_and_the_installation_follow_the_host_column() {
        let manifest = parse(COMMITTED).expect("the committed manifest parses");
        let env = environment(
            Tool::Git,
            &manifest,
            "darwin-arm64",
            Path::new(ROOT),
            &run_dirs(),
        )
        .expect("the environment is built");
        let vars = env.vars();
        assert_eq!(vars["LANG"], "en_US.UTF-8");
        assert_eq!(vars["LC_ALL"], "en_US.UTF-8");
        assert_eq!(vars["GIT_CONFIG_COUNT"], "1");
        assert_eq!(vars["GIT_CONFIG_KEY_0"], "safe.directory");
        assert_eq!(vars["GIT_CONFIG_VALUE_0"], "*");
        assert_eq!(
            vars["CARGO_HOME"],
            "/work/repo/artifacts/formal/tools/cargo"
        );
        assert_eq!(
            vars["RUSTUP_HOME"],
            "/work/repo/artifacts/formal/tools/rustup"
        );
        assert_eq!(
            vars["PATH"],
            "/work/repo/artifacts/formal/tools/lean/bin:/work/repo/artifacts/formal/tools/bin:/work/repo/artifacts/formal/tools/cargo/bin:/usr/bin:/bin:/usr/sbin:/sbin"
        );
        assert!(
            environment(
                Tool::Git,
                &manifest,
                "linux-x86_64",
                Path::new(ROOT),
                &run_dirs()
            )
            .is_err()
        );
    }

    #[test]
    fn variables_of_the_caller_do_not_reach_the_tool() {
        let manifest = parse(COMMITTED).expect("the committed manifest parses");
        let target = Path::new("/work/run/cases/arithmetic/target");
        let env = environment(
            Tool::Aeneas { target_dir: target },
            &manifest,
            "linux-aarch64",
            Path::new(ROOT),
            &run_dirs(),
        )
        .expect("the environment is built");
        let mut command = std::process::Command::new("/usr/bin/env");
        command
            .env("RUSTFLAGS", "-C target-cpu=native")
            .env("GITHUB_TOKEN", "ghs_not_a_token")
            .env("GIT_CONFIG_COUNT", "2")
            .env("GIT_CONFIG_KEY_1", "core.fsmonitor")
            .env("GIT_CONFIG_VALUE_1", "/bin/true")
            .env("GIT_CONFIG_PARAMETERS", "'core.hookspath'='/tmp'");
        env.apply(&mut command);
        let output = command.output().expect("/usr/bin/env runs");
        assert!(output.status.success());
        let seen: BTreeMap<String, String> = String::from_utf8(output.stdout)
            .expect("UTF-8 output")
            .lines()
            .map(|line| {
                let (name, value) = line.split_once('=').expect("NAME=value");
                (name.to_string(), value.to_string())
            })
            .collect();
        assert_eq!(seen, expected(&EXTRACTION));
        assert!(!seen.contains_key("RUSTFLAGS"));
        assert!(!seen.contains_key("GITHUB_TOKEN"));
        assert_eq!(seen["GIT_CONFIG_COUNT"], "1");
        assert!(!seen.contains_key("GIT_CONFIG_KEY_1"));
        assert!(!seen.contains_key("GIT_CONFIG_PARAMETERS"));
    }

    /// The script with which the image workflows check the image as a user
    /// other than root.
    const IMAGE_CHECK: &str = include_str!("../../../verification/image/non-root-check.sh");

    /// The workflow of the gate's CI jobs, whose measurement job runs
    /// `leanchecker` in the stage of a run.
    const FORMAL_WORKFLOW: &str = include_str!("../../../.github/workflows/formal.yml");

    #[test]
    fn the_image_check_runs_tools_with_the_tool_environment() {
        assert_lists_the_tool_environment(IMAGE_CHECK, Tool::LakeEnvLean);
    }

    #[test]
    fn the_measurement_job_runs_leanchecker_with_the_tool_environment() {
        assert_lists_the_tool_environment(FORMAL_WORKFLOW, Tool::Leanchecker);
    }

    /// Asserts that the lines of `text` between its only line `tool_env=(`
    /// and the next line `)`, each `NAME=value` with white space around it
    /// and quotes in it, list the variables of `tool` on `linux-aarch64`,
    /// with values of their own for `HOME` and `TMPDIR`.
    fn assert_lists_the_tool_environment(text: &str, tool: Tool) {
        let starts = text.lines().filter(|line| line.trim() == "tool_env=(");
        assert_eq!(starts.count(), 1, "the text sets tool_env once");
        let mut lines = text.lines().map(str::trim);
        lines.find(|line| *line == "tool_env=(");
        let mut script: BTreeMap<String, String> = BTreeMap::new();
        let mut ended = false;
        for line in lines {
            if line == ")" {
                ended = true;
                break;
            }
            let entry = line.replace(['\'', '"'], "");
            let (name, value) = entry.split_once('=').expect("NAME=value");
            let earlier = script.insert(name.to_string(), value.to_string());
            assert_eq!(earlier, None, "{name} is listed twice");
        }
        assert!(ended, "tool_env ends");
        let manifest = parse(COMMITTED).expect("the committed manifest parses");
        let env = environment(
            tool,
            &manifest,
            "linux-aarch64",
            Path::new(ROOT),
            &run_dirs(),
        )
        .expect("the environment is built");
        let mut gate = owned(env.vars());
        assert_eq!(
            script.keys().collect::<Vec<_>>(),
            gate.keys().collect::<Vec<_>>()
        );
        // The text gives the tools a home and a temporary directory of its
        // own.
        for name in ["HOME", "TMPDIR"] {
            script.remove(name);
            gate.remove(name);
        }
        assert_eq!(script, gate);
    }

    /// The committed image pin.
    const PIN: &str = include_str!("../../../verification/image-pin.json");

    /// The reference of the committed pin, the image that main published.
    const PINNED: &str = "ghcr.io/casxi-lab/krepi-formal@sha256:cd3bd69b780538593e4cfe247c45145d82a0c351048bcc21882062537300f013";

    /// The version manifest of the pinned image.
    const VERSIONS: &str = include_str!("fixtures/image/versions.json");

    #[test]
    fn the_committed_image_pin_names_the_published_image() {
        let (repository, reference) = image_pin(PIN).expect("the committed pin reads");
        assert_eq!(repository, "ghcr.io/casxi-lab/krepi-formal");
        assert_eq!(reference, PINNED);
    }

    #[test]
    fn an_image_pin_without_its_schema_repository_digest_or_commit_is_rejected() {
        let digest = "sha256:cd3bd69b780538593e4cfe247c45145d82a0c351048bcc21882062537300f013";
        for (from, to) in [
            ("\"schema\": 1", "\"schema\": 2"),
            ("\"schema\": 1,", ""),
            ("krepi-formal\"", "krepi-formal:latest\""),
            ("krepi-formal\"", "krepi-formal@sha256:0\""),
            ("ghcr.io/casxi-lab/krepi-formal", ""),
            (digest, &digest[7..]),
            (digest, &digest[..70]),
            (digest, &digest.replace("cd3b", "CD3B")),
            ("08316d310722d8277604a38e2608d4c9497866fe", "08316d3"),
            ("\"revision\"", "\"commit\""),
        ] {
            let text = PIN.replace(from, to);
            assert_ne!(text, PIN, "{from}");
            assert_eq!(image_pin(&text), None, "{text}");
        }
        assert_eq!(image_pin("not JSON"), None);
    }

    /// What [`image`] finds for the version manifest `versions`, if any,
    /// and the tool manifest `manifest`, as a user that cannot write the
    /// installation and without a reference.
    fn image_problems(versions: Option<&str>, manifest: &str) -> (Image, Vec<String>) {
        let scratch = crate::scratch::Scratch::temporary("image");
        if let Some(versions) = versions {
            scratch.write("versions.json", versions);
        }
        let mode = std::os::unix::fs::PermissionsExt::from_mode(0o755);
        fs::set_permissions(&scratch.0, mode).expect("set the mode");
        let mut found = Image {
            uid: super::super::process::effective_uid() + 1,
            ..Image::default()
        };
        let problems = image(&mut found, &scratch.0, manifest, &scratch.0.join("pin"));
        (found, problems)
    }

    #[test]
    fn the_published_version_manifest_agrees_with_the_committed_manifest() {
        let digest = "8b5e39cb407d4d8f5cf7fd29d0485e43a439276ea6e3808a60e24f4c196a24e6";
        assert_eq!(sha256(VERSIONS.as_bytes()), digest);
        let (found, problems) = image_problems(Some(VERSIONS), COMMITTED);
        assert_eq!(problems, Vec::<String>::new());
        assert_eq!(found.versions.as_deref(), Some(VERSIONS));
        assert_eq!(found.versions_sha256.as_deref(), Some(digest));
        assert_eq!(found.writable, Some(false));
    }

    /// The 25 compared items and the schema: the pointer into the image's
    /// version manifest, and those into the tool manifest that give it, none
    /// for the schema, which is 1.
    const COMPARED: [(&str, &[&str]); 26] = [
        ("/schema", &[]),
        ("/lean/version", &["/lean/version"]),
        ("/lean/commit", &["/lean/commit"]),
        ("/lean/sha256", &["/hosts/linux-aarch64/lean/sha256"]),
        ("/aeneas/commit", &["/aeneas/commit"]),
        ("/aeneas/patch_sha256", &["/aeneas/patch_sha256"]),
        (
            "/aeneas/lake_manifest_sha256",
            &["/aeneas/lake_manifest_sha256"],
        ),
        ("/aeneas/mathlib_commit", &["/aeneas/mathlib_commit"]),
        ("/charon/commit", &["/charon/commit"]),
        ("/rust/toolchain", &["/rust/toolchain"]),
        ("/rust/rustc_commit", &["/rust/rustc_commit"]),
        ("/rust/manifest_sha256", &["/rust/manifest_sha256"]),
        ("/rust/rustup", &["/rust/rustup"]),
        ("/rust/rustup_commit", &["/rust/rustup_commit"]),
        (
            "/rust/rustup_init_sha256",
            &["/hosts/linux-aarch64/rustup_init/sha256"],
        ),
        ("/opam/version", &["/opam/version"]),
        ("/opam/repository_commit", &["/opam/repository_commit"]),
        ("/opam/sha256", &["/hosts/linux-aarch64/opam/sha256"]),
        (
            "/opam/switch_export_sha256",
            &["/hosts/linux-aarch64/switch_export_sha256"],
        ),
        ("/gmp/version", &["/gmp/version"]),
        ("/gmp/sha256", &["/gmp/sha256"]),
        ("/opam/ocaml", &["/opam/compiler"]),
        ("/charon/version", &["/charon/version", "/charon/commit"]),
        (
            "/aeneas/version",
            &["/aeneas/commit", "/aeneas/patch_sha256"],
        ),
        ("/rust/targets", &["/rust/targets"]),
        ("/rust/components", &["/rust/components"]),
    ];

    /// `text` with the item at `pointer` changed by `change`, or removed.
    fn edited(text: &str, pointer: &str, change: Option<fn(Value) -> Value>) -> String {
        let mut value: Value = serde_json::from_str(text).expect("JSON");
        match change {
            Some(change) => {
                let item = value.pointer_mut(pointer).expect("the item");
                *item = change(item.take());
            }
            None => {
                let (parent, key) = pointer.rsplit_once('/').expect("a pointer");
                let parent = value.pointer_mut(parent).and_then(Value::as_object_mut);
                parent.expect("the parent").remove(key).expect("the item");
            }
        }
        serde_json::to_string_pretty(&value).expect("JSON")
    }

    /// Another value of the kind of `value`: a string with another first
    /// and last character, another number, or a list without its items, or,
    /// on the side of the tool manifest, with one more.
    fn other(value: Value, image: bool) -> Value {
        match value {
            Value::String(text) => format!("x{text}x").into(),
            Value::Number(_) => 2.into(),
            Value::Array(_) if image => json!([]),
            Value::Array(mut names) => {
                names.push("x-extra".into());
                names.into()
            }
            other => panic!("unexpected {other}"),
        }
    }

    #[test]
    fn each_compared_version_that_differs_fails() {
        let mut items: Vec<&str> = (IMAGE_ITEMS.split_whitespace())
            .map(|item| item.split('=').next().expect("an image item"))
            .chain(["/rust/targets", "/rust/components"])
            .collect();
        let mut compared: Vec<&str> = COMPARED.iter().map(|(ours, _)| *ours).collect();
        items.sort_unstable();
        compared.sort_unstable();
        assert_eq!(compared, items);
        let names = |ours: &str, problems: &[String]| {
            !problems.is_empty()
                && problems
                    .iter()
                    .all(|problem| problem.starts_with(&format!("{ours} ")))
        };
        let lists = ["/rust/targets", "/rust/components"];
        for (ours, theirs) in COMPARED {
            // A value of the image that differs, and a missing one, which
            // is one problem but for a list, where each missing name is.
            let changed: fn(Value) -> Value = |value| other(value, true);
            for change in [Some(changed), None] {
                let versions = edited(VERSIONS, ours, change);
                let (_, problems) = image_problems(Some(&versions), COMMITTED);
                assert!(
                    names(ours, &problems),
                    "{ours} {}: {problems:?}",
                    change.is_some()
                );
                if !lists.contains(&ours) {
                    assert_eq!(problems.len(), 1, "{ours}: {problems:?}");
                }
            }
            // A value of the tool manifest that differs, and a missing one,
            // but for a list, which pins nothing when it is missing.
            for pointer in theirs {
                let changed: fn(Value) -> Value = |value| other(value, false);
                for change in [Some(changed), None]
                    .into_iter()
                    .filter(|change| change.is_some() || !lists.contains(&ours))
                {
                    let manifest = edited(COMMITTED, pointer, change);
                    let (_, problems) = image_problems(Some(VERSIONS), &manifest);
                    let named = problems
                        .iter()
                        .any(|problem| problem.starts_with(&format!("{ours} ")));
                    assert!(named, "{ours} {pointer}: {problems:?}");
                }
            }
        }
        // The image's file has schema 1, whatever that of the tool manifest.
        let changed: fn(Value) -> Value = |value| other(value, false);
        let manifest = edited(COMMITTED, "/schema", Some(changed));
        let (_, problems) = image_problems(Some(VERSIONS), &manifest);
        assert_eq!(problems, Vec::<String>::new());
        // Not JSON: each of the 24 items and each pinned target and component.
        let (found, problems) = image_problems(Some("not JSON"), COMMITTED);
        assert_eq!(problems.len(), 24 + 1 + 3, "{problems:?}");
        assert_eq!(found.versions.as_deref(), Some("not JSON"));
        let (found, problems) = image_problems(None, COMMITTED);
        assert_eq!(problems.len(), 1, "{problems:?}");
        assert!(
            problems[0].starts_with("cannot read versions.json: "),
            "{problems:?}"
        );
        assert_eq!((found.versions, found.versions_sha256), (None, None));
    }

    #[test]
    fn a_component_counts_bare_or_for_the_host() {
        for (from, to) in [
            ("\"rust-src\"", "\"rust-src-aarch64-unknown-linux-gnu\""),
            ("\"llvm-tools-aarch64-unknown-linux-gnu\"", "\"llvm-tools\""),
        ] {
            let versions = VERSIONS.replace(from, to);
            assert_ne!(versions, VERSIONS);
            let (_, problems) = image_problems(Some(&versions), COMMITTED);
            assert_eq!(problems, Vec::<String>::new());
        }
        let versions = VERSIONS.replace(
            "rustc-dev-aarch64-unknown-linux-gnu",
            "rustc-dev-x86_64-unknown-linux-gnu",
        );
        let (_, problems) = image_problems(Some(&versions), COMMITTED);
        assert_eq!(problems, ["/rust/components lacks \"rustc-dev\""]);
    }

    #[test]
    fn a_workflow_image_reference_other_than_the_pinned_digest_fails() {
        let job = format!("on: pull_request\nenv:\n  IMAGE: {PINNED}\n");
        let check = |text: &str| image_references(PIN, &[("a.yml", &job), ("b.yml", text)]);
        // The pinned reference passes, wherever it is mentioned.
        assert_eq!(
            check(&format!("# pulls {PINNED}\nrun: docker pull {PINNED}\n")),
            Vec::<String>::new()
        );
        let (repository, digest) = PINNED.split_once('@').expect("a digest");
        for (line, other) in [
            (
                format!("{repository}@sha256:{}", "0".repeat(64)),
                "another digest",
            ),
            (format!("{repository}:latest"), "a tag"),
            (
                format!("{repository}:latest@{digest}"),
                "a tag and the digest",
            ),
            (format!("{repository}\n"), "the bare repository"),
            (format!("# pulled from {repository}"), "a comment"),
            (format!("{}:main", repository.to_uppercase()), "upper case"),
            (format!("{PINNED}0"), "a longer digest"),
        ] {
            let text = format!("on: pull_request\njobs:\n  {line}\n");
            assert_eq!(check(&text), [format!("b.yml:3: not {PINNED}")], "{other}");
        }
        // Two mentions on separate lines are reported each with its line.
        let text = format!("{repository}:a\n\n{repository}:b {PINNED}\n");
        assert_eq!(
            check(&text),
            [
                format!("b.yml:1: not {PINNED}"),
                format!("b.yml:3: not {PINNED}")
            ]
        );
        // One workflow must name the pinned image.
        assert_eq!(
            image_references(PIN, &[("b.yml", "on: push\n")]),
            [format!("no workflow names {PINNED}")]
        );
        let other = format!("{repository}@sha256:{}", "0".repeat(64));
        assert_eq!(
            image_references(PIN, &[("b.yml", &other)]),
            [
                format!("no workflow names {PINNED}"),
                format!("b.yml:1: not {PINNED}")
            ]
        );
        let pin = PIN.replace("\"schema\": 1", "\"schema\": 2");
        assert_eq!(image_references(&pin, &[("a.yml", &job)]).len(), 1);
    }
}
