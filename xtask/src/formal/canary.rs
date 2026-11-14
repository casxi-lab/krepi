//! `cargo xtask formal canary STEP`: the steps of the toolchain canary,
//! `.github/workflows/formal-canary.yml`, as "Toolchain canary" in
//! `docs/formal-verification.md` describes them. The job runs the gate once
//! a week with the tools of Aeneas main. It fetches the trees and the
//! downloads; this module derives the tool manifest from the committed one
//! and those files, checks that the patch applies, fills the build fact of
//! the image and the statement hash, and concludes the run. It fetches
//! nothing itself.
//!
//! Each step writes `artifacts/canary/<step>.json`, a [`Record`] with its
//! [`Finding`], and exits with 0 only when it passed. `verdict` gives the
//! run the finding of the first step of the job that did not pass: a
//! breakage of the tools, a defect of the canary or a failure of the run.

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;
use std::process::{Command as Process, ExitCode};

use clap::builder::PossibleValuesParser;
use clap::{Arg, ArgMatches};
use serde::{Deserialize, Serialize};
use serde_json::{Value, json};

use super::guard::{self, Standalone};
use super::outcome::{self, Status};
use super::receipt::Receipt;
use super::toolchain::{self, HOSTS, Sources};
use super::{Layout, run};
use crate::Command;

/// The directory of the canary's own files, below the repository root: the
/// trees of Aeneas main and of its Charon, the downloads, the exit statuses
/// of the build and of the gate, and the record of each step.
pub const DIR: &str = "artifacts/canary";

/// The directory of the files of the steps copied from the image build: the
/// checkouts that the image is built from, `build.log` and `versions.json`.
pub const IMAGE: &str = "artifacts/image";

/// The fields of the tool manifest that follow Aeneas main: its commit and
/// Lake lock, the Lean release that it names with the archives of that
/// release, and the Charon that it pins with that Charon's nightly.
pub const RESOLVED: &str = "/aeneas/commit /aeneas/lake_manifest_sha256 /aeneas/mathlib_commit \
    /lean/toolchain /lean/version /lean/commit /charon/commit /charon/version /rust/toolchain \
    /rust/manifest_url /rust/manifest_sha256 /rust/rustc_commit \
    /hosts/linux-aarch64/lean/url /hosts/linux-aarch64/lean/sha256 \
    /hosts/darwin-arm64/lean/url /hosts/darwin-arm64/lean/sha256";

/// The field that the image build gives: `null` for the build, as for the
/// first build of a changed switch, and the built switch for the gate.
pub const BUILT: &str = "/hosts/linux-aarch64/switch_export_sha256";

/// The ids of the steps of the job, in their order.
pub const STEPS: &str = "runner disk sampler xtask resolve derive fetch toolchain-check patch build \
    record fill probe gate";

/// The steps whose record this module writes.
pub const RECORDED: &str = "resolve derive patch fill";

/// Texts of a failed build or gate that make it a defect of the canary: the
/// recipe's checks of what it installs against the manifest, and the gate's
/// checks of the image and of the statement hash.
const DEFECTS: &str = "lean reports |the channel manifest names rustc |rustup reports |\
    opam reports |the Lake lock pins Mathlib |the switch export has SHA-256 |\
    the manifest's linux-aarch64 prefix is |, not at the pinned commit |\
    computed checksum did NOT match|image: |the statement side of the snapshot is ";

/// Texts that make it a failure of the run: the disk, the network, a
/// cancelled build, and the gate's checks of its inputs, which the canary's
/// commits keep.
const FAILURES: &str = "No space left on device|no space left on device|context canceled|\
    Could not resolve host|Temporary failure in name resolution|Connection timed out|\
    not clean at the start of the run|is not the file that the run read at its start|\
    gate inputs changed during the run";

/// The stages of the recipe whose failure the tools cause: the patch and
/// the Lake lock, Lean, the nightly, Charon, Aeneas and its Lean library.
const TOOL_STAGES: &str = "aeneas-source lean rust-toolchain charon-build aeneas-build backend";

/// The finding of a step, and of the run.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "SCREAMING_SNAKE_CASE")]
pub enum Finding {
    /// The step did what it checks.
    Passed,
    /// A breakage: a tool of Aeneas main, or a form of its pins that the
    /// committed checks refuse too, fails the patch, the recipe or the gate.
    Broken,
    /// A defect of the canary: what it derived disagrees with a tool or a
    /// check, or it cannot read a form of the trees or the downloads.
    Defect,
    /// The run did not complete: a limit, the disk, the network or the runner.
    Failed,
}

/// What a step found: its verdict, why, and what it resolved.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Record {
    pub verdict: Finding,
    pub detail: String,
    pub data: Value,
}

/// A record of `verdict` and `detail`, without data.
fn found(verdict: Finding, detail: impl Into<String>) -> Record {
    let detail = detail.into();
    Record {
        verdict,
        detail,
        data: Value::Null,
    }
}

/// The entry of `cargo xtask formal canary` among the commands of `formal`.
pub const COMMAND: Command = Command {
    name: "canary",
    about: "Run STEP of the weekly toolchain canary on what its job fetched and built: resolve, derive, patch, fill, or verdict, which with --outcomes TEXT concludes the run",
    subcommands: &[],
};

/// The command line of `cargo xtask formal canary`, with `about`.
pub fn cli(about: &'static str) -> clap::Command {
    let steps = PossibleValuesParser::new(["resolve", "derive", "patch", "fill", "verdict"]);
    let step = Arg::new("step").value_name("STEP").required(true);
    let outcomes = Arg::new("outcomes").long("outcomes").value_name("TEXT");
    let outcomes = outcomes.help("The outcome of each step of the job, as <id>=<outcome> words");
    let command = clap::Command::new("canary").about(about);
    command.arg(step.value_parser(steps)).arg(outcomes)
}

/// Entry point of `cargo xtask formal canary` in the repository `root`: it
/// runs the step, writes and prints its record, and exits with 0 only when
/// the record is written and passed. The verdict names the commit of main
/// that `GITHUB_SHA` gives.
pub fn command(root: &Path, layout: &Layout, matches: &ArgMatches) -> ExitCode {
    let text = |name| matches.get_one::<String>(name).map_or("", String::as_str);
    let step = text("step");
    let record = match step {
        "resolve" => resolve(root, layout),
        "derive" => derive(root, layout),
        "patch" => Ok(patch(root, layout)),
        "fill" => fill(root, layout),
        _ => {
            let main = std::env::var("GITHUB_SHA").unwrap_or_else(|_| "unknown".to_string());
            Ok(verdict(root, &outcomes(text("outcomes")), &main))
        }
    };
    let record = record.unwrap_or_else(|record| record);
    let (dir, path) = (root.join(DIR), root.join(DIR).join(format!("{step}.json")));
    let written = fs::create_dir_all(&dir).map_err(|error| io(&dir, error));
    let written = written.and_then(|()| write(&path, &json!(record)));
    let verdict = outcome::word(&record.verdict);
    println!("canary {step}: {verdict}: {}", record.detail);
    if let Err(error) = &written {
        eprintln!("cannot write the record: {}", error.detail);
    }
    if written.is_ok() && record.verdict == Finding::Passed {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}

/// The outcomes of the steps of the job, given as `<id>=<outcome>` words;
/// an empty outcome counts as none.
pub fn outcomes(text: &str) -> BTreeMap<String, String> {
    let pairs = (text.split_whitespace()).filter_map(|word| word.split_once('='));
    let pairs = pairs.filter(|(_, outcome)| !outcome.is_empty());
    let pairs = pairs.map(|(id, outcome)| (id.to_string(), outcome.to_string()));
    pairs.collect()
}

/// A failure of the run, for a file that cannot be read or written.
fn io(path: &Path, error: impl ToString) -> Record {
    let detail = format!("{}: {}", path.display(), error.to_string());
    found(Finding::Failed, detail)
}

/// The JSON file at `path`.
fn json(path: &Path) -> Result<Value, Record> {
    let text = fs::read_to_string(path).map_err(|error| io(path, error))?;
    serde_json::from_str(&text).map_err(|error| io(path, error))
}

/// Writes `value` to `path` as JSON, in the pretty form of `serde_json`.
fn write(path: &Path, value: &Value) -> Result<(), Record> {
    let text = serde_json::to_string_pretty(value).map_err(|error| io(path, error))?;
    fs::write(path, text + "\n").map_err(|error| io(path, error))
}

/// `text` with its one occurrence of `old` replaced by `new`; a defect when
/// it holds none or more, since each committed pin holds one.
fn swap(text: &str, old: &str, new: &str) -> Result<String, Record> {
    match text.matches(old).count() {
        1 => Ok(text.replacen(old, new, 1)),
        n => {
            let why = format!("the committed `{text}` holds `{old}` {n} times");
            Err(found(Finding::Defect, why))
        }
    }
}

/// Whether `date` is a date in the form `YYYY-MM-DD`.
fn is_date(date: &str) -> bool {
    let digit = |(at, byte): (usize, u8)| match at {
        4 | 7 => byte == b'-',
        _ => byte.is_ascii_digit(),
    };
    date.len() == 10 && date.bytes().enumerate().all(digit)
}

/// The fields of [`RESOLVED`] that the trees of Aeneas main and of its
/// Charon in [`DIR`] give, with the URLs of the downloads. A form that the
/// committed checks refuse too, such as a Lean toolchain that is not a
/// release, is a breakage; a tree that the canary fetched wrongly, or a
/// form that it cannot read, is a defect of it.
fn trees(root: &Path, layout: &Layout) -> Result<BTreeMap<&'static str, String>, Record> {
    let path = root.join(layout.toolchain);
    let committed = json(&path)?;
    let manifest = toolchain::parse(&committed.to_string()).map_err(|error| io(&path, error))?;
    let pinned = |pointer: &str| {
        let value = committed.pointer(pointer).and_then(Value::as_str);
        value.unwrap_or_default().to_string()
    };
    let [aeneas, charon] = ["aeneas", "charon"].map(|tree| root.join(DIR).join(tree));
    let broken = |why: String| found(Finding::Broken, why);
    // The job fetches Charon only for a charon-pin of one line that is not
    // a comment.
    if let Ok(pin) = fs::read_to_string(aeneas.join("charon-pin")) {
        toolchain::pinned_charon(&pin).map_err(broken)?;
    }
    let sources = Sources::read(root, layout, &manifest, &aeneas, &charon);
    let sources = sources.map_err(|problems| found(Finding::Failed, problems.join("; ")))?;
    let lean = sources.lean_toolchain.trim();
    let release = lean.strip_prefix("leanprover/lean4:v");
    let plain = |v: &&str| !v.is_empty() && !v.contains(|c: char| c == '/' || c.is_whitespace());
    let why = format!("Aeneas names the Lean toolchain `{lean}`, which is not a release");
    let version = release.filter(plain).ok_or_else(|| broken(why))?;
    let charon_commit = toolchain::pinned_charon(&sources.charon_pin).map_err(broken)?;
    if charon_commit != sources.charon_commit {
        let at = &sources.charon_commit;
        let why = format!("the Charon tree is at {at}, not at {charon_commit} of charon-pin");
        return Err(found(Finding::Defect, why));
    }
    let cargo = fs::read_to_string(charon.join("charon/Cargo.toml")).unwrap_or_default();
    let cargo = cargo.parse::<toml::Table>().ok();
    let charon_version = (cargo.as_ref()).and_then(|table| table.get("package")?.get("version"));
    let none = "Charon's charon/Cargo.toml has no package.version";
    let charon_version = charon_version.and_then(toml::Value::as_str);
    let charon_version = charon_version.ok_or_else(|| found(Finding::Defect, none))?;
    let nightly = toolchain::toolchain_channel(&sources.rust_toolchain).map_err(broken)?;
    let date = (nightly.strip_prefix("nightly-")).filter(|date| is_date(date));
    let why = format!("Charon names the Rust toolchain {nightly}, which is not a dated nightly");
    let date = date.ok_or_else(|| broken(why))?;
    let lock = &sources.lake_manifest;
    let mathlib = toolchain::locked_revision(lock, "mathlib").map_err(broken)?;
    let old = pinned("/rust/toolchain").replacen("nightly-", "", 1);
    let (from, to) = (format!("/{old}/"), format!("/{date}/"));
    let channel = swap(&pinned("/rust/manifest_url"), &from, &to)?;
    let old = pinned("/lean/version");
    let from = format!("/v{old}/lean-{old}-");
    let to = format!("/v{version}/lean-{version}-");
    let url = |host| swap(&pinned(&format!("/hosts/{host}/lean/url")), &from, &to);
    let [linux, darwin] = HOSTS.map(url);
    Ok(BTreeMap::from([
        ("/aeneas/commit", sources.aeneas_commit.clone()),
        ("/aeneas/lake_manifest_sha256", toolchain::sha256(lock)),
        ("/aeneas/mathlib_commit", mathlib),
        ("/lean/toolchain", lean.to_string()),
        ("/lean/version", version.to_string()),
        ("/charon/commit", charon_commit),
        ("/charon/version", charon_version.to_string()),
        ("/rust/toolchain", nightly.clone()),
        ("/rust/manifest_url", channel),
        ("/hosts/linux-aarch64/lean/url", linux?),
        ("/hosts/darwin-arm64/lean/url", darwin?),
    ]))
}

/// `resolve`: the fields that the trees give, and in its data the URLs of
/// what the job is to download.
fn resolve(root: &Path, layout: &Layout) -> Result<Record, Record> {
    let fields = trees(root, layout)?;
    let urls = [
        "/rust/manifest_url",
        "/hosts/linux-aarch64/lean/url",
        "/hosts/darwin-arm64/lean/url",
    ];
    let urls = urls.map(|pointer| (pointer.to_string(), Value::from(fields[pointer].as_str())));
    let detail = format!(
        "{} fields from the trees of Aeneas main and Charon",
        fields.len()
    );
    Ok(Record {
        data: Value::Object(urls.into_iter().collect()),
        ..found(Finding::Passed, detail)
    })
}

/// The fields of [`RESOLVED`] that the downloads in [`DIR`] give for the
/// fields of the trees: the digests of the two Lean archives, the commit
/// that `lean --version` of the linux archive reports for the release, and
/// the digest and rustc commit of the channel manifest of the nightly.
fn downloads(
    root: &Path,
    fields: &BTreeMap<&str, String>,
) -> Result<BTreeMap<&'static str, String>, Record> {
    let dir = root.join(DIR);
    let read = |name: &str| fs::read(dir.join(name)).map_err(|error| io(&dir.join(name), error));
    let archive = |host| read(&format!("lean-{host}.tar.zst"));
    let [linux, darwin] = HOSTS.map(|host| archive(host).map(|bytes| toolchain::sha256(&bytes)));
    let (linux, darwin) = (linux?, darwin?);
    let line = read("lean-version.txt")?;
    let line = String::from_utf8_lossy(&line);
    let line = line.trim();
    let version = (line.strip_prefix("Lean (version ")).and_then(|rest| rest.split_once(','));
    let commit = (line.split_once(", commit ")).and_then(|(_, rest)| rest.split_once(','));
    let release = version.is_some_and(|(version, _)| version == fields["/lean/version"]);
    let commit = commit.filter(|(commit, _)| release && toolchain::is_hex(commit, 40));
    let why = format!("the Lean archive reports `{line}`");
    let commit = commit.ok_or_else(|| found(Finding::Defect, why))?.0;
    let channel = read("channel-rust-nightly.toml")?;
    let table = std::str::from_utf8(&channel).ok();
    let table = table.and_then(|text| text.parse::<toml::Table>().ok());
    let date = fields["/rust/toolchain"].replacen("nightly-", "", 1);
    let dated = (table.as_ref()).and_then(|table| table.get("date")?.as_str());
    if dated != Some(date.as_str()) {
        let dated = dated.unwrap_or("no date");
        let why = format!("the channel manifest is of {dated}, not of the nightly's date {date}");
        return Err(found(Finding::Defect, why));
    }
    let rustc = (table.as_ref()).and_then(|t| t.get("pkg")?.get("rustc")?.get("git_commit_hash"));
    let rustc = (rustc.and_then(toml::Value::as_str)).filter(|c| toolchain::is_hex(c, 40));
    let none = "the channel manifest names no rustc commit";
    let rustc = rustc.ok_or_else(|| found(Finding::Defect, none))?;
    Ok(BTreeMap::from([
        ("/hosts/linux-aarch64/lean/sha256", linux),
        ("/hosts/darwin-arm64/lean/sha256", darwin),
        ("/lean/commit", commit.to_string()),
        ("/rust/manifest_sha256", toolchain::sha256(&channel)),
        ("/rust/rustc_commit", rustc.to_string()),
    ]))
}

/// The manifest of the build: `committed` with every field of [`RESOLVED`]
/// from `fields`, which holds no other, and [`BUILT`] `null`.
pub fn derived(committed: &Value, fields: &BTreeMap<&str, String>) -> Result<Value, String> {
    let pointers: Vec<&str> = RESOLVED.split_whitespace().collect();
    if let Some(other) = fields.keys().find(|pointer| !pointers.contains(pointer)) {
        return Err(format!("{other} is not a field that the canary resolves"));
    }
    let mut manifest = committed.clone();
    for pointer in pointers.into_iter().chain([BUILT]) {
        let value = match fields.get(pointer) {
            Some(value) => Value::from(value.as_str()),
            None if pointer == BUILT => Value::Null,
            None => return Err(format!("{pointer} is not resolved")),
        };
        let missing = || format!("the committed manifest has no {pointer}");
        *manifest.pointer_mut(pointer).ok_or_else(missing)? = value;
    }
    Ok(manifest)
}

/// The Lake lock of the Lake project for the lock `aeneas` of the Aeneas
/// Lean library: the `committed` lock, with its path package followed by
/// each package of `aeneas`, inherited. The two locks have one version.
pub fn lake_lock(committed: &Value, aeneas: &Value) -> Result<Value, String> {
    let version = &aeneas["version"];
    if version != &committed["version"] {
        let why = "the canary does not derive the root manifest of Lake manifest version";
        return Err(format!("{why} {version}"));
    }
    let packages = aeneas["packages"].as_array().into_iter().flatten();
    let inherited = packages.map(|package| {
        let mut package = package.as_object()?.clone();
        package.insert("inherited".to_string(), Value::Bool(true));
        Some(Value::Object(package))
    });
    let inherited: Option<Vec<Value>> = inherited.collect();
    let inherited = inherited.filter(|packages| !packages.is_empty());
    let inherited = inherited.ok_or("the Lake lock of Aeneas has no list of packages")?;
    let path = (committed.pointer("/packages/0")).filter(|path| path["type"] == "path");
    let path = path.ok_or("the committed Lake lock does not start with its path package")?;
    let mut lock = committed.clone();
    lock["packages"] = Value::Array([path.clone()].into_iter().chain(inherited).collect());
    Ok(lock)
}

/// `derive`: writes the manifest of the build into the checkout, and the
/// Lean toolchain and the Lake lock of the Lake project where Aeneas main
/// changes them, and prints each resolved field with its committed and its
/// derived value.
fn derive(root: &Path, layout: &Layout) -> Result<Record, Record> {
    let mut fields = trees(root, layout)?;
    fields.extend(downloads(root, &fields)?);
    let committed = json(&root.join(layout.toolchain))?;
    let defect = |why: String| found(Finding::Defect, why);
    let manifest = derived(&committed, &fields).map_err(defect)?;
    let backend = root.join(DIR).join("aeneas/backends/lean");
    let at = |file: &str| (root.join(layout.project).join(file), backend.join(file));
    let (ours, theirs) = at("lake-manifest.json");
    let lock = json(&ours)?;
    let derived_lock = lake_lock(&lock, &json(&theirs)?).map_err(defect)?;
    let mut changed = Vec::new();
    if derived_lock != lock {
        write(&ours, &derived_lock)?;
        changed.push(format!("{}/lake-manifest.json", layout.project));
    }
    let (ours, theirs) = at("lean-toolchain");
    let toolchain = fs::read(&theirs).map_err(|error| io(&theirs, error))?;
    if fs::read(&ours).ok().as_ref() != Some(&toolchain) {
        fs::write(&ours, toolchain).map_err(|error| io(&ours, error))?;
        changed.push(format!("{}/lean-toolchain", layout.project));
    }
    write(&root.join(layout.toolchain), &manifest)?;
    let pinned = |pointer| committed.pointer(pointer).unwrap_or(&Value::Null);
    for (pointer, value) in &fields {
        let pin = pinned(pointer).as_str().unwrap_or("null");
        println!("{pointer}: {pin} -> {value}");
    }
    let pairs = (fields.iter()).map(|(p, v)| (p.to_string(), json!([pinned(p), v])));
    let (count, changes) = (fields.len(), changed.len());
    let detail = format!("{count} fields derived; {changes} files of the Lake project changed");
    let data = json!({
        "aeneas_main": fields["/aeneas/commit"],
        "fields": Value::Object(pairs.collect()),
        "built_committed": pinned(BUILT),
        "lake_project": changed,
    });
    Ok(Record {
        data,
        ..found(Finding::Passed, detail)
    })
}

/// `patch`: whether the patch of the manifest applies to the Aeneas tree
/// that the image is built from. That it does not is one breakage, which
/// ends the job; a patch that Git cannot read, or a Git that does not run,
/// fails the run.
pub fn patch(root: &Path, layout: &Layout) -> Record {
    let path = root.join(layout.toolchain);
    let manifest = fs::read_to_string(&path).map_err(|error| error.to_string());
    let patch = manifest.and_then(|text| {
        let manifest = toolchain::parse(&text)?;
        Ok(root.join(toolchain::patch_path(&manifest, layout)?))
    });
    let patch = match patch {
        Ok(patch) => patch,
        Err(why) => return io(&path, why),
    };
    let mut git = Process::new("git");
    git.arg("-C").arg(root.join(IMAGE).join("aeneas"));
    let output = git.args(["apply", "--check"]).arg(&patch).output();
    let output = match output {
        Ok(output) => output,
        Err(error) => return found(Finding::Failed, format!("cannot run git: {error}")),
    };
    let error = String::from_utf8_lossy(&output.stderr).trim().to_string();
    match output.status.code() {
        Some(0) => found(Finding::Passed, "the patch applies"),
        Some(1) => found(
            Finding::Broken,
            format!("the patch does not apply: {error}"),
        ),
        _ => found(
            Finding::Failed,
            format!("git apply --check ended with {}: {error}", output.status),
        ),
    }
}

/// The manifest of the gate: `manifest` with [`BUILT`] from the image's
/// `versions`, which must hold a SHA-256.
pub fn built(manifest: &Value, versions: &Value) -> Result<Value, String> {
    let export = (versions.pointer("/opam/switch_export_sha256")).and_then(Value::as_str);
    let export = export.filter(|digest| toolchain::is_hex(digest, 64));
    let export = export.ok_or("the image's versions.json gives no SHA-256 of the switch export")?;
    let mut manifest = manifest.clone();
    let missing = || format!("the manifest has no {BUILT}");
    *manifest.pointer_mut(BUILT).ok_or_else(missing)? = Value::from(export);
    Ok(manifest)
}

/// `fill`: writes into the manifest the switch export of the built image,
/// and into the statement registry the statement hash of `HEAD`, the commit
/// of the derived files, each only where it changes.
fn fill(root: &Path, layout: &Layout) -> Result<Record, Record> {
    let path = root.join(layout.toolchain);
    let manifest = json(&path)?;
    let versions = json(&root.join(IMAGE).join("versions.json"))?;
    let gate = built(&manifest, &versions).map_err(|why| found(Finding::Defect, why))?;
    let committed = json(&root.join(DIR).join("derive.json"))?;
    let work = root.join(DIR).join("fill");
    fs::create_dir_all(&work).map_err(|error| io(&work, error))?;
    let hash = guard::statement_hash(&mut Standalone(root), "HEAD", layout, &work);
    let (hash, _) = hash.map_err(|why| found(Finding::Failed, why))?;
    let registry = root.join(layout.statements);
    let mut statements = json(&registry)?;
    let recorded = statements.pointer_mut("/hash");
    let recorded = recorded.ok_or_else(|| io(&registry, "the registry has no hash"))?;
    let recorded = std::mem::replace(recorded, Value::from(hash.as_str()));
    if recorded != hash.as_str() {
        write(&registry, &statements)?;
    }
    if gate != manifest {
        write(&path, &gate)?;
    }
    let committed = committed.pointer("/data/built_committed");
    let export = [committed, gate.pointer(BUILT)];
    let data = json!({"switch_export_sha256": export, "statement_hash": [recorded, hash]});
    Ok(Record {
        data,
        ..found(Finding::Passed, "the switch export and the statement hash")
    })
}

/// `verdict`: the finding of the run, with the commit `main` and the step in
/// its detail: that of the first of [`STEPS`] that did not pass, or else
/// that of the gate. A step passes when its outcome is `success` and, for
/// one of [`RECORDED`], its record passed. A failed build is classed by its
/// log, the gate by its exit status and receipt, a step of [`RECORDED`] by
/// a record that did not pass, and the tool checks, which compare the
/// derived manifest with the trees, as a defect; any other failure, and a
/// step that was cancelled, skipped or has no outcome, fails the run. The
/// data holds those of `derive` and `fill`.
pub fn verdict(root: &Path, outcomes: &BTreeMap<String, String>, main: &str) -> Record {
    let dir = root.join(DIR);
    let record = |step: &str| {
        let value = json(&dir.join(format!("{step}.json"))).ok()?;
        serde_json::from_value::<Record>(value).ok()
    };
    let data = json!({
        "derive": record("derive").map(|record| record.data),
        "fill": record("fill").map(|record| record.data),
    });
    let failed = |why: &str| found(Finding::Failed, why);
    let passed = |record: &Record| record.verdict == Finding::Passed;
    let first = STEPS.split_whitespace().find_map(|step| {
        let recorded = RECORDED.split(' ').any(|it| it == step);
        let own = recorded.then(|| record(step));
        let finding = match (outcomes.get(step).map(String::as_str), step, own) {
            (Some("success"), _, None) => return None,
            (Some("success"), _, Some(Some(record))) if passed(&record) => return None,
            (Some("success"), _, Some(_)) => failed("it succeeded without a record that passed"),
            (Some("failure"), "build", _) => build(root),
            (Some("failure"), "gate", _) => gate(root),
            (Some("failure"), _, Some(Some(record))) if !passed(&record) => record,
            (Some("failure"), "toolchain-check", _) => {
                let log = fs::read_to_string(dir.join("toolchain-check.txt")).unwrap_or_default();
                let lines = Vec::from_iter(log.lines());
                let tail = lines[lines.len().saturating_sub(12)..].join("\n");
                let why = format!("the tool checks fail on the derived manifest:\n{tail}");
                found(Finding::Defect, why)
            }
            (Some(outcome), _, _) => failed(&format!("the step ended with the outcome {outcome}")),
            (None, _, _) => failed("the step has no outcome"),
        };
        Some((step, finding))
    });
    let (step, finding) = first.unwrap_or_else(|| ("gate", gate(root)));
    let detail = format!("{step} (main {main}): {}", finding.detail);
    Record {
        detail,
        data,
        ..finding
    }
}

/// The finding of the failure `text`: a defect or a failure of the run when
/// it holds a text of [`DEFECTS`] or [`FAILURES`], else `otherwise`.
fn by_text(text: &str, otherwise: Finding) -> Finding {
    let holds = |texts: &str| texts.split('|').any(|it| text.contains(it));
    if holds(DEFECTS) {
        Finding::Defect
    } else if holds(FAILURES) {
        Finding::Failed
    } else {
        otherwise
    }
}

/// The stage of the BuildKit step `[<stage> <i>/<k>] ...`.
fn stage(text: &str) -> Option<&str> {
    let (inside, _) = text.strip_prefix('[')?.split_once(']')?;
    let (name, count) = inside.split_once(' ')?;
    count.contains('/').then_some(name)
}

/// The rest of a line of a BuildKit log after its step number `#<n> `.
fn of_step(line: &str) -> Option<&str> {
    let (number, rest) = line.split_once(' ')?;
    let digits = number.strip_prefix('#')?;
    (!digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit())).then_some(rest)
}

/// A failed image build, by its exit status in `build-status` and its log:
/// the limit, and a log without a failure block after its first error, fail
/// the run. Otherwise the block names the stage; it is a defect or a
/// failure by the error and the output of the step that it shows, else a
/// breakage in a stage of [`TOOL_STAGES`] and a failure of the run in
/// another. The first line of the block, and the script that the error of
/// a process quotes, hold the recipe's own texts and are not read.
fn build(root: &Path) -> Record {
    let failed = |why: String| found(Finding::Failed, why);
    let Ok(status) = fs::read_to_string(root.join(DIR).join("build-status")) else {
        return failed("the runner or the step limit ended the build".to_string());
    };
    let log = fs::read_to_string(root.join(IMAGE).join("build.log")).unwrap_or_default();
    let lines = Vec::from_iter(log.lines());
    if matches!(status.trim(), "124" | "137") {
        let started = lines.iter().rev().find_map(|line| stage(of_step(line)?));
        let started = started.unwrap_or("none");
        let why = "the image build reached its limit of 52 minutes; the last stage that started";
        return failed(format!("{why}: {started}"));
    }
    let is_error = |line: &&str| of_step(line).is_some_and(|rest| rest.starts_with("ERROR:"));
    let error = lines.iter().position(is_error);
    let block = |at: usize| (lines[at..].iter()).position(|line| line.starts_with(" > ["));
    let start = error.and_then(|at| Some(at + block(at)?));
    let (Some(error), Some(start)) = (error, start) else {
        return failed("the build log has no failure block after an error".to_string());
    };
    let end = lines[start + 1..].iter().position(|line| *line == "------");
    let block = &lines[start..end.map_or(lines.len(), |end| start + 1 + end)];
    let name = stage(&lines[start][" > ".len()..]).unwrap_or("of no name");
    let text = format!("{}\n{}", lines[error], block.join("\n"));
    let tools = TOOL_STAGES.split(' ').any(|tool| tool == name);
    let otherwise = [Finding::Failed, Finding::Broken][usize::from(tools)];
    let why = format!("the stage {name} failed:\n{text}");
    let message = of_step(lines[error]).and_then(|rest| rest.strip_prefix("ERROR:"));
    let message = message.unwrap_or_default().trim_start();
    let exit = "\" did not complete successfully";
    let message = match message.strip_prefix("process \"") {
        Some(script) => script.rsplit_once(exit).map_or("", |(_, rest)| rest),
        None => message,
    };
    let read = format!("{message}\n{}", block[1..].join("\n"));
    found(by_text(&read, otherwise), why)
}

/// The gate, by its exit status in `gate-status` and its one receipt:
/// passed for 0 and a complete `VERIFIED` receipt; for 1 and a receipt with
/// a verdict, a breakage unless the texts of its failures and of the units
/// that are not `VERIFIED` make it a defect or a failure of the run; and a
/// failure of the run for any other status, which is an error of the run
/// and not a verdict.
fn gate(root: &Path) -> Record {
    let failed = |why: String| found(Finding::Failed, why);
    let Ok(status) = fs::read_to_string(root.join(DIR).join("gate-status")) else {
        return failed("the gate step wrote no exit status".to_string());
    };
    let runs = fs::read_dir(root.join(run::RUNS)).into_iter().flatten();
    let receipts = runs.flatten().map(|run| run.path().join("receipt.json"));
    let receipts = Vec::from_iter(receipts.filter(|path| path.is_file()));
    let [path] = receipts.as_slice() else {
        return failed(format!("the gate left {} receipts", receipts.len()));
    };
    let text = fs::read_to_string(path).map_err(|error| error.to_string());
    let parse = |text: String| serde_json::from_str::<Receipt>(&text).map_err(|e| e.to_string());
    let receipt = match text.and_then(parse) {
        Ok(receipt) => receipt,
        Err(error) => return failed(format!("{}: {error}", path.display())),
    };
    let word = outcome::word(&receipt.status);
    let open = (receipt.units.iter()).filter(|(_, unit)| unit.status != Status::Verified);
    let open = Vec::from_iter(open);
    let units = (open.iter()).map(|(name, u)| format!("{name} {}", outcome::word(&u.status)));
    let units = Vec::from_iter(units);
    let failures = (receipt.failures.iter()).map(|failure| failure.message.as_str());
    let failures = Vec::from_iter(failures);
    let reasons = (open.iter()).filter_map(|(_, unit)| unit.reason.as_deref());
    let texts = Vec::from_iter((failures.iter().copied()).chain(reasons)).join("\n");
    match (status.trim(), receipt.status) {
        ("0", Status::Verified) if receipt.complete => {
            found(Finding::Passed, "the receipt is VERIFIED and complete")
        }
        ("1", Status::Rejected | Status::ToolFailure | Status::Budget | Status::Stale) => {
            let detail = format!(
                "the gate exited with 1, {word}; units that are not VERIFIED: {}; failures: {}",
                units.join(", "),
                failures.join("; ")
            );
            found(by_text(&texts, Finding::Broken), detail)
        }
        (status, _) => failed(format!(
            "the gate exited with `{status}`, receipt {word}, complete {}",
            receipt.complete
        )),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;
    use crate::formal::fixture::{self, Fixture};
    use crate::formal::receipt::{self, Failure, Unit};
    use crate::formal::toolchain::environment::SYSTEM_PATH;
    use crate::scratch::Scratch;

    const COMMITTED: &str = include_str!("../../../verification/toolchain.json");
    const PATCH: &[u8] =
        include_bytes!("../../../verification/tooling/aeneas-option-unwrap-mut-and-prefix.patch");
    const LAKE_LOCK: &str = include_str!("../../../verification/lake-manifest.json");
    const LEAN_TOOLCHAIN: &str = include_str!("../../../verification/lean-toolchain");
    /// `backends/lean/lake-manifest.json` of the pinned Aeneas commit.
    const AENEAS_LOCK: &str = include_str!("fixtures/canary/aeneas-lake-manifest.json");
    const CANARY: &str = include_str!("../../../.github/workflows/formal-canary.yml");
    const BUILD: &str = include_str!("../../../.github/workflows/formal-image-build.yml");
    const FORMAL: &str = include_str!("../../../.github/workflows/formal.yml");
    const MANUAL: &str = include_str!("../../../docs/formal-upgrade.md");

    /// The Mathlib commit of the pinned lock, and another.
    const MATHLIB: &str = "56a005855ea17e0b0958f73ec801ae140b0a1679";
    const OTHER_MATHLIB: &str = "1111111111111111111111111111111111111111";
    const LEAN_COMMIT: &str = "2222222222222222222222222222222222222222";
    const RUSTC: &str = "3333333333333333333333333333333333333333";
    const LINUX: &str = "the linux archive\n";
    const DARWIN: &str = "the darwin archive\n";
    const CHANNEL: &str = "manifest-version = \"2\"\ndate = \"2026-10-01\"\n\n[pkg.rustc]\n\
        version = \"1.101.0-nightly (3333333 2026-09-30)\"\n\
        git_commit_hash = \"3333333333333333333333333333333333333333\"\n";

    fn layout() -> Layout {
        Layout::PRODUCTION
    }

    fn value(text: &str) -> Value {
        serde_json::from_str(text).expect("JSON")
    }

    /// The path of the patch that the committed manifest names.
    fn patch_path() -> String {
        let manifest = toolchain::parse(COMMITTED).expect("the manifest");
        manifest.aeneas.patch
    }

    /// The line that `lean --version` of a linux archive of `version` prints.
    fn lean_version(version: &str) -> String {
        let host = "aarch64-unknown-linux-gnu";
        format!("Lean (version {version}, {host}, commit {LEAN_COMMIT}, Release)\n")
    }

    /// Runs Git in `dir` with a fixed identity and date and without system
    /// or global configuration, and gives its standard output; Git must
    /// succeed.
    fn git(dir: &Path, args: &[&str]) -> String {
        let mut command = Process::new("git");
        command.args(args).current_dir(dir).env_clear();
        command.env("PATH", SYSTEM_PATH).env("HOME", dir);
        command.env("GIT_CONFIG_NOSYSTEM", "1");
        command.env("GIT_CONFIG_GLOBAL", "/dev/null");
        for role in ["AUTHOR", "COMMITTER"] {
            command.env(format!("GIT_{role}_NAME"), "Canary");
            command.env(format!("GIT_{role}_EMAIL"), "canary@example.invalid");
            command.env(format!("GIT_{role}_DATE"), "2026-01-01T00:00:00Z");
        }
        let output = command.output().expect("run git");
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(output.status.success(), "git {args:?}: {stderr}");
        String::from_utf8_lossy(&output.stdout).trim().to_string()
    }

    /// A new Git repository at `dir` with one commit of the `files` below its
    /// name, whose texts have `CHARON` replaced by `charon`; its commit.
    fn tree(dir: &Path, files: &BTreeMap<String, Option<String>>, charon: &str) -> String {
        let name = (dir.file_name().and_then(|name| name.to_str())).expect("a name");
        for (path, text) in files {
            let (Some(path), Some(text)) = (path.strip_prefix(&format!("{name}/")), text) else {
                continue;
            };
            let path = dir.join(path);
            fs::create_dir_all(path.parent().expect("a directory")).expect("a directory");
            fs::write(path, text.replace("CHARON", charon)).expect("a file");
        }
        git(dir, &["-c", "init.defaultBranch=main", "init", "--quiet"]);
        git(dir, &["add", "--all"]);
        git(dir, &["commit", "--quiet", "--message", "tree"]);
        git(dir, &["rev-parse", "HEAD"])
    }

    /// A repository root with the committed manifest, patch and Lake project
    /// files, and in [`DIR`] what the job fetches of a later Aeneas main:
    /// its tree and that of its Charon, and the downloads. `changes` replace
    /// or, with `None`, remove files, by their paths below [`DIR`].
    fn upstream(changes: &[(&str, Option<&str>)]) -> Scratch {
        let scratch = Scratch::temporary("canary-upstream");
        scratch.write(layout().toolchain, COMMITTED);
        fs::create_dir_all(scratch.0.join(layout().tooling)).expect("the tooling directory");
        fs::write(scratch.0.join(patch_path()), PATCH).expect("the patch");
        scratch.write("verification/lake-manifest.json", LAKE_LOCK);
        scratch.write("verification/lean-toolchain", LEAN_TOOLCHAIN);
        let cargo = "[package]\nname = \"charon\"\nversion = \"0.1.313\"\n";
        let rust = "[toolchain]\nchannel = \"nightly-2026-10-01\"\n";
        let pin = "# The Charon commit of this Aeneas.\nCHARON\n";
        let lean = "leanprover/lean4:v4.36.0\n";
        let (lock, version) = (
            AENEAS_LOCK.replace(MATHLIB, OTHER_MATHLIB),
            lean_version("4.36.0"),
        );
        let files = [
            ("charon/charon/Cargo.toml", cargo),
            ("charon/charon/rust-toolchain", rust),
            ("aeneas/charon-pin", pin),
            ("aeneas/backends/lean/lean-toolchain", lean),
            ("aeneas/backends/lean/lake-manifest.json", lock.as_str()),
            ("lean-linux-aarch64.tar.zst", LINUX),
            ("lean-darwin-arm64.tar.zst", DARWIN),
            ("lean-version.txt", version.as_str()),
            ("channel-rust-nightly.toml", CHANNEL),
        ];
        let files = files.map(|(path, text)| (path.to_string(), Some(text.to_string())));
        let mut files = BTreeMap::from(files);
        for (path, text) in changes {
            files.insert(path.to_string(), text.map(str::to_string));
        }
        let dir = scratch.0.join(DIR);
        let charon = tree(&dir.join("charon"), &files, "");
        tree(&dir.join("aeneas"), &files, &charon);
        for (path, text) in &files {
            if let (false, Some(text)) = (path.contains('/'), text) {
                scratch.write(&format!("{DIR}/{path}"), text);
            }
        }
        scratch
    }

    /// What the trees and downloads of [`upstream`] give.
    fn resolved(root: &Path) -> BTreeMap<&'static str, String> {
        let head = |tree: &str| git(&root.join(DIR).join(tree), &["rev-parse", "HEAD"]);
        let (text, digest) = (str::to_string, |text: &str| {
            toolchain::sha256(text.as_bytes())
        });
        let lock = AENEAS_LOCK.replace(MATHLIB, OTHER_MATHLIB);
        let lean = "https://github.com/leanprover/lean4/releases/download/v4.36.0/lean-4.36.0";
        let linux = format!("{lean}-linux_aarch64.tar.zst");
        let darwin = format!("{lean}-darwin_aarch64.tar.zst");
        let rust = "https://static.rust-lang.org/dist/2026-10-01/channel-rust-nightly.toml";
        BTreeMap::from([
            ("/aeneas/commit", head("aeneas")),
            ("/aeneas/lake_manifest_sha256", digest(&lock)),
            ("/aeneas/mathlib_commit", text(OTHER_MATHLIB)),
            ("/lean/toolchain", text("leanprover/lean4:v4.36.0")),
            ("/lean/version", text("4.36.0")),
            ("/lean/commit", text(LEAN_COMMIT)),
            ("/charon/commit", head("charon")),
            ("/charon/version", text("0.1.313")),
            ("/rust/toolchain", text("nightly-2026-10-01")),
            ("/rust/manifest_url", text(rust)),
            ("/rust/manifest_sha256", digest(CHANNEL)),
            ("/rust/rustc_commit", text(RUSTC)),
            ("/hosts/linux-aarch64/lean/url", linux),
            ("/hosts/linux-aarch64/lean/sha256", digest(LINUX)),
            ("/hosts/darwin-arm64/lean/url", darwin),
            ("/hosts/darwin-arm64/lean/sha256", digest(DARWIN)),
        ])
    }

    #[test]
    fn resolution_reads_the_trees_and_the_downloads() {
        let scratch = upstream(&[]);
        let (root, layout) = (scratch.0.as_path(), layout());
        let expected = resolved(root);
        let mut fields = trees(root, &layout).expect("the trees");
        assert_eq!(fields.len(), 11);
        fields.extend(downloads(root, &fields).expect("the downloads"));
        assert_eq!(fields, expected);
        let resolve = resolve(root, &layout).expect("resolved");
        let urls = (expected.iter()).filter(|(pointer, _)| pointer.ends_with("url"));
        let urls = urls.map(|(pointer, url)| (pointer.to_string(), Value::from(url.as_str())));
        assert_eq!(resolve.data, Value::Object(urls.collect()));
        assert_eq!(resolve.data.as_object().map(serde_json::Map::len), Some(3));
        // `derive` writes the manifest of the build and the Lake project.
        let derive = derive(root, &layout).expect("derived");
        assert_eq!(derive.verdict, Finding::Passed);
        let committed = value(COMMITTED);
        let manifest = json(&root.join(layout.toolchain)).expect("the manifest");
        assert_eq!(manifest, derived(&committed, &expected).expect("derived"));
        let project = root.join(layout.project);
        let toolchain = fs::read_to_string(project.join("lean-toolchain")).expect("the toolchain");
        assert_eq!(toolchain, "leanprover/lean4:v4.36.0\n");
        let lock = json(&project.join("lake-manifest.json")).expect("the lock");
        let aeneas = value(&AENEAS_LOCK.replace(MATHLIB, OTHER_MATHLIB));
        assert_eq!(Ok(lock), lake_lock(&value(LAKE_LOCK), &aeneas));
        let data = &derive.data;
        assert_eq!(data["aeneas_main"], expected["/aeneas/commit"].as_str());
        assert_eq!(Some(&data["built_committed"]), committed.pointer(BUILT));
        let files = ["lake-manifest.json", "lean-toolchain"].map(|f| format!("verification/{f}"));
        assert_eq!(data["lake_project"], json!(files));
        for (pointer, derived) in &expected {
            let pair = json!([committed.pointer(pointer), derived]);
            assert_eq!(data["fields"][*pointer], pair, "{pointer}");
        }
        // The tool checks pass on the derived manifest and the trees.
        let manifest = toolchain::parse(&manifest.to_string()).expect("a manifest");
        let [aeneas, charon] = ["aeneas", "charon"].map(|tree| root.join(DIR).join(tree));
        let sources = Sources::read(root, &layout, &manifest, &aeneas, &charon).expect("sources");
        for (name, finding) in toolchain::check_sources(&manifest, &layout, &sources) {
            assert!(finding.is_ok(), "{name}: {finding:?}");
        }
        // The Lean and the Lake lock of the pins change no file of the Lake
        // project.
        let line = include_str!("fixtures/base/lean-version.txt");
        let scratch = upstream(&[
            ("aeneas/backends/lean/lean-toolchain", Some(LEAN_TOOLCHAIN)),
            ("aeneas/backends/lean/lake-manifest.json", Some(AENEAS_LOCK)),
            ("lean-version.txt", line.lines().last()),
        ]);
        let root = scratch.0.as_path();
        let derive = super::derive(root, &layout).expect("derived");
        assert_eq!(derive.data["lake_project"], json!([]));
        let project = root.join(layout.project);
        let lock = fs::read_to_string(project.join("lake-manifest.json")).expect("the lock");
        assert_eq!(lock, LAKE_LOCK, "the committed bytes stay");
    }

    #[test]
    fn forms_the_recipe_cannot_take_are_breakages_and_misreads_are_defects() {
        use Finding::{Broken, Defect, Failed};
        let mut twice = value(AENEAS_LOCK);
        let packages = twice["packages"].as_array_mut().expect("the packages");
        packages.push(packages[0].clone());
        let mut version = value(AENEAS_LOCK);
        version["version"] = Value::from("1.4.0");
        let [twice, version] = [twice, version].map(|lock| lock.to_string());
        let other = lean_version("4.35.1");
        let undated = CHANNEL.replace("2026-10-01", "2026-09-30");
        let unhashed = CHANNEL.replace("git_commit_hash", "commit");
        let (lean, lock) = (
            "aeneas/backends/lean/lean-toolchain",
            "aeneas/backends/lean/lake-manifest.json",
        );
        let (pin, rust) = ("aeneas/charon-pin", "charon/charon/rust-toolchain");
        let (cargo, channel) = ("charon/charon/Cargo.toml", "channel-rust-nightly.toml");
        let nightly = Some("leanprover/lean4:nightly-2026-10-01\n");
        let stable = Some("[toolchain]\nchannel = \"stable\"\n");
        let elsewhere = Some("0123456789abcdef0123456789abcdef01234567\n");
        let inherited = Some("[package]\nname = \"charon\"\nversion.workspace = true\n");
        let dated = Some("[toolchain]\nchannel = \"nightly-2026-1-01\"\n".to_string());
        let short = lean_version("4.36.0").replace(LEAN_COMMIT, &LEAN_COMMIT[..39]);
        let upper = lean_version("4.36.0").replace(LEAN_COMMIT, &"A".repeat(40));
        let rustc = CHANNEL.replace(&format!("\"{RUSTC}\""), "\"333333333333\"");
        let cases = [
            (lean, nightly, Broken, "which is not a release"),
            (rust, stable, Broken, "which is not a dated nightly"),
            (lock, Some(twice.as_str()), Broken, "named `mathlib`"),
            (pin, Some("CHARON\nCHARON\n"), Broken, "must have one"),
            (pin, elsewhere, Defect, "of charon-pin"),
            (cargo, inherited, Defect, "no package.version"),
            ("lean-version.txt", Some(other.as_str()), Defect, "4.35.1"),
            (channel, Some(undated.as_str()), Defect, "is of 2026-09-30"),
            (channel, Some(unhashed.as_str()), Defect, "no rustc commit"),
            (lock, Some(version.as_str()), Defect, "version \"1.4.0\""),
            ("lean-darwin-arm64.tar.zst", None, Failed, "darwin-arm64"),
            (
                lean,
                Some("leanprover/lean4:v\n"),
                Broken,
                "which is not a release",
            ),
            (
                lean,
                Some("leanprover/lean4:v4.36.0 x\n"),
                Broken,
                "which is not a release",
            ),
            (
                lean,
                Some("leanprover/lean4:v4.36.0/x\n"),
                Broken,
                "which is not a release",
            ),
            (
                rust,
                dated.as_deref(),
                Broken,
                "which is not a dated nightly",
            ),
            (
                "lean-version.txt",
                Some(short.as_str()),
                Defect,
                "the Lean archive reports",
            ),
            (
                "lean-version.txt",
                Some(upper.as_str()),
                Defect,
                "the Lean archive reports",
            ),
            (channel, Some(rustc.as_str()), Defect, "no rustc commit"),
        ];
        for (path, text, verdict, why) in cases {
            let scratch = upstream(&[(path, text)]);
            let record = derive(&scratch.0, &layout()).expect_err("no derived manifest");
            assert_eq!(record.verdict, verdict, "{path}: {record:?}");
            assert!(record.detail.contains(why), "{path}: {record:?}");
            let manifest = fs::read_to_string(scratch.0.join(layout().toolchain));
            assert_eq!(manifest.expect("the manifest"), COMMITTED, "{path}");
        }
        // A tree that the job did not fetch fails the run.
        let scratch = upstream(&[]);
        fs::remove_dir_all(scratch.0.join(DIR).join("charon")).expect("remove the tree");
        let record = resolve(&scratch.0, &layout()).expect_err("no tree");
        assert_eq!(record.verdict, Finding::Failed, "{record:?}");
        // The job fetches no Charon for a charon-pin without one line that
        // is not a comment, which is a breakage all the same.
        for text in ["# No commit.\n", "CHARON\nCHARON\n"] {
            let scratch = upstream(&[(pin, Some(text))]);
            fs::remove_dir_all(scratch.0.join(DIR).join("charon")).expect("remove the tree");
            let record = resolve(&scratch.0, &layout()).expect_err("no tree");
            assert_eq!(record.verdict, Broken, "{record:?}");
            assert!(record.detail.contains("must have one"), "{record:?}");
        }
        // A committed URL that does not hold the committed release once is a
        // defect, since the canary replaces that release.
        let lean = "https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0";
        let lean = format!("{lean}-linux_aarch64.tar.zst");
        let rust = "https://static.rust-lang.org/dist/2026-09-17/channel-rust-nightly.toml";
        for (url, changed, times) in [
            (lean.as_str(), format!("{lean}#/v4.35.0/lean-4.35.0-"), 2),
            (lean.as_str(), lean.replace("/v4.35.0/", "/4.35.0/"), 0),
            (
                rust,
                rust.replace("/2026-09-17/", "/2026-09-17/x/2026-09-17/"),
                2,
            ),
            (rust, rust.replace("/2026-09-17/", "/latest/"), 0),
        ] {
            let scratch = upstream(&[]);
            assert_eq!(COMMITTED.matches(url).count(), 1, "{url}");
            scratch.write(layout().toolchain, &COMMITTED.replace(url, &changed));
            let record = derive(&scratch.0, &layout()).expect_err("no derived manifest");
            assert_eq!(record.verdict, Defect, "{record:?}");
            assert!(
                record.detail.ends_with(&format!(" {times} times")),
                "{record:?}"
            );
        }
    }

    #[test]
    fn the_lake_project_follows_the_aeneas_lock() {
        let manifest = toolchain::parse(COMMITTED).expect("the manifest");
        let digest = toolchain::sha256(AENEAS_LOCK.as_bytes());
        assert_eq!(digest, manifest.aeneas.lake_manifest_sha256);
        let (committed, aeneas) = (value(LAKE_LOCK), value(AENEAS_LOCK));
        assert_eq!(lake_lock(&committed, &aeneas), Ok(committed.clone()));
        // Another Mathlib commit changes only the revision of Mathlib.
        let other = value(&AENEAS_LOCK.replace(MATHLIB, OTHER_MATHLIB));
        let mut expected = committed.clone();
        let packages = expected["packages"].as_array_mut().expect("the packages");
        let mathlib = (packages.iter_mut()).find(|package| package["name"] == "mathlib");
        mathlib.expect("Mathlib")["rev"] = Value::from(OTHER_MATHLIB);
        assert_eq!(lake_lock(&committed, &other), Ok(expected));
        let mut empty = aeneas.clone();
        empty["packages"] = json!([]);
        let mut unnamed = committed.clone();
        unnamed["packages"][0]["type"] = Value::from("git");
        for (committed, aeneas) in [(&committed, &empty), (&unnamed, &aeneas)] {
            assert!(lake_lock(committed, aeneas).is_err(), "{aeneas}");
        }
    }

    /// The fields that the canary resolves, as the canary's specification
    /// lists them, each with a value of a later Aeneas main.
    const MAIN: [(&str, &str); 16] = [
        ("/aeneas/commit", "c5eb4a28cef65e0aa27743105308243e535a2a2b"),
        (
            "/aeneas/lake_manifest_sha256",
            "1111111111111111111111111111111111111111111111111111111111111111",
        ),
        (
            "/aeneas/mathlib_commit",
            "2222222222222222222222222222222222222222",
        ),
        ("/lean/toolchain", "leanprover/lean4:v4.36.0"),
        ("/lean/version", "4.36.0"),
        ("/lean/commit", "3333333333333333333333333333333333333333"),
        (
            "/hosts/linux-aarch64/lean/url",
            "https://github.com/leanprover/lean4/releases/download/v4.36.0/lean-4.36.0-linux_aarch64.tar.zst",
        ),
        (
            "/hosts/linux-aarch64/lean/sha256",
            "4444444444444444444444444444444444444444444444444444444444444444",
        ),
        (
            "/hosts/darwin-arm64/lean/url",
            "https://github.com/leanprover/lean4/releases/download/v4.36.0/lean-4.36.0-darwin_aarch64.tar.zst",
        ),
        (
            "/hosts/darwin-arm64/lean/sha256",
            "5555555555555555555555555555555555555555555555555555555555555555",
        ),
        ("/charon/commit", "8cae8fd1905946de61147a65ecdd7122cc6b491b"),
        ("/charon/version", "0.1.313"),
        ("/rust/toolchain", "nightly-2026-10-01"),
        (
            "/rust/manifest_url",
            "https://static.rust-lang.org/dist/2026-10-01/channel-rust-nightly.toml",
        ),
        (
            "/rust/manifest_sha256",
            "6666666666666666666666666666666666666666666666666666666666666666",
        ),
        (
            "/rust/rustc_commit",
            "7777777777777777777777777777777777777777",
        ),
    ];

    /// Every leaf of `value`, by its JSON pointer below `at`.
    fn leaves(value: &Value, at: String, out: &mut BTreeMap<String, Value>) {
        if let Value::Object(map) = value {
            (map.iter()).for_each(|(key, value)| leaves(value, format!("{at}/{key}"), out));
        } else {
            out.insert(at, value.clone());
        }
    }

    #[test]
    fn the_derived_manifest_refills_the_resolved_fields_and_keeps_the_others() {
        let pointers = BTreeSet::from_iter(MAIN.iter().map(|(pointer, _)| *pointer));
        let resolved = Vec::from_iter(RESOLVED.split_whitespace());
        assert_eq!(pointers, BTreeSet::from_iter(resolved.iter().copied()));
        assert_eq!(pointers.len(), resolved.len());
        let committed = value(COMMITTED);
        let fields = BTreeMap::from_iter(MAIN.iter().map(|(p, v)| (*p, v.to_string())));
        let build = derived(&committed, &fields).expect("derived");
        let (mut before, mut after) = (BTreeMap::new(), BTreeMap::new());
        leaves(&committed, String::new(), &mut before);
        leaves(&build, String::new(), &mut after);
        assert_eq!(Vec::from_iter(before.keys()), Vec::from_iter(after.keys()));
        for (pointer, value) in &after {
            match MAIN.iter().find(|(p, _)| p == pointer) {
                Some((_, main)) => {
                    assert_ne!(before[pointer], Value::from(*main), "{pointer}");
                    assert_eq!(value, &Value::from(*main), "{pointer}");
                }
                None if pointer == BUILT => assert_eq!(value, &Value::Null),
                None => assert_eq!(value, &before[pointer], "{pointer}"),
            }
        }
        let manifest = toolchain::parse(&build.to_string()).expect("a manifest");
        assert!(toolchain::check_lean_pins(&manifest).is_ok());
        assert!(toolchain::check_hosts(&manifest).is_ok());
        // `built` sets the switch export of the image, and nothing else.
        let export = "8888888888888888888888888888888888888888888888888888888888888888";
        let versions = json!({"opam": {"switch_export_sha256": export}});
        let gate = built(&build, &versions).expect("built");
        assert_eq!(gate.pointer(BUILT), Some(&Value::from(export)));
        let mut rest = gate.clone();
        *rest.pointer_mut(BUILT).expect("the field") = Value::Null;
        assert_eq!(rest, build);
        assert!(built(&build, &json!({"opam": {"switch_export_sha256": "abc"}})).is_err());
        // Every resolved field, no other and a committed one for each.
        let mut short = fields.clone();
        short.remove("/charon/version");
        let why = "/charon/version is not resolved";
        assert_eq!(derived(&committed, &short), Err(why.to_string()));
        let mut extra = fields.clone();
        extra.insert("/aeneas/patch_sha256", "x".into());
        let why = "/aeneas/patch_sha256 is not a field that the canary resolves";
        assert_eq!(derived(&committed, &extra), Err(why.to_string()));
        let mut lacking = committed.clone();
        lacking["charon"] = json!({"commit": "6cc2b5f80b7edc2383cba3dab1f1e3b4059aebe2"});
        let why = "the committed manifest has no /charon/version";
        assert_eq!(derived(&lacking, &fields), Err(why.to_string()));
    }

    /// A root with the committed manifest and a patch at its path, and an
    /// Aeneas tree that is a Git repository with `a.txt`.
    fn patched(text: &str) -> Scratch {
        let scratch = Scratch::temporary("canary-patch");
        scratch.write(layout().toolchain, COMMITTED);
        let diff = "--- a/a.txt\n+++ b/a.txt\n@@ -1 +1 @@\n-two\n+three\n";
        scratch.write(&patch_path(), diff);
        scratch.write(&format!("{IMAGE}/aeneas/a.txt"), text);
        git(&scratch.0.join(IMAGE).join("aeneas"), &["init", "--quiet"]);
        scratch
    }

    /// The outcomes of a job whose steps succeeded up to `step`, which
    /// ended with `outcome`, and were skipped after it.
    fn ended_at(step: &str, outcome: &str) -> BTreeMap<String, String> {
        let mut at = "success";
        let words = STEPS.split_whitespace().map(|id| {
            let word = if id == step { outcome } else { at };
            if id == step {
                at = "skipped";
            }
            format!("{id}={word}")
        });
        outcomes(&Vec::from_iter(words).join(" "))
    }

    /// Writes the record of the step `step`: `verdict`, `detail` and `data`.
    fn record(root: &Path, step: &str, (verdict, detail, data): (Finding, &str, Value)) {
        fs::create_dir_all(root.join(DIR)).expect("the directory");
        let record = Record {
            data,
            ..found(verdict, detail)
        };
        write(&root.join(DIR).join(format!("{step}.json")), &json!(record)).expect("written");
    }

    #[test]
    fn a_patch_that_does_not_apply_is_one_breakage_that_ends_the_job() {
        let scratch = patched("one\n");
        let (root, layout) = (scratch.0.as_path(), layout());
        let broken = patch(root, &layout);
        assert_eq!(broken.verdict, Finding::Broken, "{broken:?}");
        let why = "the patch does not apply: error: patch failed: a.txt:1";
        assert!(broken.detail.starts_with(why), "{broken:?}");
        // The patch applies to the text that it expects; Git cannot read
        // what is not a patch.
        scratch.write(&format!("{IMAGE}/aeneas/a.txt"), "two\n");
        assert_eq!(patch(root, &layout).verdict, Finding::Passed);
        scratch.write(&patch_path(), "not a patch\n");
        let failed = patch(root, &layout);
        assert_eq!(failed.verdict, Finding::Failed, "{failed:?}");
        // The verdict of the job that ended there.
        for step in ["resolve", "derive"] {
            record(root, step, (Finding::Passed, "", Value::Null));
        }
        record(root, "patch", (broken.verdict, &broken.detail, Value::Null));
        let verdict = verdict(root, &ended_at("patch", "failure"), "abc");
        assert_eq!(verdict.verdict, Finding::Broken, "{verdict:?}");
        assert_eq!(
            verdict.detail,
            format!("patch (main abc): {}", broken.detail)
        );
    }

    #[test]
    fn each_step_writes_its_record_and_exits_with_0_only_when_it_passed() {
        let scratch = patched("one\n");
        let (root, layout) = (scratch.0.as_path(), layout());
        let run = |args: &[&str]| {
            let args = std::iter::once("canary").chain(args.iter().copied());
            let matches = cli("").try_get_matches_from(args).expect("a command line");
            command(root, &layout, &matches)
        };
        let written = |step: &str| json(&root.join(DIR).join(format!("{step}.json")));
        assert_eq!(run(&["patch"]), ExitCode::FAILURE);
        let broken = written("patch").expect("the record");
        assert_eq!(broken["verdict"], "BROKEN");
        let keys = Vec::from_iter(broken.as_object().expect("a record").keys());
        assert_eq!(keys, ["verdict", "detail", "data"]);
        scratch.write(&format!("{IMAGE}/aeneas/a.txt"), "two\n");
        assert_eq!(run(&["patch"]), ExitCode::SUCCESS);
        assert_eq!(written("patch").expect("the record")["verdict"], "PASSED");
        let outcomes = "runner=success disk=failure";
        assert_eq!(run(&["verdict", "--outcomes", outcomes]), ExitCode::FAILURE);
        let verdict = written("verdict").expect("the verdict");
        assert_eq!(verdict["verdict"], "FAILED");
        let detail = verdict["detail"].as_str().expect("a detail");
        assert!(detail.starts_with("disk (main "), "{detail}");
        assert_eq!(verdict["data"], json!({"derive": null, "fill": null}));
        // A record that cannot be written fails the step that passed.
        fs::remove_dir_all(root.join(DIR)).expect("remove the records");
        scratch.write(DIR, "not a directory\n");
        assert_eq!(run(&["patch"]), ExitCode::FAILURE);
    }

    #[test]
    fn fill_records_the_switch_export_and_the_statement_hash() {
        let fixture = Fixture::new("canary-fill");
        let (root, layout) = (fixture.root(), layout());
        let work = root.join("artifacts/hash");
        fs::create_dir_all(&work).expect("a work directory");
        let hash = || {
            let hash = guard::statement_hash(&mut Standalone(root), "HEAD", &layout, &work);
            hash.expect("the statement hash").0
        };
        // Commit A: the derived files, with the statement hash of the pins.
        fixture.write("verification/lean-toolchain", LEAN_TOOLCHAIN);
        fixture.commit_all();
        let pinned = hash();
        let registry = format!("{{\"schema\": 1, \"hash\": \"{pinned}\", \"statements\": []}}\n");
        fixture.write(layout.statements, &registry);
        let path = root.join(layout.toolchain);
        let mut manifest = json(&path).expect("the manifest");
        *manifest.pointer_mut(BUILT).expect("the field") = Value::Null;
        write(&path, &manifest).expect("the manifest");
        fixture.commit_all();
        fixture.write(&format!("{IMAGE}/versions.json"), fixture::VERSIONS);
        let data = json!({"built_committed": "the committed digest"});
        record(root, "derive", (Finding::Passed, "", data));
        let filled = fill(root, &layout).expect("filled");
        assert_eq!(filled.verdict, Finding::Passed);
        let export = value(fixture::VERSIONS)["opam"]["switch_export_sha256"].clone();
        let manifest = json(&path).expect("the manifest");
        assert_eq!(manifest.pointer(BUILT), Some(&export));
        let statements = fs::read_to_string(root.join(layout.statements));
        assert_eq!(
            statements.expect("the registry"),
            registry,
            "the bytes stay"
        );
        let hashes = json!({
            "switch_export_sha256": ["the committed digest", export],
            "statement_hash": [pinned, pinned],
        });
        assert_eq!(filled.data, hashes);
        // A Lean toolchain of Aeneas main changes the statement side.
        fixture.write("verification/lean-toolchain", "leanprover/lean4:v4.36.0\n");
        fixture.commit_all();
        let filled = fill(root, &layout).expect("filled");
        let head = hash();
        assert_ne!(head, pinned);
        let statements = json(&root.join(layout.statements)).expect("the registry");
        let expected = json!({"schema": 1, "hash": head, "statements": []});
        assert_eq!(statements, expected);
        assert_eq!(filled.data["statement_hash"], json!([pinned, head]));
        // An image without the digest of its switch export.
        fixture.write(&format!("{IMAGE}/versions.json"), "{\"opam\": {}}\n");
        let defect = fill(root, &layout).expect_err("no switch export");
        assert_eq!(defect.verdict, Finding::Defect, "{defect:?}");
    }

    /// The finding of a build that exited with `status` and wrote `log`.
    fn built_with(status: Option<&str>, log: &str) -> Record {
        let scratch = Scratch::temporary("canary-build");
        if let Some(status) = status {
            scratch.write(&format!("{DIR}/build-status"), &format!("{status}\n"));
        }
        scratch.write(&format!("{IMAGE}/build.log"), log);
        build(&scratch.0)
    }

    /// A plain BuildKit log of a build whose step `step`, `[<stage> i/k]`,
    /// printed `output` and failed, while the step of another stage was
    /// cancelled.
    fn failure(step: &str, output: &[&str]) -> String {
        failure_of(
            step,
            "source /pins/recipe.sh;     commit=$(pin .charon.commit)",
            output,
        )
    }

    /// The `RUN` script of the recipe that holds `text`, with its lines
    /// joined as BuildKit names its step.
    fn script(text: &str) -> String {
        let dockerfile = include_str!("../../../verification/image/Dockerfile");
        let joined = dockerfile.replace("\\\n", "");
        let runs = joined.lines().filter_map(|line| line.strip_prefix("RUN "));
        let [run] = Vec::from_iter(runs.filter(|run| run.contains(text)))[..] else {
            panic!("one RUN that holds {text}");
        };
        run.to_string()
    }

    /// [`failure`] of a step whose `RUN` script is `script`.
    fn failure_of(step: &str, script: &str, output: &[&str]) -> String {
        let run = format!("[{step}] RUN {script}");
        let quoted = script.replace('"', "\\\"");
        let process = format!("process \"/bin/bash -euo pipefail -c {quoted}\"");
        let error = format!("{process} did not complete successfully: exit code: 1");
        let mut log = Vec::from(["#1 [internal] load build definition from Dockerfile"]);
        log.extend([
            "#1 DONE 0.0s",
            "#5 [base 1/5] FROM docker.io/library/ubuntu:noble",
        ]);
        let mut log = Vec::from_iter(log.into_iter().map(str::to_string));
        log.push(format!("#12 {run}"));
        log.extend(output.iter().map(|line| format!("#12 61.20 {line}")));
        log.push(format!("#12 ERROR: {error}"));
        log.push("#13 [lean 1/1] RUN source /pins/recipe.sh\n#13 CANCELED\n------".to_string());
        log.push(format!(" > {run}:"));
        log.extend(output.iter().map(|line| format!("61.20 {line}")));
        log.push(format!(
            "------\nDockerfile:168\nERROR: failed to solve: {error}\n"
        ));
        log.join("\n")
    }

    #[test]
    fn a_failed_build_is_classed_by_its_stage_its_error_and_its_status() {
        use Finding::{Broken, Defect, Failed};
        let cargo = ["error[E0425]: cannot find value `x` in this scope"];
        let lean = ["lean reports Lean (version 4.36.1); the manifest pins 4.36.0"];
        let apt = ["E: Unable to locate package zstd"];
        let disk = ["write /usr/lib/x.so: no space left on device"];
        let cancelled = ["ERROR: failed to fetch: context canceled"];
        let cases: [(&str, &[&str], Finding); 5] = [
            ("charon-build 2/2", &cargo, Broken),
            ("lean 1/1", &lean, Defect),
            ("base 2/5", &apt, Failed),
            ("aeneas-build 4/5", &disk, Failed),
            ("backend 2/2", &cancelled, Failed),
        ];
        for (step, output, verdict) in cases {
            let record = built_with(Some("1"), &failure(step, output));
            assert_eq!(record.verdict, verdict, "{record:?}");
            let stage = step.split(' ').next().expect("a stage");
            let why = format!("the stage {stage} failed:\n#12 ERROR: process");
            assert!(record.detail.starts_with(&why), "{record:?}");
            assert!(record.detail.ends_with(output[0]), "{record:?}");
        }
        // The script that the error line quotes and the first line of the
        // block hold the recipe's own texts, which do not class the step,
        // also when the step printed nothing.
        let glibc = ["lean: /lib/aarch64-linux-gnu/libc.so.6: version `GLIBC_2.40' not found"];
        let dune = [
            "File \"src/Main.ml\", line 3, characters 2-5:",
            "Error: Unbound value foo",
        ];
        let component = ["error: component 'rustc-dev' for target \
            'aarch64-unknown-linux-gnu' is unavailable for download for channel 'nightly-2026-10-01'"];
        let resolve = ["curl: (6) Could not resolve host: github.com"];
        let opam = ["[ERROR] The compilation of ocamlfind.1.9.8 failed at \"make all\"."];
        let patched = ["error: patch failed: src/extract/Extract.ml:12"];
        let jq = ["jq: error (at <stdin>:3): Cannot index string with \"version\""];
        let cases: [(&str, &str, &[&str], Finding); 10] = [
            ("lean 1/1", "lean reports ", &glibc, Broken),
            ("lean 1/1", "lean reports ", &[], Broken),
            ("lean 1/1", "lean reports ", &resolve, Failed),
            ("lean 1/1", "lean reports ", &lean, Defect),
            ("rust-toolchain 1/1", "rustup reports ", &component, Broken),
            (
                "aeneas-source 2/2",
                "the Lake lock pins Mathlib ",
                &patched,
                Broken,
            ),
            ("aeneas-build 1/4", "opam reports ", &opam, Broken),
            (
                "aeneas-build 4/4",
                "the switch export has SHA-256 ",
                &dune,
                Broken,
            ),
            (
                "aeneas-build 4/4",
                "the switch export has SHA-256 ",
                &disk,
                Failed,
            ),
            ("versions 7/7", "base_image: ", &jq, Failed),
        ];
        for (step, text, output, verdict) in cases {
            let script = script(text);
            let record = built_with(Some("1"), &failure_of(step, &script, output));
            assert_eq!(record.verdict, verdict, "{step} {output:?}: {record:?}");
            assert!(record.detail.contains(&script), "{record:?}");
        }
        // BuildKit's own error of a step, as of a copy or a snapshot, is on
        // the error line only, and the block may show no output.
        let own = |step: &str, error: &str, output: &str| {
            format!("#25 {step}\n#25 ERROR: {error}\n------\n > {step}:\n{output}------\n")
        };
        let copy = "[aeneas-build 3/5] COPY --from=aeneas-source /src/aeneas /src/aeneas";
        let run = "[lean 1/1] RUN source /pins/recipe.sh";
        let copied = "failed to copy files: copy file range failed: no space left on device";
        let prepared = "failed to prepare sha256:abc as def: write /var/x: no space left on device";
        let missing = "failed to compute cache key: \"/src/aeneas\" not found";
        let cases = [
            (copy, copied, "", Failed),
            (run, prepared, "61.20 hi\n", Failed),
            (copy, missing, "", Broken),
        ];
        for (step, error, output, verdict) in cases {
            let record = built_with(Some("1"), &own(step, error, output));
            assert_eq!(record.verdict, verdict, "{step} {error}: {record:?}");
            assert!(record.detail.contains(error), "{record:?}");
        }
        // The first error names the stage, not a later failure block.
        let later = failure("charon-build 2/2", &cargo);
        let record = built_with(Some("1"), &(failure("lean 1/1", &lean) + &later));
        assert_eq!(record.verdict, Defect, "{record:?}");
        // A log without a failure block after an error, a limit and a
        // runner that ended the step fail the run.
        let steps = "#12 [lean 1/1] RUN source /pins/recipe.sh\n#12 DONE 9.0s\n\
            #20 [backend 1/2] COPY --from=aeneas-source /src/aeneas/backends/lean /opt\n\
            #21 [backend 2/2] RUN source /pins/recipe.sh;     lake exe cache get\n\
            #21 1000.00 Building Mathlib\n#21 CANCELED\n\
            ERROR: failed to solve: Canceled: context canceled\n";
        let record = built_with(Some("1"), steps);
        assert_eq!(record.verdict, Failed, "{record:?}");
        assert!(record.detail.contains("no failure block"), "{record:?}");
        for status in ["124", "137"] {
            let record = built_with(Some(status), &(later.clone() + steps));
            assert_eq!(record.verdict, Failed, "{record:?}");
            let why = "limit of 52 minutes; the last stage that started: backend";
            assert!(record.detail.ends_with(why), "{record:?}");
        }
        let record = built_with(None, &later);
        assert_eq!(record.verdict, Failed, "{record:?}");
        assert!(record.detail.contains("step limit"), "{record:?}");
    }

    #[test]
    fn the_texts_of_the_verdict_are_messages_of_the_recipe_and_the_gate() {
        let dockerfile = include_str!("../../../verification/image/Dockerfile");
        let recipe = include_str!("../../../verification/image/recipe.sh");
        let (run, base) = (include_str!("run.rs"), include_str!("base.rs"));
        let sources = [dockerfile, recipe, run, base];
        // sha256sum, which `check_sha256` of the recipe runs with --check,
        // writes this text itself.
        let sha256sum = "computed checksum did NOT match";
        assert!(recipe.contains("| sha256sum --check --strict"));
        assert!(DEFECTS.split('|').any(|text| text == sha256sum));
        for text in DEFECTS.split('|').filter(|text| *text != sha256sum) {
            assert!(sources.iter().any(|source| source.contains(text)), "{text}");
        }
        // The texts of the disk, the network and a cancelled build are the
        // system's; the others are the gate's checks of its inputs.
        let system = "No space left on device|no space left on device|context canceled|\
            Could not resolve host|Temporary failure in name resolution|Connection timed out";
        let system = Vec::from_iter(system.split('|'));
        let (own, gate): (Vec<&str>, _) = FAILURES.split('|').partition(|t| system.contains(t));
        assert_eq!(own, system);
        for text in gate {
            assert!(run.contains(text), "{text}");
        }
        // A text of a defect counts before one of a failure of the run.
        let disk = "write /usr/lib/x.so: no space left on device";
        let both = format!("lean reports Lean (version 4.36.1)\n{disk}");
        assert_eq!(by_text(&both, Finding::Broken), Finding::Defect);
        assert_eq!(by_text(disk, Finding::Broken), Finding::Failed);
        assert_eq!(by_text("error: no", Finding::Broken), Finding::Broken);
        // Every stage of the recipe is a tool stage or one of the others.
        let named = dockerfile.lines().filter_map(|line| {
            let (from, name) = line.strip_prefix("FROM ")?.split_once(" AS ")?;
            (!from.is_empty()).then_some(name.trim())
        });
        let others = "base gmp runtime runtime-versions notices versions image";
        let listed = Vec::from_iter(TOOL_STAGES.split(' ').chain(others.split(' ')));
        let stages = BTreeSet::from_iter(listed.iter().copied());
        assert_eq!(BTreeSet::from_iter(named), stages);
        assert_eq!(stages.len(), listed.len());
    }

    /// The text of a receipt of `status`, complete or not, with `units` of
    /// their status and reason and `failures`.
    fn receipt(
        status: Status,
        complete: bool,
        units: &[(&str, Status, &str)],
        failures: &[(Status, &str)],
    ) -> String {
        let units = units.iter().map(|(name, status, reason)| {
            let (phase, status) = ("base".to_string(), *status);
            let reason = (!reason.is_empty()).then(|| reason.to_string());
            (
                name.to_string(),
                Unit {
                    phase,
                    status,
                    reason,
                },
            )
        });
        let failures = failures.iter().map(|(status, message)| {
            let message = message.to_string();
            Failure {
                status: *status,
                message,
            }
        });
        receipt::render(&Receipt {
            status,
            complete,
            units: units.collect(),
            failures: failures.collect(),
            ..Receipt::default()
        })
    }

    /// The finding of a gate that exited with `status` and left `receipts`.
    fn gated(status: Option<&str>, receipts: &[&str]) -> Record {
        let scratch = Scratch::temporary("canary-gate");
        if let Some(status) = status {
            scratch.write(&format!("{DIR}/gate-status"), &format!("{status}\n"));
        }
        for (run, text) in receipts.iter().enumerate() {
            scratch.write(&format!("{}/{run}/receipt.json", run::RUNS), text);
        }
        fs::create_dir_all(scratch.0.join(run::RUNS).join("vectors/logs")).expect("a run");
        gate(&scratch.0)
    }

    #[test]
    fn the_gate_is_classed_by_its_status_and_receipt() {
        use Status::{Rejected, ToolFailure, Verified};
        let verified = receipt(Verified, true, &[("base", Verified, "")], &[]);
        let record = gated(Some("0"), &[&verified]);
        assert_eq!(record.verdict, Finding::Passed, "{record:?}");
        let changed = [("qualification", Rejected, "the case slices changed")];
        let rejected = receipt(Rejected, true, &changed, &[]);
        let record = gated(Some("1"), &[&rejected]);
        assert_eq!(record.verdict, Finding::Broken, "{record:?}");
        let why = "the gate exited with 1, REJECTED; units that are not VERIFIED: qualification";
        assert!(record.detail.starts_with(why), "{record:?}");
        let image = "image: /charon/version is \"0.1.313 (8cae)\", not \"0.1.312 (8cae)\"";
        let image = receipt(ToolFailure, false, &[], &[(ToolFailure, image)]);
        let record = gated(Some("1"), &[&image]);
        assert_eq!(record.verdict, Finding::Defect, "{record:?}");
        assert!(
            record.detail.ends_with(
                "failures: image: /charon/version is \"0.1.313 (8cae)\", not \"0.1.312 (8cae)\""
            ),
            "{record:?}"
        );
        for status in [Status::Budget, Status::Stale] {
            let receipt = receipt(status, true, &[("base", status, "")], &[]);
            let record = gated(Some("1"), &[&receipt]);
            assert_eq!(record.verdict, Finding::Broken, "{record:?}");
        }
        let hash = "statements.json records a, the statement side of the snapshot is b";
        let hash = receipt(Rejected, true, &[("base", Rejected, hash)], &[]);
        assert_eq!(gated(Some("1"), &[&hash]).verdict, Finding::Defect);
        let unclean = "the gate inputs are not clean at the start of the run: verification";
        let unclean = receipt(ToolFailure, false, &[], &[(ToolFailure, unclean)]);
        let unverified = receipt(Verified, false, &[], &[]);
        // A run that the disk guard refused is no verdict on the tools.
        let refused = "the file system of the run directory had 1 bytes available at the start, less than 1.5 times the disk peak of the parts of the run, 8589934592 bytes";
        let (refused, units) = ([(Status::NotRun, refused)], [("base", Status::NotRun, "")]);
        let refused = receipt(Status::NotRun, false, &units, &refused);
        let failed = [
            gated(Some("1"), &[&refused]),
            gated(Some("1"), &[&unclean]),
            gated(Some("125"), &[&rejected]),
            gated(Some("0"), &[&rejected]),
            gated(Some("0"), &[&unverified]),
            gated(Some("1"), &[&verified]),
            gated(None, &[&rejected]),
            gated(Some("1"), &[&rejected, &rejected]),
            gated(Some("1"), &[]),
            gated(Some("1"), &["{\"status\": \"REJECTED\"}\n"]),
            gated(Some("1"), &[&rejected, "not a receipt"]),
        ];
        for record in failed {
            assert_eq!(record.verdict, Finding::Failed, "{record:?}");
        }
    }

    #[test]
    fn a_step_that_passes_without_its_record_or_is_skipped_fails_the_run() {
        let scratch = Scratch::temporary("canary-verdict");
        let root = scratch.0.as_path();
        let verified = receipt(Status::Verified, true, &[], &[]);
        scratch.write(&format!("{}/1/receipt.json", run::RUNS), &verified);
        scratch.write(&format!("{DIR}/gate-status"), "0\n");
        for step in RECORDED.split(' ') {
            record(root, step, (Finding::Passed, "", json!({"step": step})));
        }
        let all = ended_at("none", "none");
        let passed = verdict(root, &all, "abc");
        assert_eq!(passed.verdict, Finding::Passed, "{passed:?}");
        assert!(passed.detail.starts_with("gate (main abc): "), "{passed:?}");
        let data = json!({"derive": {"step": "derive"}, "fill": {"step": "fill"}});
        assert_eq!(passed.data, data);
        let with = |step: &str, outcome: Option<&str>| {
            let mut outcomes = all.clone();
            match outcome {
                Some(outcome) => outcomes.insert(step.to_string(), outcome.to_string()),
                None => outcomes.remove(step),
            };
            outcomes
        };
        let failed = [
            (with("probe", Some("skipped")), "probe"),
            (with("build", Some("cancelled")), "build"),
            (with("sampler", None), "sampler"),
            (ended_at("fetch", "failure"), "fetch"),
            (ended_at("resolve", "failure"), "resolve"),
        ];
        for (outcomes, step) in failed {
            let record = verdict(root, &outcomes, "abc");
            assert_eq!(record.verdict, Finding::Failed, "{record:?}");
            let why = format!("{step} (main abc): ");
            assert!(record.detail.starts_with(&why), "{record:?}");
        }
        // Failed tool checks are a defect; a failed derivation gives its
        // record.
        let checks = "ok    patch: ...\nFAIL  hosts: no\n";
        scratch.write(&format!("{DIR}/toolchain-check.txt"), checks);
        let defect = verdict(root, &ended_at("toolchain-check", "failure"), "abc");
        assert_eq!(defect.verdict, Finding::Defect, "{defect:?}");
        assert!(defect.detail.ends_with("FAIL  hosts: no"), "{defect:?}");
        let why = "Aeneas names no release";
        record(root, "derive", (Finding::Broken, why, Value::Null));
        let broken = verdict(root, &ended_at("derive", "failure"), "abc");
        assert_eq!(broken.verdict, Finding::Broken, "{broken:?}");
        assert_eq!(broken.detail, format!("derive (main abc): {why}"));
        // A step that succeeded without a record that passed.
        for text in ["{", ""] {
            scratch.write(&format!("{DIR}/derive.json"), text);
            let failed = verdict(root, &all, "abc");
            assert_eq!(failed.verdict, Finding::Failed, "{failed:?}");
            assert!(
                failed.detail.starts_with("derive (main abc): "),
                "{failed:?}"
            );
        }
        fs::remove_file(root.join(DIR).join("resolve.json")).expect("remove the record");
        let failed = verdict(root, &all, "abc");
        assert!(
            failed.detail.starts_with("resolve (main abc): "),
            "{failed:?}"
        );
        // A failed build is classed by its log, and a failed gate by its
        // status and receipt.
        for step in ["resolve", "derive"] {
            record(root, step, (Finding::Passed, "", Value::Null));
        }
        let cargo = ["error[E0425]: cannot find value `x` in this scope"];
        scratch.write(&format!("{DIR}/build-status"), "1\n");
        scratch.write(
            &format!("{IMAGE}/build.log"),
            &failure("charon-build 2/2", &cargo),
        );
        let broken = verdict(root, &ended_at("build", "failure"), "abc");
        assert_eq!(broken.verdict, Finding::Broken, "{broken:?}");
        let why = "build (main abc): the stage charon-build failed:\n";
        assert!(broken.detail.starts_with(why), "{broken:?}");
        let receipts = root.join(run::RUNS).join("1/receipt.json");
        let rejected = receipt(
            Status::Rejected,
            true,
            &[("base", Status::Rejected, "")],
            &[],
        );
        fs::write(&receipts, &rejected).expect("the receipt");
        scratch.write(&format!("{DIR}/gate-status"), "1\n");
        let broken = verdict(root, &ended_at("gate", "failure"), "abc");
        assert_eq!(broken.verdict, Finding::Broken, "{broken:?}");
        let why = "gate (main abc): the gate exited with 1, REJECTED; ";
        assert!(broken.detail.starts_with(why), "{broken:?}");
        // After the last step, the gate must still have exited with 0 and
        // left one complete VERIFIED receipt.
        scratch.write(&format!("{DIR}/gate-status"), "0\n");
        let incomplete = receipt(Status::Verified, false, &[], &[]);
        for receipt in [Some(incomplete), Some(rejected), None] {
            match &receipt {
                Some(receipt) => fs::write(&receipts, receipt).expect("the receipt"),
                None => fs::remove_file(&receipts).expect("remove the receipt"),
            }
            let failed = verdict(root, &all, "abc");
            assert_eq!(failed.verdict, Finding::Failed, "{failed:?}");
            assert!(failed.detail.starts_with("gate (main abc): "), "{failed:?}");
        }
    }

    /// The steps of the only job of `workflow`: the name and lines of each.
    fn steps(workflow: &str) -> Vec<(&str, Vec<&str>)> {
        let steps = workflow.split("\n      - name: ").skip(1);
        let steps = steps.map(|step| step.split_once('\n').unwrap_or((step, "")));
        let steps = steps.map(|(name, rest)| (name, Vec::from_iter(rest.lines())));
        steps.collect()
    }

    /// The lines of the step `name` of `workflow` without its id, limit and
    /// condition, and without the comments after it and the lines `dropped`.
    fn step(workflow: &str, name: &str, dropped: &[&str]) -> Vec<String> {
        let found = steps(workflow).into_iter().find(|(step, _)| *step == name);
        let lines = found.expect(name).1.into_iter();
        let kept = lines.take_while(|line| line.is_empty() || line.starts_with("        "));
        let kept = kept.filter(|line| {
            let key = line.trim_start();
            let own = ["id:", "timeout-minutes:", "if:"]
                .iter()
                .any(|k| key.starts_with(k));
            !(own && line.len() - key.len() == 8) && !dropped.contains(&key)
        });
        let mut kept = Vec::from_iter(kept.map(str::to_string));
        while kept.last().is_some_and(|line| line.is_empty()) {
            kept.pop();
        }
        kept
    }

    #[test]
    fn the_job_ends_at_the_first_step_that_does_not_pass() {
        let steps = steps(CANARY);
        let names = Vec::from_iter(steps.iter().map(|(name, _)| *name));
        assert_eq!(names.len(), 20);
        let always = (steps.iter()).filter(|(_, lines)| lines.contains(&"        if: always()"));
        let always = Vec::from_iter(always.map(|(name, _)| *name));
        assert_eq!(always, names[15..], "the steps that record the run");
        for (name, lines) in &steps[..15] {
            let condition = (lines.iter()).any(|line| line.trim_start().starts_with("if:"));
            assert!(
                !condition,
                "{name} runs only when each step before it passed"
            );
        }
        assert!(!CANARY.contains("continue-on-error"));
        let ids = (CANARY.lines()).filter_map(|line| line.strip_prefix("        id: "));
        let ids = Vec::from_iter(ids);
        assert_eq!(ids, Vec::from_iter(STEPS.split_whitespace()));
        let first = (steps[1..15].iter()).map(|(_, lines)| lines.first().copied());
        let first = Vec::from_iter(first.map(|line| line.unwrap_or_default()));
        let named = Vec::from_iter(ids.iter().map(|id| format!("        id: {id}")));
        assert_eq!(first, named, "steps 2 to 15 have an id");
        // The verdict reads the outcome of each of them.
        for id in &ids {
            let outcome = format!("{id}=${{{{ steps.{id}.outcome }}}}");
            assert!(CANARY.contains(&outcome), "{outcome}");
        }
    }

    #[test]
    fn the_canary_workflow_runs_weekly_reads_only_and_publishes_nothing() {
        let path = ".github/workflows/formal-canary.yml";
        let problems = crate::workflows::check([(path, Some(CANARY.as_bytes()))]);
        assert_eq!(problems, Vec::<String>::new());
        assert!(!crate::workflows::runs_on_pull_request(CANARY));
        let on = "\non:\n  schedule:\n    - cron: \"17 9 * * 6\"\n  workflow_dispatch:\n\n";
        assert!(
            CANARY.contains(&format!("{on}concurrency:")),
            "a weekly and a manual run"
        );
        let once = |text: &str| CANARY.matches(text).count() == 1;
        assert!(once("\non:") && once("cron:") && once("permissions:"));
        let job = "    timeout-minutes: 240\n    permissions:\n      contents: read\n    env:\n";
        assert!(CANARY.contains(job), "the job may only read the contents");
        let main = "    if: github.ref == 'refs/heads/main'\n    runs-on: ubuntu-24.04-arm\n";
        assert!(CANARY.contains(main), "a run tests main only");
        // Charon is fetched for a charon-pin of one line that is not a
        // comment, the lines that `toolchain::pinned_charon` reads.
        let lines = "grep -Ev '^[[:space:]]*(#|$)' \"$pin\"";
        let fetched = format!("charon=$({lines} | tr -d '[:space:]') || true");
        let one = "if [ \"$(grep -cEv '^[[:space:]]*(#|$)' \"$pin\")\" = 1 ]; then";
        let pinned = CANARY.contains(&fetched) && CANARY.contains(one);
        assert!(pinned, "the lines of charon-pin");
        let limits =
            (CANARY.lines()).filter_map(|line| line.trim().strip_prefix("timeout-minutes: "));
        let limits = Vec::from_iter(limits.map(|limit| limit.parse::<u32>().expect("minutes")));
        assert_eq!(limits[0], 240);
        assert_eq!(
            limits.len() - 1,
            steps(CANARY).len(),
            "each step has a limit"
        );
        assert!(limits[1..].iter().sum::<u32>() <= 235, "{limits:?}");
        let words = "docker login|docker push|packages:|secrets|ghcr.io|KREPI_FORMAL_IMAGE|\
            : write|write-all|id-token";
        for word in words.split('|') {
            assert!(!CANARY.contains(word), "{word}");
        }
        // The steps copied from the image build and from the job of the gate.
        let copied = [
            (BUILD, "Record the disk and remove preinstalled software"),
            (BUILD, "Sample the disk every 15 seconds"),
            (BUILD, "Fetch the pinned Aeneas and Charon sources"),
            (BUILD, "Record the image"),
            (BUILD, "Summarize the disk measurement"),
            (FORMAL, "Build xtask"),
            (FORMAL, "Probe the container of the gate"),
            (FORMAL, "Remove the container of the gate"),
            (FORMAL, "Summarize the receipt"),
        ];
        for (source, name) in copied {
            assert_eq!(step(CANARY, name, &[]), step(source, name, &[]), "{name}");
        }
        let check = "Check the sources and the patch against the manifest";
        let tee = ["2>&1 | tee artifacts/canary/toolchain-check.txt"];
        assert_eq!(step(CANARY, check, &tee), step(BUILD, check, &[]));
        let gate = "Run the gate in the image";
        let image = "--env KREPI_FORMAL_IMAGE=\"$IMAGE\" \\";
        // The deadline and the command line alone differ: the canary runs
        // the whole gate, whose deadline is the gate's, the budgets of the
        // formal targets, which it selects, and that of its receipt, and
        // keeps its exit status for the verdict; the job of `formal` runs
        // the qualification part, whose deadline adds the extraction of the
        // formal targets. Each step ends a minute after `deadline.sh` kills
        // the gate. Registering a formal target thus fails this test until
        // the deadline and the limits of the canary grow by its budget.
        let xtask = "\"$IMAGE\" \"$GITHUB_WORKSPACE/xtask/target/debug/xtask\" formal run";
        let (whole, part) = (
            xtask.to_string(),
            format!("{xtask} --shard qualification --keep"),
        );
        let minutes = |seconds: u64| seconds.div_ceil(60);
        let gate_seconds = run::GATE_BUDGET.as_secs() + run::RECEIPT_MARGIN.as_secs();
        let extraction = crate::formal::merge::EXTRACTION_MARGIN.as_secs();
        let registry = include_str!("../../../verification/targets.json");
        let targets = crate::formal::registry::parse(registry)
            .expect("the registry")
            .targets;
        let formal = targets
            .iter()
            .filter(|t| t.state == crate::formal::registry::State::Formal);
        let budgets = formal.map(|target| target.budget).sum::<u64>();
        let own = minutes(gate_seconds + budgets);
        let theirs = minutes(gate_seconds + extraction);
        let deadline = |options: &str, minutes: u64| {
            format!("exec bash .github/scripts/deadline.sh {options} {minutes}m 1m \\")
        };
        let status = "--stop-commands --status artifacts/canary/gate-status";
        let (canary, formal) = (deadline(status, own), deadline("--stop-commands", theirs));
        let has = |workflow, line: &str| {
            let lines = step(workflow, gate, &[]);
            lines.iter().any(|l| l.trim_start() == line)
        };
        assert!(has(CANARY, &whole) && has(FORMAL, &part));
        assert!(has(CANARY, &canary) && has(FORMAL, &formal), "{canary}");
        let limit = |workflow: &str, minutes: u64| {
            let (_, lines) = (steps(workflow).into_iter())
                .find(|(name, _)| *name == gate)
                .expect(gate);
            lines.contains(&format!("        timeout-minutes: {}", minutes + 2).as_str())
        };
        assert!(limit(CANARY, own) && limit(FORMAL, theirs));
        let formal_lines = step(FORMAL, gate, &[image]).into_iter();
        let formal_lines =
            formal_lines.map(|line| line.replace(&part, &whole).replace(&formal, &canary));
        assert_eq!(step(CANARY, gate, &[]), Vec::from_iter(formal_lines));
        let build = |workflow: &'static str| {
            let start = workflow
                .find("docker build --progress=plain")
                .expect("the build");
            let end = workflow[start..].find("| tee artifacts/image/build.log");
            &workflow[start..start + end.expect("its log")]
        };
        assert_eq!(build(CANARY), build(BUILD));
        let flags = |workflow: &'static str| {
            let flags = workflow.lines().map(str::trim_start);
            (flags.filter(|line| line.starts_with("GATE_FLAGS: "))).collect::<Vec<_>>()
        };
        assert_eq!(flags(CANARY), flags(FORMAL));
    }

    #[test]
    fn the_upgrade_manual_is_a_skill_file() {
        let rest = MANUAL.strip_prefix("---\nname: formal-upgrade\ndescription: ");
        let (description, rest) = (rest.and_then(|rest| rest.split_once('\n'))).expect("a header");
        assert!(!description.trim().is_empty() && !description.contains("cargo xtask"));
        let header = rest.starts_with("---\n\n# Formal upgrade\n");
        assert!(header, "a description of one line");
        let costs = "| Proof | Pull request | Hours | Heartbeats | Cause |";
        assert!(
            MANUAL.lines().any(|line| line == costs),
            "the fields of the cost"
        );
    }
}
