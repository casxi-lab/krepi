//! A Git repository that holds the gate inputs in a minimal form, for the
//! tests of `cargo xtask formal run`: a kernel workspace with one crate and
//! its `Cargo.lock`, a target registry without targets, an empty shard
//! plan, a file for each other gate input, and the committed tool manifest
//! with the installation at `artifacts/formal/tools`, which holds only
//! scripts that start the Cargo and `rustc` of the build, the fake tools
//! that a test installs, the version manifest of the pinned image, which a
//! run on the CI host compares with the tool manifest, and the directories
//! of the Aeneas Lean library and of Lean, which a run lists before its
//! first phase and after its last.
//! Commits have a fixed identity and date, and Git reads no system or global
//! configuration.
//!
//! The fixture of the qualification adds the qualification crate with its
//! cases and the stand-ins for the tools: shell scripts in the installation.
//! Charon writes the LLBC file that it is asked for. Aeneas writes, for the
//! module path of its `-subdir`, what the pinned Aeneas wrote for a captured
//! shape of the qualification crate (the fixtures of `extract.rs`) when the
//! test names one, and otherwise a translation without items in an empty
//! `Types.lean` and `Funs.lean`; it prints the log and exits with the status
//! that the test gives the module. Lake and `lean` are described at
//! [`LAKE`] and [`LEAN`].

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

use serde_json::{Value, json};

use super::lean;
use super::outcome::Status;
use super::paths::Git;
use super::receipt;
use super::run::tests::Done;
use super::toolchain::environment::SYSTEM_PATH;
use crate::scratch::Scratch;

/// The committed tool manifest.
const MANIFEST: &str = include_str!("../../../verification/toolchain.json");

/// The version manifest of the pinned image, `/opt/krepi-formal/versions.json`.
pub const VERSIONS: &str = include_str!("fixtures/image/versions.json");

/// The Cargo that builds the tests.
const CARGO: &str = env!("CARGO");

pub struct Fixture {
    scratch: Scratch,
}

impl Fixture {
    /// A new repository with one commit of the gate inputs, outside the
    /// repository of the build, whose Cargo configuration would otherwise
    /// lie above the export of every run.
    pub fn new(label: &str) -> Fixture {
        let fixture = Fixture {
            scratch: Scratch::temporary(label),
        };
        fixture.git(&["-c", "init.defaultBranch=main", "init", "--quiet"]);
        fixture.write(".gitignore", "/artifacts/\n");
        fixture.write("README.md", "A fixture of the proof gate.\n");
        fixture.write(
            "kernel/Cargo.toml",
            "[workspace]\nresolver = \"3\"\nmembers = [\"abi\"]\n",
        );
        fixture.write(
            "kernel/abi/Cargo.toml",
            "[package]\nname = \"abi\"\nedition = \"2024\"\n",
        );
        fixture.write("kernel/abi/src/lib.rs", "");
        fixture.lock();
        fixture.write(
            "verification/targets.json",
            "{\"schema\": 2, \"specifications\": [], \"targets\": []}\n",
        );
        fixture.write(
            "verification/shards.json",
            "{\"schema\": 1, \"parts\": []}\n",
        );
        let local = MANIFEST.replace(
            "\"prefix\": \"/opt/krepi-formal\"",
            "\"prefix\": \"artifacts/formal/tools\"",
        );
        assert_ne!(local, MANIFEST, "the CI column names /opt/krepi-formal");
        fixture.write("verification/toolchain.json", &local);
        fixture.write("xtask/README", "The repository tasks.\n");
        fixture.write(".github/workflows/check.yml", "name: check\n");
        fixture.write(".cargo/config.toml", "# Cargo configuration.\n");
        fixture.write("rust-toolchain.toml", "[toolchain]\nchannel = \"1.99.0\"\n");
        fixture.write("toolchains.toml", "# Tool versions.\n");
        let bin = Path::new("artifacts/formal/tools/cargo/bin");
        let rustc = Path::new(CARGO).with_file_name("rustc");
        for (name, program) in [("cargo", Path::new(CARGO)), ("rustc", rustc.as_path())] {
            let program = program.to_str().expect("a UTF-8 path");
            assert!(!program.contains('\''), "{program}");
            let path = bin.join(name);
            let path = path.to_str().expect("a UTF-8 path");
            fixture.write(path, &format!("#!/bin/sh\nexec '{program}' \"$@\"\n"));
            fixture.chmod(path, 0o755);
        }
        // Whatever the umask, the installation has no write bit for the
        // group or others, which a run on the CI host refuses. A run lists
        // the Aeneas Lean library and Lean before its first phase and after
        // its last.
        fixture.write("artifacts/formal/tools/versions.json", VERSIONS);
        fixture.write("artifacts/formal/tools/backend/.lake/packages/README", "");
        fixture.write("artifacts/formal/tools/lean/bin/README", "");
        fixture.chmod("artifacts/formal/tools", 0o755);
        fixture.commit_all();
        fixture
    }

    pub fn root(&self) -> &Path {
        &self.scratch.0
    }

    /// Writes `text` to the relative path `path`, with its directories.
    pub fn write(&self, path: &str, text: &str) {
        self.scratch.write(path, text);
    }

    /// Sets the permission bits of the relative path `path`.
    pub fn chmod(&self, path: &str, mode: u32) {
        fs::set_permissions(self.root().join(path), fs::Permissions::from_mode(mode))
            .expect("set the permissions");
    }

    /// Installs the fake tool `name`, the shell script `script`, in the
    /// directory of `aeneas`, `charon` and `charon-driver` of the
    /// installation, which the tool commands find through `PATH`.
    pub fn tool(&self, name: &str, script: &str) {
        let path = format!("artifacts/formal/tools/bin/{name}");
        self.write(&path, &format!("#!/bin/sh\n{script}\n"));
        self.chmod(&path, 0o755);
    }

    /// Creates the symbolic link `path` to `target`.
    pub fn symlink(&self, path: &str, target: &str) {
        std::os::unix::fs::symlink(target, self.root().join(path)).expect("create a link");
    }

    /// Writes `kernel/Cargo.lock`, offline.
    pub fn lock(&self) {
        self.scratch.lock();
    }

    /// Commits every change.
    pub fn commit_all(&self) {
        self.git(&["add", "--all"]);
        self.git(&["commit", "--quiet", "--no-verify", "--message", "fixture"]);
    }

    /// Runs Git with `args` and returns its standard output; Git must
    /// succeed.
    pub fn git(&self, args: &[&str]) -> String {
        let output = self
            .run_git(args, None)
            .unwrap_or_else(|error| panic!("git {}: {error}", args.join(" ")));
        String::from_utf8(output).expect("UTF-8 output")
    }

    /// Runs Git with `args` and the input `stdin`, with a fixed identity and
    /// date and without system or global configuration.
    fn run_git(&self, args: &[&str], stdin: Option<&Path>) -> Result<Vec<u8>, String> {
        let mut command = Command::new("git");
        command
            .args(args)
            .current_dir(self.root())
            .env_clear()
            .env("PATH", SYSTEM_PATH)
            .env("HOME", self.root())
            .env("GIT_CONFIG_NOSYSTEM", "1")
            .env("GIT_CONFIG_GLOBAL", "/dev/null");
        for role in ["AUTHOR", "COMMITTER"] {
            command
                .env(format!("GIT_{role}_NAME"), "Fixture")
                .env(format!("GIT_{role}_EMAIL"), "fixture@example.invalid")
                .env(format!("GIT_{role}_DATE"), "2026-01-01T00:00:00Z");
        }
        match stdin {
            Some(path) => command.stdin(fs::File::open(path).map_err(|error| error.to_string())?),
            None => command.stdin(Stdio::null()),
        };
        let output = command.output().map_err(|error| error.to_string())?;
        if output.status.success() {
            Ok(output.stdout)
        } else {
            Err(String::from_utf8_lossy(&output.stderr).into_owned())
        }
    }
}

impl Git for Fixture {
    fn git(&mut self, args: &[&str], stdin: Option<&Path>) -> Result<Vec<u8>, String> {
        let args: Vec<&str> = ["--literal-pathspecs", "--no-optional-locks"]
            .into_iter()
            .chain(args.iter().copied())
            .collect();
        self.run_git(&args, stdin)
    }
}

/// The theorem of the case `arithmetic`.
pub const MUL_MOD: &str = "Krepi.Qualification.Arithmetic.mul_mod_spec";

/// The manifest of a qualification crate that the gate accepts.
pub const CRATE_MANIFEST: &str = "[package]\nname = \"formal-qualification\"\nversion = \"0.0.0\"\n\
    edition = \"2024\"\nlicense = \"MIT\"\npublish = false\n\n[workspace]\n";

/// A Charon stand-in that writes the LLBC file it is asked for.
pub const CHARON: &str = "while [ $# -gt 0 ]; do\n  \
    if [ \"$1\" = --dest-file ]; then : > \"$2\"; fi\n  shift\ndone";

/// The Aeneas stand-in of the fixture at `root`.
fn aeneas(root: &str) -> String {
    format!(
        "while [ $# -gt 0 ]; do\n  \
           case \"$1\" in -subdir) subdir=$2 ;; -dest) dest=$2 ;; esac\n  \
           shift\n\
         done\n\
         shape='{root}/artifacts/shapes/'$(echo \"$subdir\" | tr / .)\n\
         mkdir -p \"$dest/$subdir\"\n\
         if [ -f \"$shape.from\" ]; then\n  \
           cp -R \"$(cat \"$shape.from\")/.\" \"$dest\"\n\
         else\n  \
           : > \"$dest/$subdir/Types.lean\"\n  \
           : > \"$dest/$subdir/Funs.lean\"\n  \
           echo '{{\"functions\": [], \"types\": []}}' > \"$dest/translation.json\"\n\
         fi\n\
         if [ -f \"$shape.log\" ]; then cat \"$shape.log\"; fi\n\
         if [ -f \"$shape.status\" ]; then exit \"$(cat \"$shape.status\")\"; fi"
    )
}

/// The Lake stand-in, whose `@ROOT@` is the root of the fixture. It
/// records each call and keys it: in the stage of the base round by what it
/// runs, `build`, `planned` (a build without `--wfail`), `audit`,
/// `heartbeats` or `leanchecker-<module>`; in the stage of a proof target
/// the audit is `audit` too; elsewhere by the target that it builds, or
/// `Audit`. It runs the script `<key>.sh` of `artifacts/lake` that
/// a test gives, then answers. A build completes. The case audit reports
/// `propext` and `Quot.sound` for each theorem that `Audit.lean` names. The
/// base audit prints, for each own module of `Audit.lean`, its marker and,
/// for each `public theorem` of its file but planned ones, the axioms in
/// `artifacts/lake/axioms/<theorem>` (none without the file, no line when it
/// says `none`), and for every one its line; then for each proved statement
/// the module and whether its theorem has its type: those in
/// `artifacts/lake/statements/<statement>`, else the name without its last
/// component when that file exists, and `true`. A
/// heartbeat copy is counted ten heartbeats per line at each inserted line.
/// `leanchecker` passes, and so does `lake comparator`, keyed `comparator`,
/// whose configuration is its third argument. The range printer
/// `Ranges.lean`, keyed `ranges`, prints for each module that it names a
/// range on the line of each theorem of its file, and their count.
const LAKE: &str = r##"lake='@ROOT@/artifacts/lake'
mkdir -p "$lake"
echo "$PWD $*" >> "$lake/calls"
file=$4
case "$PWD $1 $2 $3" in
  *" env lean Ranges.lean") key=ranges ;;
  */base/stage/*" build "*) key=planned; case " $* " in *" --wfail "*) key=build ;; esac ;;
  */base/stage/*" env lean --json") key=heartbeats ;;
  */base/stage/*" env lean "*) key=audit ;;
  */base/stage/*" env leanchecker "*) key=leanchecker-$4 ;;
  */targets/*" env lean "*) key=audit ;;
  *" comparator --config "*) key=comparator ;;
  *" build "*) for argument; do key=$argument; done ;;
  *) key=Audit ;;
esac
if [ -f "$lake/$key.sh" ]; then . "$lake/$key.sh"; fi
names() { sed -n "s/^  let $1 : Array Name := #\[\(.*\)\]\$/\1/p" Audit.lean | tr -d '`,'; }
path() { echo "$1" | tr . /; }
case $key in
  Audit)
    while read -r first rest; do
      if [ "$first" = '#print' ]; then
        echo "'${rest#axioms }' depends on axioms: [propext, Quot.sound]"
      fi
    done < Audit.lean ;;
  audit)
    planned=" $(names planned) "
    for module in $(names own); do
      echo "krepi-audit module $module"
      grep -n '^public theorem ' "$(path "$module").lean" | while IFS=: read -r line text; do
        name=$module.$(echo "$text" | cut -d ' ' -f 3)
        axioms="$lake/axioms/$name"
        case "$planned" in
          *" $name "*) ;;
          *) if [ ! -f "$axioms" ]; then echo "'$name' does not depend on any axioms"
             elif [ "$(cat "$axioms")" != none ]; then echo "'$name' depends on axioms: [$(cat "$axioms")]"; fi ;;
        esac
        echo "krepi-audit range $name $line"
      done
    done
    pairs=$(sed -n 's/^  for (statement, thm) in (#\[\(.*\)\] : Array (Name × Name)) do$/\1/p' Audit.lean)
    set -- $(echo "$pairs" | tr -d '`(),')
    while [ $# -gt 1 ]; do
      statement=$1 module=${1%.*} exact=true
      shift 2
      if [ ! -f "$(path "$module").lean" ]; then module='[anonymous]'; fi
      if [ -f "$lake/statements/$statement" ]; then read -r module exact < "$lake/statements/$statement"; fi
      echo "krepi-audit statement $statement $module ${exact:-true}"
    done ;;
  heartbeats)
    grep -n '^#count_heartbeats in$' "$file" | while IFS=: read -r line rest; do
      data="Used $((line * 10)) heartbeats, which is less than the current maximum of 200000."
      echo "{\"severity\":\"information\",\"data\":\"$data\",\"pos\":{\"line\":$line,\"column\":0}}"
    done ;;
  leanchecker-*) ;;
  comparator) echo 'Your solution is okay!' ;;
  ranges)
    for module in $(sed -n 's/^#krepi_declaration_ranges //p' Ranges.lean); do
      count=0
      file="$(path "$module").lean"
      for entry in $(grep -n -E '^(public |private )?theorem ' "$file" | sed -E 's/^([0-9]+):(public |private )?theorem ([^ ]+).*/\1:\3/'); do
        echo "krepi-range $module ${entry%%:*} 0 ${entry%%:*} 80 theorem $module.${entry#*:}"
        count=$((count + 1))
      done
      echo "krepi-ranges-module $module $count"
    done ;;
  *) echo 'Build completed successfully (2 jobs).' ;;
esac"##;

/// The stand-in of `lean`, which records each call, runs the script
/// `lean.sh` of `artifacts/lake` that a test gives, and prints what the
/// pinned Lean prints for `--version`.
const LEAN: &str = r##"echo "$PWD lean $*" >> '@ROOT@/artifacts/lake/calls'
if [ -f '@ROOT@/artifacts/lake/lean.sh' ]; then . '@ROOT@/artifacts/lake/lean.sh'; fi
echo '@VERSION@'"##;

/// The directory of the captured shape `shape`.
pub fn captured(shape: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("src/formal/fixtures/extraction")
        .join(shape)
}

/// The text of `cases.json` with `cases`.
pub fn cases_text(cases: &Value) -> String {
    let document = json!({"schema": 1, "cases": cases});
    let mut text = serde_json::to_string_pretty(&document).expect("JSON");
    text.push('\n');
    text
}

/// A case `name` of `module` that expects `expect`, with no items.
pub fn case(name: &str, module: &str, expect: &str) -> Value {
    json!({
        "name": name,
        "module": module,
        "start_from": [format!("crate::{}", name.replace('-', "_"))],
        "expect": expect,
        "diagnostics": [],
        "external_functions": [],
        "external_types": [],
    })
}

/// The case of the captured shape `arithmetic`, with its loop and its
/// theorem.
pub fn arithmetic() -> Value {
    let mut case = case("arithmetic", "Qual.Arithmetic", "translated");
    case["loop_sources"] = json!(["arithmetic.pow_mod_loop src/lib.rs"]);
    case["proof"] = json!({"module": "Krepi.Qualification.Arithmetic", "theorems": [MUL_MOD]});
    case
}

/// The case of the captured shape `shared-pointers`.
pub fn shared_pointers() -> Value {
    let mut case = case("shared-pointers", "Qual.SharedPointers", "translated");
    case["external_functions"] = json!([
        "alloc::sync::{alloc::sync::Arc<T>}::ptr_eq",
        "alloc::sync::{impl core::ops::deref::Deref<T> for alloc::sync::Arc<T>}::deref",
    ]);
    case["external_types"] = json!(["alloc::sync::Arc"]);
    case
}

/// The case of the captured shape `nested-loop`, which Aeneas rejects.
pub fn nested_loop() -> Value {
    let mut case = case("nested-loop", "Qual.NestedLoop", "rejected");
    case["diagnostics"] = json!([
        "[Error] Ignoring the body of 'formal_qualification::nested_loop::charge_grid' because of previous error",
        "[Error] Returns inside of nested loops are not supported yet",
    ]);
    case["external_functions"] = json!(["formal_qualification::nested_loop::charge_grid"]);
    case
}

/// An ill-typed case, whose type error the Lake stand-in prints.
pub fn ill() -> Value {
    let mut case = case("ill", "Qual.Ill", "ill-typed");
    case["type_errors_in"] = json!("Funs.lean");
    case
}

/// A build log of Lake that reports `lines` of the module `module` and
/// fails, with the status `status`.
pub fn failing(module: &str, lines: &[&str], status: i32) -> String {
    let mut script = format!("echo '\u{2716} [2/2] Building {module} (1.6s)'\n");
    for line in lines {
        script.push_str(&format!("echo '{line}'\n"));
    }
    script.push_str(&format!(
        "echo 'Some required targets logged failures:'\necho '- {module}'\n\
         echo 'error: build failed'\nexit {status}\n"
    ));
    script
}

/// A fixture with the qualification `cases`, not committed: the
/// qualification crate, the Lake project files, the extraction
/// configuration, the proof module of `arithmetic`, the stand-ins, and the
/// shapes and Lake scripts of the cases above.
pub fn qualification(label: &str, cases: &Value) -> Fixture {
    let fixture = Fixture::new(label);
    let root = fixture.root().to_str().expect("a UTF-8 path").to_string();
    assert!(!root.contains('\''), "{root}");
    fixture.write(".gitignore", "/artifacts/\n/verification/.lake/\n");
    fixture.write("verification/qualification/Cargo.toml", CRATE_MANIFEST);
    fixture.write("verification/qualification/src/lib.rs", "");
    fixture.write("verification/qualification/cases.json", &cases_text(cases));
    fixture.write(
        "verification/extraction.toml",
        include_str!("../../../verification/extraction.toml"),
    );
    for file in lean::PROJECT_FILES {
        fixture.write(&format!("verification/{file}"), &format!("-- {file}\n"));
    }
    fixture.write(
        "verification/Krepi/Qualification/Arithmetic.lean",
        "module\n",
    );
    fixture.write(
        "artifacts/formal/tools/lean/bin/leanchecker",
        "leanchecker\n",
    );
    fixture.tool("charon", CHARON);
    fixture.tool("aeneas", &aeneas(&root));
    fixture.tool("lake", &LAKE.replace("@ROOT@", &root));
    let version = include_str!("fixtures/base/lean-version.txt")
        .lines()
        .nth(1);
    let lean = LEAN.replace("@VERSION@", version.expect("the version"));
    fixture.tool("lean", &lean.replace("@ROOT@", &root));
    for name in ["arithmetic", "shared-pointers", "nested-loop"] {
        let module = match name {
            "arithmetic" => "Qual.Arithmetic",
            "shared-pointers" => "Qual.SharedPointers",
            _ => "Qual.NestedLoop",
        };
        let key = format!("artifacts/shapes/KrepiGen.{module}");
        let directory = captured(name);
        fixture.write(&format!("{key}.from"), directory.to_str().expect("UTF-8"));
        if name == "nested-loop" {
            let log = fs::read_to_string(directory.join("aeneas.log")).expect("the log");
            fixture.write(&format!("{key}.log"), &log);
            fixture.write(&format!("{key}.status"), "1\n");
        }
    }
    let type_error = "error: KrepiGen/Qual/Ill/Funs.lean:3:8: type mismatch";
    lake_script(
        &fixture,
        "KrepiGen.Qual.Ill.Funs",
        &failing("KrepiGen.Qual.Ill.Funs", &[type_error], 1),
    );
    fixture
}

/// Makes Lake run `script` for the calls of `key`.
pub fn lake_script(fixture: &Fixture, key: &str, script: &str) {
    fixture.write(&format!("artifacts/lake/{key}.sh"), script);
}

/// The conclusion of `unit`.
pub fn status<'a>(done: &'a Done, unit: &str) -> (Status, Option<&'a str>) {
    let entry = &done.receipt.units[unit];
    (entry.status, entry.reason.as_deref())
}

/// The commands of `unit`.
pub fn commands<'a>(done: &'a Done, unit: &str) -> Vec<&'a receipt::Command> {
    (done.receipt.commands.iter())
        .filter(|command| command.unit.as_deref() == Some(unit))
        .collect()
}
