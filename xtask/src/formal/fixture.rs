//! A Git repository that holds the gate inputs in a minimal form, for the
//! tests of `cargo xtask formal run`: a kernel workspace with one crate and
//! its `Cargo.lock`, a target registry with the target `demo`, the committed
//! tool manifest with the installation at `artifacts/formal/tools`, which
//! holds only scripts that start the Cargo and `rustc` of the build and the
//! fake tools that a test installs, and a file for each other gate input.
//! Commits have a fixed identity and date, and Git reads no system or global
//! configuration.

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::Path;
use std::process::{Command, Stdio};

use super::paths::Git;
use super::toolchain::environment::SYSTEM_PATH;
use crate::scratch::Scratch;

/// The committed tool manifest.
const MANIFEST: &str = include_str!("../../../verification/toolchain.json");

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
            "{\"schema\": 1, \"specifications\": [], \"targets\": [{\"name\": \"demo\"}]}\n",
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
