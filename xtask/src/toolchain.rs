//! The toolchain step: the installed tools match `toolchains.toml`.

use std::collections::BTreeMap;
use std::path::Path;
use std::process::Command;

use toml::{Table, Value};

/// The manifest of exact tool versions, at the repository root.
pub const MANIFEST: &str = "toolchains.toml";
/// The rustup toolchain file, at the repository root.
pub const RUST_TOOLCHAIN: &str = "rust-toolchain.toml";

/// A tool pinned to an exact version and the command that runs it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Tool {
    pub version: String,
    pub command: String,
}

/// The pinned versions for one host.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Column {
    pub rustc: String,
    pub clang: Tool,
    pub lld: Tool,
    pub qemu: Tool,
}

/// The versions found on the host.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Observed {
    pub rustc: String,
    pub clang: String,
    pub lld: String,
    pub qemu: String,
}

/// The manifest section for the host this program runs on.
pub fn host_column() -> Option<&'static str> {
    match (std::env::consts::OS, std::env::consts::ARCH) {
        ("macos", "aarch64") => Some("darwin-arm64"),
        ("linux", "aarch64") => Some("linux-aarch64"),
        _ => None,
    }
}

/// Parses `toolchains.toml` into its sections.
pub fn parse_manifest(text: &str) -> Result<BTreeMap<String, Column>, String> {
    let table: Table = text
        .parse()
        .map_err(|error| format!("{MANIFEST} is not valid TOML: {error}"))?;
    let mut columns = BTreeMap::new();
    for (host, section) in &table {
        let section = section
            .as_table()
            .ok_or_else(|| format!("{MANIFEST}: [{host}] is not a table"))?;
        let rustc = section
            .get("rustc")
            .and_then(Value::as_str)
            .ok_or_else(|| format!("{MANIFEST}: [{host}] has no rustc version"))?
            .to_string();
        let tool = |name: &str| -> Result<Tool, String> {
            let entry = section
                .get(name)
                .and_then(Value::as_table)
                .ok_or_else(|| format!("{MANIFEST}: [{host}] has no {name} entry"))?;
            let field = |key: &str| {
                entry
                    .get(key)
                    .and_then(Value::as_str)
                    .map(str::to_string)
                    .ok_or_else(|| format!("{MANIFEST}: [{host}] {name} has no {key}"))
            };
            Ok(Tool {
                version: field("version")?,
                command: field("command")?,
            })
        };
        let column = Column {
            rustc,
            clang: tool("clang")?,
            lld: tool("lld")?,
            qemu: tool("qemu")?,
        };
        columns.insert(host.clone(), column);
    }
    Ok(columns)
}

/// The channel pinned in `rust-toolchain.toml`.
pub fn pinned_channel(text: &str) -> Result<String, String> {
    let table: Table = text
        .parse()
        .map_err(|error| format!("{RUST_TOOLCHAIN} is not valid TOML: {error}"))?;
    table
        .get("toolchain")
        .and_then(|toolchain| toolchain.get("channel"))
        .and_then(Value::as_str)
        .map(str::to_string)
        .ok_or_else(|| format!("{RUST_TOOLCHAIN} has no toolchain.channel"))
}

/// Every section pins the rustc of `rust-toolchain.toml`.
pub fn check_consistency(columns: &BTreeMap<String, Column>, channel: &str) -> Vec<String> {
    columns
        .iter()
        .filter(|(_, column)| column.rustc != channel)
        .map(|(host, column)| {
            format!(
                "{MANIFEST}: [{host}] pins rustc {}, but {RUST_TOOLCHAIN} pins {channel}",
                column.rustc
            )
        })
        .collect()
}

/// The differences between the pinned and the found versions.
pub fn compare(host: &str, column: &Column, observed: &Observed) -> Vec<String> {
    let pairs = [
        ("rustc", &column.rustc, &observed.rustc),
        ("clang", &column.clang.version, &observed.clang),
        ("lld", &column.lld.version, &observed.lld),
        ("qemu", &column.qemu.version, &observed.qemu),
    ];
    pairs
        .into_iter()
        .filter(|(_, pinned, found)| pinned != found)
        .map(|(tool, pinned, found)| {
            format!("{tool}: {MANIFEST} [{host}] pins {pinned}, found {found}")
        })
        .collect()
}

/// The version number that follows `marker` on the first line of `output`.
pub fn version_after(output: &str, marker: &str) -> Option<String> {
    let line = output.lines().next()?;
    let rest = &line[line.find(marker)? + marker.len()..];
    let version: String = rest
        .trim_start()
        .chars()
        .take_while(|c| c.is_ascii_digit() || *c == '.')
        .collect();
    (!version.is_empty()).then_some(version)
}

/// Runs a command in `dir` and returns its standard output.
fn output_of(dir: &Path, program: &str, args: &[&str]) -> Result<String, String> {
    let output = Command::new(program)
        .args(args)
        .current_dir(dir)
        .output()
        .map_err(|error| format!("cannot run {program}: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "{program} {} failed: {}",
            args.join(" "),
            String::from_utf8_lossy(&output.stderr).trim()
        ));
    }
    Ok(String::from_utf8_lossy(&output.stdout).into_owned())
}

/// Finds the version of each tool of `column` on this host.
fn observe(root: &Path, column: &Column) -> Result<Observed, String> {
    let rustc_version = output_of(root, "rustc", &["--version"])?;
    let rustc = version_after(&rustc_version, "rustc")
        .ok_or_else(|| format!("cannot read the rustc version from `{rustc_version}`"))?;

    let clang_version = output_of(root, &column.clang.command, &["--version"])?;
    let clang = version_after(&clang_version, "clang version")
        .ok_or_else(|| format!("cannot read the Clang version from `{clang_version}`"))?;

    let lld_version = if column.lld.command == "rust-lld" {
        // rust-lld is not on PATH; it ships in the rustc sysroot.
        let sysroot = output_of(root, "rustc", &["--print", "sysroot"])?;
        let verbose = output_of(root, "rustc", &["-vV"])?;
        let host = verbose
            .lines()
            .find_map(|line| line.strip_prefix("host: "))
            .ok_or("rustc -vV does not name the host")?;
        let program = Path::new(sysroot.trim())
            .join("lib/rustlib")
            .join(host)
            .join("bin/rust-lld");
        let program = program.to_string_lossy();
        output_of(root, &program, &["-flavor", "gnu", "--version"])?
    } else {
        output_of(root, &column.lld.command, &["--version"])?
    };
    let lld = version_after(&lld_version, "LLD")
        .ok_or_else(|| format!("cannot read the lld version from `{lld_version}`"))?;

    let qemu_version = output_of(root, &column.qemu.command, &["--version"])?;
    let qemu = version_after(&qemu_version, "version")
        .ok_or_else(|| format!("cannot read the QEMU version from `{qemu_version}`"))?;

    Ok(Observed {
        rustc,
        clang,
        lld,
        qemu,
    })
}

/// The toolchain step.
pub fn run(root: &Path) -> Result<(), String> {
    let read = |name: &str| {
        std::fs::read_to_string(root.join(name))
            .map_err(|error| format!("cannot read {name}: {error}"))
    };
    let columns = parse_manifest(&read(MANIFEST)?)?;
    let channel = pinned_channel(&read(RUST_TOOLCHAIN)?)?;
    let mut problems = check_consistency(&columns, &channel);
    let host = host_column().ok_or_else(|| {
        format!(
            "{MANIFEST} has no section for {}-{}",
            std::env::consts::OS,
            std::env::consts::ARCH
        )
    })?;
    let column = columns
        .get(host)
        .ok_or_else(|| format!("{MANIFEST} has no [{host}] section"))?;
    let observed = observe(root, column)?;
    problems.extend(compare(host, column, &observed));
    if problems.is_empty() {
        println!(
            "toolchain [{host}]: rustc {}, clang {}, lld {}, qemu {}",
            observed.rustc, observed.clang, observed.lld, observed.qemu
        );
        Ok(())
    } else {
        Err(problems.join("\n"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn repository_manifest() -> BTreeMap<String, Column> {
        parse_manifest(include_str!("../../toolchains.toml")).expect("the manifest parses")
    }

    fn matching(column: &Column) -> Observed {
        Observed {
            rustc: column.rustc.clone(),
            clang: column.clang.version.clone(),
            lld: column.lld.version.clone(),
            qemu: column.qemu.version.clone(),
        }
    }

    #[test]
    fn manifest_has_both_hosts_and_the_pinned_rustc() {
        let columns = repository_manifest();
        let hosts: Vec<&str> = columns.keys().map(String::as_str).collect();
        assert_eq!(hosts, ["darwin-arm64", "linux-aarch64"]);
        let channel = pinned_channel(include_str!("../../rust-toolchain.toml")).unwrap();
        assert_eq!(check_consistency(&columns, &channel), Vec::<String>::new());
    }

    #[test]
    fn matching_versions_pass() {
        for (host, column) in repository_manifest() {
            assert!(compare(&host, &column, &matching(&column)).is_empty());
        }
    }

    #[test]
    fn rejects_a_changed_rustc_version() {
        for (host, column) in repository_manifest() {
            let mut pinned = column.clone();
            pinned.rustc = "1.98.0".to_string();
            let problems = compare(&host, &pinned, &matching(&column));
            assert_eq!(problems.len(), 1, "{problems:?}");
            assert!(problems[0].starts_with("rustc: "), "{problems:?}");
            let mut columns = BTreeMap::new();
            columns.insert(host, pinned);
            assert_eq!(check_consistency(&columns, &column.rustc).len(), 1);
        }
    }

    #[test]
    fn rejects_a_changed_clang_version() {
        for (host, column) in repository_manifest() {
            let mut pinned = column.clone();
            pinned.clang.version = "17.0.0".to_string();
            let problems = compare(&host, &pinned, &matching(&column));
            assert_eq!(problems.len(), 1, "{problems:?}");
            assert!(problems[0].starts_with("clang: "), "{problems:?}");
        }
    }

    #[test]
    fn reads_versions_from_tool_output() {
        assert_eq!(
            version_after("rustc 1.99.0 (b940084d7 2026-09-28)", "rustc").as_deref(),
            Some("1.99.0")
        );
        assert_eq!(
            version_after(
                "Homebrew clang version 23.1.3\nTarget: arm64",
                "clang version"
            )
            .as_deref(),
            Some("23.1.3")
        );
        assert_eq!(
            version_after("Ubuntu clang version 18.1.3 (1ubuntu1)", "clang version").as_deref(),
            Some("18.1.3")
        );
        assert_eq!(
            version_after("LLD 23.1.1 (https://example.invalid 1b9c0d5)", "LLD").as_deref(),
            Some("23.1.1")
        );
        assert_eq!(
            version_after(
                "QEMU emulator version 8.2.2 (Debian 1:8.2.2+ds-0ubuntu1.4)",
                "version"
            )
            .as_deref(),
            Some("8.2.2")
        );
        assert_eq!(version_after("no number here", "version"), None);
    }
}
