//! The binary of `cargo xtask qemu` boots the test image on the QEMU of the
//! host, found on the search path as the command finds it: CI installs QEMU
//! 8.2 from the Ubuntu archive, and `toolchains.toml` names the version of
//! each host. The command's rules are tested in the host tooling crate with
//! fake QEMU executables; this test starts the binary of this build, the one
//! that `cargo xtask` runs, on the real QEMU, and names its output directory
//! below the target's temporary directory.

use serde_json::Value;
use std::path::{Path, PathBuf};
use std::process::Command;

/// The binary of this build.
const XTASK: &str = env!("CARGO_BIN_EXE_xtask");
/// The SHA-256 digest of the test image, from `shasum -a 256` of the file
/// that `krepi_tools::test_elf::write` writes.
const IMAGE_SHA256: &str = "976e92deeebc2bd2eb3c224f570facfef845c2c2adb987ef5960eb1061e7d7a6";
/// The SHA-256 digest of the line that the test image writes, from
/// `shasum -a 256`.
const MESSAGE_SHA256: &str = "66d45e472695370d9d47f8463e4600bde3a9edaa03389b3f2f63befb96cd74cf";
/// The SHA-256 digest of no bytes.
const EMPTY_SHA256: &str = "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855";

/// A directory below the target's temporary directory, removed at its end.
struct Scratch(PathBuf);

impl Scratch {
    #[track_caller]
    fn new(name: &str) -> Self {
        let path = Path::new(env!("CARGO_TARGET_TMPDIR"))
            .join(format!("qemu-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&path);
        std::fs::create_dir_all(&path).unwrap();
        Scratch(path)
    }

    fn join(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Requires a time stamp in the form of the receipts of the host tools,
/// such as `2026-10-14T07:45:17.000123Z`.
#[track_caller]
fn assert_stamp(value: &Value) {
    let stamp = value.as_str().expect("a time stamp");
    assert_eq!(stamp.len(), "2026-10-14T07:45:17.000123Z".len(), "{stamp}");
    assert!(
        stamp.ends_with('Z') && stamp.as_bytes()[10] == b'T',
        "{stamp}"
    );
}

/// The test image writes its line to the PL011 UART and powers the machine
/// off through PSCI: QEMU ends by itself with status 0, the run is a
/// `guest_shutdown` with status 0, the transcript is the line, QEMU writes
/// nothing on its standard error, and the receipt names the image, the QEMU
/// that ran it and its command line. Only a run that fails reaches the
/// timeout.
#[test]
fn the_test_image_runs_until_the_guest_powers_off() {
    let scratch = Scratch::new("image");
    let image = scratch.join("test.elf");
    krepi_tools::test_elf::write(&image).expect("write the test image");
    let output = scratch.join("run");
    let run = Command::new(XTASK)
        .arg("qemu")
        .arg(&image)
        .arg("--output-dir")
        .arg(&output)
        .args(["--timeout", "120"])
        .output()
        .expect("start the xtask binary");
    let stderr = String::from_utf8_lossy(&run.stderr);
    assert_eq!(run.status.code(), Some(0), "{stderr}");
    assert_eq!(stderr, "");
    let summary = std::fs::canonicalize(&output).unwrap().join("summary.json");
    assert_eq!(
        String::from_utf8(run.stdout).unwrap(),
        format!(
            "guest_shutdown: 54 bytes of serial output; the output is not evaluated.\nReceipt: {}\n",
            summary.display()
        )
    );
    assert_eq!(
        std::fs::read(output.join("transcript.bin")).unwrap(),
        b"krepi test image: PL011 output, then PSCI SYSTEM_OFF\r\n"
    );
    assert_eq!(
        std::fs::read(output.join("qemu-stderr.txt")).unwrap(),
        b"",
        "QEMU's standard error"
    );
    let receipt: Value = serde_json::from_str(&std::fs::read_to_string(&summary).unwrap()).unwrap();
    assert_eq!(receipt["schema_version"], 1);
    assert_eq!(receipt["exit_reason"], "guest_shutdown");
    assert_eq!(
        receipt["process"],
        serde_json::json!({
            "exit_code": 0,
            "forced_kill": false,
            "intentional_shutdown": false,
            "signal": null,
        })
    );
    assert_eq!(
        receipt["transcript"],
        serde_json::json!({"bytes": 54, "file": "transcript.bin", "sha256": MESSAGE_SHA256})
    );
    assert_eq!(
        receipt["stderr"],
        serde_json::json!({"bytes": 0, "file": "qemu-stderr.txt", "sha256": EMPTY_SHA256})
    );
    let canonical = std::fs::canonicalize(&image).unwrap();
    let canonical = canonical.to_str().unwrap();
    assert_eq!(
        receipt["image"],
        serde_json::json!({"bytes": 8_760, "path": canonical, "sha256": IMAGE_SHA256})
    );
    let qemu = &receipt["qemu"];
    let version = qemu["version"].as_str().unwrap();
    assert!(
        version.starts_with("QEMU emulator version ") && !version.contains('\n'),
        "{version:?}"
    );
    let executable = qemu["executable"].as_str().unwrap();
    let mut command = vec![
        executable,
        "-accel",
        "tcg,thread=single",
        "-machine",
        "virt-8.2,secure=off,virtualization=off,gic-version=2",
        "-cpu",
        "cortex-a76",
        "-smp",
        "1",
        "-m",
        "128M",
        "-nic",
        "none",
        "-display",
        "none",
        "-serial",
        "stdio",
        "-monitor",
        "none",
        "-kernel",
    ];
    command.push(canonical);
    assert_eq!(qemu["command"], serde_json::json!(command));
    assert!(
        Path::new(executable).is_absolute()
            && executable.ends_with("qemu-system-aarch64")
            && std::fs::canonicalize(executable).unwrap() == Path::new(executable),
        "{executable}"
    );
    assert_eq!(receipt["clock"], "host");
    assert_eq!(receipt["max_bytes"], 262_144);
    assert_eq!(receipt["timeout_seconds"], 120.0);
    assert!(
        receipt["elapsed_seconds"]
            .as_f64()
            .is_some_and(|seconds| seconds >= 0.0)
    );
    assert_stamp(&receipt["started_at"]);
    assert_stamp(&receipt["finished_at"]);
    assert!(receipt.get("errors").is_none(), "{receipt}");
    let mut names: Vec<String> = std::fs::read_dir(&output)
        .unwrap()
        .map(|entry| entry.unwrap().file_name().into_string().unwrap())
        .collect();
    names.sort();
    assert_eq!(names, ["qemu-stderr.txt", "summary.json", "transcript.bin"]);
}
