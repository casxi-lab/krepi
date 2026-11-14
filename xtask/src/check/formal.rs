//! The formal step of `cargo xtask check`: `cargo xtask formal check` on the
//! host, then the test vectors in containers of the pinned image with
//! [`GATE_FLAGS`], as the owner of the repository root, which they mount at
//! its path: Lake's version, the replay of [`FIXTURE`], the host tests of the
//! kernel and user-space workspaces, which write their results below an
//! emptied `artifacts/formal/vectors`, and `cargo xtask formal vectors`. A
//! container is named after the check's process and its part and removed
//! before and after it runs, as a stop of the check kills only the client.

use std::fs;
use std::os::unix::fs::MetadataExt;
use std::path::Path;
use std::process::Command;
use std::time::Instant;

use serde_json::Value;

use super::lanes::{Stop, output};
use super::{Cmd, FIXTURE, Facts, GATE_FLAGS, REPLAYED, Status, Supervisor, cargo};
use crate::formal::{Layout, toolchain as tools};

/// The programs that the step runs, xtask, Cargo and Docker, and whether the
/// image runs executables of the host, as on linux-aarch64.
pub(super) struct Programs(pub String, pub String, pub String, pub bool);

/// The formal step with the programs of the host, or skipped with `skip`.
pub fn step(skip: bool) -> Supervisor {
    let xtask = std::env::current_exe().unwrap_or_default();
    let (xtask, cargo) = (xtask.display().to_string(), cargo().display().to_string());
    let host = cfg!(all(target_os = "linux", target_arch = "aarch64"));
    let programs = Programs(xtask, cargo, "docker".into(), host);
    Box::new(move |root, log, stop, facts| match skip {
        true => Status::Skipped("--skip-formal".to_string()),
        false => parts(root, log, stop, &programs, facts)
            .map_or_else(|status| status, |()| Status::Passed),
    })
}

/// Runs the parts of the step in order with their output in `log`, until
/// one does not pass; the image runs what the host builds, so another host
/// and a missing Docker, image or tool of the image are a tool failure.
fn parts(
    root: &Path,
    log: &Path,
    stop: &Stop,
    programs: &Programs,
    facts: &mut Facts,
) -> Result<(), Status> {
    let Programs(xtask, cargo, docker, image_host) = programs;
    let mut fact = |key: &str, value: String| facts.push((key.to_string(), value));
    let words = |text: &str| Vec::from_iter(text.split(' ').map(str::to_string));
    let run = |program: &str, args: Vec<String>, log: &Path, failure: fn(String) -> Status| {
        let program = program.into();
        output(root, &Cmd { program, args }, log, stop, failure)
    };
    run(xtask, words("formal check"), log, Status::Failed)?;
    if !image_host {
        let host = "the formal step runs host-built executables in the image: it needs a \
                    linux-aarch64 host; elsewhere use --skip-formal";
        return Err(Status::ToolFailure(host.to_string()));
    }
    let failed = |detail: String| Err(Status::Failed(detail));
    let pin = fs::read_to_string(root.join(Layout::PRODUCTION.image_pin)).unwrap_or_default();
    let Some((_, image)) = tools::image_pin(&pin) else {
        return failed(format!("{} pins no image", Layout::PRODUCTION.image_pin));
    };
    let owner = fs::metadata(root).map_err(|error| Status::Failed(error.to_string()))?;
    let user = format!("{}:{}", owner.uid(), owner.gid());
    let mut container = words(&format!("{GATE_FLAGS} --user {user} --volume"));
    let path = root.display().to_string();
    container.extend([format!("{path}:{path}"), "--workdir".into(), path]);
    container.push(image.clone());
    fact("image", image);
    let in_image = |part: &str, args: &[&str]| {
        let name = format!("krepi-check-{}-{part}", std::process::id());
        let remove = || Command::new(docker).args(["rm", "--force", &name]).output();
        let _ = remove();
        let mut all = words(&format!("run --rm --name {name}"));
        all.extend(container.iter().cloned());
        all.extend(args.iter().map(|arg| arg.to_string()));
        let ran = run(docker, all, log, Status::ToolFailure);
        let _ = remove();
        ran
    };
    let version = match in_image("probe", &["/opt/krepi-formal/lean/bin/lake", "--version"]) {
        Err(Status::Failed(detail)) => return Err(Status::ToolFailure(detail)),
        probed => probed?,
    };
    fact("lake", version.trim().to_string());
    let build = "test --locked --manifest-path xtask/Cargo.toml --bin xtask --no-run \
                 --message-format=json-render-diagnostics";
    let json = log.with_extension("json");
    let json = run(cargo, words(build), &json, Status::Failed)?;
    let messages = json.lines().flat_map(serde_json::from_str::<Value>);
    let tests = messages.filter(|item| item["profile"]["test"] == true);
    let tests = Vec::from_iter(tests.map(|item| item["executable"].clone()));
    let below = |path: &str| Path::new(path).starts_with(root);
    let wrong = "xtask and exactly one test executable must lie below the root";
    let test = match &tests[..] {
        [Value::String(test)] if below(test) && below(xtask) => test.as_str(),
        _ => return failed(format!("{wrong}: {xtask}, {tests:?}")),
    };
    fact("test executable", test.to_string());
    let replay = [test, "--exact", "--ignored", "--nocapture", FIXTURE];
    let replay = in_image("fixture", &replay)?;
    if !replay.lines().any(|line| line.starts_with(REPLAYED)) {
        return failed(format!("the fixture replay printed no line `{REPLAYED}`"));
    }
    let results = root.join("artifacts/formal/vectors");
    if results.exists() {
        fs::remove_dir_all(&results).map_err(|error| Status::Failed(error.to_string()))?;
    }
    let set = format!("KREPI_VECTOR_RESULTS={}", results.display());
    let started = Instant::now();
    for manifest in ["kernel/Cargo.toml", "user/Cargo.toml"] {
        let mut args = vec![set.clone(), cargo.clone()];
        args.extend(words("test --workspace --locked --manifest-path"));
        args.push(manifest.to_string());
        run("env", args, log, Status::Failed)?;
    }
    let seconds = started.elapsed().as_secs_f64();
    fact("host tests", format!("{seconds:.1} s"));
    let compared = in_image("vectors", &[xtask, "formal", "vectors"])?;
    let counts = compared.lines().rfind(|line| line.ends_with(" problems"));
    fact("vectors", counts.unwrap_or_default().to_string());
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::os::unix::fs::PermissionsExt;
    use std::time::Duration;

    use super::super::lanes::{self, Run};
    use super::super::{Action, Lane, Mode, Options, Step, ci, options, run, steps};
    use super::*;
    use crate::repo::Tree;
    use crate::scratch::Scratch;

    /// The command of the probe in the image.
    const PROBE: &str = "/opt/krepi-formal/lean/bin/lake --version";

    /// What the fake Cargo prints for the build of the test executable of
    /// xtask: an executable that is no test, then the test executable.
    const CARGO: &str = r#"case "$*" in *--no-run*) printf '%s\n' \
        '{"profile":{"test":false},"executable":"ROOT/bin/xtask"}' \
        '{"profile":{"test":true},"executable":"ROOT/bin/tests"}' ;; esac"#;

    /// What the fake Docker prints for the commands of the parts in the image.
    fn docker() -> String {
        format!(
            "case \"$*\" in\n  'run '*' --version') echo 'Lake version 5.0.0-test' ;;\n  \
             'run '*' --nocapture {FIXTURE}') echo '{REPLAYED}; 0 ignored' ;;\n  \
             'run '*' formal vectors') echo '0 components, 0 problems' ;;\nesac"
        )
    }

    /// A repository root in `scratch` with the committed image pin and fakes
    /// of xtask, Cargo and Docker in `bin/` with the shell scripts `bodies`:
    /// each first appends its name, its arguments and the directory of the
    /// host results, when that is set, to `calls`.
    fn fakes(scratch: &Scratch, bodies: [&str; 3]) -> Programs {
        let pin = Layout::PRODUCTION.image_pin;
        let text = fs::read_to_string(crate::repo::root().join(pin)).expect("the pin");
        scratch.write(pin, &text);
        let calls = scratch.0.join("calls").display().to_string();
        let root = scratch.0.display().to_string();
        let [xtask, cargo, docker] = [("xtask", 0), ("cargo", 1), ("docker", 2)].map(|(name, at)| {
            let record = format!(
                "echo \"{name} $*${{KREPI_VECTOR_RESULTS:+ with $KREPI_VECTOR_RESULTS}}\" >> {calls}"
            );
            let body = bodies[at].replace("ROOT", &root);
            scratch.write(&format!("bin/{name}"), &format!("#!/bin/sh\n{record}\n{body}\n"));
            let path = scratch.0.join("bin").join(name);
            let executable = fs::Permissions::from_mode(0o755);
            fs::set_permissions(&path, executable).expect("make the fake executable");
            path.display().to_string()
        });
        Programs(xtask, cargo, docker, true)
    }

    /// The formal step with `programs`.
    fn formal(programs: Programs) -> Step {
        let supervise: Supervisor = Box::new(move |root, log, stop, facts| {
            let ran = parts(root, log, stop, &programs, facts);
            ran.err().unwrap_or(Status::Passed)
        });
        Step {
            name: "formal",
            lane: Lane::Formal,
            action: Action::Supervised(supervise),
        }
    }

    /// The calls that the fakes recorded in `scratch`.
    fn calls(scratch: &Scratch) -> Vec<String> {
        let text = fs::read_to_string(scratch.0.join("calls")).unwrap_or_default();
        Vec::from_iter(text.lines().map(str::to_string))
    }

    /// The calls of Docker for the part `part` that runs `args`: the removal
    /// of its container, its run and the removal again.
    fn in_image(scratch: &Scratch, part: &str, args: &str) -> [String; 3] {
        let pin = fs::read_to_string(scratch.0.join(Layout::PRODUCTION.image_pin));
        let (_, image) = tools::image_pin(&pin.expect("the pin")).expect("the pin reads");
        let owner = fs::metadata(&scratch.0).expect("the root");
        let root = scratch.0.display();
        let name = format!("krepi-check-{}-{part}", std::process::id());
        let remove = format!("docker rm --force {name}");
        let user = format!("{}:{}", owner.uid(), owner.gid());
        let run = format!(
            "docker run --rm --name {name} {GATE_FLAGS} --user {user} --volume {root}:{root} \
             --workdir {root} {image} {args}"
        );
        [remove.clone(), run, remove]
    }

    /// Runs `step` alone in `scratch`, with its log there.
    fn alone(scratch: &Scratch, step: Step) -> Run {
        let logs = scratch.0.join("logs");
        fs::create_dir_all(&logs).expect("create the log directory");
        lanes::run(&scratch.0, &[step], Mode::Sequential, Ok(&logs))
    }

    #[test]
    fn the_formal_step_runs_its_parts_in_order_in_the_pinned_image() {
        let scratch = Scratch::temporary("formal-parts");
        let docker = docker();
        let programs = fakes(&scratch, ["", CARGO, &docker]);
        let stale = scratch.0.join("artifacts/formal/vectors/a/b.results");
        scratch.write("artifacts/formal/vectors/a/b.results", "stale");
        let root = scratch.0.display().to_string();
        let ran = alone(&scratch, formal(programs));
        let outcome = &ran.outcomes[0];
        assert_eq!(outcome.status, Status::Passed, "{outcome:?}");
        assert!(!stale.exists());
        let results = format!("with {root}/artifacts/formal/vectors");
        let tests = |manifest: &str| {
            format!("cargo test --workspace --locked --manifest-path {manifest} {results}")
        };
        let replay = format!("{root}/bin/tests --exact --ignored --nocapture {FIXTURE}");
        let compare = format!("{root}/bin/xtask formal vectors");
        let build = "cargo test --locked --manifest-path xtask/Cargo.toml --bin xtask --no-run \
                     --message-format=json-render-diagnostics";
        let expected = [
            vec!["xtask formal check".to_string()],
            in_image(&scratch, "probe", PROBE).to_vec(),
            vec![build.to_string()],
            in_image(&scratch, "fixture", &replay).to_vec(),
            vec![tests("kernel/Cargo.toml"), tests("user/Cargo.toml")],
            in_image(&scratch, "vectors", &compare).to_vec(),
        ]
        .concat();
        assert_eq!(calls(&scratch), expected);
        let facts = Vec::from_iter(outcome.facts.iter().map(|(key, _)| key.as_str()));
        let keys = ["image", "lake", "test executable", "host tests", "vectors"];
        assert_eq!(facts, keys);
        assert_eq!(outcome.facts[1].1, "Lake version 5.0.0-test");
        assert_eq!(outcome.facts[2].1, format!("{root}/bin/tests"));
        assert!(outcome.facts[3].1.ends_with(" s"), "{:?}", outcome.facts[3]);
        assert_eq!(outcome.facts[4].1, "0 components, 0 problems");
        // The replay passes only with the line of libtest at its start.
        for printed in [
            "",
            "test result: ok. 0 passed; 0 failed",
            &format!("x {REPLAYED}"),
        ] {
            let scratch = Scratch::temporary("formal-replay");
            let fixture = format!("case \"$*\" in *{FIXTURE}) echo '{printed}'; exit ;; esac");
            let docker = format!("{fixture}\n{docker}");
            let ran = alone(&scratch, formal(fakes(&scratch, ["", CARGO, &docker])));
            let detail = format!("the fixture replay printed no line `{REPLAYED}`");
            assert_eq!(ran.outcomes[0].status, Status::Failed(detail), "{printed}");
            assert_eq!(calls(&scratch).len(), 8, "{printed}");
        }
        // Not one test executable.
        let scratch = Scratch::temporary("formal-tests");
        let twice = CARGO.replace("\"test\":false", "\"test\":true");
        let ran = alone(&scratch, formal(fakes(&scratch, ["", &twice, &docker])));
        let Status::Failed(detail) = &ran.outcomes[0].status else {
            panic!("{:?}", ran.outcomes[0]);
        };
        assert!(
            detail.starts_with("xtask and exactly one test executable"),
            "{detail}"
        );
        // A failure of `cargo xtask formal check` ends the step before Docker.
        let scratch = Scratch::temporary("formal-check");
        let ran = alone(
            &scratch,
            formal(fakes(&scratch, ["exit 1", CARGO, &docker])),
        );
        let Status::Failed(detail) = &ran.outcomes[0].status else {
            panic!("{:?}", ran.outcomes[0]);
        };
        assert!(
            detail.ends_with("formal check` exited with exit status: 1"),
            "{detail}"
        );
        assert_eq!(calls(&scratch), ["xtask formal check"]);
    }

    #[test]
    fn the_formal_step_removes_its_container_when_the_check_stops() {
        let scratch = Scratch::temporary("formal-stop");
        // Docker starts the probe and waits; another lane then fails.
        let waits = "[ \"$1\" = run ] && touch started && exec sleep 240";
        let programs = fakes(&scratch, ["", CARGO, waits]);
        let failer = "i=0; while [ ! -f started ] && [ $i -lt 6000 ]; do sleep 0.01; \
                      i=$((i+1)); done; exit 3";
        let cmd = Cmd {
            program: "/bin/sh".into(),
            args: vec!["-c".to_string(), failer.to_string()],
        };
        let steps = [
            formal(programs),
            Step {
                name: "failer",
                lane: Lane::Release,
                action: Action::Commands(vec![cmd]),
            },
        ];
        let logs = scratch.0.join("logs");
        fs::create_dir_all(&logs).expect("create the log directory");
        let ran = lanes::run(&scratch.0, &steps, Mode::Parallel, Ok(&logs));
        let reason = "step failer failed".to_string();
        assert_eq!(ran.outcomes[0].status, Status::Cancelled(reason));
        assert!(ran.outcomes[0].duration < Duration::from_secs(60));
        let probe = in_image(&scratch, "probe", PROBE);
        let expected = [vec!["xtask formal check".to_string()], probe.to_vec()].concat();
        assert_eq!(calls(&scratch), expected);
    }

    /// The receipt that `path` holds.
    fn receipt(path: &Path) -> Value {
        let text = fs::read_to_string(path).expect("the receipt");
        serde_json::from_str(&text).expect("the receipt is JSON")
    }

    #[test]
    fn skip_formal_records_the_formal_step_as_not_run_and_no_workflow_passes_it() {
        let scratch = Scratch::temporary("skip-formal");
        let path = scratch.0.join("receipt.json");
        let line = ["--skip-formal", "--receipt", &path.display().to_string()].map(String::from);
        let options = options(&line.each_ref().map(String::as_str)).expect("the options");
        let steps = steps(options.slow, options.skip_formal);
        let formal = Vec::from_iter(steps.into_iter().filter(|step| step.name == "formal"));
        assert_eq!(run(&scratch.0, &options, &formal), 0);
        let receipt = receipt(&path);
        assert_eq!(receipt["result"], "passed");
        let steps = receipt["steps"].as_array().expect("the steps");
        assert_eq!(steps.len(), 1);
        let step = &steps[0];
        assert_eq!(
            [
                &step["name"],
                &step["lane"],
                &step["status"],
                &step["detail"]
            ],
            ["formal", "formal", "not run", "--skip-formal"]
        );
        assert_eq!(step["offset_ms"], Value::Null);
        // The condition of the step after the check in the workflows: one
        // formal step, which passed.
        let formal = Vec::from_iter(steps.iter().filter(|step| step["name"] == "formal"));
        assert!(!(formal.len() == 1 && formal[0]["status"] == "passed"));
        // No workflow passes the option, in any letter case, not even in a
        // comment.
        let tree = Tree::load(&crate::repo::root()).expect("the tracked files");
        assert_eq!(
            ci::skip_formal_problems(&ci::github(&tree)),
            Vec::<String>::new()
        );
        let comment = [(
            ".github/workflows/a.yml",
            "# cargo xtask check --SKIP-FORMAL\n",
        )];
        assert_eq!(ci::skip_formal_problems(&comment).len(), 1);
    }

    #[test]
    fn a_formal_step_without_docker_the_image_or_its_tools_is_a_tool_failure() {
        let docker = docker();
        let image = format!("[ \"$1\" = run ] && exit 125\n{docker}");
        let lake = format!("case \"$*\" in *' --version') exit 127 ;; esac\n{docker}");
        // Whether the image runs the executables of the host, another Docker
        // than the fake, the fake's script, and whether Docker is reached and
        // removes the container of the probe.
        let cases = [
            ("host", false, None, &docker, false),
            ("docker", true, Some("/nonexistent/docker"), &docker, false),
            ("image", true, None, &image, true),
            ("lake", true, None, &lake, true),
        ];
        for (case, host, other, body, removed) in cases {
            let scratch = Scratch::temporary("formal-tool");
            let mut programs = fakes(&scratch, ["", CARGO, body]);
            programs.3 = host;
            programs.2 = other.map_or(programs.2, str::to_string);
            let shown = in_image(&scratch, "probe", PROBE)[1].replacen("docker", &programs.2, 1);
            let path = scratch.0.join("receipt.json");
            let options = Options {
                sequential: false,
                slow: false,
                skip_formal: false,
                receipt: Some(path.clone()),
            };
            assert_eq!(run(&scratch.0, &options, &[formal(programs)]), 1, "{case}");
            let receipt = receipt(&path);
            assert_eq!(receipt["result"], "failed", "{case}");
            let step = &receipt["steps"][0];
            assert_eq!(step["status"], "tool failure", "{case}");
            let detail = step["detail"].as_str().expect("the detail");
            let expected = match case {
                "host" => "the formal step runs host-built executables in the image: it needs a \
                           linux-aarch64 host; elsewhere use --skip-formal"
                    .to_string(),
                "docker" => format!("cannot run `{shown}`: "),
                "image" => format!("`{shown}` exited with exit status: 125"),
                _ => format!("`{shown}` exited with exit status: 127"),
            };
            assert!(detail.starts_with(&expected), "{case}: {detail}");
            let mut expected = vec!["xtask formal check".to_string()];
            if removed {
                expected.extend(in_image(&scratch, "probe", PROBE));
            }
            assert_eq!(calls(&scratch), expected, "{case}");
        }
    }
}
